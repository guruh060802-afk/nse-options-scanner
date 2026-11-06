#!/usr/bin/env python3
"""
main.py - NSE option-buying scanner. Long calls and long puts only.

Design notes
------------
Two feeds, each doing what it is actually good at:

  * NSE public JSON  - the option chain. It is the canonical source for open
    interest, change in OI, traded volume and per-strike IV, and nothing else
    publishes that for the whole board.
  * Angel One SmartAPI - daily candles for ATR and the EMA stack, and an
    independent last-traded price to cross-check NSE's spot. Yahoo is kept as a
    fallback for candles only. No decision is made from a single feed's price.

A setup is published only if it clears every gate in `gates()`. The filters are
deliberately strict, which means many sessions produce nothing at all. That is
the intended behaviour: silence is a valid output, and a padded list is not.

No win rate is claimed anywhere, and none is implied. The gates rank quality;
they do not predict outcomes. Premium paid on a long option can be lost in full.

Security posture
----------------
  * Credentials come from environment variables only. There is no config-file
    fallback, so nothing can be committed by accident.
  * Every string that reaches a log or a Telegram message passes through
    `scrub()`, which removes any secret substring. This matters because the
    Telegram API carries the bot token in the URL, and requests puts URLs in
    its exception messages - an unscrubbed traceback leaks the token.
  * All outbound calls carry timeouts. No eval, no exec, no shell, no dynamic
    import, no third-party code beyond `requests`.
  * The workflow runs with `contents: read`; the bot has no write access to
    the repository it lives in.
"""

import csv
import datetime
import html
import io
import json
import math
import os
import random
import sys
import time

import requests

# --------------------------------------------------------------------- config
BUDGET_MIN, BUDGET_MAX = 3000, 7000     # rupees of capital per lot
MIN_SESSIONS = 5                        # refuse final-week contracts
MIN_DELTA, MAX_DELTA = 0.25, 0.60
TARGET_DELTA = 0.45
MAX_THETA_PCT = 10.0                    # % of premium per calendar day
MAX_RISK_FRAC = 0.55                    # ATR stop may not exceed this share of premium
MAX_SPREAD_PCT = 5.0
MIN_OI = 500
MIN_VOLUME_INDEX, MIN_VOLUME_STOCK = 500, 100
STRIKE_WINDOW = 0.06
MAX_SETUPS = 2                          # per tier
CORE_MAX_COST = 15000                   # ceiling for the no-budget core tier
MAX_EXPIRIES = 2                        # scan the next two tradeable series
RISK_FREE = 0.065
VIX_BLOCK = 30.0                        # above this, publish nothing new
STOP_ATR_MULT = 0.5
REQUEST_TIMEOUT = 15

INDEX_UNIVERSE = [
    {"symbol": "NIFTY", "label": "NIFTY 50", "token": "99926000",
     "yahoo": "^NSEI"},
    {"symbol": "BANKNIFTY", "label": "Nifty Bank", "token": "99926009",
     "yahoo": "^NSEBANK"},
]
STOCK_WATCHLIST = ["HDFCBANK", "RELIANCE", "SBIN", "ICICIBANK"]

IST = datetime.timezone(datetime.timedelta(hours=5, minutes=30))
UA = ("Mozilla/5.0 (Windows NT 10.0; Win64; x64) AppleWebKit/537.36 "
      "(KHTML, like Gecko) Chrome/128.0.0.0 Safari/537.36")
ANGEL_BASE = "https://apiconnect.angelbroking.com"
MONTH_COL = {1: "JAN", 2: "FEB", 3: "MAR", 4: "APR", 5: "MAY", 6: "JUN",
             7: "JUL", 8: "AUG", 9: "SEP", 10: "OCT", 11: "NOV", 12: "DEC"}

_SECRETS = []


# ------------------------------------------------------------------ utilities
def register_secret(value):
    if value and len(value) >= 6 and value not in _SECRETS:
        _SECRETS.append(value)


def scrub(text):
    """Remove every registered secret from a string. Used on all log output."""
    out = str(text)
    for s in _SECRETS:
        if s in out:
            out = out.replace(s, "***")
    return out


def log(*parts):
    print(scrub(" ".join(str(p) for p in parts)), file=sys.stderr)


def env(name, required=False):
    v = (os.getenv(name) or "").strip()
    if required and not v:
        raise RuntimeError("missing environment variable: %s" % name)
    if v:
        register_secret(v)
    return v


def now_ist():
    return datetime.datetime.now(IST)


def _request(session, method, url, **kw):
    kw.setdefault("timeout", REQUEST_TIMEOUT)
    try:
        return session.request(method, url, **kw)
    except Exception as e:
        log("request failed:", type(e).__name__, scrub(e))
        return None


def backoff(attempt, base=1.0, cap=8.0):
    time.sleep(min(cap, base * (2 ** attempt)) + random.uniform(0, 0.4))


# --------------------------------------------------------------------- Angel
class Angel:
    """SmartAPI client. Candles and spot cross-check. Never used for selection."""

    def __init__(self):
        self.api_key = env("ANGEL_API_KEY")
        self.client_code = env("ANGEL_CLIENT_CODE")
        self.pin = env("ANGEL_PIN")
        self.totp_key = env("ANGEL_TOTP_KEY")
        self.session = requests.Session()
        self.headers = None
        self._tokens = {}

    @property
    def enabled(self):
        return bool(self.api_key and self.client_code and self.pin and self.totp_key)

    def _totp(self):
        import base64
        import hashlib
        import hmac
        import struct
        secret = self.totp_key.replace(" ", "").upper()
        secret += "=" * ((8 - len(secret) % 8) % 8)
        key = base64.b32decode(secret)
        msg = struct.pack(">Q", int(time.time()) // 30)
        h = hmac.new(key, msg, hashlib.sha1).digest()
        o = h[19] & 15
        code = struct.unpack(">I", h[o:o + 4])[0] & 0x7fffffff
        return str(code % 1000000).zfill(6)

    def login(self):
        if not self.enabled:
            log("angel: credentials absent, falling back to NSE + Yahoo")
            return False
        h = {
            "Content-Type": "application/json",
            "Accept": "application/json",
            "X-UserType": "USER",
            "X-SourceID": "WEB",
            "X-ClientLocalIP": "127.0.0.1",
            "X-ClientPublicIP": "127.0.0.1",
            "X-MACAddress": "00:00:00:00:00:00",
            "X-PrivateKey": self.api_key,
        }
        r = _request(self.session, "POST", ANGEL_BASE +
                     "/rest/auth/angelbroking/user/v1/loginByPassword",
                     json={"clientcode": self.client_code,
                           "password": self.pin, "totp": self._totp()}, headers=h)
        if r is None or r.status_code != 200:
            log("angel login: http", getattr(r, "status_code", "n/a"))
            return False
        try:
            body = r.json()
        except ValueError:
            return False
        if body.get("status") is not True:
            log("angel login rejected:", scrub(body.get("message", "")))
            return False
        register_secret(body["data"].get("jwtToken", ""))
        h["Authorization"] = "Bearer " + body["data"]["jwtToken"]
        self.headers = h
        return True

    def token_for(self, symbol, is_index, index_token=None):
        """Resolve a symboltoken. Cached per run."""
        if is_index and index_token:
            return index_token
        key = symbol.upper()
        if key in self._tokens:
            return self._tokens[key]
        if not self.headers:
            return None
        for probe in ("%s-EQ" % key, key):
            r = _request(self.session, "POST", ANGEL_BASE +
                         "/rest/secure/angelbroking/order/v1/searchScrip",
                         json={"exchange": "NSE", "searchscrip": probe},
                         headers=self.headers)
            if r is None or r.status_code != 200:
                continue
            try:
                rows = r.json().get("data") or []
            except ValueError:
                continue
            for row in rows:
                if row.get("tradingsymbol", "").upper() == "%s-EQ" % key:
                    self._tokens[key] = row.get("symboltoken")
                    return self._tokens[key]
        return None

    def candles(self, symbol, is_index, index_token=None, days=140):
        """Daily OHLC candles. Returns [(high, low, close), ...] or []."""
        token = self.token_for(symbol, is_index, index_token)
        if not token or not self.headers:
            return []
        end = now_ist()
        start = end - datetime.timedelta(days=days)
        r = _request(self.session, "POST", ANGEL_BASE +
                     "/rest/secure/angelbroking/historical/v1/getCandleData",
                     json={"exchange": "NSE", "symboltoken": token,
                           "interval": "ONE_DAY",
                           "fromdate": start.strftime("%Y-%m-%d 09:15"),
                           "todate": end.strftime("%Y-%m-%d %H:%M")},
                     headers=self.headers)
        if r is None or r.status_code != 200:
            return []
        try:
            rows = r.json().get("data") or []
        except ValueError:
            return []
        out = []
        for row in rows:
            try:
                out.append((float(row[2]), float(row[3]), float(row[4])))
            except (IndexError, TypeError, ValueError):
                continue
        return out

    def ltp(self, symbol, is_index, index_token=None, label=None):
        token = self.token_for(symbol, is_index, index_token)
        if not token or not self.headers:
            return None
        name = label or ("%s-EQ" % symbol.upper())
        r = _request(self.session, "POST", ANGEL_BASE +
                     "/rest/secure/angelbroking/order/v1/getLtpData",
                     json={"exchange": "NSE", "tradingsymbol": name,
                           "symboltoken": token}, headers=self.headers)
        if r is None or r.status_code != 200:
            return None
        try:
            body = r.json()
        except ValueError:
            return None
        if body.get("status") is True:
            try:
                return float(body["data"]["ltp"])
            except (KeyError, TypeError, ValueError):
                return None
        return None


# ----------------------------------------------------------------------- NSE
class NSE:
    def __init__(self):
        self.session = requests.Session()
        self.session.headers.update({
            "User-Agent": UA,
            "Accept": "text/html,application/xhtml+xml,application/xml;q=0.9,*/*;q=0.8",
            "Accept-Language": "en-US,en;q=0.9",
            "Connection": "keep-alive",
        })
        self.warm = False

    def warmup(self):
        if self.warm:
            return
        for attempt in range(3):
            r = _request(self.session, "GET", "https://www.nseindia.com/option-chain")
            if r is not None and r.status_code == 200:
                self.warm = True
                time.sleep(1.0)
                return
            backoff(attempt)
        log("nse: warmup did not return 200, continuing anyway")

    def json(self, url, referer="https://www.nseindia.com/option-chain"):
        self.warmup()
        for attempt in range(3):
            r = _request(self.session, "GET", url, headers={
                "Referer": referer,
                "Accept": "application/json, text/plain, */*"})
            if r is not None and r.status_code == 200:
                try:
                    return r.json()
                except ValueError:
                    pass
            backoff(attempt)
        return None

    def vix(self):
        d = self.json("https://www.nseindia.com/api/allIndices",
                      referer="https://www.nseindia.com/market-data/live-market-indices")
        if not d:
            return None
        for row in d.get("data", []):
            if str(row.get("index", "")).upper().startswith("INDIA VIX"):
                try:
                    return float(row["last"])
                except (KeyError, TypeError, ValueError):
                    return None
        return None

    def expiries(self, symbol, is_index):
        """Tradeable series worth scanning: the nearest with enough time, plus the next."""
        kind = "Indices" if is_index else "Equity"
        info = self.json("https://www.nseindia.com/api/option-chain-contract-info"
                         "?type=%s&symbol=%s" % (kind, symbol))
        if not info or not info.get("expiryDates"):
            return []
        out = []
        for e in info["expiryDates"]:
            n = sessions_left(e)
            if n >= MIN_SESSIONS:
                out.append((e, n))
            if len(out) >= MAX_EXPIRIES:
                break
        return out

    def chain(self, symbol, is_index, expiry):
        kind = "Indices" if is_index else "Equity"
        data = self.json("https://www.nseindia.com/api/option-chain-v3"
                         "?type=%s&symbol=%s&expiry=%s" % (kind, symbol, expiry))
        if not data or "records" not in data:
            return None
        return data["records"]

    def lot_file(self):
        for attempt in range(3):
            r = _request(self.session, "GET",
                         "https://nsearchives.nseindia.com/content/fo/fo_mktlots.csv",
                         headers={"User-Agent": UA})
            if r is not None and r.status_code == 200:
                text = r.content.decode("utf-8-sig", "ignore")
                reader = csv.reader(io.StringIO(text))
                try:
                    header = [c.strip() for c in next(reader)]
                except StopIteration:
                    return None
                rows = [dict(zip(header, [c.strip() for c in x]))
                        for x in reader if any(c.strip() for c in x)]
                return {"header": header, "rows": rows}
            backoff(attempt)
        return None


# ------------------------------------------------------------------- candles
def yahoo_candles(ticker):
    if not ticker:
        return []
    s = requests.Session()
    r = _request(s, "GET",
                 "https://query1.finance.yahoo.com/v8/finance/chart/" + ticker,
                 params={"interval": "1d", "range": "6mo"},
                 headers={"User-Agent": UA})
    if r is None or r.status_code != 200:
        return []
    try:
        q = r.json()["chart"]["result"][0]["indicators"]["quote"][0]
    except (KeyError, IndexError, TypeError, ValueError):
        return []
    out = []
    for h, l, c in zip(q.get("high") or [], q.get("low") or [], q.get("close") or []):
        if None in (h, l, c):
            continue
        out.append((float(h), float(l), float(c)))
    return out


def indicators(rows, atr_period=14, ema_fast=20, ema_slow=50):
    """Wilder ATR and the EMA stack, from completed daily candles."""
    if len(rows) < max(atr_period + 2, ema_slow + 2):
        return None
    trs = []
    for i in range(1, len(rows)):
        h, l, _ = rows[i]
        pc = rows[i - 1][2]
        trs.append(max(h - l, abs(h - pc), abs(l - pc)))
    atr = sum(trs[:atr_period]) / atr_period
    for t in trs[atr_period:]:
        atr = (atr * (atr_period - 1) + t) / atr_period
    closes = [r[2] for r in rows]

    def ema(period):
        k = 2.0 / (period + 1.0)
        v = sum(closes[:period]) / period
        for c in closes[period:]:
            v = c * k + v * (1 - k)
        return v

    return {"atr": round(atr, 2), "ema_fast": round(ema(ema_fast), 2),
            "ema_slow": round(ema(ema_slow), 2),
            "last_close": round(closes[-1], 2), "bars": len(rows)}


# -------------------------------------------------------------------- greeks
def _ncdf(x):
    return 0.5 * (1.0 + math.erf(x / math.sqrt(2.0)))


def _npdf(x):
    return math.exp(-0.5 * x * x) / math.sqrt(2.0 * math.pi)


def greeks(spot, strike, years, iv_pct, side):
    """Black-Scholes. iv_pct is NSE's impliedVolatility, quoted in per cent."""
    if not spot or not strike or years <= 0 or not iv_pct or iv_pct <= 0:
        return None
    sig = iv_pct / 100.0
    root_t = math.sqrt(years)
    d1 = (math.log(spot / strike) + (RISK_FREE + 0.5 * sig * sig) * years) / (sig * root_t)
    d2 = d1 - sig * root_t
    disc = math.exp(-RISK_FREE * years)
    decay = -spot * _npdf(d1) * sig / (2 * root_t)
    if side == "CE":
        delta = _ncdf(d1)
        theta = decay - RISK_FREE * strike * disc * _ncdf(d2)
    else:
        delta = _ncdf(d1) - 1.0
        theta = decay + RISK_FREE * strike * disc * _ncdf(-d2)
    return {"delta": round(delta, 4), "theta": round(theta / 365.0, 4),
            "iv": round(iv_pct, 2)}


# -------------------------------------------------------------------- levels
def build_levels(entry, atr, delta, theta, sessions):
    """Stop from ATR through delta; targets from an achievable move. R:R is an output."""
    d = abs(delta)
    if entry <= 0 or atr <= 0 or d <= 0:
        return None
    risk = STOP_ATR_MULT * atr * d
    if risk > entry * MAX_RISK_FRAC:
        return None
    out = {"entry": round(entry, 2), "risk": round(risk, 2),
           "sl": round(entry - risk, 2)}
    for name, mult in (("t1", 0.5), ("t2", 1.0)):
        move = mult * atr * math.sqrt(max(sessions, 1))
        gain = d * move - abs(theta) * sessions
        out[name] = round(entry + gain, 2)
        out[name + "_rr"] = round(gain / risk, 2)
        out[name + "_move"] = round(move, 1)
    return out


# --------------------------------------------------------------------- gates
def gates(c):
    """Every reason this contract is not publishable. Empty list means it passes."""
    bad = []
    if c["lot"] is None:
        bad.append("lot size unresolved")
    if c["cost"] is None or c["cost"] > CORE_MAX_COST:
        bad.append("cost Rs %s above the Rs %d core ceiling" % (c["cost"], CORE_MAX_COST))
    if not (MIN_DELTA <= abs(c["delta"]) <= MAX_DELTA):
        bad.append("delta %.3f outside %.2f-%.2f" % (abs(c["delta"]), MIN_DELTA, MAX_DELTA))
    if c["premium"] > 0 and abs(c["theta"]) / c["premium"] * 100 > MAX_THETA_PCT:
        bad.append("theta %.1f%% of premium per day" % (abs(c["theta"]) / c["premium"] * 100))
    if c["spread_pct"] > MAX_SPREAD_PCT:
        bad.append("spread %.2f%%" % c["spread_pct"])
    if c["oi"] < MIN_OI:
        bad.append("OI %d below %d" % (c["oi"], MIN_OI))
    if c["volume"] < c["min_volume"]:
        bad.append("volume %d" % c["volume"])
    if c["sessions"] < MIN_SESSIONS:
        bad.append("only %d sessions left" % c["sessions"])
    if not c["trend_ok"]:
        bad.append("EMA stack against %s" % c["side"])
    if not (c["chg_oi_own"] > 0 and c["chg_oi_opp"] <= 0):
        bad.append("chain does not confirm %s (own dOI %+d, opposite %+d)"
                   % (c["side"], c["chg_oi_own"], c["chg_oi_opp"]))
    if c["bid_qty"] < c["lot"] or c["ask_qty"] < c["lot"]:
        bad.append("depth %d/%d below one lot" % (c["bid_qty"], c["ask_qty"]))
    return bad


BLOCKER_LABELS = ("lot size", "cost", "delta", "theta", "spread", "OI",
                  "volume", "sessions", "EMA stack", "chain", "depth",
                  "risk-reward", "only")


def blocker_key(reason):
    """Collapse a gate message to a stable short label for tallying."""
    low = reason.lower()
    for label in BLOCKER_LABELS:
        if low.startswith(label.lower()):
            return "sessions" if label == "only" else label
    return reason.split()[0]


def score(c):
    """Composite quality score, 0-1. Ranking only; it is not a probability."""
    delta_fit = max(0.0, 1.0 - abs(abs(c["delta"]) - TARGET_DELTA) / 0.35)
    spread_fit = max(0.0, 1.0 - c["spread_pct"] / MAX_SPREAD_PCT)
    liq = min(1.0, c["volume"] / float(max(c["min_volume"], 1) * 8))
    denom = abs(c["chg_oi_own"]) + abs(c["chg_oi_opp"])
    oi_fit = c["chg_oi_own"] / denom if denom else 0.0
    return round(0.30 * delta_fit + 0.25 * liq + 0.20 * spread_fit + 0.25 * oi_fit, 4)


# ------------------------------------------------------------------ calendar
def sessions_left(expiry):
    """Weekday sessions from now to expiry, inclusive. Today counts before 15:30 IST."""
    try:
        exp = datetime.datetime.strptime(expiry, "%d-%b-%Y").date()
    except (ValueError, TypeError):
        return 0
    now = now_ist()
    cur = now.date() if now.time() < datetime.time(15, 30) else now.date() + datetime.timedelta(days=1)
    n = 0
    while cur <= exp:
        if cur.weekday() < 5:
            n += 1
        cur += datetime.timedelta(days=1)
    return n


def pick_expiry(expiry_dates):
    for e in expiry_dates:
        n = sessions_left(e)
        if n >= MIN_SESSIONS:
            return e, n
    if expiry_dates:
        return expiry_dates[0], sessions_left(expiry_dates[0])
    return None, 0


def expiry_column(expiry):
    try:
        dt = datetime.datetime.strptime(expiry, "%d-%b-%Y")
    except (ValueError, TypeError):
        return None
    return "%s-%s" % (MONTH_COL[dt.month], dt.strftime("%y"))


def lot_for(symbol, expiry, lot_file):
    if not lot_file:
        return None, "lot file unavailable"
    col = expiry_column(expiry)
    if col is None:
        return None, "unparseable expiry %s" % expiry
    if col not in lot_file["header"]:
        return None, "no %s column in lot file" % col
    for row in lot_file["rows"]:
        if row.get("SYMBOL") == symbol:
            v = row.get(col, "").strip()
            if v.isdigit():
                return int(v), "NSE fo_mktlots.csv %s" % col
            return None, "blank %s lot" % col
    return None, "%s not in lot file" % symbol


# ---------------------------------------------------------------------- scan
def scan(nse, angel, lot_file, symbol, is_index, meta):
    """Scan the next two tradeable series. Returns (contexts, setups, notes)."""
    notes = []
    expiries = nse.expiries(symbol, is_index)
    if not expiries:
        return [], [], ["%s: no tradeable expiry with %d+ sessions" % (symbol, MIN_SESSIONS)]

    lot_note = ""
    lot = None
    candles = []
    ind = None
    source = "unavailable"
    if angel:
        candles = angel.candles(symbol, is_index, meta.get("token")) or []
        source = "Angel One"
    if len(candles) < 60:
        ticker = (meta.get("yahoo") if is_index else symbol + ".NS") or symbol
        candles = yahoo_candles(ticker)
        source = "Yahoo fallback"
    ind = indicators(candles)
    if ind is None:
        notes.append("%s: no usable candles, technicals skipped" % symbol)

    contexts, setups = [], []
    for expiry, sessions in expiries:
        rec = nse.chain(symbol, is_index, expiry)
        if not rec:
            notes.append("%s %s: chain unavailable" % (symbol, expiry))
            continue
        spot = float(rec.get("underlyingValue") or 0)
        rows = rec.get("data") or []
        if not spot or not rows:
            notes.append("%s %s: empty chain" % (symbol, expiry))
            continue

        lot, lot_note = lot_for(symbol, expiry, lot_file)
        if lot is None:
            notes.append("%s: %s" % (symbol, lot_note))

        xcheck = None
        if angel:
            a = angel.ltp(symbol, is_index, meta.get("token"),
                          label=meta.get("label") if is_index else None)
            if a:
                xcheck = round((a / spot - 1) * 100, 3)

        try:
            exp_dt = datetime.datetime.strptime(expiry, "%d-%b-%Y").replace(
                hour=15, minute=30, tzinfo=IST)
            years = max((exp_dt - now_ist()).total_seconds(), 0) / (365 * 24 * 3600)
        except ValueError:
            years = 0

        tot_ce = tot_pe = 0
        for row in rows:
            for side in ("CE", "PE"):
                if side in row:
                    oi = row[side].get("openInterest", 0) or 0
                    if side == "CE":
                        tot_ce += oi
                    else:
                        tot_pe += oi

        passing, rejected, blockers = [], 0, {}
        for row in rows:
            strike = row.get("strikePrice")
            if not strike or abs(strike - spot) / spot > STRIKE_WINDOW:
                continue
            for side in ("CE", "PE"):
                if side not in row or lot is None:
                    continue
                o = row[side]
                premium = float(o.get("lastPrice") or 0)
                bid = float(o.get("buyPrice1") or 0)
                ask = float(o.get("sellPrice1") or 0)
                if premium <= 0 or bid <= 0 or ask <= 0 or ask < bid:
                    continue
                g = greeks(spot, strike, years,
                           float(o.get("impliedVolatility") or 0), side)
                if not g:
                    continue
                trend_ok = False
                if ind:
                    if side == "CE":
                        trend_ok = spot > ind["ema_fast"] and spot > ind["ema_slow"]
                    else:
                        trend_ok = spot < ind["ema_fast"] and spot < ind["ema_slow"]
                opp = row.get("PE" if side == "CE" else "CE", {})
                c = {
                    "symbol": symbol, "side": side, "strike": strike,
                    "expiry": expiry, "sessions": sessions, "spot": spot,
                    "premium": premium, "lot": lot,
                    "cost": round(premium * lot, 2),
                    "spread_pct": round((ask - bid) / premium * 100, 2),
                    "oi": int(o.get("openInterest") or 0),
                    "chg_oi_own": int(o.get("changeinOpenInterest") or 0),
                    "chg_oi_opp": int(opp.get("changeinOpenInterest") or 0),
                    "volume": int(o.get("totalTradedVolume") or 0),
                    "bid_qty": int(o.get("totalBuyQuantity") or 0),
                    "ask_qty": int(o.get("totalSellQuantity") or 0),
                    "min_volume": MIN_VOLUME_INDEX if is_index else MIN_VOLUME_STOCK,
                    "trend_ok": trend_ok, "delta": g["delta"],
                    "theta": g["theta"], "iv": g["iv"],
                }
                bad = gates(c)
                if bad:
                    rejected += 1
                    for reason in bad:
                        key = blocker_key(reason)
                        blockers[key] = blockers.get(key, 0) + 1
                    continue
                lv = build_levels(premium, (ind or {}).get("atr") or 0,
                                  g["delta"], g["theta"], sessions)
                if not lv:
                    rejected += 1
                    continue
                if lv["t1_rr"] < 1.0:
                    rejected += 1
                    continue
                c["levels"] = lv
                c["score"] = score(c)
                c["tier"] = ("budget" if BUDGET_MIN <= c["cost"] <= BUDGET_MAX
                             else "core")
                passing.append(c)

        contexts.append({
            "symbol": symbol, "spot": spot, "stamp": rec.get("timestamp", ""),
            "expiry": expiry, "sessions": sessions, "lot": lot,
            "lot_note": lot_note,
            "pcr": round(tot_pe / tot_ce, 2) if tot_ce else 0.0,
            "resistance": top_strike(rows, "CE"),
            "support": top_strike(rows, "PE", exclude=top_strike(rows, "CE")),
            "atr": (ind or {}).get("atr"), "ema_fast": (ind or {}).get("ema_fast"),
            "ema_slow": (ind or {}).get("ema_slow"), "candle_source": source,
            "bars": (ind or {}).get("bars"), "angel_xcheck_pct": xcheck,
            "scanned": len(passing) + rejected, "rejected": rejected,
            "blockers": sorted(blockers.items(), key=lambda kv: -kv[1])[:3],
        })
        setups += passing

    return contexts, setups, notes


def top_strike(rows, side, exclude=None):
    """Highest-OI strike on a side. `exclude` avoids printing the same level twice."""
    ranked = []
    for row in rows:
        if side in row:
            oi = row[side].get("openInterest", 0) or 0
            strike = row.get("strikePrice")
            if oi > 0 and strike:
                ranked.append((oi, strike))
    ranked.sort(reverse=True)
    for _, strike in ranked:
        if strike != exclude:
            return strike
    return ranked[0][1] if ranked else None


# ------------------------------------------------------------------ telegram
def esc(x):
    return html.escape(str(x), quote=False)


def chunk(text, limit=3800):
    if len(text) <= limit:
        return [text]
    parts, buf = [], ""
    for line in text.split("\n"):
        while len(line) > limit:
            if buf:
                parts.append(buf)
                buf = ""
            parts.append(line[:limit])
            line = line[limit:]
        if len(buf) + len(line) + 1 > limit:
            parts.append(buf)
            buf = line
        else:
            buf = buf + "\n" + line if buf else line
    if buf:
        parts.append(buf)
    return parts


def telegram(token, chat_id, text):
    if not token or not chat_id:
        log("telegram: credentials absent, printing only")
        return False
    ok = True
    for part in chunk(text):
        sent = False
        for attempt in range(3):
            r = _request(requests.Session(), "POST",
                         "https://api.telegram.org/bot%s/sendMessage" % token,
                         json={"chat_id": chat_id, "text": part,
                               "parse_mode": "HTML",
                               "disable_web_page_preview": True})
            if r is not None and r.status_code == 200:
                sent = True
                break
            log("telegram: attempt %d failed (%s)"
                % (attempt + 1, getattr(r, "status_code", "no response")))
            backoff(attempt)
        ok = ok and sent
    return ok


# ------------------------------------------------------------------- message
def render(results, budget, core, notes, vix, blocked):
    now = now_ist()
    lines = ["<b>NSE option-buying scan</b>  %s" % now.strftime("%d-%b-%Y %H:%M IST")]
    if vix is not None:
        lines.append("India VIX %s" % vix)

    by_symbol = {}
    for r in results:
        by_symbol.setdefault(r["context"]["symbol"], []).append(r["context"])

    for symbol, ctxs in by_symbol.items():
        head = ctxs[0]
        expiries = " + ".join("%s (%d)" % (c["expiry"], c["sessions"]) for c in ctxs)
        scanned = sum(c["scanned"] for c in ctxs)
        passed = sum(c["scanned"] - c["rejected"] for c in ctxs)
        lines.append("")
        lines.append("<b>%s</b> %s   PCR %s   S %s / R %s"
                     % (esc(symbol), esc("{:,.2f}".format(head["spot"])),
                        head["pcr"], head["support"], head["resistance"]))
        lines.append("  %s | lot %s | ATR %s | %s | scanned %d, passed %d"
                     % (esc(expiries), head["lot"], head["atr"],
                        esc(head["candle_source"]), scanned, passed))
        if head["angel_xcheck_pct"] is not None:
            lines.append("  Angel vs NSE spot %+.3f%% | chain %s"
                         % (head["angel_xcheck_pct"], esc(head["stamp"])))
        if not passed:
            agg = {}
            for c in ctxs:
                for key, n in c.get("blockers", []):
                    agg[key] = agg.get(key, 0) + n
            if agg:
                top = sorted(agg.items(), key=lambda kv: -kv[1])[:3]
                lines.append("  blocked by: %s"
                             % ", ".join("%s %d" % (k, v) for k, v in top))

    def block(title, rows):
        if not rows:
            return
        lines.append("")
        lines.append("<b>%s</b>" % title)
        for s in rows:
            lv = s["levels"]
            lines.append("")
            lines.append("<b>%s %d %s</b>  %s, %d sessions"
                         % (esc(s["symbol"]), s["strike"], s["side"],
                            esc(s["expiry"]), s["sessions"]))
            lines.append("Entry %s | SL %s | T1 %s (%.2fR) | T2 %s (%.2fR)"
                         % (lv["entry"], lv["sl"], lv["t1"], lv["t1_rr"],
                            lv["t2"], lv["t2_rr"]))
            lines.append("Cost Rs %s = %s x %d | risk Rs %s per lot"
                         % (int(s["cost"]), s["premium"], s["lot"],
                            int(round(lv["risk"] * s["lot"]))))
            lines.append("delta %.3f | theta %.2f/day | IV %.1f | spread %.2f%%"
                         % (s["delta"], s["theta"], s["iv"], s["spread_pct"]))
            lines.append("OI %s | dOI %+d | vol %s | score %.2f"
                         % ("{:,}".format(s["oi"]), s["chg_oi_own"],
                            "{:,}".format(s["volume"]), s["score"]))

    if blocked:
        lines.append("")
        lines.append("<b>No setups published.</b> %s" % esc(blocked))
    else:
        block("Budget tier  Rs %d-%d per lot" % (BUDGET_MIN, BUDGET_MAX), budget)
        block("Core tier  above budget, under Rs %d" % CORE_MAX_COST, core)
        if not budget and not core:
            lines.append("")
            lines.append("<b>No qualifying setup today.</b> Nothing cleared every "
                         "gate. The blockers above are the reason.")

    if notes:
        lines.append("")
        lines.append("<i>%s</i>" % esc("; ".join(notes)))
    return "\n".join(lines)


# ---------------------------------------------------------------------- main
def main():
    dry = (os.getenv("DRY_RUN") or "").strip().lower() in ("1", "true", "yes")
    token = env("TG_BOT_TOKEN")
    chat_id = env("TG_CHAT_ID")
    if chat_id and not chat_id.lstrip("-").isdigit():
        raise RuntimeError("TG_CHAT_ID must be numeric")

    angel = Angel()
    angel_ok = angel.login()
    nse = NSE()
    lot_file = nse.lot_file()
    vix = nse.vix()

    results, setups, notes = [], [], []
    meta = {i["symbol"]: i for i in INDEX_UNIVERSE}

    for item in INDEX_UNIVERSE:
        ctxs, found, note = scan(nse, angel if angel_ok else None, lot_file,
                                 item["symbol"], True, item)
        notes += note
        if not ctxs:
            notes.append("%s not scanned" % item["symbol"])
        results += [{"context": c} for c in ctxs]
        setups += found

    for symbol in STOCK_WATCHLIST:
        ctxs, found, note = scan(nse, angel if angel_ok else None, lot_file,
                                 symbol, False, {})
        notes += note
        if not ctxs:
            notes.append("%s not scanned" % symbol)
        results += [{"context": c} for c in ctxs]
        setups += found

    blocked = None
    if not results:
        blocked = ("No option chain could be retrieved from NSE, so nothing is "
                   "being published. This is a feed failure, not an empty scan.")
    elif vix is not None and vix > VIX_BLOCK:
        blocked = ("India VIX is above %.0f. New positional long-premium entries "
                   "are suppressed at this volatility." % VIX_BLOCK)
        setups = []

    setups.sort(key=lambda s: s["score"], reverse=True)
    budget = [s for s in setups if s["tier"] == "budget"][:MAX_SETUPS]
    core = [s for s in setups if s["tier"] == "core"][:MAX_SETUPS]

    text = render(results, budget, core, notes, vix, blocked)
    print(text)
    if not dry:
        telegram(token, chat_id, text)
    else:
        log("dry run: nothing sent")


if __name__ == "__main__":
    main()
