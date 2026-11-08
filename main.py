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

import threading
import urllib.parse

import requests

# --------------------------------------------------------------------- config
BUDGET_MIN, BUDGET_MAX = 3000, 7000     # rupees of capital per lot
MIN_SESSIONS = 5                        # refuse final-week contracts
MIN_DELTA, MAX_DELTA = 0.25, 0.60
BUDGET_MIN_DELTA = 0.20                 # cheap contracts sit further out; relax only here
TARGET_DELTA = 0.45
MAX_THETA_PCT = 10.0                    # % of premium per calendar day
T1_R, T2_R = 4.0, 6.0                   # target multiples the backtest supported
MOVE_BUDGET = 0.75                      # required move must sit inside 0.75 x ATR x sqrt(sessions)
MIN_DTE, MAX_DTE = 31, 60               # the only expiry band with positive expectancy
WIDE_DTE, WIDE_MAX_DTE = 21, 90         # fallback band when nothing sits in the above
MAX_RISK_FRAC = 0.55                    # ATR stop may not exceed this share of premium
IV_RV_MAX = 1.05                        # pay no more than 5% over realised volatility
MAX_SPREAD_PCT = 5.0                    # widened back: pre-open quotes are stale and look wide
MIN_OI = 100
MIN_VOLUME_INDEX, MIN_VOLUME_STOCK = 500, 100
STRIKE_WINDOW = 0.06
MAX_SETUPS = 2                          # per tier
EXPANSION_REF = 1.5                     # today's range vs its 20-day average
SCAN_WORKERS = 4                        # NSE throttles hard above this
SCAN_SECONDS = 420                      # hard budget; publish what finished
MIN_DTE_BUDGET = 8                      # budget tier cannot reach 31-60 days

# Measured on NSE F&O bhavcopy, Jan-2025 to Nov-2026. These are historical
# base rates for the filter combination, NOT predictions for any single trade.
HIT_CORE = (18.7, 1378)
HIT_BUDGET = (15.0, 4882)
CORE_MAX_COST = 20000                   # ceiling for the no-budget core tier
MAX_EXPIRIES = 2                        # scan up to two series inside the band
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
# Fallback only - the live universe is read from NSE's own lot file.
STOCK_WATCHLIST = ["HDFCBANK", "RELIANCE", "SBIN", "ICICIBANK"]
INDEX_NAMES = {"NIFTY", "BANKNIFTY", "FINNIFTY", "MIDCPNIFTY", "NIFTYNXT50"}

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
        self._lock = threading.Lock()   # SmartAPI allows 3 req/s; serialise

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
        with self._lock:
            token = self.token_for(symbol, is_index, index_token)
        if not token or not self.headers:
            return []
        end = now_ist()
        start = end - datetime.timedelta(days=days)
        with self._lock:
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
        with self._lock:
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
        """(all dates, core picks, band). The raw list lets the budget tier reach nearer series."""
        kind = "Indices" if is_index else "Equity"
        info = self.json("https://www.nseindia.com/api/option-chain-contract-info"
                         "?type=%s&symbol=%s" % (kind, urllib.parse.quote(symbol, safe="")))
        if not info or not info.get("expiryDates"):
            return [], [], None
        picks, band = pick_expiries(info["expiryDates"])
        return info["expiryDates"], [(e, sessions_left(e)) for e, _ in picks], band

    def chain(self, symbol, is_index, expiry):
        kind = "Indices" if is_index else "Equity"
        data = self.json("https://www.nseindia.com/api/option-chain-v3"
                         "?type=%s&symbol=%s&expiry=%s"
                         % (kind, urllib.parse.quote(symbol, safe=""),
                            urllib.parse.quote(expiry, safe="")))
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

    rets = [math.log(closes[i] / closes[i - 1]) for i in range(1, len(closes))
            if closes[i - 1] > 0]
    rv = None
    if len(rets) >= 20:
        window = rets[-20:]
        mean = sum(window) / len(window)
        var = sum((x - mean) ** 2 for x in window) / (len(window) - 1)
        rv = round(math.sqrt(var) * math.sqrt(252) * 100, 2)
    trs_recent = trs[-20:]
    expansion = round(trs[-1] / (sum(trs_recent) / len(trs_recent)), 2) if trs_recent and sum(trs_recent) > 0 else 0.0
    return {"atr": round(atr, 2), "ema_fast": round(ema(ema_fast), 2),
            "ema_slow": round(ema(ema_slow), 2), "rv": rv,
            "expansion": expansion,
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
def build_levels(entry, atr, delta, theta, sessions, r1=None, r2=None):
    """
    Stop from ATR through delta; targets at fixed R multiples.

    The multiples are a parameter, not a measurement: 4R and 6R are what the
    457-session NSE bhavcopy study supported. What is measured, per contract, is
    whether the underlying move needed to reach T1 fits inside 1.0 x ATR x
    sqrt(sessions). That feasibility check is the real filter - it is what
    rejects near-month contracts, whose decay makes a 4R target unreachable.
    """
    r1 = T1_R if r1 is None else r1
    r2 = T2_R if r2 is None else r2
    d = abs(delta)
    if entry <= 0 or atr <= 0 or d <= 0:
        return None
    risk = min(STOP_ATR_MULT * atr * d, MAX_RISK_FRAC * entry)
    if risk <= 0:
        return None
    budget = MOVE_BUDGET * atr * math.sqrt(max(sessions, 1))
    move_t1 = (r1 * risk + abs(theta) * sessions) / d
    out = {"entry": round(entry, 2), "risk": round(risk, 2),
           "sl": round(entry - risk, 2), "t1": round(entry + r1 * risk, 2),
           "t2": round(entry + r2 * risk, 2), "t1_rr": r1, "t2_rr": r2,
           "move_t1": round(move_t1, 1), "move_budget": round(budget, 1),
           "feasible": move_t1 <= budget}
    return out


# --------------------------------------------------------------------- gates
def gates(c, min_delta=None):
    """Every reason this contract is not publishable. Empty list means it passes."""
    bad = []
    if c["lot"] is None:
        bad.append("lot size unresolved")
    if c["cost"] is None or c["cost"] > CORE_MAX_COST:
        bad.append("cost Rs %s above the Rs %d core ceiling" % (c["cost"], CORE_MAX_COST))
    lo = MIN_DELTA if min_delta is None else min_delta
    if not (lo <= abs(c["delta"]) <= MAX_DELTA):
        bad.append("delta %.3f outside %.2f-%.2f" % (abs(c["delta"]), lo, MAX_DELTA))
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
    # Own side must be gaining open interest. The opposite side unwinding was
    # tested and is only marginally better per trade (+0.138R vs +0.119R) while
    # passing 40.5% of candidates against 90.5% - on a daily alert that strictness
    # produced empty scans, so only the own-side test is enforced.
    if c["chg_oi_own"] < 0:
        bad.append("own side losing OI (%+d)" % c["chg_oi_own"])
    if c["bid_qty"] < c["lot"] or c["ask_qty"] < c["lot"]:
        bad.append("depth %d/%d below one lot" % (c["bid_qty"], c["ask_qty"]))
    if c.get("rv") and c["iv"] > c["rv"] * IV_RV_MAX:
        bad.append("IV %.1f above realised %.1f" % (c["iv"], c["rv"]))
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
def universe_from_lot_file(lot_file):
    """Every F&O underlying NSE lists, indices first. No hardcoded watchlist."""
    if not lot_file:
        return [(s, s in INDEX_NAMES) for s in INDEX_NAMES] + \
               [(s, False) for s in STOCK_WATCHLIST]
    seen, out = set(), []
    for row in lot_file["rows"]:
        sym = (row.get("SYMBOL") or "").strip().upper()
        if not sym or sym in seen or sym in ("SYMBOL", "UNDERLYING"):
            continue
        seen.add(sym)
        out.append((sym, sym in INDEX_NAMES))
    idx = [x for x in out if x[1]]
    stk = sorted([x for x in out if not x[1]])
    return idx + stk


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


def days_to_expiry(expiry):
    try:
        d = datetime.datetime.strptime(expiry, "%d-%b-%Y").date()
    except (ValueError, TypeError):
        return None
    return (d - now_ist().date()).days


def pick_expiries(expiry_dates):
    """Series inside the 31-60 day band the backtest supported, widened if empty."""
    for lo, hi in ((MIN_DTE, MAX_DTE), (WIDE_DTE, WIDE_MAX_DTE)):
        out = [(e, days_to_expiry(e)) for e in expiry_dates
               if days_to_expiry(e) is not None and lo <= days_to_expiry(e) <= hi]
        if out:
            return out[:MAX_EXPIRIES], (lo, hi)
    return [], (MIN_DTE, MAX_DTE)


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
    """Every qualifying contract for one underlying, flat. Returns (cands, scanned, notes)."""
    all_dates, core_expiries, band = nse.expiries(symbol, is_index)
    if not all_dates:
        return [], 0, ["%s: no option chain" % symbol], {}

    # core band first, then the nearest tradeable series for the budget tier
    wanted = list(core_expiries)
    for e in all_dates:
        d = days_to_expiry(e)
        if d is not None and d >= MIN_DTE_BUDGET and sessions_left(e) >= MIN_SESSIONS:
            if e not in [x[0] for x in wanted]:
                wanted.append((e, sessions_left(e)))
            break
    if not wanted:
        return [], 0, ["%s: no expiry between %d and %d days" % (symbol, band[0], band[1])], {}

    candles = angel.candles(symbol, is_index, meta.get("token")) if angel else []
    source = "Angel One"
    if len(candles) < 60:
        ticker = (meta.get("yahoo") if is_index else symbol + ".NS") or symbol
        candles = yahoo_candles(ticker)
        source = "Yahoo"
    ind = indicators(candles)
    notes = []
    if ind is None:
        notes.append("%s: no candles" % symbol)

    cands, scanned, blockers = [], 0, {}
    for expiry, sessions in wanted[:MAX_EXPIRIES + 1]:
        rec = nse.chain(symbol, is_index, expiry)
        if not rec:
            continue
        spot = float(rec.get("underlyingValue") or 0)
        rows = rec.get("data") or []
        if not spot or not rows:
            continue
        lot, lot_note = lot_for(symbol, expiry, lot_file)
        if lot is None:
            notes.append("%s: %s" % (symbol, lot_note))
            continue
        dte = days_to_expiry(expiry) or 0
        try:
            exp_dt = datetime.datetime.strptime(expiry, "%d-%b-%Y").replace(
                hour=15, minute=30, tzinfo=IST)
            years = max((exp_dt - now_ist()).total_seconds(), 0) / (365 * 24 * 3600)
        except ValueError:
            continue

        for row in rows:
            strike = row.get("strikePrice")
            if not strike or abs(strike - spot) / spot > STRIKE_WINDOW:
                continue
            for side in ("CE", "PE"):
                if side not in row:
                    continue
                o = row[side]
                premium = float(o.get("lastPrice") or 0)
                bid = float(o.get("buyPrice1") or 0)
                ask = float(o.get("sellPrice1") or 0)
                if premium <= 0 or bid <= 0 or ask <= 0 or ask < bid:
                    continue
                scanned += 1
                g = greeks(spot, strike, years,
                           float(o.get("impliedVolatility") or 0), side)
                if not g:
                    continue
                trend_ok = False
                if ind:
                    trend_ok = (spot > ind["ema_fast"] and spot > ind["ema_slow"]) if side == "CE" \
                               else (spot < ind["ema_fast"] and spot < ind["ema_slow"])
                opp = row.get("PE" if side == "CE" else "CE", {})
                c = {
                    "symbol": symbol, "side": side, "strike": strike, "expiry": expiry,
                    "dte": dte, "sessions": sessions, "spot": spot, "premium": premium,
                    "lot": lot, "cost": round(premium * lot, 2),
                    "spread_pct": round((ask - bid) / premium * 100, 2),
                    "oi": int(o.get("openInterest") or 0),
                    "chg_oi_own": int(o.get("changeinOpenInterest") or 0),
                    "chg_oi_opp": int(opp.get("changeinOpenInterest") or 0),
                    "volume": int(o.get("totalTradedVolume") or 0),
                    "bid_qty": int(o.get("totalBuyQuantity") or 0),
                    "ask_qty": int(o.get("totalSellQuantity") or 0),
                    "min_volume": MIN_VOLUME_INDEX if is_index else MIN_VOLUME_STOCK,
                    "trend_ok": trend_ok, "delta": g["delta"], "theta": g["theta"],
                    "iv": g["iv"], "rv": (ind or {}).get("rv"),
                    "expansion": (ind or {}).get("expansion") or 0.0,
                }
                cheap = BUDGET_MIN <= c["cost"] <= BUDGET_MAX
                bad = gates(c, BUDGET_MIN_DELTA if cheap else None)
                if bad:
                    for reason in bad:
                        k = blocker_key(reason)
                        blockers[k] = blockers.get(k, 0) + 1
                    continue
                if c["cost"] > CORE_MAX_COST:
                    continue
                core_ok = MIN_DTE <= dte <= MAX_DTE and c["cost"] > BUDGET_MAX
                budget_ok = BUDGET_MIN <= c["cost"] <= BUDGET_MAX and dte >= MIN_DTE_BUDGET
                if not (core_ok or budget_ok):
                    k = ("too cheap for budget" if c["cost"] < BUDGET_MIN
                         else "wrong dte for core" if c["cost"] > BUDGET_MAX
                         else "outside tiers")
                    blockers["tier:" + k] = blockers.get("tier:" + k, 0) + 1
                    continue
                lv = build_levels(premium, (ind or {}).get("atr") or 0,
                                  g["delta"], g["theta"], sessions)
                if not lv or not lv["feasible"]:
                    continue
                c.update({"levels": lv, "sl": lv["sl"], "t1": lv["t1"], "t2": lv["t2"],
                          "risk": lv["risk"], "tier": "core" if core_ok else "budget"})
                c["score"] = score(c) + (0.20 if core_ok and c["expansion"] >= EXPANSION_REF else 0)
                cands.append(c)
    return cands, scanned, notes, blockers


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
def render(cands, notes, vix, blocked, stats):
    now = now_ist()
    L = ["<b>NSE option-buying scan</b>  %s" % now.strftime("%d-%b-%Y %H:%M IST")]
    if vix is not None:
        L.append("India VIX %s" % vix)
    L.append("")
    L.append("Scanned %d names, %s contracts | %d cleared every gate"
             % (stats["names_done"], "{:,}".format(stats["contracts"]), len(cands)))
    if cands:
        L.append("across %d names | %d core, %d budget"
                 % (len(set(c["symbol"] for c in cands)),
                    sum(1 for c in cands if c["tier"] == "core"),
                    sum(1 for c in cands if c["tier"] == "budget")))
    if stats["names_done"] < stats["names_total"]:
        L.append("_%d of %d names did not finish in time_"
                 % (stats["names_total"] - stats["names_done"], stats["names_total"]))

    def block(title, sub, rows):
        if not rows:
            return
        L.append("")
        L.append("<b>%s</b>" % title)
        L.append("<i>%s</i>" % sub)
        for s in rows:
            L.append("")
            L.append("<b>%s %d %s</b>  %s, %d days" % (esc(s["symbol"]), s["strike"],
                     s["side"], esc(s["expiry"]), s["dte"]))
            L.append("Entry %s | SL %s | T1 %s (4R) | T2 %s (6R)"
                     % (s["premium"], s["sl"], s["t1"], s["t2"]))
            L.append("Cost Rs %s = %s x %d | risk Rs %s per lot"
                     % ("{:,}".format(int(s["cost"])), s["premium"], s["lot"],
                        "{:,}".format(int(round(s["risk"] * s["lot"])))))
            L.append("delta %.3f | theta %.2f/day | IV %.1f vs RV %.1f | spread %.2f%%"
                     % (s["delta"], s["theta"], s["iv"], s["rv"] or 0, s["spread_pct"]))
            L.append("range %.2fx | OI %s | dOI %+d | vol %s"
                     % (s["expansion"], "{:,}".format(s["oi"]), s["chg_oi_own"],
                        "{:,}".format(s["volume"])))

    if blocked:
        L.append("")
        L.append("<b>Nothing published.</b> %s" % esc(blocked))
    else:
        core = sorted([c for c in cands if c["tier"] == "core"],
                      key=lambda x: -x["score"])[:MAX_SETUPS]
        bud = sorted([c for c in cands if c["tier"] == "budget"],
                     key=lambda x: -x["score"])[:MAX_SETUPS]
        block("CORE TIER   Rs %s-%s   31-60 days"
              % ("{:,}".format(BUDGET_MAX), "{:,}".format(CORE_MAX_COST)),
              "T1 reached by %.1f%% of %s similar trades in the 2025-26 test"
              % (HIT_CORE[0], "{:,}".format(HIT_CORE[1])), core)
        block("BUDGET TIER   Rs %s-%s   short dated, higher risk"
              % ("{:,}".format(BUDGET_MIN), "{:,}".format(BUDGET_MAX)),
              "T1 reached by %.1f%% of %s similar trades - a base rate, not a forecast"
              % (HIT_BUDGET[0], "{:,}".format(HIT_BUDGET[1])), bud)
        if not core and not bud:
            L.append("")
            L.append("<b>No qualifying setup today.</b> Nothing cleared every gate.")

    if notes:
        L.append("")
        L.append("<i>%s</i>" % esc("; ".join(notes[:6])))
    return "\n".join(L)


# ---------------------------------------------------------------------- main
def main():
    import concurrent.futures as cf
    import threading

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

    universe = universe_from_lot_file(lot_file)
    meta = {i["symbol"]: i for i in INDEX_UNIVERSE}
    local = threading.local()

    def worker(item):
        symbol, is_index = item
        if not hasattr(local, "nse"):
            local.nse = NSE()
        m = meta.get(symbol, {})
        return scan(local.nse, angel if angel_ok else None, lot_file,
                    symbol, is_index, m)

    cands, notes, blockers = [], [], {}
    done, total_scanned = 0, 0
    t0 = time.time()
    with cf.ThreadPoolExecutor(max_workers=SCAN_WORKERS) as ex:
        futs = {ex.submit(worker, item): item for item in universe}
        for f in cf.as_completed(futs, timeout=None):
            if time.time() - t0 > SCAN_SECONDS:
                break
            try:
                c, sc, nt, bl = f.result()
            except Exception as e:
                log("scan failed:", futs[f][0], type(e).__name__)
                continue
            done += 1
            total_scanned += sc
            cands += c
            notes += nt
            for k, v in bl.items():
                blockers[k] = blockers.get(k, 0) + v
            if done % 25 == 0:
                log("progress %d/%d" % (done, len(universe)))

    stats = {"names_done": done, "names_total": len(universe),
             "contracts": total_scanned}
    blocked = None
    if done == 0:
        blocked = ("No option chain could be retrieved from NSE. This is a feed "
                   "failure, not an empty scan.")
    elif vix is not None and vix > VIX_BLOCK:
        blocked = ("India VIX is above %.0f. New positional entries are suppressed "
                   "at this volatility." % VIX_BLOCK)
        cands = []

    log("blockers:", sorted(blockers.items(), key=lambda kv: -kv[1])[:5])
    text = render(cands, notes, vix, blocked, stats)
    print(text)
    if dry:
        log("dry run: nothing sent")
    else:
        telegram(token, chat_id, text)


if __name__ == "__main__":
    main()
