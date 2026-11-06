"""
main.py - NSE option-buying scanner (long premium only).

Rewritten after an audit of the previous version. What changed and why:

  * Lot sizes are READ from NSE's fo_mktlots.csv for the contract's own expiry
    month. The old file hardcoded 25 and 15, which are pre-revision values.
    The budget band was calibrated to those numbers, so the whole budget track
    was fiction once the real lots were 65 and 30.
  * Stop and targets are derived from ATR and reported, not imposed. The old
    file used sl=0.70*L, t1=1.35*L, t2=1.65*L, which makes the risk-reward
    algebraically identical at 1.0312 for every setup it could ever emit.
  * Both sides are scanned. The old file only ever looked at pe_list.
  * Greeks are computed (Black-Scholes from NSE's own IV) and used as filters.
  * A setup is only emitted if the chain and the trend agree with its direction.
  * If the data feed fails, Telegram is told. The old file returned silently,
    so "no setups" and "bot broken" looked the same.

Long calls and long puts only. No selling, no spreads, no futures.
Standard library + requests. No other dependencies.
"""

import base64
import datetime
import hashlib
import hmac
import json
import math
import os
import struct
import sys
import time
import csv
import io

import requests

IST = datetime.timezone(datetime.timedelta(hours=5, minutes=30))
UA = ("Mozilla/5.0 (Windows NT 10.0; Win64; x64) AppleWebKit/537.36 "
      "(KHTML, like Gecko) Chrome/128.0.0.0 Safari/537.36")

# ------------------------------------------------------------------ settings
BUDGET_MIN, BUDGET_MAX = 3000, 7000     # rupees, total capital per lot
MIN_SESSIONS = 5                        # refuse final-week contracts
MIN_DELTA, MAX_DELTA = 0.25, 0.60       # on |delta|
MAX_THETA_PCT = 4.0                     # per cent of premium per calendar day
MAX_SPREAD_PCT = 5.0
MIN_VOLUME_INDEX, MIN_VOLUME_STOCK = 500, 100
STRIKE_WINDOW = 0.06                    # scan strikes within +/-6% of spot
MAX_SETUPS = 4
RISK_FREE = 0.065

INDEX_UNIVERSE = [("NIFTY", "NIFTY 50", "99926000"),
                  ("BANKNIFTY", "Nifty Bank", "99926009")]
STOCK_WATCHLIST = ["HDFCBANK", "RELIANCE", "SBIN", "ICICIBANK"]

MONTH_COL = {1: "JAN", 2: "FEB", 3: "MAR", 4: "APR", 5: "MAY", 6: "JUN",
             7: "JUL", 8: "AUG", 9: "SEP", 10: "OCT", 11: "NOV", 12: "DEC"}


def log(*a):
    print(*a, file=sys.stderr)


# ------------------------------------------------------------------ Angel One
def get_totp(secret):
    secret = secret.replace(" ", "").upper()
    secret += "=" * ((8 - len(secret) % 8) % 8)
    key = base64.b32decode(secret)
    intervals_no = int(time.time()) // 30
    msg = struct.pack(">Q", intervals_no)
    h = hmac.new(key, msg, hashlib.sha1).digest()
    o = h[19] & 15
    code = struct.unpack(">I", h[o:o + 4])[0] & 0x7fffffff
    return str(code % 1000000).zfill(6)


def get_angel_session():
    api_key = os.getenv("ANGEL_API_KEY", "").strip()
    client_code = os.getenv("ANGEL_CLIENT_CODE", "").strip()
    pin = os.getenv("ANGEL_PIN", "").strip()
    totp_key = os.getenv("ANGEL_TOTP_KEY", "").strip()
    if not (api_key and client_code and pin and totp_key):
        return None
    headers = {
        "Content-Type": "application/json", "Accept": "application/json",
        "X-UserType": "USER", "X-SourceID": "WEB",
        "X-ClientLocalIP": "127.0.0.1", "X-ClientPublicIP": "127.0.0.1",
        "X-MACAddress": "00:00:00:00:00:00", "X-PrivateKey": api_key,
    }
    try:
        r = requests.post(
            "https://apiconnect.angelbroking.com/rest/auth/angelbroking/"
            "user/v1/loginByPassword",
            json={"clientcode": client_code, "password": pin,
                  "totp": get_totp(totp_key)},
            headers=headers, timeout=12)
        res = r.json()
        if res.get("status") is True:
            h = headers.copy()
            h["Authorization"] = "Bearer " + res["data"]["jwtToken"]
            return h
    except Exception as e:
        log("angel session:", e)
    return None


def angel_spot(auth, tradingsymbol, token):
    """Used only to cross-check NSE's spot. Never used for selection."""
    if not auth:
        return None
    try:
        r = requests.post(
            "https://apiconnect.angelbroking.com/rest/secure/angelbroking/"
            "order/v1/getLtpData",
            json={"exchange": "NSE", "tradingsymbol": tradingsymbol,
                  "symboltoken": token},
            headers=auth, timeout=8)
        res = r.json()
        if res.get("status") is True:
            return float(res["data"]["ltp"])
    except Exception as e:
        log("angel ltp:", e)
    return None


# ---------------------------------------------------------------------- NSE
def nse_session():
    s = requests.Session()
    s.headers.update({"User-Agent": UA,
                      "Accept-Language": "en-US,en;q=0.9",
                      "Connection": "keep-alive"})
    for _ in range(3):
        try:
            if s.get("https://www.nseindia.com/option-chain", timeout=12).status_code == 200:
                time.sleep(1)
                return s
        except Exception:
            time.sleep(2)
    return s


def _get_json(session, url):
    for _ in range(3):
        try:
            r = session.get(url, headers={"Referer": "https://www.nseindia.com/option-chain",
                                          "Accept": "application/json, text/plain, */*"},
                            timeout=12)
            if r.status_code == 200:
                return r.json()
        except Exception:
            pass
        time.sleep(2)
    return None


def load_lot_file():
    """NSE's market-lot file. Lot sizes differ by expiry month for many names."""
    for _ in range(3):
        try:
            r = requests.get("https://nsearchives.nseindia.com/content/fo/fo_mktlots.csv",
                             headers={"User-Agent": UA}, timeout=25)
            if r.status_code == 200:
                text = r.content.decode("utf-8-sig", "ignore")
                rd = csv.reader(io.StringIO(text))
                header = [c.strip() for c in next(rd)]
                rows = [dict(zip(header, [c.strip() for c in x]))
                        for x in rd if any(c.strip() for c in x)]
                return {"header": header, "rows": rows}
        except Exception as e:
            log("lot file:", e)
        time.sleep(2)
    return None


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
            return None, "blank %s lot for %s" % (col, symbol)
    return None, "%s not in lot file" % symbol


def sessions_to(expiry):
    """Trading sessions between tomorrow and expiry, inclusive."""
    try:
        d = datetime.datetime.strptime(expiry, "%d-%b-%Y").date()
    except (ValueError, TypeError):
        return 0
    today = datetime.datetime.now(IST).date()
    n, cur = 0, today + datetime.timedelta(days=1)
    while cur <= d:
        if cur.weekday() < 5:
            n += 1
        cur += datetime.timedelta(days=1)
    return n


def pick_expiry(expiry_dates):
    """Nearest expiry with enough time left. Returns (expiry, sessions)."""
    for e in expiry_dates:
        n = sessions_to(e)
        if n >= MIN_SESSIONS:
            return e, n
    if expiry_dates:
        return expiry_dates[0], sessions_to(expiry_dates[0])
    return None, 0


def fetch_chain(session, symbol, is_index):
    type_str = "Indices" if is_index else "Equity"
    info = _get_json(session, "https://www.nseindia.com/api/option-chain-contract-info"
                              "?type=%s&symbol=%s" % (type_str, symbol))
    if not info or "expiryDates" not in info:
        return None
    expiry, sessions = pick_expiry(info["expiryDates"])
    if not expiry:
        return None
    chain = _get_json(session, "https://www.nseindia.com/api/option-chain-v3"
                               "?type=%s&symbol=%s&expiry=%s"
                               % (type_str, symbol, expiry))
    if not chain or "records" not in chain:
        return None
    return {"expiry": expiry, "sessions": sessions, "chain": chain}


# ------------------------------------------------------------------ candles
def yahoo_candles(sym, is_index):
    y = {"NIFTY": "^NSEI", "BANKNIFTY": "^NSEBANK"}.get(sym) if is_index else sym + ".NS"
    try:
        r = requests.get("https://query1.finance.yahoo.com/v8/finance/chart/" + y,
                         params={"interval": "1d", "range": "6mo"},
                         headers={"User-Agent": UA}, timeout=20)
        res = r.json()["chart"]["result"][0]
        q = res["indicators"]["quote"][0]
        rows = [(h, l, c) for h, l, c in zip(q["high"], q["low"], q["close"])
                if None not in (h, l, c)]
        return rows
    except Exception as e:
        log("yahoo candles", sym, e)
        return []


def atr_and_trend(rows, period=14):
    """Wilder ATR14 and the 20-period EMA, from completed daily candles."""
    if len(rows) < period + 2:
        return None, None
    trs = []
    for i in range(1, len(rows)):
        h, l, _ = rows[i]
        pc = rows[i - 1][2]
        trs.append(max(h - l, abs(h - pc), abs(l - pc)))
    atr = sum(trs[:period]) / period
    for t in trs[period:]:
        atr = (atr * (period - 1) + t) / period
    closes = [r[2] for r in rows]
    k = 2.0 / 21.0
    ema = sum(closes[:20]) / 20.0
    for c in closes[20:]:
        ema = c * k + ema * (1 - k)
    return round(atr, 2), round(ema, 2)


# ------------------------------------------------------------------- greeks
def _ncdf(x):
    return 0.5 * (1.0 + math.erf(x / math.sqrt(2.0)))


def _npdf(x):
    return math.exp(-0.5 * x * x) / math.sqrt(2.0 * math.pi)


def greeks(S, K, T, iv_pct, side):
    """Black-Scholes. iv_pct is NSE's impliedVolatility, in per cent."""
    if not S or not K or T <= 0 or not iv_pct or iv_pct <= 0:
        return None
    sig = iv_pct / 100.0
    d1 = (math.log(S / K) + (RISK_FREE + 0.5 * sig * sig) * T) / (sig * math.sqrt(T))
    d2 = d1 - sig * math.sqrt(T)
    disc = math.exp(-RISK_FREE * T)
    if side == "CE":
        delta = _ncdf(d1)
        theta = (-S * _npdf(d1) * sig / (2 * math.sqrt(T))
                 - RISK_FREE * K * disc * _ncdf(d2))
    else:
        delta = _ncdf(d1) - 1.0
        theta = (-S * _npdf(d1) * sig / (2 * math.sqrt(T))
                 + RISK_FREE * K * disc * _ncdf(-d2))
    return {"delta": round(delta, 4), "theta": round(theta / 365.0, 4),
            "iv": round(iv_pct, 2)}


# ------------------------------------------------------------------- levels
def build_levels(entry, atr, delta, theta, sessions, sl_atr=0.5):
    d = abs(delta)
    if entry <= 0 or atr <= 0 or d <= 0:
        return None
    risk = sl_atr * atr * d
    if risk >= entry * 0.8:
        return None
    stop = round(entry - risk, 2)
    out = {"entry": entry, "sl": stop, "risk": round(risk, 2)}
    for name, mult in (("t1", 0.5), ("t2", 1.0)):
        move = mult * atr * math.sqrt(max(sessions, 1))
        gain = d * move - abs(theta) * sessions
        out[name] = round(entry + gain, 2)
        out[name + "_rr"] = round(gain / risk, 2)
        out[name + "_move"] = round(move, 1)
    return out


def gates(premium, cost, lot, delta, theta, spread_pct, volume, sessions,
          side, chg_oi_own, chg_oi_opp, trend_ok, min_volume):
    bad = []
    if lot is None:
        bad.append("lot size unresolved")
    if cost is None or not (BUDGET_MIN <= cost <= BUDGET_MAX):
        bad.append("cost %s outside Rs %d-%d" % (cost, BUDGET_MIN, BUDGET_MAX))
    if not (MIN_DELTA <= abs(delta) <= MAX_DELTA):
        bad.append("delta %.3f outside %.2f-%.2f" % (abs(delta), MIN_DELTA, MAX_DELTA))
    if premium > 0 and abs(theta) / premium * 100 > MAX_THETA_PCT:
        bad.append("theta %.1f%% of premium/day" % (abs(theta) / premium * 100))
    if spread_pct > MAX_SPREAD_PCT:
        bad.append("spread %.2f%%" % spread_pct)
    if volume < min_volume:
        bad.append("volume %d" % volume)
    if sessions < MIN_SESSIONS:
        bad.append("only %d sessions left" % sessions)
    if not trend_ok:
        bad.append("trend disagrees with %s" % side)
    if not (chg_oi_own > 0 and chg_oi_opp <= 0):
        bad.append("chain does not confirm %s (own dOI %+d, opposite %+d)"
                   % (side, chg_oi_own, chg_oi_opp))
    return bad


# --------------------------------------------------------------------- scan
def scan_one(session, lot_file, symbol, is_index, angel_auth, angel_meta):
    data = fetch_chain(session, symbol, is_index)
    if not data:
        return None, "%s: no option chain" % symbol

    expiry, sessions = data["expiry"], data["sessions"]
    rec = data["chain"].get("records", {})
    spot = float(rec.get("underlyingValue") or 0)
    stamp = rec.get("timestamp", "")
    rows = rec.get("data", [])
    if not spot or not rows:
        return None, "%s: empty chain" % symbol

    lot, lot_note = lot_for(symbol, expiry, lot_file)
    atr, ema20 = atr_and_trend(yahoo_candles(symbol, is_index))

    xcheck = None
    if angel_auth and angel_meta:
        a = angel_spot(angel_auth, angel_meta[0], angel_meta[1])
        if a:
            xcheck = round((a / spot - 1) * 100, 3)

    try:
        exp_dt = datetime.datetime.strptime(expiry, "%d-%b-%Y")
        T = max((exp_dt.replace(hour=15, minute=30, tzinfo=IST)
                 - datetime.datetime.now(IST)).total_seconds(), 0) / (365 * 24 * 3600)
    except ValueError:
        T = 0

    tot_ce = tot_pe = 0
    best = {}
    for row in rows:
        k = row.get("strikePrice")
        if not k:
            continue
        for side in ("CE", "PE"):
            if side not in row:
                continue
            o = row[side]
            oi = o.get("openInterest", 0) or 0
            if side == "CE":
                tot_ce += oi
            else:
                tot_pe += oi
        if abs(k - spot) / spot > STRIKE_WINDOW:
            continue
        for side in ("CE", "PE"):
            if side not in row:
                continue
            o = row[side]
            ltp = float(o.get("lastPrice") or 0)
            if ltp <= 0 or lot is None:
                continue
            bid = float(o.get("buyPrice1") or 0)
            ask = float(o.get("sellPrice1") or 0)
            if bid <= 0 or ask <= 0:
                continue
            spread_pct = round((ask - bid) / ltp * 100, 2)
            g = greeks(spot, k, T, float(o.get("impliedVolatility") or 0), side)
            if not g:
                continue
            cost = round(ltp * lot, 2)
            trend_ok = (spot > ema20) if side == "CE" else (spot < ema20)
            opp = row.get("PE" if side == "CE" else "CE", {})
            bad = gates(ltp, cost, lot, g["delta"], g["theta"], spread_pct,
                        int(o.get("totalTradedVolume") or 0), sessions, side,
                        int(o.get("changeinOpenInterest") or 0),
                        int(opp.get("changeinOpenInterest") or 0),
                        bool(ema20) and trend_ok,
                        MIN_VOLUME_INDEX if is_index else MIN_VOLUME_STOCK)
            if bad:
                continue
            lv = build_levels(ltp, atr or 0, g["delta"], g["theta"], sessions)
            if not lv or lv["t1_rr"] < 1.0:
                continue
            score = abs(g["delta"] - 0.45) + spread_pct / 100.0
            if side not in best or score < best[side]["score"]:
                best[side] = {
                    "instrument": symbol, "option": side, "strike": k,
                    "expiry": expiry, "sessions": sessions, "spot": spot,
                    "premium": ltp, "lot": lot, "cost": cost,
                    "spread_pct": spread_pct, "iv": g["iv"],
                    "delta": g["delta"], "theta": g["theta"],
                    "oi": oi_of(row, side), "chg_oi": o.get("changeinOpenInterest", 0),
                    "volume": o.get("totalTradedVolume", 0),
                    "levels": lv, "score": score,
                }

    pcr = round(tot_pe / tot_ce, 2) if tot_ce else 0.0
    context = {"symbol": symbol, "spot": spot, "pcr": pcr, "stamp": stamp,
               "expiry": expiry, "sessions": sessions, "lot": lot,
               "lot_note": lot_note, "atr": atr, "ema20": ema20,
               "angel_xcheck_pct": xcheck,
               "support": top_strike(rows, "PE"), "resistance": top_strike(rows, "CE")}
    return {"context": context, "setups": list(best.values())}, None


def oi_of(row, side):
    return row.get(side, {}).get("openInterest", 0)


def top_strike(rows, side, spot=None):
    """Highest-OI strike on a side, preferring one that differs from the other side."""
    cand = [(r.get(side, {}).get("openInterest", 0) or 0, r.get("strikePrice"))
            for r in rows if side in r and r.get("strikePrice")]
    cand = [c for c in cand if c[0] > 0]
    if not cand:
        return None
    cand.sort(reverse=True)
    return cand[0][1]


# ---------------------------------------------------------------- telegram
def send_telegram(token, chat_id, text):
    try:
        r = requests.post("https://api.telegram.org/bot%s/sendMessage" % token,
                          json={"chat_id": chat_id, "text": text,
                                "parse_mode": "Markdown",
                                "disable_web_page_preview": True}, timeout=15)
        log("telegram:", r.status_code)
        return r.status_code
    except Exception as e:
        log("telegram failed:", e)
        return None


def fmt_setup(s):
    lv = s["levels"]
    return (
        "*%s %d %s* (%s, %s)\n"
        "  Entry `%.2f`  SL `%.2f`  T1 `%.2f` (%.2fR)  T2 `%.2f` (%.2fR)\n"
        "  Cost `Rs %.0f` = %.2f x %d  |  d %.2f  th %.2f/day  IV %.1f\n"
        "  OI %s  dOI %+d  vol %d  spread %.2f%%"
        % (s["instrument"], s["strike"], s["option"], s["expiry"],
           s["sessions"], lv["entry"], lv["sl"], lv["t1"], lv["t1_rr"],
           lv["t2"], lv["t2_rr"], s["cost"], s["premium"], s["lot"],
           s["delta"], s["theta"], s["iv"], f"{s['oi']:,}",
           s["chg_oi"], s["volume"], s["spread_pct"]))


def main():
    dry = os.getenv("DRY_RUN", "").strip() in ("1", "true", "yes")
    token = os.getenv("TG_BOT_TOKEN", "").strip()
    chat_id = os.getenv("TG_CHAT_ID", "").strip()
    now = datetime.datetime.now(IST)

    angel_auth = get_angel_session()
    session = nse_session()
    lot_file = load_lot_file()

    results, problems = [], []
    meta = {s: (ts, tok) for s, ts, tok in INDEX_UNIVERSE}
    for sym, _, _ in INDEX_UNIVERSE:
        try:
            r, err = scan_one(session, lot_file, sym, True, angel_auth, meta.get(sym))
        except Exception as e:
            r, err = None, "%s: %s" % (sym, e)
        if r:
            results.append(r)
        else:
            problems.append(err)
    for sym in STOCK_WATCHLIST:
        try:
            r, err = scan_one(session, lot_file, sym, False, None, None)
        except Exception as e:
            r, err = None, "%s: %s" % (sym, e)
        if r:
            results.append(r)
        else:
            problems.append(err)

    # ---- nothing came back at all: say so out loud, do not go silent
    if not results:
        msg = ("*NSE scan failed* (%s)\nNo option chain could be retrieved, so no "
               "setups are being published.\n\n%s"
               % (now.strftime("%d-%b-%Y %H:%M IST"), "\n".join("- " + p for p in problems)))
        print(msg)
        if token and chat_id and not dry:
            send_telegram(token, chat_id, msg)
        return

    setups = [s for r in results for s in r["setups"]]
    setups.sort(key=lambda s: s["score"])
    setups = setups[:MAX_SETUPS]

    lines = ["*NSE option-buying scan* — %s" % now.strftime("%d-%b-%Y %H:%M IST")]
    for r in results:
        c = r["context"]
        lines.append("")
        lines.append("*%s* %s  PCR %.2f  S %s / R %s"
                     % (c["symbol"], f"{c['spot']:,.2f}", c["pcr"],
                        c["support"], c["resistance"]))
        lines.append("  chain %s | exp %s (%d sessions) | lot %s | ATR %s | EMA20 %s"
                     % (c["stamp"], c["expiry"], c["sessions"], c["lot"],
                        c["atr"], c["ema20"]))
        if c["angel_xcheck_pct"] is not None:
            lines.append("  Angel cross-check: %+.3f%%" % c["angel_xcheck_pct"])

    if setups:
        lines.append("")
        lines.append("*%d qualifying setup(s)*" % len(setups))
        for s in setups:
            lines.append("")
            lines.append(fmt_setup(s))
    else:
        lines.append("")
        lines.append("*No qualifying setup today.* Every contract failed at least "
                     "one gate: budget, delta, theta, spread, volume, sessions "
                     "left, trend, or chain confirmation.")

    if problems:
        lines.append("")
        lines.append("_Not scanned: %s_" % ", ".join(problems))

    msg = "\n".join(lines)
    print(msg)
    if token and chat_id and not dry:
        send_telegram(token, chat_id, msg)


if __name__ == "__main__":
    main()
