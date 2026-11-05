import json
import os
import sys
import time
import datetime
import urllib.parse
import base64
import hashlib
import hmac
import struct
import requests

def get_totp(secret):
    secret = secret.replace(" ", "").upper()
    secret += "=" * ((8 - len(secret) % 8) % 8)
    key = base64.b32decode(secret)
    intervals_no = int(time.time()) // 30
    msg = struct.pack(">Q", intervals_no)
    h = hmac.new(key, msg, hashlib.sha1).digest()
    o = h[19] & 15
    code = struct.unpack(">I", h[o:o+4])[0] & 0x7fffffff
    return str(code % 1000000).zfill(6)

def get_angel_session():
    api_key = os.getenv("ANGEL_API_KEY", "").strip()
    client_code = os.getenv("ANGEL_CLIENT_CODE", "").strip()
    pin = os.getenv("ANGEL_PIN", "").strip()
    totp_key = os.getenv("ANGEL_TOTP_KEY", "").strip()
    
    if not (api_key and client_code and pin and totp_key):
        cfg_file = "angel_config.json"
        if os.path.exists(cfg_file):
            with open(cfg_file, "r") as f:
                c = json.load(f)
                api_key = c.get("api_key", "")
                client_code = c.get("client_code", "")
                pin = c.get("pin", "")
                totp_key = c.get("totp_key", "")
                
    if not (api_key and client_code and pin and totp_key):
        print("Angel One credentials not provided. Continuing with official NSE stream...")
        return None, None
        
    totp_code = get_totp(totp_key)
    login_url = "https://apiconnect.angelbroking.com/rest/auth/angelbroking/user/v1/loginByPassword"
    headers = {
        "Content-Type": "application/json",
        "Accept": "application/json",
        "X-UserType": "USER",
        "X-SourceID": "WEB",
        "X-ClientLocalIP": "192.168.1.1",
        "X-ClientPublicIP": "49.36.99.149",
        "X-MACAddress": "fe80::1",
        "X-PrivateKey": api_key
    }
    try:
        r = requests.post(login_url, json={"clientcode": client_code, "password": pin, "totp": totp_code}, headers=headers, timeout=12)
        res = r.json()
        if res.get("status") is True:
            jwt = res["data"]["jwtToken"]
            auth_headers = headers.copy()
            auth_headers["Authorization"] = f"Bearer {jwt}"
            return auth_headers, res["data"]
        else:
            print(f"Angel One Login failed: {res.get('message')}")
    except Exception as e:
        print(f"Angel One session error: {e}")
    return None, None

def get_angel_ohlc(auth_headers):
    if not auth_headers:
        return {}
    ltp_url = "https://apiconnect.angelbroking.com/rest/secure/angelbroking/order/v1/getLtpData"
    results = {}
    tokens = [("NIFTY", "Nifty 50", "99926000"), ("BANKNIFTY", "Nifty Bank", "99926009")]
    for sym_key, tradingsymbol, token in tokens:
        try:
            payload = {"exchange": "NSE", "tradingsymbol": tradingsymbol, "symboltoken": token}
            res = requests.post(ltp_url, json=payload, headers=auth_headers, timeout=8).json()
            if res.get("status") is True and "data" in res:
                results[sym_key] = res["data"]
        except Exception as e:
            print(f"Error fetching Angel quote for {sym_key}: {e}")
    return results

def get_nse_session():
    headers = {
        "User-Agent": "Mozilla/5.0 (Windows NT 10.0; Win64; x64) AppleWebKit/537.36 (KHTML, like Gecko) Chrome/128.0.0.0 Safari/537.36",
        "Accept": "text/html,application/xhtml+xml,application/xml;q=0.9,*/*;q=0.8",
        "Accept-Language": "en-US,en;q=0.9",
        "Connection": "keep-alive"
    }
    s = requests.Session()
    s.headers.update(headers)
    for _ in range(3):
        try:
            r = s.get("https://www.nseindia.com/option-chain", timeout=12)
            if r.status_code == 200:
                time.sleep(1)
                return s
        except Exception:
            time.sleep(2)
    return s

def fetch_nse_data(session, symbol, is_index=True):
    headers = {
        "Referer": "https://www.nseindia.com/option-chain",
        "Accept": "application/json, text/plain, */*"
    }
    type_str = "Indices" if is_index else "Equity"
    c_url = f"https://www.nseindia.com/api/option-chain-contract-info?type={type_str}&symbol={symbol}"
    
    contract_info = None
    for _ in range(3):
        try:
            r = session.get(c_url, headers=headers, timeout=12)
            if r.status_code == 200:
                contract_info = r.json()
                break
        except Exception:
            time.sleep(2)
            
    if not contract_info or "expiryDates" not in contract_info:
        return None
        
    expiry = contract_info["expiryDates"][0]
    chain_url = f"https://www.nseindia.com/api/option-chain-v3?type={type_str}&symbol={symbol}&expiry={expiry}"
    
    chain_data = None
    for _ in range(3):
        try:
            r = session.get(chain_url, headers=headers, timeout=12)
            if r.status_code == 200:
                chain_data = r.json()
                break
        except Exception:
            time.sleep(2)
            
    if not chain_data or "records" not in chain_data:
        return None
        
    return {
        "contract_info": contract_info,
        "chain_data": chain_data,
        "selected_expiry": expiry
    }

def analyze_index(symbol, data_payload, lot_size, angel_quote):
    chain_data = data_payload["chain_data"]
    expiry = data_payload["selected_expiry"]
    records = chain_data.get("records", {})
    underlying_value = records.get("underlyingValue", 0.0)
    timestamp = records.get("timestamp", datetime.datetime.now().strftime("%d-%b-%Y %H:%M:%S"))
    rows = records.get("data", [])
    
    tot_ce_oi = 0
    tot_pe_oi = 0
    ce_list = []
    pe_list = []
    
    for row in rows:
        strike = row.get("strikePrice")
        if "CE" in row:
            ce = row["CE"]
            tot_ce_oi += ce.get("openInterest", 0)
            ce_list.append({
                "strike": strike,
                "oi": ce.get("openInterest", 0),
                "change_oi": ce.get("changeinOpenInterest", 0),
                "ltp": ce.get("lastPrice", 0.0),
                "iv": ce.get("impliedVolatility", 0.0),
                "volume": ce.get("totalTradedVolume", 0),
                "bid": ce.get("buyPrice1", 0.0),
                "ask": ce.get("sellPrice1", 0.0),
                "spread": round(ce.get("sellPrice1", 0.0) - ce.get("buyPrice1", 0.0), 2)
            })
        if "PE" in row:
            pe = row["PE"]
            tot_pe_oi += pe.get("openInterest", 0)
            pe_list.append({
                "strike": strike,
                "oi": pe.get("openInterest", 0),
                "change_oi": pe.get("changeinOpenInterest", 0),
                "ltp": pe.get("lastPrice", 0.0),
                "iv": pe.get("impliedVolatility", 0.0),
                "volume": pe.get("totalTradedVolume", 0),
                "bid": pe.get("buyPrice1", 0.0),
                "ask": pe.get("sellPrice1", 0.0),
                "spread": round(pe.get("sellPrice1", 0.0) - pe.get("buyPrice1", 0.0), 2)
            })
            
    pcr = round(tot_pe_oi / tot_ce_oi, 2) if tot_ce_oi > 0 else 0.0
    
    top_ce_oi = sorted(ce_list, key=lambda x: x["oi"], reverse=True)[:5]
    top_pe_oi = sorted(pe_list, key=lambda x: x["oi"], reverse=True)[:5]
    
    resistance = top_ce_oi[0]["strike"] if top_ce_oi else 0
    support = top_pe_oi[0]["strike"] if top_pe_oi else 0
    
    return {
        "symbol": symbol,
        "spot": underlying_value,
        "timestamp": timestamp,
        "expiry": expiry,
        "lot_size": lot_size,
        "pcr": pcr,
        "support": support,
        "resistance": resistance,
        "top_ce_oi": top_ce_oi,
        "top_pe_oi": top_pe_oi,
        "ce_list": ce_list,
        "pe_list": pe_list,
        "angel_quote": angel_quote
    }

def send_telegram(bot_token, chat_id, message):
    url = f"https://api.telegram.org/bot{bot_token}/sendMessage"
    payload = {
        "chat_id": chat_id,
        "text": message,
        "parse_mode": "Markdown",
        "disable_web_page_preview": True
    }
    return requests.post(url, json=payload, timeout=12)

def main():
    print("--- Starting Morning NSE Derivatives Cloud Scan ---")
    angel_auth, _ = get_angel_session()
    angel_quotes = get_angel_ohlc(angel_auth) if angel_auth else {}
    if angel_quotes:
        print(f"Angel One Verified: Feeds active for {list(angel_quotes.keys())}")
        
    s = get_nse_session()
    indices = [("NIFTY", True, 25), ("BANKNIFTY", True, 15)]
    analysis_map = {}
    
    for sym, is_idx, lot in indices:
        payload = fetch_nse_data(s, sym, is_idx)
        if payload:
            an_quote = angel_quotes.get(sym, {})
            analysis_map[sym] = analyze_index(sym, payload, lot, an_quote)
            
    today_str = datetime.datetime.now().strftime("%Y-%m-%d")
    if not analysis_map:
        print("Market data currently unavailable from upstream feeds.")
        return
        
    setups = []
    
    # NIFTY Budget Setup
    if "NIFTY" in analysis_map:
        an = analysis_map["NIFTY"]
        spot = an["spot"]
        candidates = [x for x in an["pe_list"] if 120 <= x["ltp"] <= 280 and x["volume"] > 500]
        chosen = None
        for cand in sorted(candidates, key=lambda x: abs(x["strike"] - spot)):
            if cand["spread"] <= 2.5:
                chosen = cand
                break
        if chosen:
            entry_low = round(chosen["ltp"] * 0.95, 1)
            entry_high = round(chosen["ltp"] * 1.02, 1)
            sl = round(chosen["ltp"] * 0.70, 1)
            t1 = round(chosen["ltp"] * 1.35, 1)
            t2 = round(chosen["ltp"] * 1.65, 1)
            risk = round(entry_high - sl, 1)
            reward_t1 = round(t1 - entry_high, 1)
            rr_ratio = round(reward_t1 / risk, 2) if risk > 0 else 0
            setups.append({
                "instrument": "NIFTY",
                "option": "PE",
                "strike": chosen["strike"],
                "expiry": an["expiry"],
                "entry": f"{entry_low} - {entry_high}",
                "sl": sl,
                "t1": t1,
                "t2": t2,
                "lot": 25,
                "cost": f"Rs {round(chosen['ltp'] * 25, 2)}",
                "rr": f"1:{rr_ratio}"
            })
            
    # BANKNIFTY Budget Setup
    if "BANKNIFTY" in analysis_map:
        an = analysis_map["BANKNIFTY"]
        spot = an["spot"]
        candidates = [x for x in an["pe_list"] if 200 <= x["ltp"] <= 466 and x["volume"] > 200]
        chosen = None
        for cand in sorted(candidates, key=lambda x: abs(x["strike"] - spot)):
            if cand["spread"] <= 6.0:
                chosen = cand
                break
        if chosen:
            entry_low = round(chosen["ltp"] * 0.95, 1)
            entry_high = round(chosen["ltp"] * 1.02, 1)
            sl = round(chosen["ltp"] * 0.70, 1)
            t1 = round(chosen["ltp"] * 1.35, 1)
            t2 = round(chosen["ltp"] * 1.65, 1)
            risk = round(entry_high - sl, 1)
            reward_t1 = round(t1 - entry_high, 1)
            rr_ratio = round(reward_t1 / risk, 2) if risk > 0 else 0
            setups.append({
                "instrument": "BANKNIFTY",
                "option": "PE",
                "strike": chosen["strike"],
                "expiry": an["expiry"],
                "entry": f"{entry_low} - {entry_high}",
                "sl": sl,
                "t1": t1,
                "t2": t2,
                "lot": 15,
                "cost": f"Rs {round(chosen['ltp'] * 15, 2)}",
                "rr": f"1:{rr_ratio}"
            })

    # Dispatch to Telegram
    bot_token = os.getenv("TG_BOT_TOKEN", "").strip()
    chat_id = os.getenv("TG_CHAT_ID", "").strip()
    if bot_token and chat_id:
        tg_msg = f"📊 *NSE Daily Derivatives Cloud Scan ({today_str})*\n"
        tg_msg += "⚡ _Cloud Runner: NSE Chain + Angel One SmartAPI_\n\n"
        for k in ["NIFTY", "BANKNIFTY"]:
            if k in analysis_map:
                an = analysis_map[k]
                tg_msg += f"• *{k} Spot*: `{an['spot']}` | PCR: `{an['pcr']}` | S: `{an['support']}` / R: `{an['resistance']}`\n"
        tg_msg += f"\n🎯 *Qualifying Budget Setups ({len(setups)})*:\n"
        for s in setups:
            tg_msg += f"\n🔹 *{s['instrument']} {s['strike']} {s['option']}* ({s['expiry']})\n"
            tg_msg += f"  • Entry Range: `{s['entry']}`\n"
            tg_msg += f"  • Stop Loss: `{s['sl']}` | Target 1: `{s['t1']}` | Target 2: `{s['t2']}`\n"
            tg_msg += f"  • Cost/Lot: `{s['cost']}` (Lot: `{s['lot']}`) | R:R: {s['rr']}\n"
            
        res = send_telegram(bot_token, chat_id, tg_msg)
        print("Telegram Dispatch Result:", res.status_code)
    else:
        print("Telegram credentials not configured in environment.")

if __name__ == "__main__":
    main()
