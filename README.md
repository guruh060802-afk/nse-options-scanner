# nse-options-scanner

A daily NSE option-buying scanner that posts to Telegram. Long calls and long
puts only — no selling, no spreads, no futures, no hedges.

**This is a filter and a calculator, not advice.** It does not forecast, and it
claims no win rate. The gates rank quality; they cannot predict outcomes. A long
option can lose its entire premium.

## What it does

Runs once at 09:00 IST on weekdays, before the open, and builds a plan from the
previous session's closing chain.

Two feeds, each used for what it is good at:

| Feed | Used for |
|---|---|
| NSE public JSON | the option chain — OI, change in OI, volume, per-strike IV |
| Angel One SmartAPI | daily candles for ATR and the EMA stack, plus an independent spot cross-check |
| Yahoo Finance | fallback for candles only, if Angel is unavailable |

No decision is taken from a single feed's price.

## The gates

A contract is published only if it clears all of these:

- lot size resolved from NSE `fo_mktlots.csv` for the contract's own expiry month
- capital per lot within the tier (Rs 3,000–7,000 budget, or up to Rs 15,000 core)
- `|delta|` between 0.25 and 0.60
- theta at most 10% of premium per calendar day
- bid-ask spread at most 5%
- open interest at least 500, and traded volume above the index or stock floor
- at least 5 sessions left — final-week contracts are never published
- EMA20/EMA50 stack aligned with the trade direction
- chain confirmation: the side being bought is gaining OI while the other side unwinds
- both bid and ask depth at least one lot
- ATR-derived stop no wider than 55% of premium
- T1 risk-reward at least 1.0 after ATR and theta

Two tiers are published: **budget** (Rs 3,000–7,000 per lot) and **core** (above
that, under Rs 15,000). If nothing clears the gates, the alert says so. Silence
is a valid output and the list is never padded.

## Levels

- Stop = entry − 0.5 × ATR × |delta|, capped at 55% of premium.
- T1 = entry + the gain from a 0.5 × ATR × √sessions move, less theta decay.
- T2 = the same from a 1.0 × ATR × √sessions move.
- Risk-reward is computed from those numbers and reported. It is not imposed.

## Credentials

Environment variables only. There is no config-file fallback, so nothing can be
committed by accident.

| Variable | Purpose |
|---|---|
| `ANGEL_API_KEY` | SmartAPI key |
| `ANGEL_CLIENT_CODE` | client code |
| `ANGEL_PIN` | trading PIN |
| `ANGEL_TOTP_KEY` | TOTP seed for the login |
| `TG_BOT_TOKEN` | Telegram bot token |
| `TG_CHAT_ID` | numeric chat id |

Store them under **Settings → Secrets and variables → Actions**. If a token is
ever committed or pasted anywhere, revoke it with BotFather (`/revoke`) and
issue a new one.

## Security

- The workflow runs with `contents: read`. The bot cannot write to this repo.
- Every string that reaches a log or an alert passes through `scrub()`, which
  strips registered secrets. This matters because the Telegram API carries the
  bot token in the URL and `requests` puts URLs into its exception messages.
- All outbound calls carry timeouts; no `eval`, no shell, no dynamic import.
- `requests` is pinned in `requirements.txt`.

## Running it yourself

```
pip install -r requirements.txt
export TG_BOT_TOKEN=... TG_CHAT_ID=...
export DRY_RUN=1        # print to stdout, send nothing
python main.py
```

## Known limitations

- The chain timestamp is the previous close when this runs at 09:00 IST. Check it
  before acting.
- GitHub's scheduler is best-effort: it queues, delays, and occasionally drops
  runs. A missed alert is not a signal.
- No IV percentile history is kept, so IV is reported but not ranked.
- `STOCK_WATCHLIST` is four names. Each one costs a chain fetch per expiry.
