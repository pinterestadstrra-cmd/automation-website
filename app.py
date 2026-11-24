#!/usr/bin/env python3
"""
Automation Website - app.py
================================
Blogger auto-posting + Bluesky marketing dashboard and worker.

WHAT IT DOES
------------
1. MOST IMPORTANT: checks what is TRENDING on Bluesky FIRST, then writes
   news based on those trending topics (not the other way round).
2. Verifies every story with >= 2 independent sources before publishing.
3. Writes articles with a hook + SEO (Gemini), images with NO logo/text.
4. STRICT RULE: NO photo = NO post. A topic with no suitable photo is
   dropped entirely (never text-only, never a placeholder).
5. CARD-ONLY: the worker publishes to Blogger ONLY through the cards
   in data/cards.json - each card has its own schedule, posts-per-day,
   posts-per-run, posting window, topic and bold toggle. There is NO
   global cycle any more (it once auto-published unwanted posts).
   AUTO-SPREAD: a card's posting times are computed from its posts
   per day + posting window (evenly, or at peak "best times"). The
   card RUNS every X minutes to check replies; it only PUBLISHES at
   a scheduled posting time. A card can also be Draft-only (write
   the article, save as a draft, never publish).
   Too many posts risks a Blogger suspension, so posts are spaced out.
6. Posts to Bluesky only through Bluesky cards. The SAME post never
   goes to all Bluesky accounts - each account gets a different /
   rotated post. Dedup via data/state.json (same news never reposted).
7. Replies to comments on the account's OWN posts (all of them inside
   each card's lookback window, default 7 days - old posts included),
   and - with strict safety limits - to fresh comments on
   high-engagement posts. Every reply is unique English text (never
   copy-paste duplicates) and is logged under its card's name.
8. Dashboard (flat UI, white / sky-blue / red / teal) with fully MANUAL
   cards: link to market, account, post/reply count, interval (minutes),
   daily schedule (how many + at what times), Run / Pause / Delete,
   live status. Everything is saved in the database, so a refresh loses
   nothing and the site keeps running while the user is offline
   (GitHub Actions does the work on schedule).

SECRETS (never in the repo - GitHub Secrets / environment only)
---------------------------------------------------------------
  GEMINI_API_KEYS        comma-separated Gemini keys (separate Google projects)
  GROQ_API_KEYS          comma-separated Groq keys (separate Groq accounts)
  BLOGGER_CLIENT_ID      Google OAuth client id (Blogger API enabled)
  BLOGGER_CLIENT_SECRET  Google OAuth client secret
  BLOGGER_REFRESH_TOKEN  Blogger OAuth refresh token (offline access)
  BLOG_ID                Blogger blog id
  BLUESKY_ACCOUNTS       JSON list [{"handle": "...", "app_password": "..."}]
  PEXELS_API_KEY         (optional) free Pexels key for photos
  PIXABAY_API_KEY        (optional) free Pixabay key for photos
  ADMIN_PASSWORD         dashboard password (admin panel)
  SECRET_KEY             Flask session secret (any random string)

RUN
---
  Web dashboard :  python app.py            (then open http://localhost:5000)
  One worker run:  python app.py --worker   (what GitHub Actions runs)
  Blogger only :  python app.py --worker --only blogger
  Bluesky only :  python app.py --worker --only bluesky
  Docker        :  docker build -t automation-website . && docker run -p 5000:5000 --env-file .env automation-website
"""

import os
import sys
import json
import time
import random
import re
import hashlib
import sqlite3
import threading
import html as html_lib
import xml.etree.ElementTree as ET
from datetime import datetime, timedelta, timezone
from urllib.parse import quote_plus, urlparse, urljoin

import requests
from flask import Flask, request, jsonify, session, send_from_directory

# ---------------------------------------------------------------- optional deps
try:
    from googleapiclient.discovery import build as google_build
    from google.oauth2.credentials import Credentials as GoogleCredentials
    GOOGLE_AVAILABLE = True
except Exception:  # pragma: no cover - library not installed
    google_build = None
    GoogleCredentials = None
    GOOGLE_AVAILABLE = False

try:
    from atproto import Client as AtprotoClient
    ATPROTO_AVAILABLE = True
except Exception:  # pragma: no cover - library not installed
    AtprotoClient = None
    ATPROTO_AVAILABLE = False

# ---------------------------------------------------------------- config
BASE_DIR = os.path.dirname(os.path.abspath(__file__))
DATA_DIR = os.path.join(BASE_DIR, "data")
IMAGES_DIR = os.path.join(DATA_DIR, "images")
DB_PATH = os.path.join(DATA_DIR, "app.db")
STATE_PATH = os.path.join(DATA_DIR, "state.json")
LOGS_PATH = os.path.join(DATA_DIR, "logs.json")
CONFIG_PATH = os.path.join(DATA_DIR, "config.json")
CONFIG_PATH_ALT = os.path.join(DATA_DIR, "Config.json")  # capital-C fallback
DASHBOARD_PATH = os.path.join(DATA_DIR, "dashboard.json")
os.makedirs(IMAGES_DIR, exist_ok=True)

SECRET_KEY = os.environ.get("SECRET_KEY", "change-this-secret-key")
ADMIN_PASSWORD = os.environ.get("ADMIN_PASSWORD", "changeme123")

def _parse_api_keys(raw):
    """Parse a comma- or newline-separated API-key secret: split,
    strip whitespace and surrounding quotes, skip empties. (Rebuild
    #7.2: a key pasted with quotes or on separate lines must still
    load - a format slip must never look like 'no keys'.)"""
    keys = []
    for part in re.split(r"[,\n]+", raw or ""):
        k = part.strip().strip('"').strip("'").strip()
        if k:
            keys.append(k)
    return keys


GEMINI_KEYS = _parse_api_keys(os.environ.get("GEMINI_API_KEYS", ""))
GROQ_KEYS = _parse_api_keys(os.environ.get("GROQ_API_KEYS", ""))

BLOGGER_CLIENT_ID = os.environ.get("BLOGGER_CLIENT_ID", "")
BLOGGER_CLIENT_SECRET = os.environ.get("BLOGGER_CLIENT_SECRET", "")
BLOGGER_REFRESH_TOKEN = os.environ.get("BLOGGER_REFRESH_TOKEN", "")
BLOG_ID = os.environ.get("BLOG_ID", "")

PEXELS_API_KEY = os.environ.get("PEXELS_API_KEY", "")
PIXABAY_API_KEY = os.environ.get("PIXABAY_API_KEY", "")

# Bluesky accounts can come from the env secret (GitHub Actions) or from
# the dashboard database (cards). Env wins for the worker; the dashboard
# lets the user add accounts in a card and stores them in the DB.
def _load_env_bluesky_accounts():
    raw = os.environ.get("BLUESKY_ACCOUNTS", "").strip()
    if not raw:
        return []
    try:
        data = json.loads(raw)
        if isinstance(data, list):
            return [a for a in data if a.get("handle") and a.get("app_password")]
    except Exception:
        pass
    return []

ENV_BLUESKY_ACCOUNTS = _load_env_bluesky_accounts()

# Gemini models to try, in order (latest first).
# Rebuild #7.4: gemini-2.5-flash-lite is DEAD for new users (live
# API error 2026-11-23: HTTP 404 "no longer available to new users -
# use models/gemini-3.5-flash-lite") - it is now LAST, never first.
# User order 2026-11-23: install the LATEST Gemini model. Nov 2026
# lineup: Gemini 4 Argon (flagship), Gemini 4 Hydrogen (fast,
# lower-cost), Gemini 3.8 Flash (Google's recommended default for new
# projects), then 3.5 Flash-Lite. Failover walks the whole list, so a
# model that 404s costs one attempt and the next one is tried.
GEMINI_MODELS = ["gemini-4-argon", "gemini-4-hydrogen",
                 "gemini-3.8-flash", "gemini-3.5-flash-lite",
                 "gemini-3.1-flash-lite", "gemini-2.5-flash",
                 "gemini-2.0-flash", "gemini-2.5-flash-lite"]
# Groq models to try, in order (free tier, confirmed model ids on
# console.groq.com/docs/models, 2026-11-23). gpt-oss are reasoning
# models - see _groq_call (reasoning_effort + max_completion_tokens).
GROQ_MODELS = ["openai/gpt-oss-120b", "openai/gpt-oss-20b",
               "qwen/qwen3.8-27b"]

# CARD-ONLY operation: every posting limit lives inside a card
# (data/cards.json). There is no global posts-per-day, per-run,
# interval, window, forced topic or blacklist any more - the global
# cycle that used them was removed after it auto-published unwanted
# posts. Limits: 0 = UNLIMITED (no cap). The user chose unlimited.
# WARNING: unlimited posting risks a Blogger suspension and Bluesky
# spam flags / account bans. The 429 auto-pause is still active.
DEFAULT_DRY_RUN = "false"             # "true" = test mode, nothing is posted
DEFAULT_MAX_CONSECUTIVE_FAILURES = 5  # circuit breaker: pause after N failed runs
# --- per-workflow On/Off toggles (safety switches only) ---
DEFAULT_BLOGGER_ENABLED = "true"      # Blogger cards on/off
DEFAULT_BSKY_ENABLED = "true"         # Bluesky cards on/off
DEFAULT_REPLIES_ENABLED = "true"      # Bluesky replies on/off
DEFAULT_CARDS_ENABLED = "true"        # cards cycle on/off
# --- Blogger article formatting ---
DEFAULT_BLOGGER_BOLD_FORMAT = "true"  # bold headings + bold lead sentence
# --- per-card defaults (a new card starts with these) ---
DEFAULT_CARD_INTERVAL_HOURS = 0       # per-card run interval hours (reply checks)
DEFAULT_CARD_INTERVAL_MINUTES = 30    # per-card run interval minutes
DEFAULT_CARD_POSTS_PER_DAY = 0        # per-card posts per day (0 = unlimited)
DEFAULT_CARD_REPLY_OWN = "true"       # per-card: reply to own-post comments
DEFAULT_CARD_REPLY_OTHERS = "true"    # per-card: reply to others' comments
DEFAULT_CARD_LOOKBACK_DAYS = 7        # per-card: check comments from the last N days (1-30)
DEFAULT_CARD_SPREAD_MODE = "even"     # auto-spread: "even" | "best" (peak hours)
DEFAULT_CARD_LENGTH_MODE = "auto"     # article length: "auto"|"short"|"medium"|"long"
DEFAULT_CARD_TONE = "dramatic"        # tone: "dramatic"|"serious"|"funny"|"simple"
DEFAULT_CARD_JITTER_MINUTES = 10      # random +/- jitter on posting times (0-30)
DEFAULT_CARD_BSKY_IMAGE_RATIO = "16:9"  # Bluesky image ratio: "16:9"|"1:1"|"4:5"
DEFAULT_CARD_RETRY_AFTER_MINUTES = 30 # retry a failed run after this many minutes
DEFAULT_CARD_RETRY_MAX = 2            # max retries after a failed run

UTC = timezone.utc


def now_utc():
    return datetime.now(UTC)


def now_iso():
    return now_utc().isoformat()


def today_str():
    return now_utc().strftime("%Y-%m-%d")


# ---------------------------------------------------------------- flask app
app = Flask(__name__)
app.secret_key = SECRET_KEY
app.config["JSON_SORT_KEYS"] = False

# ---------------------------------------------------------------- database
def db_connect():
    conn = sqlite3.connect(DB_PATH)
    conn.row_factory = sqlite3.Row
    return conn


def init_db():
    conn = db_connect()
    cur = conn.cursor()
    cur.executescript("""
    CREATE TABLE IF NOT EXISTS accounts (
        id INTEGER PRIMARY KEY AUTOINCREMENT,
        handle TEXT UNIQUE NOT NULL,
        app_password TEXT NOT NULL,
        display_name TEXT DEFAULT '',
        active INTEGER DEFAULT 1,
        created_at TEXT NOT NULL
    );
    CREATE TABLE IF NOT EXISTS cards (
        id INTEGER PRIMARY KEY AUTOINCREMENT,
        name TEXT NOT NULL,
        type TEXT NOT NULL,
        link TEXT DEFAULT '',
        account_handle TEXT DEFAULT '',
        count INTEGER DEFAULT 1,
        interval_minutes INTEGER DEFAULT 30,
        interval_hours INTEGER DEFAULT 0,
        posts_per_day INTEGER DEFAULT 0,
        schedule_times TEXT DEFAULT '[]',
        window_start TEXT DEFAULT '',
        window_end TEXT DEFAULT '',
        text TEXT DEFAULT '',
        status TEXT DEFAULT 'active',
        done_count INTEGER DEFAULT 0,
        success_count INTEGER DEFAULT 0,
        fail_count INTEGER DEFAULT 0,
        error TEXT DEFAULT '',
        source TEXT DEFAULT 'trending',
        topic_override TEXT DEFAULT '',
        reply_own INTEGER DEFAULT 1,
        reply_others INTEGER DEFAULT 1,
        replies_per_run INTEGER DEFAULT 0,
        bold_format INTEGER DEFAULT 1,
        notes TEXT DEFAULT '',
        color TEXT DEFAULT '',
        last_run TEXT DEFAULT '',
        next_run TEXT DEFAULT '',
        created_at TEXT NOT NULL,
        updated_at TEXT NOT NULL
    );
    CREATE TABLE IF NOT EXISTS posts (
        id INTEGER PRIMARY KEY AUTOINCREMENT,
        title TEXT NOT NULL,
        url TEXT DEFAULT '',
        topic TEXT DEFAULT '',
        source TEXT DEFAULT '',
        image_url TEXT DEFAULT '',
        status TEXT DEFAULT 'published',
        created_at TEXT NOT NULL
    );
    CREATE TABLE IF NOT EXISTS replies (
        id INTEGER PRIMARY KEY AUTOINCREMENT,
        post_uri TEXT DEFAULT '',
        comment_uri TEXT DEFAULT '',
        reply_text TEXT DEFAULT '',
        account_handle TEXT DEFAULT '',
        status TEXT DEFAULT 'sent',
        created_at TEXT NOT NULL
    );
    CREATE TABLE IF NOT EXISTS logs (
        id INTEGER PRIMARY KEY AUTOINCREMENT,
        level TEXT DEFAULT 'info',
        message TEXT NOT NULL,
        created_at TEXT NOT NULL
    );
    CREATE TABLE IF NOT EXISTS settings (
        key TEXT PRIMARY KEY,
        value TEXT NOT NULL
    );
    """)
    # Migration: add the new card columns to databases created before them.
    _card_cols = {
        "interval_hours": "INTEGER DEFAULT 0",
        "posts_per_day": "INTEGER DEFAULT 0",
        "success_count": "INTEGER DEFAULT 0",
        "fail_count": "INTEGER DEFAULT 0",
        "error": "TEXT DEFAULT ''",
        "source": "TEXT DEFAULT 'trending'",
        "topic_override": "TEXT DEFAULT ''",
        "reply_own": "INTEGER DEFAULT 1",
        "reply_others": "INTEGER DEFAULT 1",
        "replies_per_run": "INTEGER DEFAULT 0",
        "lookback_days": "INTEGER DEFAULT 7",
        "bold_format": "INTEGER DEFAULT 1",
        "notes": "TEXT DEFAULT ''",
        "color": "TEXT DEFAULT ''",
        "window_start": "TEXT DEFAULT ''",
        "window_end": "TEXT DEFAULT ''",
        # Rebuild #5 (advanced card features):
        "spread_mode": "TEXT DEFAULT 'even'",
        "length_mode": "TEXT DEFAULT 'auto'",
        "tone": "TEXT DEFAULT 'dramatic'",
        "draft_only": "INTEGER DEFAULT 0",
        "days_of_week": "TEXT DEFAULT '[0,1,2,3,4,5,6]'",
        "jitter_minutes": "INTEGER DEFAULT 10",
        "labels": "TEXT DEFAULT ''",
        "max_posts_per_week": "INTEGER DEFAULT 0",
        "max_posts_per_month": "INTEGER DEFAULT 0",
        "retry_after_minutes": "INTEGER DEFAULT 30",
        "retry_max": "INTEGER DEFAULT 2",
        "replies_per_day": "INTEGER DEFAULT 0",
        "reply_never": "TEXT DEFAULT ''",
        "reply_only": "TEXT DEFAULT ''",
        "reply_skip_words": "TEXT DEFAULT ''",
        "bsky_image_ratio": "TEXT DEFAULT '16:9'",
    }
    try:
        existing = {r[1] for r in cur.execute("PRAGMA table_info(cards)").fetchall()}
        for col, ddl in _card_cols.items():
            if col not in existing:
                cur.execute(f"ALTER TABLE cards ADD COLUMN {col} {ddl}")
    except Exception:
        pass
    defaults = {
        "dry_run": str(DEFAULT_DRY_RUN),
        "max_consecutive_failures": str(DEFAULT_MAX_CONSECUTIVE_FAILURES),
        "blogger_enabled": str(DEFAULT_BLOGGER_ENABLED),
        "bsky_enabled": str(DEFAULT_BSKY_ENABLED),
        "replies_enabled": str(DEFAULT_REPLIES_ENABLED),
        "cards_enabled": str(DEFAULT_CARDS_ENABLED),
        "blogger_bold_format": str(DEFAULT_BLOGGER_BOLD_FORMAT),
        "card_default_interval_hours": str(DEFAULT_CARD_INTERVAL_HOURS),
        "card_default_interval_minutes": str(DEFAULT_CARD_INTERVAL_MINUTES),
        "card_default_posts_per_day": str(DEFAULT_CARD_POSTS_PER_DAY),
        "card_default_reply_own": str(DEFAULT_CARD_REPLY_OWN),
        "card_default_reply_others": str(DEFAULT_CARD_REPLY_OTHERS),
        "card_default_lookback_days": str(DEFAULT_CARD_LOOKBACK_DAYS),
        "card_default_spread_mode": str(DEFAULT_CARD_SPREAD_MODE),
        "card_default_length_mode": str(DEFAULT_CARD_LENGTH_MODE),
        "card_default_tone": str(DEFAULT_CARD_TONE),
        "card_default_jitter_minutes": str(DEFAULT_CARD_JITTER_MINUTES),
        "card_default_bsky_image_ratio": str(DEFAULT_CARD_BSKY_IMAGE_RATIO),
        "card_default_retry_after_minutes": str(DEFAULT_CARD_RETRY_AFTER_MINUTES),
        "card_default_retry_max": str(DEFAULT_CARD_RETRY_MAX),
    }
    for k, v in defaults.items():
        cur.execute("INSERT OR IGNORE INTO settings(key, value) VALUES(?, ?)", (k, v))
    conn.commit()
    conn.close()


_FILE_CONFIG = None


def file_config():
    """Settings from data/config.json (the GitHub-only control panel).
    Edit this file in the repo to change limits - no server needed.
    Returns {} when the file is missing. Falls back to data/Config.json
    (capital C) so a case difference can never silently break settings
    again - that exact bug once made the worker ignore Pause."""
    global _FILE_CONFIG
    if _FILE_CONFIG is None:
        _FILE_CONFIG = {}
        path = CONFIG_PATH
        if not os.path.exists(path) and os.path.exists(CONFIG_PATH_ALT):
            print("config.json missing - using Config.json (case fallback)",
                  flush=True)
            path = CONFIG_PATH_ALT
        if os.path.exists(path):
            try:
                with open(path, "r", encoding="utf-8") as f:
                    data = json.load(f)
                if isinstance(data, dict):
                    _FILE_CONFIG = data
            except Exception as e:
                print(f"config.json load failed: {e}", flush=True)
    return _FILE_CONFIG


def get_setting(key, default=""):
    # data/config.json wins over the database (GitHub-only control).
    cfg = file_config()
    if key in cfg:
        return str(cfg[key])
    conn = db_connect()
    try:
        row = conn.execute("SELECT value FROM settings WHERE key=?", (key,)).fetchone()
        return row["value"] if row else default
    finally:
        conn.close()


def set_setting(key, value):
    conn = db_connect()
    try:
        conn.execute("INSERT INTO settings(key, value) VALUES(?, ?) "
                     "ON CONFLICT(key) DO UPDATE SET value=excluded.value",
                     (key, str(value)))
        conn.commit()
    finally:
        conn.close()


# In-memory log for THIS worker run (rebuild #7.2). The SQLite DB does
# not survive GitHub Actions runners, so the dashboard-visible log is
# data/logs.json, mirrored from this list at the end of the run.
_RUN_LOGS = []
_RUN_LOGS_FLUSHED = 0
LOGS_JSON_MAX = 200


def _log_card_from_message(message):
    """Card name from a "card 'Name': ..." log prefix, or ''."""
    m = re.match(r"card '([^']+)'", str(message or ""))
    return m.group(1) if m else ""


def log(level, message):
    """Write a log row (dashboard activity log) and print it."""
    msg = str(message)[:1000]
    try:
        _RUN_LOGS.append({"level": level, "message": msg,
                          "created_at": now_iso(),
                          "card": _log_card_from_message(msg)})
        if len(_RUN_LOGS) > 500:
            del _RUN_LOGS[:-500]
    except Exception:
        pass
    try:
        conn = db_connect()
        try:
            conn.execute("INSERT INTO logs(level, message, created_at) VALUES(?, ?, ?)",
                         (level, msg, now_iso()))
            conn.execute("DELETE FROM logs WHERE id NOT IN "
                         "(SELECT id FROM logs ORDER BY id DESC LIMIT 500)")
            conn.commit()
        finally:
            conn.close()
    except Exception:
        pass
    print(f"[{now_iso()}] {level.upper()}: {msg}", flush=True)


# ---------------------------------------------------------------- json state file
# GitHub Actions runners are fresh VMs, so the SQLite DB does not survive
# between runs. data/state.json IS committed back to the repo, so dedup
# (posted news, replied comments) survives across runs.
def load_state():
    # BACKUP PLAN: if state.json is corrupt, fall back to state.json.bak.
    for path in (STATE_PATH, STATE_PATH + ".bak"):
        if os.path.exists(path):
            try:
                with open(path, "r", encoding="utf-8") as f:
                    data = json.load(f)
                if isinstance(data, dict):
                    if path.endswith(".bak"):
                        print("state.json corrupt - restored from state.json.bak", flush=True)
                    return data
            except Exception:
                continue
    return {"posted_urls": [], "posted_topics": [], "replied_comments": [],
            "last_run": "", "runs": 0}


def backup_state():
    """Keep a backup copy of state.json before overwriting it."""
    try:
        if os.path.exists(STATE_PATH):
            import shutil
            shutil.copyfile(STATE_PATH, STATE_PATH + ".bak")
    except Exception:
        pass


def save_state(state):
    try:
        backup_state()
        state["posted_urls"] = state.get("posted_urls", [])[-500:]
        state["posted_topics"] = state.get("posted_topics", [])[-500:]
        state["replied_comments"] = state.get("replied_comments", [])[-2000:]
        state["issues"] = state.get("issues", [])[-50:]
        # Rebuild #7.3: cap the promo cooldown stores too. They are
        # DICTS {key: iso_timestamp} (not lists) - keep only the 500
        # newest entries. (_store_record already prunes them to 7 days
        # on write; this is a safety cap so state.json stays small.)
        for _key in ("posted_promo_topics", "posted_promo_captions",
                     "posted_promo_link_topics", "posted_promo_accounts"):
            _store = state.get(_key)
            if isinstance(_store, dict) and len(_store) > 500:
                _items = sorted(_store.items(),
                                key=lambda kv: str(kv[1] or ""))
                state[_key] = dict(_items[-500:])
        with open(STATE_PATH, "w", encoding="utf-8") as f:
            json.dump(state, f, ensure_ascii=False, indent=2)
    except Exception as e:
        print(f"state save failed: {e}", flush=True)


def merge_worker_state(remote, local):
    """Merge a worker run's just-saved state (local) into the remote
    state.json (fresh from origin/main) for the workflow commit-back.
    Rebuild #7.5: the old rebase-based commit-back NEVER persisted
    state (zero 'automation state update' commits in the repo
    history) - a rebase conflicts on data/state.json whenever the
    dashboard commits a flag mid-run, the abort drops the push, and
    the step still exits 0. Merging is deterministic: newest
    timestamps win for cooldown stores, counters take the max,
    dashboard flags set after this run started (remote, non-empty)
    are kept so a Run-now clicked mid-run is never lost. Pure
    function (no I/O) - unit-tested."""
    remote = remote if isinstance(remote, dict) else {}
    local = local if isinstance(local, dict) else {}
    merged = dict(remote)
    for k in ("runs", "consecutive_failures"):
        try:
            merged[k] = max(int(remote.get(k) or 0), int(local.get(k) or 0))
        except Exception:
            merged[k] = remote.get(k) or local.get(k) or 0
    for k in ("last_run", "issues"):
        if local.get(k) is not None:
            merged[k] = local[k]
    for k in ("posted_promo_topics", "posted_promo_captions",
              "posted_promo_link_topics", "posted_promo_accounts",
              "last_bsky_post_at"):
        m = dict(remote.get(k) or {})
        for kk, vv in (local.get(k) or {}).items():
            if kk not in m or str(vv or "") >= str(m.get(kk) or ""):
                m[kk] = vv
        if m:
            merged[k] = m
    for k, cap in (("posted_urls", 500), ("posted_topics", 500),
                   ("replied_comments", 2000), ("recent_articles", 50)):
        seen = {}
        for e in (remote.get(k) or []) + (local.get(k) or []):
            key = e.get("url") if isinstance(e, dict) else e
            seen[key] = e
        if seen:
            merged[k] = list(seen.values())[-cap:]
    for k in ("file_card_stats", "file_card_runs", "file_card_retries"):
        m = dict(remote.get(k) or {})
        m.update(local.get(k) or {})
        if m:
            merged[k] = m
    for k in ("run_card_now", "test_card_now"):
        if remote.get(k):
            merged[k] = remote[k]
        elif local.get(k):
            merged[k] = local[k]
    return merged


def append_logs_json():
    """Mirror this run's logs into data/logs.json (newest first, last
    ~200 entries) for the repo commit, so the static dashboard can show
    what the worker did. Merges with the file's previous entries (the
    SQLite DB does not survive GitHub Actions runners, so the DB alone
    cannot supply history). Only entries not yet flushed are added, so
    calling it twice in one run never duplicates. Never raises - a
    failed write only prints a warning, the run is unaffected.
    Rebuild #7.2."""
    global _RUN_LOGS_FLUSHED
    try:
        prev = []
        if os.path.exists(LOGS_PATH):
            try:
                with open(LOGS_PATH, "r", encoding="utf-8") as f:
                    data = json.load(f)
                if isinstance(data, list):
                    prev = [e for e in data if isinstance(e, dict)]
            except Exception:
                prev = []
        new = _RUN_LOGS[_RUN_LOGS_FLUSHED:]
        _RUN_LOGS_FLUSHED = len(_RUN_LOGS)
        merged = (list(reversed(new)) + prev)[:LOGS_JSON_MAX]
        with open(LOGS_PATH, "w", encoding="utf-8") as f:
            json.dump(merged, f, ensure_ascii=False, indent=2)
    except Exception as e:
        print(f"logs.json write failed: {e}", flush=True)


def write_dashboard_json(state):
    """Write data/dashboard.json - the status file the STATIC Pages
    dashboard reads. Contains NO secrets (only public status: posts,
    logs, trending topics, settings). The workflow commits it back so
    GitHub Pages always shows the latest run."""
    try:
        conn = db_connect()
        try:
            posts = [dict(r) for r in conn.execute(
                "SELECT title, url, topic, source, image_url, created_at FROM posts "
                "ORDER BY id DESC LIMIT 10").fetchall()]
            if not posts:
                # GitHub Actions runners have an empty DB - show the
                # articles recorded in state.json instead.
                posts = [dict(a) for a in (state.get("recent_articles") or [])[:10]]
            # Rebuild #7.2: the dashboard-visible log is data/logs.json
            # (merged across runs, newest first) - the SQLite DB only
            # holds this run. Fall back to the DB if the file is missing.
            logs = []
            try:
                if os.path.exists(LOGS_PATH):
                    with open(LOGS_PATH, "r", encoding="utf-8") as f:
                        data = json.load(f)
                    if isinstance(data, list):
                        logs = [e for e in data
                                if isinstance(e, dict)][:50]
            except Exception:
                logs = []
            if not logs:
                logs = [dict(r) for r in conn.execute(
                    "SELECT level, message, created_at FROM logs "
                    "ORDER BY id DESC LIMIT 50").fetchall()]
            total_posts = conn.execute("SELECT COUNT(*) c FROM posts").fetchone()["c"]
            total_replies = conn.execute("SELECT COUNT(*) c FROM replies").fetchone()["c"]
        finally:
            conn.close()
        try:
            trending = get_bluesky_trending(limit=10)
        except Exception:
            trending = []
        accounts_detail = []
        for a in list_accounts():
            h = a["handle"]
            accounts_detail.append({
                "handle": h,
                "enabled": account_enabled(h),
                "posts_limit": account_posts_limit(h),
                "posts_today": posts_today_for_account(state, h),
            })
        # Enriched file cards (data/cards.json) for the dashboard: status
        # badge, last run, next 5 runs (Dhaka), success/fail counters.
        file_stats = state.get("file_card_stats", {}) or {}
        file_runs = state.get("file_card_runs", {}) or {}
        file_cards_out = []
        for c in load_file_cards():
            nm = c.get("name", "")
            s = file_stats.get(nm, {}) or {}
            st = (c.get("status") or "active")
            if st != "active":
                computed = "paused"
            elif s.get("last_ok") is False and int(s.get("fail", 0) or 0) > 0:
                computed = "error"
            else:
                computed = "active"
            file_cards_out.append({
                "name": nm, "type": c.get("type", ""), "status": st,
                "computed_status": computed,
                "link": c.get("link", ""),
                "account_handle": c.get("account_handle", ""),
                "interval_minutes": card_interval_minutes(c),
                "posts_per_day": card_posts_per_day(c),
                "schedule_times": _parse_schedule_times(c),
                "last_run": file_runs.get(nm, ""),
                "runs_today": card_runs_today(state, nm),
                "posts_today": card_posts_today(state, nm),
                "next_runs": [d.isoformat()
                              for d in next_runs_for_card(
                                  c, count=5,
                                  last_run_iso=file_runs.get(nm, ""))],
                "next_post_times": [d.isoformat()
                                    for d in next_post_times_for_card(c, count=5)],
                "success": int(s.get("success", 0) or 0),
                "fail": int(s.get("fail", 0) or 0),
                "last_error": s.get("last_error", ""),
                "color": c.get("color", ""),
                "notes": c.get("notes", ""),
                "source": c.get("source", "trending"),
                "topic_override": c.get("topic_override", ""),
                "bold_format": c.get("bold_format", True),
                "window_start": c.get("window_start", ""),
                "window_end": c.get("window_end", ""),
                "posts_per_run": card_posts_per_run(c),
                "reply_own": c.get("reply_own", True),
                "reply_others": c.get("reply_others", True),
                "replies_per_run": c.get("replies_per_run", 0),
                "lookback_days": card_reply_settings(c)[3],
                "spread_mode": card_spread_mode(c),
                "length_mode": card_length_mode(c),
                "tone": card_tone(c),
                "draft_only": card_draft_only(c),
                "days_of_week": sorted(card_days_of_week(c)),
                "jitter_minutes": card_jitter_minutes(c),
                "labels": card_labels(c),
                "max_posts_per_week": card_max_posts_per_week(c),
                "max_posts_per_month": card_max_posts_per_month(c),
                "retry_after_minutes": card_retry_after_minutes(c),
                "retry_max": card_retry_max(c),
                "replies_per_day": card_replies_per_day(c),
                "reply_never": c.get("reply_never", ""),
                "reply_only": c.get("reply_only", ""),
                "reply_skip_words": c.get("reply_skip_words", ""),
                "bsky_image_ratio": card_bsky_image_ratio(c),
            })
        data = {
            "generated_at": now_iso(),
            "last_run": state.get("last_run", ""),
            "runs": state.get("runs", 0),
            "stats": {
                "blogger_today": blogger_posts_today(),
                "replies_today": replies_today(),
                "total_posts": total_posts,
                "total_replies": total_replies,
                "accounts": len(list_accounts()),
            },
            "settings": {k: get_setting(k, "") for k in
                         ("paused", "dry_run",
                          "max_consecutive_failures", "blogger_enabled",
                          "bsky_enabled", "replies_enabled", "cards_enabled",
                          "blogger_bold_format",
                          "card_default_interval_hours",
                          "card_default_interval_minutes",
                          "card_default_posts_per_day",
                          "card_default_reply_own",
                          "card_default_reply_others",
                          "card_default_lookback_days",
                          "card_default_spread_mode",
                          "card_default_length_mode",
                          "card_default_tone",
                          "card_default_jitter_minutes",
                          "card_default_bsky_image_ratio",
                          "card_default_retry_after_minutes",
                          "card_default_retry_max")},
            "file_card_runs": state.get("file_card_runs", {}),
            "file_card_stats": file_stats,
            "file_cards": file_cards_out,
            "account_handles": [a["handle"] for a in list_accounts()],
            "accounts_detail": accounts_detail,
            "health": health_check(state),
            "issues": get_issues(state),
            "dry_run": is_dry_run(),
            "circuit_breaker": {
                "consecutive_failures": int(state.get("consecutive_failures", 0) or 0),
                "open": int(state.get("consecutive_failures", 0) or 0) >= 5,
            },
            "trending": trending,
            "recent_posts": posts,
            "logs": logs,
        }
        with open(DASHBOARD_PATH, "w", encoding="utf-8") as f:
            json.dump(data, f, ensure_ascii=False, indent=2)
    except Exception as e:
        print(f"dashboard.json write failed: {e}", flush=True)


def slugify(text):
    text = re.sub(r"[^a-zA-Z0-9]+", "-", (text or "").strip().lower()).strip("-")
    return text[:80] or "post"

# ---------------------------------------------------------------- AI clients
# Gemini writes, Groq handles the rest. Keys rotate (failover) so one dead
# key never stops the run. Gemini quota is per Google project, Groq quota
# is per Groq account - so keys MUST come from different projects/accounts
# for the quota to multiply.

def _api_error_detail(r):
    """Short error reason from an API error response (never the key):
    e.g. 'API key not valid', 'model not found', 'quota exceeded'.
    Truncated to ~150 chars so the log stays readable."""
    try:
        err = (r.json() or {}).get("error") or {}
        msg = (err.get("message") or "").strip()
        if msg:
            return msg[:150]
    except Exception:
        pass
    try:
        return (r.text or "").strip()[:150] or f"HTTP {r.status_code}"
    except Exception:
        return f"HTTP {r.status_code}"


def _gemini_call(key, model, prompt, max_tokens):
    """One Gemini call. Returns (text, http_code, error_detail).
    error_detail is '' on success. Network errors return code 0."""
    url = (f"https://generativelanguage.googleapis.com/v1beta/models/{model}"
           f":generateContent?key={key}")
    body = {"contents": [{"parts": [{"text": prompt}]}],
            "generationConfig": {"maxOutputTokens": max_tokens,
                                 "temperature": 0.7}}
    try:
        r = requests.post(url, json=body, timeout=60)
    except Exception as e:
        return None, 0, f"network: {type(e).__name__}: {e}"[:150]
    if r.status_code != 200:
        return None, r.status_code, _api_error_detail(r)
    try:
        data = r.json()
        text = data["candidates"][0]["content"]["parts"][0]["text"]
        return (text or "").strip(), 200, ""
    except Exception:
        keys = []
        try:
            keys = sorted((r.json() or {}).keys())[:6]
        except Exception:
            pass
        return None, 200, ("bad response shape (no candidates/parts; "
                           f"top-level keys={','.join(keys) or 'none'})")


def _gemini_vision_call(key, model, image_b64, mime, prompt):
    """One Gemini VISION call (image + text). Returns
    (text, http_code, error_detail) - same shape as _gemini_call.
    Rebuild #7.7: Groq cannot see images (its Llama 4 vision
    models were retired in 2026; gpt-oss is text-only), so Gemini -
    the only provider that can see images - is the judge of
    whether a photo matches its news story. The image rides as
    inline_data; temperature is low (0.2) so the YES/NO answer is
    deterministic; maxOutputTokens is small (200) because only a
    YES/NO plus one short reason is needed. Network errors return
    code 0."""
    url = (f"https://generativelanguage.googleapis.com/v1beta/models/{model}"
           f":generateContent?key={key}")
    body = {"contents": [{"parts": [
        {"inline_data": {"mime_type": mime, "data": image_b64}},
        {"text": prompt}]}],
        "generationConfig": {"maxOutputTokens": 200, "temperature": 0.2}}
    try:
        r = requests.post(url, json=body, timeout=90)
    except Exception as e:
        return None, 0, f"network: {type(e).__name__}: {e}"[:150]
    if r.status_code != 200:
        return None, r.status_code, _api_error_detail(r)
    try:
        data = r.json()
        text = data["candidates"][0]["content"]["parts"][0]["text"]
        return (text or "").strip(), 200, ""
    except Exception:
        keys = []
        try:
            keys = sorted((r.json() or {}).keys())[:6]
        except Exception:
            pass
        return None, 200, ("bad response shape (no candidates/parts; "
                           f"top-level keys={','.join(keys) or 'none'})")


def gemini_text(prompt, max_tokens=1500):
    """Write with Gemini. Returns text or '' (never raises).
    Rebuild #7.2: on total failure, log the SPECIFIC reason (how many
    keys were found, which models were tried, the exact error per
    status) instead of failing silently - the workflow log must show
    WHY the AI is down. Key VALUES are never logged, only counts."""
    if not GEMINI_KEYS:
        log("warning", "gemini_text: no GEMINI_API_KEYS configured (0 keys)")
        return ""
    keys = GEMINI_KEYS[:]
    random.shuffle(keys)
    seen = {}  # (code, detail) -> attempts
    for model in GEMINI_MODELS:
        for key in keys:
            try:
                text, code, detail = _gemini_call(key, model, prompt, max_tokens)
                if text:
                    return text
                if code == 429:
                    time.sleep(2)
                sig = (code, detail or "no text returned")
                seen[sig] = seen.get(sig, 0) + 1
            except Exception as e:
                sig = (0, f"network: {type(e).__name__}")
                seen[sig] = seen.get(sig, 0) + 1
    summary = "; ".join(
        f"HTTP {c} x{n}: {d}" for (c, d), n in list(seen.items())[:3])
    log("warning", f"gemini_text: all {len(keys)} key(s) x "
                   f"{len(GEMINI_MODELS)} model(s) failed - {summary}")
    return ""


def _groq_shape_detail(data, problem, finish=None):
    """Short shape summary of a Groq HTTP 200 response with no usable
    text (never the key, never the text): which top-level keys exist,
    how many choices, the finish_reason. Used so the log shows WHY
    Groq gave no text instead of swallowing it (rebuild #7.4)."""
    try:
        keys = sorted((data or {}).keys())[:6] if isinstance(data, dict) else []
        n = len((data or {}).get("choices") or [])
        out = f"{problem} (keys={','.join(keys) or 'none'}, choices={n}"
        if finish is not None:
            out += f", finish_reason={finish}"
        return (out + ")")[:150]
    except Exception:
        return problem[:150]


def _groq_call(key, model, prompt, max_tokens):
    """One Groq call. Returns (text, http_code, error_detail).
    error_detail is '' on success. Network errors return code 0.
    Rebuild #7.4: gpt-oss are REASONING models - their reasoning
    tokens eat the output budget, so a tiny max_tokens (or the legacy
    `max_tokens` param) can return HTTP 200 with NO text at all.
    The request therefore uses `max_completion_tokens` and
    `reasoning_effort: low` for gpt-oss, and when a 200 still has no
    text the detail describes the RESPONSE SHAPE (choices present?
    how many? content null or empty? finish_reason? reasoning
    present?) - never the key or the full text."""
    url = "https://api.groq.com/openai/v1/chat/completions"
    headers = {"Authorization": f"Bearer {key}", "Content-Type": "application/json"}
    body = {"model": model,
            "messages": [{"role": "user", "content": prompt}],
            "max_completion_tokens": max_tokens, "temperature": 0.7}
    if "gpt-oss" in model:
        body["reasoning_effort"] = "low"
    try:
        r = requests.post(url, json=body, headers=headers, timeout=60)
    except Exception as e:
        return None, 0, f"network: {type(e).__name__}: {e}"[:150]
    if r.status_code != 200:
        return None, r.status_code, _api_error_detail(r)
    try:
        data = r.json()
    except Exception:
        return None, 200, "bad JSON response"
    if isinstance(data, dict) and data.get("error"):
        err = data["error"]
        msg = (err.get("message") if isinstance(err, dict)
               else str(err)) or ""
        return None, 200, f"error field: {msg}"[:150]
    choices = data.get("choices") if isinstance(data, dict) else None
    if not isinstance(choices, list) or not choices:
        return None, 200, _groq_shape_detail(data, "no text returned: no choices")
    first = choices[0] if isinstance(choices[0], dict) else {}
    finish = first.get("finish_reason")
    msg = first.get("message")
    if not isinstance(msg, dict):
        return None, 200, _groq_shape_detail(
            data, "no text returned: no message in choice", finish)
    content = msg.get("content")
    if isinstance(content, str) and content.strip():
        return content.strip(), 200, ""
    reasoning = msg.get("reasoning")
    note = "content null" if content is None else "content empty"
    extra = ""
    if isinstance(reasoning, str) and reasoning:
        extra = f", reasoning present ({len(reasoning)} chars)"
    return None, 200, (f"no text returned ({note}, choices={len(choices)}, "
                       f"finish_reason={finish}{extra})")[:150]


def groq_text(prompt, max_tokens=800):
    """Fast replies / small jobs with Groq. Returns text or ''.
    Rebuild #7.2: on total failure, log the SPECIFIC reason (key
    count, models tried, exact error) - never the key values."""
    if not GROQ_KEYS:
        log("warning", "groq_text: no GROQ_API_KEYS configured (0 keys)")
        return ""
    keys = GROQ_KEYS[:]
    random.shuffle(keys)
    seen = {}  # (code, detail) -> attempts
    for model in GROQ_MODELS:
        for key in keys:
            try:
                text, code, detail = _groq_call(key, model, prompt, max_tokens)
                if text:
                    return text
                if code == 429:
                    time.sleep(2)
                sig = (code, detail or "no text returned")
                seen[sig] = seen.get(sig, 0) + 1
            except Exception as e:
                sig = (0, f"network: {type(e).__name__}")
                seen[sig] = seen.get(sig, 0) + 1
    summary = "; ".join(
        f"HTTP {c} x{n}: {d}" for (c, d), n in list(seen.items())[:3])
    log("warning", f"groq_text: all {len(keys)} key(s) x "
                   f"{len(GROQ_MODELS)} model(s) failed - {summary}")
    return ""


def ai_write(prompt, max_tokens=1500):
    """Primary writer: Gemini, Groq as fallback. Rebuild #7.2: when
    BOTH fail, log one summary line (key counts only, never values)
    so the workflow log shows the AI is down and why - captions then
    fall back to the news headline, never to a generic hook."""
    text = gemini_text(prompt, max_tokens=max_tokens)
    if text:
        return text
    text = groq_text(prompt, max_tokens=max_tokens)
    if text:
        return text
    log("warning", f"ai_write: Gemini ({len(GEMINI_KEYS)} key(s)) and Groq "
                   f"({len(GROQ_KEYS)} key(s)) both failed - captions will "
                   f"fall back to the news headline")
    return ""


def _ai_health_check():
    """Startup AI health check (rebuild #7.3, model failover #7.4).
    Logs the key counts (counts only, never values) and the result
    of ONE tiny test call per provider, so the workflow log shows WHY
    Gemini/Groq fail even when the photo step fails first and AI is
    never attempted for a caption. Rebuild #7.4: the check walks
    EVERY model in order (up to 3 keys per model - a retired model
    404s for every key, so trying all 10 keys per model would only
    waste time) and logs WHICH model answered ok, e.g. 'ai health:
    gemini ok (gemini-3.5-flash-lite)'. A provider whose first model
    is dead must NOT report FAIL when a later model works.
    Called at worker startup, before the card cycle. Never raises."""
    try:
        log("info", f"ai health: Gemini {len(GEMINI_KEYS)} key(s), "
                    f"Groq {len(GROQ_KEYS)} key(s) configured")
        for label, keys, models, call in (
                ("gemini", GEMINI_KEYS, GEMINI_MODELS, _gemini_call),
                ("groq", GROQ_KEYS, GROQ_MODELS, _groq_call)):
            if not keys:
                log("warning", f"ai health: {label} FAIL (0 keys configured)")
                continue
            if not models:
                log("warning", f"ai health: {label} FAIL (no models configured)")
                continue
            ok_model = None
            seen = {}  # (code, detail) -> attempts
            for model in models:
                for key in keys[:3]:
                    try:
                        text, code, err = call(key, model,
                                               AI_HEALTH_TEST_PROMPT,
                                               AI_HEALTH_MAX_TOKENS)
                    except Exception as e:
                        code, err, text = 0, f"network: {type(e).__name__}", None
                    if text:
                        ok_model = model
                        break
                    sig = (code, err or "no text returned")
                    seen[sig] = seen.get(sig, 0) + 1
                if ok_model:
                    break
            if ok_model:
                log("info", f"ai health: {label} ok ({ok_model})")
            else:
                summary = "; ".join(
                    f"HTTP {c} x{n}: {d}"
                    for (c, d), n in list(seen.items())[:3])
                log("warning", f"ai health: {label} FAIL (tried "
                               f"{len(models)} model(s) - {summary})")
    except Exception as e:
        log("warning", f"ai health check failed: {e}")


# ---------------------------------------------------------------- photos
# STRICT RULE: no photo = no post. Real stock photos first (clean, no
# logo/text). Pollinations (AI image, nologo) is only the last fallback.
# A topic is dropped ONLY when no image can be obtained from any source.
BAD_PHOTO_WORDS = ("logo", "watermark", "banner", "text overlay", "advert")


def _photo_ok(meta):
    title = (meta.get("alt") or meta.get("title") or "").lower()
    return not any(w in title for w in BAD_PHOTO_WORDS)


def _pexels_photo(topic):
    """First real photo from Pexels (needs PEXELS_API_KEY). Rebuild
    #7.4: logs WHY nothing is found (no key / HTTP status / result
    count / rejection reason) instead of silently returning None -
    the workflow log must show which source failed and why."""
    if not PEXELS_API_KEY:
        log("info", "pexels: API key not configured - skipping")
        return None
    try:
        r = requests.get("https://api.pexels.com/v1/search",
                         params={"query": topic, "per_page": 5, "orientation": "landscape"},
                         headers={"Authorization": PEXELS_API_KEY}, timeout=20)
        if r.status_code != 200:
            log("info", f"pexels: search HTTP {r.status_code} for '{topic[:60]}'")
            return None
        photos = r.json().get("photos", [])
        log("info", f"pexels: {len(photos)} result(s) for '{topic[:60]}'")
        for p in photos:
            src = p.get("src", {})
            url = src.get("large2x") or src.get("large") or src.get("original")
            meta = {"alt": p.get("alt") or "", "title": ""}
            if url and _photo_ok(meta):
                # Rebuild #7.6: the photo page URL + the photo's own
                # description are the relevance evidence (Pexels has
                # no keyword slug in its page URL).
                return {"url": url, "source": "pexels", "alt": meta["alt"],
                        "page_url": p.get("url") or "",
                        "page_title": p.get("alt") or ""}
            if url:
                log("info", f"pexels: rejected candidate (bad title): {url[:100]}")
    except Exception as e:
        log("warning", f"pexels error: {e}")
    return None


def _pixabay_photo(topic):
    """First real photo from Pixabay (needs PIXABAY_API_KEY). Rebuild
    #7.4: logs WHY nothing is found, like _pexels_photo."""
    if not PIXABAY_API_KEY:
        log("info", "pixabay: API key not configured - skipping")
        return None
    try:
        r = requests.get("https://pixabay.com/api/",
                         params={"key": PIXABAY_API_KEY, "q": topic,
                                 "image_type": "photo", "per_page": 5,
                                 "orientation": "horizontal", "safesearch": "true"},
                         timeout=20)
        if r.status_code != 200:
            log("info", f"pixabay: search HTTP {r.status_code} for '{topic[:60]}'")
            return None
        hits = r.json().get("hits", [])
        log("info", f"pixabay: {len(hits)} result(s) for '{topic[:60]}'")
        for h in hits:
            url = h.get("largeImageURL") or h.get("webformatURL")
            meta = {"alt": h.get("tags") or "", "title": ""}
            if url and _photo_ok(meta):
                # Rebuild #7.6: the Pixabay photo page URL carries a
                # descriptive slug (relevance evidence) and the tags
                # describe the photo.
                return {"url": url, "source": "pixabay", "alt": meta["alt"],
                        "page_url": h.get("pageURL") or "",
                        "page_title": h.get("tags") or ""}
            if url:
                log("info", f"pixabay: rejected candidate (bad title): {url[:100]}")
    except Exception as e:
        log("warning", f"pixabay error: {e}")
    return None


def _openverse_photos(topic, limit=5):
    """Up to `limit` real-photo candidates from Openverse (free, no
    key). Returns a list of {url, source, alt} dicts (may be empty).
    Several candidates are needed because a single file may 429 or
    fail verification - the caller tries each until one downloads
    and verifies as a real photo (rebuild #7.3). Rebuild #7.4: logs
    the HTTP status, result count and rejection reasons."""
    try:
        r = requests.get("https://api.openverse.org/v1/images/",
                         params={"q": topic, "page_size": limit,
                                 "license_type": "commercial"},
                         timeout=20)
        if r.status_code != 200:
            log("info", f"openverse: search HTTP {r.status_code} for '{topic[:60]}'")
            return []
        results = r.json().get("results", [])
        log("info", f"openverse: {len(results)} result(s) for '{topic[:60]}'")
        out = []
        for item in results[:limit]:
            url = item.get("url") or item.get("foreign_landing_url")
            meta = {"alt": item.get("title") or "", "title": item.get("title") or ""}
            if url and _photo_ok(meta):
                # Rebuild #7.6: the foreign landing page (the page
                # hosting the image) + the item title are the
                # relevance evidence.
                out.append({"url": url, "source": "openverse",
                            "alt": meta["alt"],
                            "page_url": item.get("foreign_landing_url") or "",
                            "page_title": item.get("title") or ""})
            elif url:
                log("info", f"openverse: rejected candidate (bad title): {url[:100]}")
        return out
    except Exception as e:
        log("warning", f"openverse error: {e}")
        return []


def _openverse_photo(topic):
    found = _openverse_photos(topic, limit=1)
    return found[0] if found else None


# Browser User-Agent for keyless image searches (Google/Bing serve a
# bot page or a 403 to a bare requests UA).
_IMAGE_SEARCH_UA = ("Mozilla/5.0 (Windows NT 10.0; Win64; x64) "
                    "AppleWebKit/537.36 (KHTML, like Gecko) "
                    "Chrome/120.0.0.0 Safari/537.36")


def _wikimedia_photos(topic, limit=5):
    """Real-photo candidates from Wikimedia Commons (free, no key).
    Returns a list of {url, source, alt} dicts (may be empty).
    Rebuild #7.4: a keyless source so a photo can be found even when
    Pexels/Pixabay have no key and Openverse returns nothing. The
    1280px thumbnail URL is used (iiurlwidth=1280); mime must be
    JPEG/PNG and the file at least 400px wide."""
    try:
        r = requests.get("https://commons.wikimedia.org/w/api.php",
                         params={"action": "query", "generator": "search",
                                 "gsrsearch": f"{topic} filetype:bitmap",
                                 "gsrnamespace": 6, "gsrlimit": limit,
                                 "prop": "imageinfo",
                                 "iiprop": "url|size|mime", "iiurlwidth": 1280,
                                 "format": "json"},
                         headers={"User-Agent": _IMAGE_SEARCH_UA},
                         timeout=20)
        if r.status_code != 200:
            log("info", f"wikimedia: search HTTP {r.status_code} for '{topic[:60]}'")
            return []
        pages = (r.json().get("query") or {}).get("pages", {})
        log("info", f"wikimedia: {len(pages)} result(s) for '{topic[:60]}'")
        out = []
        for page in pages.values():
            info = (page.get("imageinfo") or [{}])[0]
            mime = info.get("mime") or ""
            width = info.get("width") or 0
            url = info.get("thumburl") or info.get("url") or ""
            if not url:
                continue
            if mime not in ("image/jpeg", "image/png"):
                log("info", f"wikimedia: rejected candidate (mime={mime or 'unknown'}): {url[:100]}")
                continue
            if width and width < 400:
                log("info", f"wikimedia: rejected candidate (width {width}px < 400): {url[:100]}")
                continue
            meta = {"alt": page.get("title") or "", "title": page.get("title") or ""}
            if _photo_ok(meta):
                # Rebuild #7.6: the Commons file page (descriptionurl)
                # + the file title are the relevance evidence - the
                # file title usually names the subject.
                out.append({"url": url, "source": "wikimedia",
                            "alt": meta["alt"],
                            "page_url": info.get("descriptionurl") or "",
                            "page_title": page.get("title") or ""})
            else:
                log("info", f"wikimedia: rejected candidate (bad title): {url[:100]}")
        return out[:limit]
    except Exception as e:
        log("warning", f"wikimedia error: {e}")
        return []


def _add_image_url(found, seen, url, source, topic, page_url=None,
                   page_title=None):
    """Append one scraped image URL to `found` (deduped, logo/icon
    and AI URLs rejected, webp skipped - the download gate only
    accepts JPEG/PNG). Rebuild #7.4 (live finding): Bing's results
    HTML double-encodes its JSON (quotes become &quot;), so a raw
    regex match can run on through the escaped blob and swallow the
    page URL + the next entry's image URL as one junk string - the
    URL is therefore HTML-unescaped, cut at the first quote /
    whitespace, and must end with a real image extension. Search
    engines' own UI images (bing.com, google.com, gstatic) are
    never real photos. Rebuild #7.6: page_url / page_title are the
    SOURCE PAGE of the image (Bing's purl/t, Google's ru/pt) so the
    caller can check the photo is RELEVANT to the story; a candidate
    with no source page cannot be verified relevant."""
    try:
        u = html_lib.unescape(str(url or "")).strip()
        for stop in ('"', "'", " ", "\t", "\n", "<"):
            if stop in u:
                u = u.split(stop, 1)[0]
        if not u.startswith("http") or u in seen:
            return
        seen.add(u)
        if u.lower().split("?")[0].endswith(".webp"):
            return
        if not re.search(r"\.(?:jpg|jpeg|png)(?:\?|$)", u, re.IGNORECASE):
            return
        netloc = (urlparse(u).netloc or "").lower()
        if any(h in netloc for h in ("bing.com", "google.com",
                                     "gstatic", "googleusercontent")):
            return
        if _is_logo_image_url(u) or _is_pollinations_url(u):
            return
        found.append({"url": u, "source": source, "alt": topic,
                      "page_url": page_url or "",
                      "page_title": page_title or ""})
    except Exception:
        return


def _extract_image_search_urls(html, source, topic, limit=5):
    """Direct image URLs from an image-search results page. Google
    Images embeds the original URL as "ou":"https://..."; Bing
    Images as "murl":"https://...". Falls back to any direct image
    file URL in the page. Google/gstatic hosts and logo/icon URLs
    are skipped. Returns a list of {url, source, alt} dicts.
    Rebuild #7.6: each entry also carries its SOURCE PAGE - Bing's
    "purl" (page URL) + "t" (page title), Google's "ru" + "pt" - so
    the caller can check the photo is RELEVANT to the story (the
    source page must be about the story, _photo_relevant). The page
    info is taken from the same result entry as the image URL (the
    text between this entry's image URL and the next entry's), never
    from a neighbouring entry."""
    # Bing double-encodes its JSON (quotes become &quot;): unescape
    # the page FIRST, or one regex match swallows a page URL + the
    # next entry's image URL as a single junk string.
    html = html_lib.unescape(html or "")
    found, seen = [], set()
    matches = list(re.finditer(
        r'"(?:ou|murl)"\s*:\s*"(https?://[^"\\]+)"', html or ""))
    for i, m in enumerate(matches):
        end = (matches[i + 1].start() if i + 1 < len(matches)
               else m.end() + 1000)
        window = (html or "")[m.start():end]
        page_url = None
        pm = re.search(r'"(?:purl|ru)"\s*:\s*"(https?://[^"\\]+)"', window)
        if pm:
            page_url = pm.group(1)
        page_title = None
        tm = re.search(r'"(?:t|pt)"\s*:\s*"([^"\\]{1,200})"', window)
        if tm:
            page_title = tm.group(1)
        _add_image_url(found, seen, m.group(1), source, topic,
                       page_url, page_title)
        if len(found) >= limit:
            break
    if len(found) < limit:
        for m in re.finditer(
                r'https?://[^\s"\'\\<>]+\.(?:jpg|jpeg|png)(?:\?[^\s"\'\\<>]*)?',
                html or "", re.IGNORECASE):
            _add_image_url(found, seen, m.group(0), source, topic)
            if len(found) >= limit:
                break
    log("info", f"{source}: {len(found)} candidate(s) for '{topic[:60]}'")
    return found[:limit]


def _google_images_photos(topic, limit=5):
    """Real-photo candidates from a Google Images search (keyless).
    Fetches the image-search page with a browser User-Agent and
    extracts direct image URLs. Candidates still pass the logo/AI
    rejection + Pillow real-photo check in the caller, so a logo or
    icon scraped from the results can never be posted. Rebuild #7.4:
    Google has plenty of images - when every API source fails, search
    the web's biggest image index instead of giving up. LIVE FINDING
    (2026-11-23): Google now serves a JavaScript shell to plain
    requests (noscript 'enablejs' page, zero image URLs in the HTML),
    so this usually returns 0 candidates and logs it - Bing Images
    is the working image-search fallback; this stays as a best-effort
    source in case Google ever serves a plain page again."""
    try:
        r = requests.get("https://www.google.com/search",
                         params={"tbm": "isch", "q": topic, "hl": "en"},
                         headers={"User-Agent": _IMAGE_SEARCH_UA},
                         timeout=20)
        if r.status_code != 200:
            log("info", f"google images: search HTTP {r.status_code} for '{topic[:60]}'")
            return []
        return _extract_image_search_urls(r.text, "google-images", topic, limit)
    except Exception as e:
        log("warning", f"google images error: {e}")
        return []


def _bing_images_photos(topic, limit=5):
    """Real-photo candidates from a Bing Images search (keyless) -
    same idea as _google_images_photos, second fallback when Google
    blocks or returns nothing."""
    try:
        r = requests.get("https://www.bing.com/images/search",
                         params={"q": topic},
                         headers={"User-Agent": _IMAGE_SEARCH_UA},
                         timeout=20)
        if r.status_code != 200:
            log("info", f"bing images: search HTTP {r.status_code} for '{topic[:60]}'")
            return []
        return _extract_image_search_urls(r.text, "bing-images", topic, limit)
    except Exception as e:
        log("warning", f"bing images error: {e}")
        return []


def _pollinations_photo(topic):
    """AI-generated image, no logo. Last fallback only."""
    try:
        prompt = quote_plus(f"{topic}, dramatic news photo, daytime, photorealistic, 16:9")
        url = (f"https://image.pollinations.ai/prompt/{prompt}"
               f"?width=1280&height=720&nologo=true&model=flux")
        r = requests.get(url, timeout=90)
        ctype = (r.headers.get("Content-Type") or "").lower()
        if r.status_code == 200 and len(r.content) > 20000 \
                and ctype.startswith("image/"):
            fname = f"pollinations-{slugify(topic)}-{int(time.time())}.jpg"
            path = os.path.join(IMAGES_DIR, fname)
            with open(path, "wb") as f:
                f.write(r.content)
            # The REMOTE URL is what Blogger must load - a local
            # /images/... path 404s on the blog, which is how earlier
            # posts ended up with broken thumbnails.
            return {"url": url, "source": "pollinations",
                    "alt": topic, "local_path": path}
    except Exception as e:
        log("warning", f"pollinations error: {e}")
    return None


def _is_real_photo_bytes(data):
    """True only if the bytes are a valid JPEG/PNG photograph at least
    400px wide. Rebuild #7.2 (strict order): a logo, icon, tiny
    graphic, or corrupt download is never a 'real photo'. Without
    Pillow, falls back to a magic-byte check (JPEG SOI / PNG
    signature) with no width check."""
    if not data or len(data) < 100:
        return False
    try:
        from PIL import Image
        import io
        im = Image.open(io.BytesIO(data))
        if im.format not in ("JPEG", "PNG"):
            return False
        if im.width < 400:
            return False
        try:
            im.verify()
        except Exception:
            return False
        return True
    except ImportError:
        return data[:3] == b"\xff\xd8\xff" or data[:8] == b"\x89PNG\r\n\x1a\n"
    except Exception:
        return False


def download_image(url, topic):
    try:
        r = requests.get(url, timeout=30,
                         headers={"User-Agent": "Mozilla/5.0"})
        if r.status_code != 200 or len(r.content) < 1000:
            return None
        if not (r.headers.get("Content-Type") or "").lower().startswith("image/"):
            return None
        # Rebuild #7.2: the bytes must be a VALID photograph (JPEG/PNG,
        # >= 400px wide) - a logo, icon, or corrupt download is never
        # a 'real photo', no matter what the content-type claims.
        if not _is_real_photo_bytes(r.content):
            log("info", f"download_image: rejected (not a valid photo "
                        f">=400px): {url[:120]}")
            return None
        ext = ".jpg"
        if "png" in (r.headers.get("Content-Type") or ""):
            ext = ".png"
        fname = f"{slugify(topic)}-{int(time.time())}{ext}"
        path = os.path.join(IMAGES_DIR, fname)
        with open(path, "wb") as f:
            f.write(r.content)
        return path
    except Exception as e:
        log("warning", f"download_image error: {e}")
        return None


def verify_photo_url(url):
    """True only if the photo URL really loads as an image
    (HTTP 200 + content-type image/*). HEAD first, ranged-GET fallback
    for hosts that refuse HEAD."""
    if not url or not str(url).startswith("http"):
        return False
    try:
        r = requests.head(url, timeout=15, allow_redirects=True,
                          headers={"User-Agent": "Mozilla/5.0"})
        if r.status_code == 200:
            ctype = (r.headers.get("Content-Type") or "").lower()
            if ctype.startswith("image/"):
                return True
        r = requests.get(url, timeout=20, stream=True,
                         headers={"User-Agent": "Mozilla/5.0",
                                  "Range": "bytes=0-1023"})
        if r.status_code in (200, 206):
            ctype = (r.headers.get("Content-Type") or "").lower()
            return ctype.startswith("image/")
    except Exception as e:
        log("warning", f"verify_photo_url error: {e}")
    return False


def fetch_verified_photo(topic):
    """PHOTO-FIRST gate: fetch a photo AND verify its URL really loads
    as an image. Returns the photo dict or None. The article is only
    written after this succeeds - never waste an AI call on a topic
    with no usable photo."""
    photo = fetch_photo(topic)
    if not photo:
        return None
    url = photo.get("url", "")
    if verify_photo_url(url):
        return photo
    log("warning", f"photo URL failed verification for '{topic}': {url}")
    return None


def fetch_og_image(url, _depth=0, topic=None):
    """The og:image (or twitter:image) of a link, verified as a real
    image. Used so a link-promo post still has a photo (no photo =
    no post). Returns the image URL or None.
    Rebuild #7.2: a Google News link is followed to the PUBLISHER's
    page first (its og:image is the Google News logo otherwise), and
    any og:image that is a logo / icon / generic graphic is rejected
    - a logo is never a 'real photo'. Rebuild #7.6: when the caller
    knows the story (topic), the page itself must be about that
    story - its <title>/og:title must contain the story's key
    entities (_photo_relevant) - or the og:image is not the
    article's image and is rejected. The og:image of a wrong page
    is by definition unrelated to the story."""
    if not url or not str(url).startswith("http"):
        return None
    try:
        r = requests.get(url, timeout=20, allow_redirects=True,
                         headers={"User-Agent": "Mozilla/5.0"})
        if r.status_code != 200:
            return None
        html = r.text
        # Still on a Google News page? The redirect to the publisher
        # was not followed (meta-refresh) - resolve it and retry once.
        final_host = (urlparse(r.url).netloc or "").lower()
        if "news.google.com" in final_host and _depth == 0:
            target = _extract_redirect_url(html, r.url)
            if target and "news.google.com" not in \
                    (urlparse(target).netloc or "").lower():
                log("info", f"og:image: following Google News link to "
                           f"publisher {urlparse(target).netloc}")
                return fetch_og_image(target, _depth=1, topic=topic)
        if "news.google.com" in final_host:
            # Rebuild #7.4: the page did NOT redirect to a publisher
            # (no HTTP 302, no meta-refresh, canonical points to
            # itself) and its og:image IS the Google News logo -
            # parsing it would only ever return that logo. Log the
            # final URL so the run shows where it got stuck, return
            # None at once; the caller falls back to a real-photo
            # search for the story instead.
            log("info", "og:image: no publisher redirect (Google News "
                        f"page, final URL {r.url[:120]}) - skipping, "
                        "og:image would be the logo")
            return None
        # Rebuild #7.6: when the caller knows the story (topic), the
        # page itself must be about that story - its <title> /
        # og:title must contain the story's key entities - or the
        # og:image is not the article's image and is rejected. The
        # og:image of a wrong page is by definition unrelated to
        # the story. (A Google News page never reaches here - it
        # returned None above, so this gate only runs on the
        # publisher's page or a direct publisher link.)
        if topic:
            title = ""
            tm = (re.search(r'<title[^>]*>([^<]{1,200})</title>', html, re.IGNORECASE)
                  or re.search(r'<meta[^>]+property=["\']og:title["\'][^>]+content=["\']([^"\']+)["\']',
                               html, re.IGNORECASE))
            if tm:
                title = tm.group(1).strip()
            rel, rel_reason = _photo_relevant(r.url, title, topic)
            if not rel:
                log("info", f"og:image rejected (page not about "
                            f"'{topic[:50]}'): {r.url[:120]} "
                            f"(page title: {title[:100]} - {rel_reason})")
                return None
        m = (re.search(r'<meta[^>]+property=["\']og:image["\'][^>]+content=["\']([^"\']+)["\']',
                       html, re.IGNORECASE)
             or re.search(r'<meta[^>]+content=["\']([^"\']+)["\'][^>]+property=["\']og:image["\']',
                          html, re.IGNORECASE)
             or re.search(r'<meta[^>]+name=["\']twitter:image["\'][^>]+content=["\']([^"\']+)["\']',
                          html, re.IGNORECASE))
        if not m:
            return None
        img = m.group(1).strip()
        if img.startswith("//"):
            img = "https:" + img
        elif img.startswith("/"):
            p = urlparse(r.url)
            img = f"{p.scheme}://{p.netloc}{img}"
        if _is_logo_image_url(img):
            log("info", f"og:image rejected (logo/icon, not a real photo): {img[:120]}")
            return None
        if verify_photo_url(img):
            return img
    except Exception as e:
        log("warning", f"og:image fetch error for {url}: {e}")
    return None


def _is_pollinations_url(url):
    """True if the URL is a Pollinations (AI-generated) image. Bluesky
    posts NEVER use AI-generated images (rebuild #7, strict user order)."""
    try:
        return "pollinations" in (urlparse(str(url or "")).netloc or "").lower()
    except Exception:
        return False


LOGO_HOST_PARTS = ("google", "gstatic", "gnews")
LOGO_PATH_WORDS = ("logo", "gnews", "google-news", "favicon", "sprite",
                   "placeholder", "no-image", "default-image", "blank")
LOGO_PATH_TOKENS = ("logo", "logos", "icon", "icons", "favicon")


def _is_logo_image_url(url):
    """True if an image URL is a logo / icon / generic graphic, not a
    real news photograph. Rebuild #7.2 (strict order): the Google News
    logo must never be posted as a 'news photo'. Checks the host
    (google / gstatic / gnews) and the path/filename (logo, icon,
    favicon, ...). A real publisher photo URL never matches these.
    The 'icon' check is token-based, so 'iconic' is NOT rejected."""
    try:
        u = str(url or "").strip().lower()
        if not u.startswith("http"):
            return True
        netloc = urlparse(u).netloc
        if any(part in netloc for part in LOGO_HOST_PARTS):
            return True
        parsed = urlparse(u)
        path = parsed.path + "?" + parsed.query
        if any(w in path for w in LOGO_PATH_WORDS):
            return True
        tokens = [t for t in re.split(r"[^a-z0-9]+", path) if t]
        return any(t in LOGO_PATH_TOKENS for t in tokens)
    except Exception:
        return False


def _extract_redirect_url(html, base_url):
    """Publisher URL from a Google News redirect/interstitial page:
    a meta refresh, the <link rel="canonical">, or an outbound
    anchor to the publisher's article page. Returns the URL or None.
    Rebuild #7.4: the meta-refresh is tried FIRST - Google News
    interstitial pages redirect via meta-refresh to the publisher,
    while their canonical often points to the Google News page
    ITSELF; a candidate still on news.google.com is never returned
    (fetch_og_image would only ever read the Google News logo from
    it). The HTTP 302 redirect is separate: requests follows it
    automatically, so fetch_og_image usually never reaches this
    function - this is for pages that do NOT 302. Rebuild #7.6:
    (3) an outbound anchor, for pages with neither a refresh nor an
    outside canonical - the link text should read like an article
    headline (10-200 chars). LIVE FINDING (2026-11-23): a real
    Google News article page's HTML contains ZERO outbound links
    to non-Google domains (59 hrefs, all google.com /
    news.google.com), so (3) is best-effort - the CBMi token decodes
    to an obfuscated blob, not a URL, and plain requests gets NO
    HTTP 302 - so a Google News link that yields nothing here still
    has the real-photo search fallback. Google's own pages,
    javascript links, fragments and logo URLs are never followed."""
    if not html:
        return None
    candidates = []
    m = re.search(r'<meta[^>]+http-equiv=["\']refresh["\'][^>]+content=["\'][^"\']*?url=([^"\';]+)',
                  html, re.IGNORECASE)
    if m:
        candidates.append(m.group(1).strip())
    m = (re.search(r'<link[^>]+rel=["\']canonical["\'][^>]+href=["\']([^"\']+)["\']',
                   html, re.IGNORECASE)
         or re.search(r'<link[^>]+href=["\']([^"\']+)["\'][^>]+rel=["\']canonical["\']',
                      html, re.IGNORECASE))
    if m:
        candidates.append(m.group(1).strip())
    # (3) Rebuild #7.6: an outbound anchor to the publisher's
    # article page, for Google News pages with neither a refresh nor
    # an outside canonical. Google's own pages and logo URLs are
    # never followed.
    for m in re.finditer(r'<a[^>]*href=["\'](https?://[^"\']+)["\'][^>]*>'
                         r'([^<]{10,200})</a>',
                         html, re.IGNORECASE):
        target = m.group(1).strip()
        host = (urlparse(target).netloc or "").lower()
        if "google.com" in host or "gstatic" in host:
            continue
        if _is_logo_image_url(target):
            continue
        candidates.append(target)
    for c in candidates:
        u = urljoin(base_url or "", c)
        if "news.google.com" not in (urlparse(u).netloc or "").lower():
            return u
    return None


def _news_photo(topic, state=None):
    """A REAL image from online news for a topic (rebuild #7).
    Uses Google News RSS (verify_news) and takes the first article
    whose og:image downloads and verifies as a real image. Text, logo
    or watermark on the image is FINE (news photos carry them) - the
    image is never rejected for that. Never Pollinations. Rebuild
    #7.4: a Google News article link IS fetched for its og:image -
    IF it redirects (HTTP 302) to the publisher, fetch_og_image
    follows it to the PUBLISHER's og:image (a meta-refresh redirect
    is resolved too). LIVE CHECK 2026-11-23: plain requests gets NO
    redirect from these links (the page serves the Google News
    article itself, og:image IS the logo) - so in practice the
    redirect path rarely fires and the real-photo search below is
    what usually finds the photo; the fetch is still tried because
    a redirect may happen for other links. If no article image works,
    a REAL photo is searched for the topic from real-photo sources
    (Openverse / Pexels / Pixabay / Wikimedia / Google Images /
    Bing Images); a real stock / editorial photo is acceptable when
    the article's own image is unavailable. Returns a photo dict
    with local_path, or None."""
    topic = (topic or "").strip()
    if not topic:
        return None
    try:
        _verified, _sources, items = verify_news(topic)
    except Exception as e:
        log("warning", f"news photo error for '{topic}': {e}")
        return None
    # Rebuild #7.8: one shared vision budget for this whole lookup.
    vision = {"used": 0}
    seen = set()
    for item in (items or [])[:5]:
        link = (item.get("link") or "").strip()
        if not link or link in seen:
            continue
        seen.add(link)
        # Rebuild #7.8: pass topic= so the publisher page's title is
        # checked against the story (relevance) - a bare fetch_og_image
        # never verified the image belonged to the story.
        img = fetch_og_image(link, topic=topic)
        if not img or _is_pollinations_url(img) or _is_logo_image_url(img):
            log("info", f"photo candidate for '{topic}': "
                        f"'{(item.get('title') or '')[:50]}' - rejected "
                        "(no usable og:image)")
            continue
        local = download_image(img, topic)
        if local:
            # Rebuild #7.8: vision is the FINAL gate on the article's
            # own og:image too - a publisher og:image can be the
            # wrong photo. A vision NO rejects this candidate (the
            # next candidate / real-photo fallback is tried); a vision
            # failure falls back to the keyword check, which
            # fetch_og_image already passed.
            if _vision_gate(local, topic, vision) is False:
                log("info", f"photo candidate for '{topic}': "
                            f"'{(item.get('title') or '')[:50]}' - rejected "
                            "(vision: does not show the person/subject)")
                continue
            log("info", f"photo: real news image for '{topic}' "
                        f"(from {item.get('source') or 'news'})")
            return {"url": img, "source": "news",
                    "alt": item.get("title", ""), "local_path": local}
        log("info", f"photo candidate for '{topic}': "
                    f"'{(item.get('title') or '')[:50]}' - rejected "
                    "(og:image download failed)")
    # Rebuild #7.3: no article image worked - search real-photo
    # sources for this topic instead of giving up.
    photo = _real_photo_for_topic(topic, vision)
    if photo and photo.get("local_path"):
        return photo
    log("info", f"photo: no real news image found for '{topic}'")
    return None


# Stopwords stripped when a headline is shortened into a photo-search
# query (Openverse matches far better on short keyword queries than
# on a full sentence).
_PHOTO_QUERY_STOPWORDS = frozenset(
    "the a an and or of to in on for with is are was were be by at from "
    "as it its this that can one you your how why what when after before "
    "new top".split())


def _photo_search_queries(topic):
    """Search queries for a real photo, longest first: the full
    headline, then the headline without its trailing ' - Source',
    then its first 5 keywords, then its first 3 keywords. Capped at
    3 queries - a full-sentence query almost never matches, the short
    keyword queries are the ones that find a photo."""
    raw = (topic or "").strip()
    if not raw:
        return []
    queries = [raw]
    head = raw.split(" - ")[0].strip()
    if head and head != raw:
        queries.append(head)
    keys = [w for w in re.split(r"[^A-Za-z0-9]+", head)
            if w and w.lower() not in _PHOTO_QUERY_STOPWORDS]
    if len(keys) > 5:
        queries.append(" ".join(keys[:5]))
    if len(keys) > 3:
        queries.append(" ".join(keys[:3]))
    elif keys and " ".join(keys) not in queries:
        queries.append(" ".join(keys))
    seen, out = set(), []
    for q in queries:
        k = q.lower()
        if k and k not in seen:
            seen.add(k)
            out.append(q)
    return out[:3]


# ---------------------------------------------------------------- rebuild #7.7
# GEMINI VISION CHECK (user order 2026-11-23): the photo must MATCH
# the news story - and the judge must be an AI that can actually SEE
# the image. Groq cannot (its Llama 4 Scout/Maverick vision models
# were retired in 2026; gpt-oss-120b is text-only), so Gemini is the
# judge. The vision check runs on the FINAL chosen photo only (not
# on every candidate - the run must stay fast), at most
# VISION_MAX_CHECKS_PER_POST checks per post: if the chosen photo
# fails vision, the next best candidate is tried, up to that budget.
# A vision API failure NEVER blocks a post by itself - the #7.6
# keyword relevance check decides instead.
VISION_MAX_CHECKS_PER_POST = 3  # max Gemini vision calls per promo post
VISION_MAX_ATTEMPTS = 6         # max key/model attempts per vision check

# Words that can never be part of a person's name in a headline:
# places, organisations, publications, months, weekdays, titles,
# media/event words - and the verbs headlines use ("Trump Blames
# Biden" - "Blames" is a verb, not a surname).
_PERSON_NAME_BLOCKWORDS = frozenset(
    "united states kingdom union house court street york angeles korea "
    "east west north south central federal reserve world cup bowl series "
    "league day christmas thanksgiving new san las hong saudi arabia "
    "africa zealand ireland republic bank rate sunday friday monday "
    "saturday thursday tuesday wednesday january february march april "
    "june july august september october november december prime "
    # NOTE: 'may' is deliberately NOT in this list - it is Theresa
    # May's surname as often as it is a month, and 'May Day' is
    # already blocked by 'day'.
    "minister president secretary general chief justice senator "
    "governor mayor doctor professor captain colonel lieutenant "
    "sergeant officer inspector detective sheriff deputy agent "
    "director manager chairman ceo cfo cto founder valley journal "
    "times post news mail guardian sun express mirror star standard "
    "financial telegraph economist rolling vanity harper vogue forbes "
    "bloomberg reuters associated press daily weekly monthly morning "
    "evening tour album film movie song concert show award awards "
    "festival season episode series book novel game match final semi "
    "quarter".split())
_HEADLINE_VERBS = frozenset(
    "blames tells urges says warns slams hits backs vows pledges "
    "unveils launches announces reveals confirms denies admits claims "
    "insists demands threatens praises attacks defends accuses sues "
    "wins loses dies marries splits joins leaves quits resigns "
    "retires returns arrives visits meets calls asks wants needs gets "
    "takes gives makes breaks shocks stuns blasts rips roasts drags "
    "trolls mocks bashes hails cheers boos jeers beats tops leads "
    "trails edges falls rises jumps drops soars sinks surges slumps "
    "rallies tumbles plummets climbs slides gains".split())


# Common first names (US politicians, world leaders, celebrities).
# A capitalised pair is only treated as a person's name when its
# FIRST word is a plausible first name - title-case headlines
# capitalise every word, so 'High Prices' or 'Big Storm' would
# otherwise look like names. A missed name only loses the
# person-specific question (the prompt still carries the headline);
# a WRONG name would make the vision check ask about a non-person
# and wrongly reject good photos. So this gate prefers missing a
# name over inventing one.
_PERSON_FIRST_NAMES = frozenset(
    "aaron abigail adam adrian alan albert alberto alejandro alex "
    "alexander alexandra alfred alice alicia allan allen alma alonzo "
    "alvin amanda amber amelia amos amy ana andre andrea andres andrew "
    "andy angela angelo anita anna anne annette annie anthony antonio "
    "april archie ariana ariel arlene arnold arthur ashley aubrey "
    "audrey barack barbara benjamin bernie betty beyonce bill billy bob "
    "bobby boris brandon brian bruce bryan caleb cameron camila carl "
    "carlos carmen carol caroline carrie casey catherine cathy chad "
    "charles charlie charlotte chase chelsea cheryl chris christian "
    "christina christine christopher chuck cindy claire clara clarence "
    "claudia clint clinton cody colin colleen connie corey courtney "
    "craig crystal curtis cynthia dale dan daniel danielle danny darla "
    "darlene darrell darren daryl dave david dawn dean debra deborah "
    "denise dennis derek diana diane dominic don donald donna dora "
    "doris dorothy doug douglas duane dustin dwight dylan earl ed eddie "
    "edgar edith edward edwin eileen elaine eleanor elena eli elias "
    "elijah elisa elizabeth ella ellen elliot eloise elsa emily emma "
    "emmanuel eric erica erik erin ernest esther ethan ethel eugene eva "
    "evan evelyn everett faith felicia felix fernando fiona flora floyd "
    "frances francis frank franklin fred freddie frederick gabriel gail "
    "garrett gary gavin gene geoffrey george gerald geraldine gilbert "
    "gina ginger gladys glen glenn gloria gordon grace greg gregory "
    "greta guy gwen hannah harold harriet harry harvey hassan hattie "
    "hazel heather hector helen henry herbert herman hilda hillary "
    "holly homer hope horace howard hubert hugh ian ida ike ilene ines "
    "ingrid ira irene iris irma irving isaac isabel isabella israel ivan "
    "jack jackie jacob jaime james jamie jan jane janet janice jared "
    "jasmine jason javier jay jean jeanette jeff jeffrey jenna jennifer "
    "jeremy jerome jesse jessica jill jim jimmie jimmy joan joanna "
    "joanne jodi jodie jody joe joel john johnny jon jonathan jorge jose "
    "joseph josephine josh joshua joyce juan juanita judith judy julia "
    "julian julie julio june justin kara karen karl kate katherine "
    "kathleen kathryn kathy katie katrina kay keith kelley kelli kellie "
    "kelly ken kendra kenneth kenny kent kerry kevin kim kimberly kirk "
    "kristen kristin kristina kurt kyle lamar lana lance larry laura "
    "lauren laurie lawrence leah lee leigh leland lena leo leon leonard "
    "leroy leslie lester levi lewis lillian lillie linda lindsay lionel "
    "lisa lloyd lois lonnie lora loren lorenzo loretta lori lorraine lou "
    "louise lucille lucy luis luke luther lydia lyle lynda lynn mabel "
    "mack madeline mae manuel mara marc marcella marcia marcus margaret "
    "margie maria marian marianne marie marilyn marion marjorie mark "
    "marlene marsha marshall marta martha martin marvin mary matthew "
    "maureen maurice max maxine melanie melinda melissa melvin mercedes "
    "meredith michael michele michelle miguel mike mildred milton mindy "
    "minnie miriam mitchell monica monique morris moses muriel myra "
    "myrtle nadia nancy naomi natalie nathan nathaniel neal neil nellie "
    "nelson nicholas nick nicolas nicole nina noah noel nora norma "
    "norman olga olive oliver ollie omar opal orlando oscar owen pablo "
    "pamela pat patricia patrick patti paul paula pauline pearl pedro "
    "penny percy perry pete peter phil philip phillip phoebe phyllis "
    "preston priscilla rachel rafael ralph ramiro ramon randall randy "
    "raul ray raymond rebecca regina reginald renee rex rhonda ricardo "
    "richard rick ricky rita robert roberta roberto robin rochelle rocky "
    "roderick rodney rodrigo rogelio roland ron ronald ronnie rosa "
    "rosalie rose rosemary ross roxanne roy ruben ruby rudolph rudy "
    "rufus russell ruth ryan sabrina sadie sally salvador sam samantha "
    "samuel sandra sandy santiago sara sarah saul scott sean sergio seth "
    "shane shannon shari sharon shaun shawn sheila shelley shelly sheri "
    "sherman sherry shirley sidney silvia simon sonia sonya sophia "
    "stacey stacy stanley stella stephanie stephen steve steven stuart "
    "susan suzanne sylvia tabitha tamara tammie tammy tanya tara taylor "
    "ted terence teresa terrence terri terry thelma theodore theresa "
    "thomas tiffany tim timothy tina tobias todd tom tommy toni tony "
    "tonya tracy travis trevor tricia troy tyler tyrone valerie vanessa "
    "vera vernon veronica vicente vickie vicky victor victoria vincent "
    "viola violet virgil virginia vivian wade wallace walter wanda "
    "warren wayne wendell wendy wesley wilbur wilfred willard william "
    "willie wilma winifred winston wyatt xavier yolanda yvette yvonne "
    "zachary zoe adele billie bradley camilla carmelo chappell conan "
    "derrick devin drake dua draymond giannis gracie jalen jayson "
    "kanye kawhi keir kendrick klay kyrie lebron luka meghan nikola "
    "olivia rihanna rishi steph tyrese vladimir volodymyr narendra "
    "suella priti sadiq nicola humza elon sundar satya jensen xi "
    "jinping jong recep tayyip yair naftali ebrahim mohammed salman "
    "bashar abdel uhuru cyril bola muhammadu goodluck olusegun yoweri "
    "felix denis teodoro faustin idriss mahamat ismail abiy "
    "hailemariam meles isaias".split())


def _headline_person_names(headline):
    """Likely person names in a headline: two consecutive capitalised
    words whose FIRST word is a plausible first name (see
    _PERSON_FIRST_NAMES) and neither word is a place/org/title/verb
    word. Returns up to 2 names. This is a heuristic, not NER - the
    vision prompt also carries the full headline, so a missed name
    only loses the person-specific question, never the relevance
    check itself. Examples: 'Theresa May tells Andy Burnham...' ->
    ['Theresa May', 'Andy Burnham']; 'Donald Trump meets Vladimir
    Putin' -> ['Donald Trump', 'Vladimir Putin']; 'Trump Blames
    Biden for High Prices' -> [] ('Trump'/'High' are not first
    names, 'Blames' is a verb, 'Biden' is a single word)."""
    if not headline:
        return []
    names = []
    for m in re.finditer(r"\b([A-Z][a-z]+ [A-Z][a-z]+)\b", headline):
        words = m.group(1).split()
        low = [w.lower() for w in words]
        if low[0] not in _PERSON_FIRST_NAMES:
            continue
        if any(w in _PERSON_NAME_BLOCKWORDS or w in _HEADLINE_VERBS
               for w in low):
            continue
        name = " ".join(words)
        if name not in names:
            names.append(name)
        if len(names) >= 2:
            break
    return names


def _vision_prompt(headline, person_names):
    """The question Gemini's vision check answers. PERSON-AWARE:
    when the headline names a person, the question names them
    explicitly - a political post must show the named leader (Trump,
    Putin, PMs), a celebrity post must show the named celebrity
    being talked about. Without a name, the question is about the
    headline's subject in general. The answer must start with YES
    or NO, then one short reason."""
    headline = (headline or "").strip()[:200]
    if person_names:
        names = " and ".join(person_names[:2])
        return (f"News headline: \"{headline}\"\n"
                f"Does this photo clearly show {names}? "
                "Answer YES only if the named person is clearly visible "
                "in the photo. Answer NO if the photo shows someone else, "
                "a product, a cartoon, a chart, a poster, or anything "
                "unrelated. Reply with YES or NO first, then one short reason.")
    return (f"News headline: \"{headline}\"\n"
            "Does this photo show the people, place or event in this "
            "headline? Answer YES only if the photo clearly matches the "
            "headline. Answer NO if it shows a product, a cartoon, a "
            "chart, a poster, a different person, or anything unrelated. "
            "Reply with YES or NO first, then one short reason.")


def _vision_image_b64(local_path):
    """A downloaded photo, downscaled to max 1024px on the long edge
    and re-encoded as JPEG (quality 70), returned as (base64, mime).
    Keeps the vision payload small (~100-200KB) so the call is fast
    and cheap. Returns (None, None) when the file cannot be read or
    Pillow is missing. Never raises."""
    if not local_path or not os.path.exists(local_path):
        return None, None
    try:
        from PIL import Image
        import base64
        import io
        im = Image.open(local_path)
        if im.mode in ("RGBA", "LA", "P"):
            im = im.convert("RGB")
        w, h = im.size
        if max(w, h) > 1024:
            scale = 1024 / max(w, h)
            im = im.resize((max(1, int(w * scale)),
                            max(1, int(h * scale))))
        buf = io.BytesIO()
        im.save(buf, "JPEG", quality=70)
        return base64.b64encode(buf.getvalue()).decode("ascii"), "image/jpeg"
    except Exception as e:
        log("warning", f"vision: could not prepare image ({e})")
        return None, None


def _gemini_vision_check(image_b64, mime, headline, person_names=None):
    """Ask Gemini (the only provider that can see images) whether a
    photo matches a news story. Returns (True, reason) / (False,
    reason) / (None, reason) - None means the vision call could not
    be made or its answer was unusable, and the caller must fall back
    to the #7.6 keyword relevance check instead. A vision API failure
    NEVER blocks a post by itself. Walks the GEMINI_MODELS failover
    list (gemini-3.5-flash-lite is the working model live), bounded
    to VISION_MAX_ATTEMPTS attempts so one check cannot grind through
    all keys x models. Never raises. Key values are never logged."""
    if not GEMINI_KEYS:
        return None, "no GEMINI_API_KEYS configured"
    if not image_b64:
        return None, "no image data to check"
    prompt = _vision_prompt(headline, person_names or [])
    keys = GEMINI_KEYS[:]
    random.shuffle(keys)
    attempts = 0
    seen = {}
    for model in GEMINI_MODELS:
        for key in keys:
            if attempts >= VISION_MAX_ATTEMPTS:
                break
            attempts += 1
            try:
                text, code, detail = _gemini_vision_call(
                    key, model, image_b64, mime, prompt)
            except Exception as e:
                sig = (0, f"network: {type(e).__name__}")
                seen[sig] = seen.get(sig, 0) + 1
                continue
            if not text:
                if code == 429:
                    time.sleep(2)
                sig = (code, detail or "no text returned")
                seen[sig] = seen.get(sig, 0) + 1
                continue
            ans = text.strip().upper()
            reason = text.strip()
            if ans.startswith("YES"):
                return True, (reason[3:].strip(" -:") or "vision: YES")[:150]
            if ans.startswith("NO"):
                return False, (reason[2:].strip(" -:") or "vision: NO")[:150]
            return None, ("vision answer unusable (did not start YES/NO): "
                          f"{reason[:80]}")
        if attempts >= VISION_MAX_ATTEMPTS:
            break
    summary = "; ".join(
        f"HTTP {c} x{n}: {d}" for (c, d), n in list(seen.items())[:3])
    return None, (f"vision failed ({attempts} attempt(s) - "
                  f"{summary or 'no detail'}")[:200]


def _vision_gate(local_path, headline, vision_state):
    """Gemini vision check on ONE downloaded candidate photo - the
    FINAL gate before a photo is accepted (rebuild #7.7, user order
    2026-11-23: the photo must MATCH the news, judged by an AI that
    can actually see the image). Returns True (vision says the photo
    matches), False (vision says NO - reject this candidate and try
    the next), or None (vision could not run or its answer was
    unusable - the caller falls back to the #7.6 keyword check,
    which already passed for this candidate). Budget: at most
    VISION_MAX_CHECKS_PER_POST vision calls per post (vision_state
    is a shared {"used": n} dict); when the budget is used up, later
    candidates are decided by the keyword check alone. Never raises."""
    if vision_state is None:
        vision_state = {"used": 0}
    if vision_state.get("used", 0) >= VISION_MAX_CHECKS_PER_POST:
        log("info", "vision: budget used "
                    f"({VISION_MAX_CHECKS_PER_POST} checks) - keyword "
                    "check decides this candidate")
        return None
    b64, mime = _vision_image_b64(local_path)
    if not b64:
        log("info", "vision: image could not be prepared - keyword "
                    "check decides this candidate")
        return None
    vision_state["used"] = vision_state.get("used", 0) + 1
    names = _headline_person_names(headline)
    ok, reason = _gemini_vision_check(b64, mime, headline, names)
    if ok is True:
        log("info", f"vision: YES - photo matches '{headline[:50]}' "
                    f"({reason})")
        return True
    if ok is False:
        log("info", f"vision: NO - photo rejected for '{headline[:50]}' "
                    f"({reason})")
        return False
    log("info", f"vision: unavailable - keyword check decides "
                f"('{headline[:50]}': {reason})")
    return None


def _photo_relevant(page_url, page_title, headline):
    """Is a candidate photo RELEVANT to the news story? Rebuild #7.6
    (live failure, run #17, 2026-11-23): Bing attached REAL photos
    that had nothing to do with the story - a UV nail lamp for a
    Theresa May / Brexit post, a white lace wedding dress for a
    Theresa May / Burnham post. The old check (valid JPEG/PNG
    >=400px, not a logo/AI) never asked whether the image matches
    the story, and an alt text that mentions a name is NOT proof
    (the wedding dress's alt text said 'Theresa May'). The rule:
    the SOURCE PAGE (the page hosting the image) must be about the
    story - its title and/or URL must contain the story's key
    entities (the event words of the headline, see _event_words).
    A candidate with no source page at all cannot be verified and
    is rejected. Returns (relevant, reason)."""
    words = _event_words(headline)
    if not words:
        return False, "no key entities in the headline"
    page_title = (page_title or "").strip()
    page_url = (page_url or "").strip()
    if not page_title and not page_url:
        return False, "no source page to verify relevance"
    hay = (page_title + " " + page_url).lower()
    hay_words = {_stem_word(w) for w in re.findall(r"[a-z0-9]+", hay)}
    hits = [w for w in words if w in hay_words]
    # Rebuild #7.8: when the headline names a PERSON, the source page
    # must name that person too - a generic word match is NOT enough.
    # (Run #20: a Celebrity Cruises SHIP matched only the word
    # "celebrity" + "2026" for a Zosia Mamet split story. The page
    # must contain the person's name, or the photo is rejected here,
    # before the vision gate ever sees it.)
    names = _headline_person_names(headline)
    if names:
        name_words = set()
        for _nm in names:
            for _w in _nm.lower().split():
                name_words.add(_stem_word(_w))
        if not (name_words & hay_words):
            return False, ("the named person is not in the source page "
                           f"({', '.join(sorted(name_words)[:4])})")
    need = 2 if len(words) >= 3 else 1
    if len(hits) >= need:
        return True, (f"matches {len(hits)} key entit"
                      f"{'y' if len(hits) == 1 else 'ies'} "
                      f"({', '.join(hits[:4])})")
    return False, (f"only {len(hits)} of {len(words)} key entities "
                   "in the source page")


def _real_photo_for_topic(topic, vision=None):
    """A REAL photo for a topic from real-photo sources only
    (Pexels / Pixabay / Openverse / Wikimedia Commons / Google Images
    / Bing Images). Never AI-generated, never a logo, never a generic
    icon. Tries progressively shorter search queries and several
    candidates per query, because a single file may 429 or fail
    verification - the caller must not give up on the first failure.
    Every candidate still passes the real-photo check (valid JPEG/PNG,
    >=400px wide, not a logo) in download_image. Rebuild #7.4: the
    search is logged per source (status / result count / rejection
    reason) and has two more keyless sources (Wikimedia Commons,
    Google Images, Bing Images) so a photo is actually found - a
    download budget bounds the run. Rebuild #7.6: every candidate
    must also be RELEVANT to the story - its source page (title/URL)
    must contain the story's key entities (_photo_relevant); a real
    photo from an unrelated page (a product photo, a wedding dress)
    is rejected before downloading, and an alt text that mentions a
    name is never enough on its own. Rebuild #7.7: after download,
    Gemini vision is the FINAL gate (vision) - a photo the vision
    check says NO to is rejected and the next candidate is tried;
    when vision cannot run, the keyword check above (already passed)
    decides instead, so a vision failure never blocks the post.
    Returns a photo dict with local_path, or None (with a summary log
    of what was tried)."""
    tried_downloads = 0
    for q in _photo_search_queries(topic):
        cands = []
        for fn in (_pexels_photo, _pixabay_photo):
            try:
                found = fn(q)
            except Exception:
                found = None
            if found:
                cands.append(found)
        try:
            cands.extend(_openverse_photos(q, limit=PICK_MAX_PHOTO_CANDIDATES))
        except Exception:
            pass
        try:
            cands.extend(_wikimedia_photos(q, limit=PICK_MAX_PHOTO_CANDIDATES))
        except Exception:
            pass
        try:
            cands.extend(_google_images_photos(q, limit=4))
        except Exception:
            pass
        try:
            cands.extend(_bing_images_photos(q, limit=4))
        except Exception:
            pass
        for cand in cands:
            url = (cand or {}).get("url", "")
            if not url or _is_pollinations_url(url):
                continue
            if _is_logo_image_url(url):
                log("info", f"photo: rejected (logo/icon URL): {url[:100]}")
                continue
            # Rebuild #7.6: RELEVANCE - the candidate's source page
            # must be about this story (its title/URL must contain
            # the story's key entities). A real photo from an
            # unrelated page is rejected BEFORE downloading, so it
            # never consumes the download budget. The page (not the
            # alt text) is the evidence - an alt text that mentions a
            # name proves nothing (run #17: a wedding dress whose alt
            # text said 'Theresa May').
            page = ((cand.get("page_url") or "") + " | " +
                    (cand.get("page_title") or "")).strip(" |")
            rel, rel_reason = _photo_relevant(
                cand.get("page_url"), cand.get("page_title"), topic)
            if not rel:
                log("info", f"photo: rejected (irrelevant to "
                            f"'{topic[:50]}'): {url[:100]} "
                            f"(page: {page[:100]} - {rel_reason})")
                continue
            if tried_downloads >= MAX_REAL_PHOTO_DOWNLOADS:
                log("info", "photo: download budget reached "
                            f"({MAX_REAL_PHOTO_DOWNLOADS}) - stopping")
                return None
            tried_downloads += 1
            local = download_image(url, topic)
            if local:
                # Rebuild #7.7: Gemini vision is the FINAL gate -
                # the photo must MATCH the story, judged by an AI
                # that can actually see the image. A vision NO
                # rejects this candidate (the next candidate is
                # tried); a vision failure falls back to the keyword
                # check above, which already passed - it never
                # blocks the post by itself.
                if _vision_gate(local, topic, vision) is False:
                    log("info", f"photo: rejected (vision NO): {url[:100]}")
                    continue
                log("info", f"photo: ACCEPTED relevant photo for "
                            f"'{topic[:60]}': {url[:100]} "
                            f"(from {cand.get('source') or 'stock'}, "
                            f"query '{q}', page: {page[:100]} - "
                            f"{rel_reason})")
                return {"url": url, "source": cand.get("source") or "stock",
                        "alt": cand.get("alt") or topic, "local_path": local,
                        "page_url": cand.get("page_url") or "",
                        "page_title": cand.get("page_title") or ""}
            log("info", f"photo: candidate rejected (download/verify failed): {url[:100]}")
    log("info", f"photo: no real photo found for '{topic}' "
                f"({tried_downloads} download(s) tried)")
    return None


# ---------------------------------------------------------------- rebuild #7.1
# BLUESKY PROMO FIXES (user's strict orders, 2026-11-23):
# - ONE link always (the card's link never changes), but the caption
#   is DIFFERENT every time: written about a current/trending news
#   story (Bluesky trending first, else a Google News top story).
# - The cooldown is PER-CAPTION / PER-TOPIC (24h), NOT per-link:
#   the same link may post many times a day (up to posts_per_day),
#   but the same news topic / caption is never reused within 24h.
# - The photo is a REAL image from online news FOR THAT NEWS STORY
#   (the news article's og:image). Text/logo/watermark on the image
#   is FINE. Pollinations (AI) and stock photos are NEVER used for a
#   Bluesky post. No verified real photo for that news = no post.
# - The worker re-reads the card's UI settings fresh from
#   data/cards.json BEFORE EACH POST and logs the effective settings,
#   so the workflow log proves the UI was checked for every post.
#   Settings are never cached across posts within a run.
# - A promo post's text is a real caption (hook + link), NEVER just
#   the bare link. If the AI fails, a built-in hook is used instead.
# - posts_per_run is enforced strictly (a run can never post more
#   than the card's count, even if several slots are due).
PROMO_TOPIC_COOLDOWN_HOURS = 24
BSKY_MAX_CHARS = 300

# Minimum gap between two Bluesky posts of the SAME card (rebuild #7.2).
# Concurrent workflow runs (or a Run-now right after a scheduled run)
# must never produce a burst of posts at once.
BSKY_MIN_POST_GAP_MINUTES = 5

# Rebuild #7.3: bounds for the promo photo search. A Google News RSS
# article link can never yield a real og:image (its page's og:image IS
# the Google News logo), so the picker must not grind through dozens
# of doomed fetches - it tries different stories, then a real-photo
# search, and stops after these budgets.
PICK_MAX_ITEMS = 25            # max news items examined per promo pick
PICK_MAX_FALLBACK_SEARCHES = 6  # max real-photo searches per promo pick
PICK_MAX_PHOTO_CANDIDATES = 5  # max real-photo candidates tried per search
MAX_REAL_PHOTO_DOWNLOADS = 12  # max image downloads per real-photo search (bounds the run)

# Rebuild #7.8: ONLY the user's two promo news categories (user order
# 2026-11-24). USA celebrity news and USA finance news are REMOVED
# from the rotation entirely - promo posts are Political News and War
# News only, tried FIRST (rotating) before anything else. There is
# NO fallback to trending / breaking news: if neither category yields
# a fresh story with a verified people's photo, the run SKIPS posting
# (a clean skip, logged) - a wrong-category post is worse than no post.
PROMO_NEWS_CATEGORIES = ["USA political news", "war news"]


def _rotated_promo_categories(state):
    """The two user-ordered promo news categories, rotated so
    consecutive posts cover different categories. The starting
    category is derived from the number of promo posts already
    recorded in state (len of posted_promo_topics % 2) - deterministic
    and survives restarts, and it advances after every post because
    the post is recorded in state before the next pick."""
    cats = list(PROMO_NEWS_CATEGORIES)
    if not cats:
        return cats
    n = len((state or {}).get("posted_promo_topics") or {})
    start = n % len(cats)
    return cats[start:] + cats[:start]

# Rebuild #7.3: startup AI health check (one tiny test call per
# provider, first model only - NOT the full key/model failover).
AI_HEALTH_TEST_PROMPT = "Reply with the single word OK."
# Rebuild #7.4: 10 tokens was too small - Groq gpt-oss are reasoning
# models, their reasoning tokens eat the output budget, so a 10-token
# test call returns HTTP 200 with NO text (the live Groq failure).
# 150 leaves room for a short reasoning trace + the one-word answer.
AI_HEALTH_MAX_TOKENS = 150

# Why the last _card_bluesky_post skipped a post: "cooldown" (no fresh
# news topic/caption left within 24h), "no_photo" (fresh news exists
# but no real image could be fetched), "no_news" (no trending/top
# news at all - network/API down), or None (posted / other reason).
LAST_BSKY_SKIP = None

PROMO_HOOK_FALLBACKS = [
    "You need to see this - it is everywhere right now.",
    "This one is blowing up today. Take a look.",
    "Everyone is talking about this right now.",
    "Worth a minute of your time - check this out.",
    "This caught my eye today. Have a look.",
    "Big story doing the rounds today - see for yourself.",
    "Fresh news you should not miss - have a look.",
    "This is the story everyone will be talking about.",
    "Just in - this one is worth your attention.",
    "Do not scroll past this one. Take a look.",
]


def _promo_fallback_hook(card, link, state=None):
    """A human-sounding hook used ONLY when the AI returns nothing
    (keys down, rate limit). Never the bare link: a promo post always
    carries a hook. Rebuild #7.1: the hook must be one whose caption
    was NOT used in the last 24h (per-caption cooldown) - the list is
    walked in a day-rotated order so repeated posts do not all read
    the same. Returns None when every fallback hook was already used
    within 24h (then the post is skipped, never repeated). If the
    card has a topic, it is named in the hook. With no state given
    (last-resort call from _fit_bsky_text) the day-rotated hook is
    returned without a dedup check."""
    topic = ""
    if isinstance(card, dict):
        topic = (card.get("topic_override") or "").strip()
    cands = []
    if topic:
        cands.append(f"Big news on {topic} - worth a look. Do not miss this one.")
    start = (now_utc().toordinal() + len(link or "")) % len(PROMO_HOOK_FALLBACKS)
    cands.extend(PROMO_HOOK_FALLBACKS[start:] + PROMO_HOOK_FALLBACKS[:start])
    for hook in cands:
        if state is None:
            return hook
        if _promo_caption_cooldown_left(
                state, _fit_bsky_text(hook, link, cta="")) is None:
            return hook
    return None


# Rebuild #7.7: every Bluesky promo caption ENDS with an explicit
# call-to-action telling the reader to click/enter the link, THEN
# the link itself (user order 2026-11-23 - "Caption যে দেয় তখন
# লিংকে ডোকতে বলবে"). The CTA rotates deterministically by post
# count (like the category rotation) so consecutive captions do not
# all end identically.
BSKY_CTA_VARIANTS = [
    "Full story here 👇",
    "Tap the link for more 👇",
    "Read the full story at the link 👇",
    "Click the link for the full story 👇",
]


def _next_bsky_cta(state):
    """The CTA for the next promo post, rotated by the number of
    promo posts already recorded in state - deterministic, survives
    restarts, and advances after every post (the post is recorded
    in state before the next pick)."""
    n = len((state or {}).get("posted_promo_topics") or {})
    return BSKY_CTA_VARIANTS[n % len(BSKY_CTA_VARIANTS)]


def _fit_bsky_text(hook, link, cta=None):
    """Combine a hook, a call-to-action and a link into ONE Bluesky
    post (max 300 chars). Rebuild #7.7: the caption ALWAYS ends
    with CTA + link - the CTA and the link are NEVER truncated, the
    hook is trimmed to fit, so the final text always ends with the
    CTA and then the link, and the link appears exactly once.
    cta defaults to the first variant; the caller passes the
    rotated variant via _next_bsky_cta(state). Never returns just
    the bare link unless the link alone already fills the post."""
    hook = (hook or "").strip()
    link = (link or "").strip()
    if cta is None:
        cta = BSKY_CTA_VARIANTS[0]
    cta = (cta or "").strip()
    # Drop a link the AI already appended, so it is not doubled.
    if link and link in hook:
        hook = hook.replace(link, "").strip()
    if not hook:
        hook = _promo_fallback_hook(None, link)
    if not link:
        return hook[:BSKY_MAX_CHARS]
    # CTA + link always fit (both are short); only the hook is trimmed.
    # cta="" means NO call-to-action (used for the caption-dedup
    # identity - see _card_bluesky_post): the tail is then just the link.
    tail = f"{cta}\n{link}" if cta else link
    if len(tail) >= BSKY_MAX_CHARS:
        return link
    room = BSKY_MAX_CHARS - len(tail) - 1
    if room < 10:
        return tail
    if len(hook) > room:
        hook = hook[:room - 1].rstrip() + "\u2026"
    return f"{hook}\n{tail}"


# Words too generic to identify a news event (dropped from event
# keys): articles, prepositions, and headline filler verbs.
_NEWS_STOPWORDS = frozenset(
    "a an and are as at be been by for from has have had he her his in "
    "into is it its of on or per say says said she that the their they "
    "this to via was were will with about after before over under "
    "between through during new just not no more most can could should "
    "would".split())


def _stem_word(w):
    """Light stem so 'accepting'/'accept' and 'urges'/'urge' match.
    Conservative: only strips -ing/-ed/-s when enough of the word
    is left, and never touches words ending in -ss/-us/-is."""
    if len(w) > 5 and w.endswith("ing"):
        return w[:-3]
    if len(w) > 4 and w.endswith("ed"):
        return w[:-2]
    if len(w) > 4 and w.endswith("s") and not w.endswith(("ss", "us", "is")):
        return w[:-1]
    return w


def _event_words(text):
    """Core keywords of a headline/topic: lowercase alphanumeric
    tokens, >=3 chars, stopwords dropped, lightly stemmed, sorted
    and de-duplicated."""
    words = re.findall(r"[a-z0-9]+", (text or "").lower())
    return sorted({_stem_word(w) for w in words
                   if len(w) >= 3 and w not in _NEWS_STOPWORDS})


def _event_keys_match(words_a, words_b):
    """True when two keyword sets are the SAME event: identical sets,
    or >=3 shared words covering >=60% of the smaller set. Two
    different headlines about one event share its names and keywords
    ('Theresa May urges accepting Brexit' vs 'Theresa May tells
    Burnham to accept Brexit' share theresa/may/brexit/accept);
    two different events rarely share 3 keywords."""
    if not words_a or not words_b:
        return False
    if list(words_a) == list(words_b):
        return True
    inter = set(words_a) & set(words_b)
    return len(inter) >= 3 and \
        len(inter) / min(len(words_a), len(words_b)) >= 0.6


def _norm_news_key(text):
    """Normalise a news headline/topic into an EVENT key: lowercase,
    punctuation stripped, stopwords dropped, core keywords sorted.
    Two different headlines about the SAME event share most keywords,
    so they map to overlapping keys (see _event_keys_match).
    Rebuild #7.5: the old key was the exact headline string, which
    is why the same event posted twice on 2026-11-23 (15:11 + 15:16)
    with different headlines - the 24h cooldown never saw them as
    the same story."""
    return " ".join(_event_words(text))


def _matching_event_key(store, words, hours):
    """The stored event key (if any, not expired) that matches these
    keywords, plus its time left - or (None, None). Stored keys are
    canonicalised before comparing, so entries written before #7.5
    (exact headline strings) still match."""
    for stored_key in list((store or {}).keys()):
        left = _store_cooldown_left(store, stored_key, hours)
        if left is None:
            continue  # expired (or unparseable) - may be reused
        if _event_keys_match(words, _norm_news_key(stored_key).split()):
            return stored_key, left
    return None, None


def _store_dt(store, key):
    """When a timestamp-store entry was recorded (aware datetime) or None."""
    rec = (store or {}).get(key or "")
    if not rec:
        return None
    try:
        dt = datetime.fromisoformat(rec)
        if dt.tzinfo is None:
            dt = dt.replace(tzinfo=UTC)
        return dt
    except Exception:
        return None


def _store_cooldown_left(store, key, hours):
    """Time left on a no-reuse cooldown for a key, or None when the
    key may be used again."""
    dt = _store_dt(store, key)
    if not dt:
        return None
    left = dt + timedelta(hours=hours) - now_utc()
    return left if left.total_seconds() > 0 else None


def _store_record(store, key, max_age_days=7):
    """Remember that a key was used now. Entries older than
    max_age_days are pruned."""
    if not key:
        return
    store[key] = now_iso()
    cutoff = now_utc() - timedelta(days=max_age_days)
    for k in list(store.keys()):
        dt = _store_dt(store, k)
        if dt is None or dt < cutoff:
            store.pop(k, None)


def _promo_topic_cooldown_left(state, key):
    """Time left on the 24h no-reuse cooldown for a news topic /
    headline, or None when it may be used again. Rebuild #7.5: the
    match is by EVENT, not by exact headline - a stored event whose
    keywords overlap this headline's keywords is the SAME event, even
    if the headline is worded differently. Expired entries (older
    than 24h) never match."""
    _, left = _matching_event_key(
        state.get("posted_promo_topics") or {},
        _event_words(key), PROMO_TOPIC_COOLDOWN_HOURS)
    return left


def _record_promo_topic_posted(state, key):
    """Remember that this news topic/headline was used for a promo
    post now (state.json, so it survives across worker runs)."""
    _store_record(state.setdefault("posted_promo_topics", {}),
                  _norm_news_key(key))


def _caption_hash(text):
    """Stable hash of a caption (normalised) for dedup."""
    return hashlib.sha1(_norm_news_key(text).encode("utf-8")).hexdigest()


def _promo_caption_cooldown_left(state, text):
    """Time left on the 24h no-reuse cooldown for an exact caption,
    or None when it may be used again."""
    return _store_cooldown_left(state.get("posted_promo_captions") or {},
                                _caption_hash(text), PROMO_TOPIC_COOLDOWN_HOURS)


def _record_promo_caption_posted(state, text):
    """Remember that this exact caption was posted now (state.json)."""
    _store_record(state.setdefault("posted_promo_captions", {}),
                  _caption_hash(text))


def _promo_link_topic_key(link, headline):
    """Key for the same-link + same-topic guard: the promo link plus
    the event key of the headline."""
    return f"{(link or '').strip()}||{_norm_news_key(headline)}"


def _promo_link_topic_cooldown_left(state, link, headline):
    """Time left on the 24h no-reuse guard for this exact (link,
    event) pair, or None when it may be used again. Same link +
    same event = BLOCK even with a different caption; same link +
    a DIFFERENT event stays allowed (the user's rule). The event
    match is the same fuzzy overlap as the topic cooldown, scoped
    to this link - a second net if the topic check ever misses."""
    store = state.get("posted_promo_link_topics") or {}
    link = (link or "").strip()
    words = _event_words(headline)
    for stored_key in list(store.keys()):
        if "||" not in stored_key:
            continue
        stored_link, stored_event = stored_key.split("||", 1)
        if stored_link != link:
            continue
        left = _store_cooldown_left(store, stored_key,
                                    PROMO_TOPIC_COOLDOWN_HOURS)
        if left is None:
            continue
        if _event_keys_match(words, _norm_news_key(stored_event).split()):
            return left
    return None


def _record_promo_link_topic_posted(state, link, headline):
    """Remember that this (link, event) pair was posted now."""
    _store_record(state.setdefault("posted_promo_link_topics", {}),
                  _promo_link_topic_key(link, headline))


def _record_promo_account_posted(state, headline, handle):
    """Remember WHICH account posted this news event (rebuild #7.8).
    The per-topic/event cooldown is GLOBAL across accounts - a topic
    posted by ANY account is dead for ALL accounts for 24h - and this
    record proves which account posted what (the picker must choose a
    DIFFERENT story for each account within a run). Stored as
    {event_key: "iso_timestamp|handle"} so the newest timestamp still
    wins in save_state / merge_worker_state (ISO timestamps sort
    first, the handle rides along). Pruned to 7 days, capped at 500
    by save_state like the other promo stores."""
    key = _norm_news_key(headline)
    if not key:
        return
    store = state.setdefault("posted_promo_accounts", {})
    store[key] = f"{now_iso()}|{(handle or '').strip()}"
    cutoff = now_utc() - timedelta(days=7)
    for k in list(store.keys()):
        v = store.get(k, "")
        try:
            dt = datetime.fromisoformat(str(v).split("|", 1)[0])
            if dt.tzinfo is None:
                dt = dt.replace(tzinfo=UTC)
        except Exception:
            dt = None
        if dt is None or dt < cutoff:
            store.pop(k, None)


def _promo_account_for(state, headline):
    """The account handle that posted this news event, or None."""
    v = (state.get("posted_promo_accounts") or {}).get(
        _norm_news_key(headline), "")
    if isinstance(v, str) and "|" in v:
        return v.split("|", 1)[1] or None
    return None


def _bsky_gap_key(card):
    """The key the 5-minute no-burst gap is stored under (rebuild
    #7.8): the ACCOUNT handle, not the card name. Two cards sharing
    one account must not burst-post to that account - a gap keyed by
    card name let two cards (or two accounts) post to the same
    account seconds apart. Falls back to the card name when the card
    has no account set."""
    if isinstance(card, dict):
        return (card.get("account_handle") or "").strip() or card.get("name", "")
    return str(card or "")


def _bsky_gap_left(state, card_name):
    """Time left on the 5-minute no-burst gap for a card, or None when
    the card may post again. (Rebuild #7.2.)"""
    last = (state.get("last_bsky_post_at") or {}).get(card_name or "")
    if not last:
        return None
    try:
        dt = datetime.fromisoformat(last)
        if dt.tzinfo is None:
            dt = dt.replace(tzinfo=UTC)
    except Exception:
        return None
    left = dt + timedelta(minutes=BSKY_MIN_POST_GAP_MINUTES) - now_utc()
    return left if left.total_seconds() > 0 else None


def _record_bsky_post_at(state, card_name):
    """Remember that this card posted a Bluesky post now (state.json,
    so the gap survives across worker runs)."""
    state.setdefault("last_bsky_post_at", {})[card_name or ""] = now_iso()


def _pick_fresh_promo_news(card, state):
    """Pick a FRESH news story for a promo post: (topic, headline, photo).
    Candidates: ONLY the user's two news categories (Rebuild #7.8,
    user order 2026-11-24 - USA political news and war news, rotating
    the starting category per post). The card's topic_override is the
    ONLY other allowed topic (an explicit user instruction). There is
    NO fallback to custom text, Bluesky trending or "breaking news":
    if neither category yields a fresh story with a verified people's
    photo, the run SKIPS posting (a clean skip, logged) - a
    wrong-category post is worse than no post. A story is fresh only
    if its headline was NOT used for a promo post in the last 24h
    (per-topic cooldown, GLOBAL across accounts). The photo is the
    story's REAL online image (the news article's og:image, downloaded
    and verified); text/logo/watermark on it is FINE. Pollinations
    (AI) images are never used. Rebuild #7.4: a Google News article
    link IS fetched for its og:image - IF it redirects (HTTP 302) to
    the publisher, fetch_og_image follows it (meta-refresh resolved
    too); live check 2026-11-23: plain requests gets NO redirect
    from these links (the page serves the Google News logo as
    og:image), so the real-photo fallback below is what usually
    finds the photo. When the article's own image is unavailable, a
    REAL photo is searched for that story from real-photo sources
    (Openverse / Pexels / Pixabay / Wikimedia / Google Images /
    Bing Images); a real stock / editorial photo is acceptable - but
    Rebuild #7.6: it must be RELEVANT to the story (its source page
    must be about the story, _photo_relevant); a real photo from an
    unrelated page is rejected, and an alt text that mentions a name
    is never enough. Rebuild #7.8: when the headline names a PERSON,
    the source page must name that person too, and the Gemini vision
    gate must verify the photo shows that person. Every candidate
    tried is logged (story + image URL + accept/reject) so the log
    shows the search, and the search is bounded (max items + max
    fallback searches) so a run can never grind through dozens of
    doomed fetches. The chosen category is logged on every post
    ('promo category: ...'). The returned photo dict carries the
    story's own URL as "article_url", so a card with no link of its
    own can still post the news with the story link in the caption.
    Returns (None, None, None) when no fresh story with a real image
    exists; LAST_BSKY_SKIP says why ("cooldown" = every story used
    within 24h, "no_photo" = fresh stories exist but no real image
    could be fetched, "no_news" = no news at all in the categories)."""
    global LAST_BSKY_SKIP
    LAST_BSKY_SKIP = None
    # Rebuild #7.8: ONLY the two categories (rotating the starting
    # category per post) plus the card's topic_override (an explicit
    # user instruction). NO custom text, NO Bluesky trending, NO
    # "breaking news" fallback - a post is Political or War news, or
    # it does not go out at all.
    cat_topics = _rotated_promo_categories(state)
    category_of = {_norm_news_key(c): c for c in cat_topics}
    topics = list(cat_topics)
    if isinstance(card, dict):
        override = (card.get("topic_override") or "").strip()
        if override:
            topics.append(override)
    seen_topics = set()
    uniq = []
    for t in topics:
        k = _norm_news_key(t)
        if k and k not in seen_topics:
            seen_topics.add(k)
            uniq.append(t)
    topics = uniq
    had_items = False
    fresh_no_photo = False
    tried = 0            # news items examined (budgeted)
    fallback_tries = 0   # real-photo searches done (budgeted)
    vision = {"used": 0}  # Rebuild #7.7: Gemini vision calls used
    # this pick - at most VISION_MAX_CHECKS_PER_POST per post; the
    # same budget covers the og:image gate and the fallback search,
    # so one post can never burn more than 3 vision calls.
    seen_imgs = set()    # image URLs already rejected this pick - the
    # same logo must never be fetched/downloaded twice in one run
    tried_fallback = set()  # normalised headlines already fallback-searched
    for topic in topics:
        try:
            _verified, _sources, items = verify_news(topic)
        except Exception:
            continue
        if items:
            had_items = True
        seen = set()
        for item in (items or [])[:5]:
            if tried >= PICK_MAX_ITEMS:
                log("info", "promo: candidate budget reached "
                            f"({PICK_MAX_ITEMS} items) - stopping the search")
                break
            link = (item.get("link") or "").strip()
            if not link or link in seen:
                continue
            seen.add(link)
            tried += 1
            headline = (item.get("title") or "").strip() or topic
            if _promo_topic_cooldown_left(state, headline) is not None:
                log("info", f"photo candidate: '{headline[:60]}' - "
                            "skipped (same event used within 24h, event "
                            f"key '{_norm_news_key(headline)[:60]}')")
                continue
            if _promo_link_topic_cooldown_left(
                    state, (card.get("link") or ""), headline) is not None:
                log("info", f"photo candidate: '{headline[:60]}' - "
                            "skipped (same link + same event within 24h, "
                            f"event key '{_norm_news_key(headline)[:60]}')")
                continue
            src = item.get("source") or "news"
            # 1) The article's own og:image. Rebuild #7.4: a Google
            # News link IS fetched - IF it redirects (HTTP 302) to
            # the publisher, fetch_og_image follows that redirect to
            # the publisher's og:image (a meta-refresh redirect is
            # resolved too). Live check 2026-11-23: plain requests
            # gets NO redirect from these links, so the logo is
            # rejected below and the real-photo fallback runs.
            photo = None
            skip_fallback = False
            img = fetch_og_image(link, topic=headline)
            if img and img in seen_imgs:
                log("info", f"photo candidate: '{headline[:60]}' - "
                            "rejected (same image already tried)")
            elif not img:
                log("info", f"photo candidate: '{headline[:60]}' - "
                            "rejected (no og:image)")
            elif _is_pollinations_url(img):
                # An AI-generated og:image taints the story: skip
                # it entirely (rebuild #7.1) - never rescue it
                # with a fallback photo.
                seen_imgs.add(img)
                log("info", f"photo candidate: '{headline[:60]}' - "
                            f"rejected (AI-generated og:image): {img[:100]}")
                skip_fallback = True
            elif _is_logo_image_url(img):
                seen_imgs.add(img)
                log("info", f"photo candidate: '{headline[:60]}' - "
                            f"rejected (logo og:image): {img[:100]}")
            else:
                local = download_image(img, topic)
                if local:
                    # Rebuild #7.7: Gemini vision is the FINAL gate
                    # on the article's own image too - a publisher
                    # og:image can still be the wrong photo (a chart,
                    # a poster, a different person). A vision NO
                    # rejects it and the real-photo fallback below
                    # runs for the same story; a vision failure falls
                    # back to the #7.6 keyword check in
                    # fetch_og_image, which already passed.
                    if _vision_gate(local, headline, vision) is False:
                        seen_imgs.add(img)
                        log("info", f"photo candidate: '{headline[:60]}' - "
                                    "rejected (vision NO - photo does not "
                                    "match the story)")
                    else:
                        cat = category_of.get(_norm_news_key(topic))
                        if cat:
                            log("info", f"promo category: {cat}")
                        log("info", f"photo candidate: '{headline[:60]}' - "
                                    f"ACCEPTED og:image (from {src})")
                        return topic, headline, {
                            "url": img, "source": "news",
                            "alt": headline, "local_path": local,
                            "article_url": link}
                else:
                    seen_imgs.add(img)
                    log("info", f"photo candidate: '{headline[:60]}' - "
                                "rejected (og:image download failed)")
            # 2) Real-photo fallback (rebuild #7.3, user order): a REAL
            # photo for this story from real-photo sources (Openverse /
            # Pexels / Pixabay / Wikimedia / Google Images / Bing
            # Images) - never AI, never a logo. A real stock /
            # editorial photo is acceptable when the article's own
            # image is unavailable. (Skipped for an AI-image story.)
            key = _norm_news_key(headline)
            if not skip_fallback and key not in tried_fallback and \
                    fallback_tries < PICK_MAX_FALLBACK_SEARCHES:
                tried_fallback.add(key)
                fallback_tries += 1
                photo = _real_photo_for_topic(headline, vision)
                if photo and photo.get("local_path"):
                    cat = category_of.get(_norm_news_key(topic))
                    if cat:
                        log("info", f"promo category: {cat}")
                    log("info", f"photo candidate: '{headline[:60]}' - "
                                f"ACCEPTED real photo (from "
                                f"{photo.get('source') or 'stock'})")
                    # Rebuild #7.8: carry the story URL so a card
                    # with no link of its own still posts the news
                    # with the story link in the caption.
                    photo.setdefault("article_url", link)
                    return topic, headline, photo
                log("info", f"photo candidate: '{headline[:60]}' - "
                            "rejected (no real photo found for this story)")
            fresh_no_photo = True
        if tried >= PICK_MAX_ITEMS:
            break
    log("info", f"promo: photo search done - {tried} candidate(s) tried, "
                f"{fallback_tries} real-photo search(es), no usable photo")
    if not had_items:
        LAST_BSKY_SKIP = "no_news"
        log("info", "promo: no news available in Political / War - "
                    "skipping (no fallback to other categories)")
    elif fresh_no_photo:
        LAST_BSKY_SKIP = "no_photo"
        log("info", "promo: fresh news exists but no real image could "
                    "be fetched - skipping")
    else:
        LAST_BSKY_SKIP = "cooldown"
        log("info", "promo: every fresh news story was already used "
                    "within 24h - cooldown, skipping")
    return None, None, None


def _refresh_card(card):
    """Re-read a card's UI settings fresh from data/cards.json - the
    UI is the source of truth for EVERY post (user's strict order,
    2026-11-23). File cards are matched by name; a card deleted or
    renamed mid-run falls back to the in-memory card. The worker runs
    file cards only (the DB is empty on GitHub Actions), so DB cards
    are returned unchanged."""
    if not isinstance(card, dict) or card.get("id"):
        return card
    name = card.get("name", "")
    try:
        for c in load_file_cards():
            if c.get("name") == name:
                return c
    except Exception as e:
        log("warning", f"card '{name}': could not re-read settings, "
                       f"using in-memory card: {e}")
    return card


def log_card_settings(card):
    """Rebuild #7: print the card's EFFECTIVE settings at the start of
    every run, so the workflow log proves the worker is using exactly
    the values saved in the UI (data/cards.json) - nothing invented,
    nothing defaulted silently."""
    name = card.get("name", "")
    reply_own, reply_others, rpr, lb = card_reply_settings(card)
    log("info", f"card '{name}': settings type={card.get('type', '')} "
                f"posts/day={card_posts_per_day(card)} "
                f"posts/run={card_posts_per_run(card)} "
                f"interval={card_interval_minutes(card)}m "
                f"image_ratio={card_bsky_image_ratio(card)} "
                f"tone={card_tone(card)} spread={card_spread_mode(card)} "
                f"replies: own={reply_own} others={reply_others} "
                f"{rpr}/run lookback={lb}d "
                f"days={sorted(card_days_of_week(card))} "
                f"jitter={card_jitter_minutes(card)}m "
                f"week_cap={card_max_posts_per_week(card)} "
                f"month_cap={card_max_posts_per_month(card)} "
                f"retry={card_retry_after_minutes(card)}m/"
                f"{card_retry_max(card)} "
                f"replies/day={card_replies_per_day(card)}")


def fetch_photo(topic):
    """Find a clean photo for a topic. Returns dict or None (strict)."""
    for fn in (_pexels_photo, _pixabay_photo, _openverse_photo):
        try:
            found = fn(topic)
        except Exception:
            found = None
        if found:
            local = download_image(found["url"], topic)
            if local:
                found["local_path"] = local
                log("info", f"photo: {found['source']} for '{topic}'")
                return found
    # Last fallback: generate one (still no logo/text).
    found = _pollinations_photo(topic)
    if found:
        log("info", f"photo: pollinations (generated) for '{topic}'")
        return found
    log("warning", f"photo: NONE found for '{topic}' -> topic dropped")
    return None


# ---------------------------------------------------------------- Bluesky trending (MOST IMPORTANT)
# News discovery starts HERE: what is trending on Bluesky decides what
# news gets written. Only if Bluesky trending is unavailable do we fall
# back to RSS top stories.
BSKY_PUBLIC = "https://public.api.bsky.app/xrpc"


def get_bluesky_trending(limit=10):
    """Return a list of trending topic strings from Bluesky."""
    topics = []
    try:
        r = requests.get(f"{BSKY_PUBLIC}/app.bsky.unspecced.getTrendingTopics",
                         timeout=20)
        if r.status_code == 200:
            for t in r.json().get("topics", [])[:limit]:
                name = (t.get("topic") or "").strip()
                if name:
                    topics.append(name)
            if topics:
                log("info", f"trending (bluesky): {topics[:5]}")
                return topics
    except Exception as e:
        log("warning", f"trending topics error: {e}")
    # Fallback: What's Hot feed -> pull hashtags/keywords from hot posts.
    try:
        feed_uri = ("at://did:plc:z72i7hdynmk6r22z27h6tvur/"
                    "app.bsky.feed.generator/whats-hot")
        r = requests.get(f"{BSKY_PUBLIC}/app.bsky.feed.getFeed",
                         params={"feed": feed_uri, "limit": 25}, timeout=20)
        if r.status_code == 200:
            seen = []
            for item in r.json().get("feed", []):
                text = ((item.get("post") or {}).get("record") or {}).get("text", "")
                for tag in re.findall(r"#(\w+)", text):
                    if tag.lower() not in [s.lower() for s in seen]:
                        seen.append(tag)
                if len(seen) >= limit:
                    break
            if seen:
                log("info", f"trending (whats-hot hashtags): {seen[:5]}")
                return seen
    except Exception as e:
        log("warning", f"whats-hot error: {e}")
    return []


def search_bluesky_posts(query, limit=10):
    """Search Bluesky posts (public, no login). Returns list of posts."""
    try:
        r = requests.get(f"{BSKY_PUBLIC}/app.bsky.feed.searchPosts",
                         params={"q": query, "sort": "top", "limit": limit},
                         timeout=20)
        if r.status_code == 200:
            return r.json().get("posts", [])
    except Exception as e:
        log("warning", f"bluesky search error: {e}")
    return []


# ---------------------------------------------------------------- news verification
def verify_news(topic):
    """Check a topic against Google News RSS. Returns (verified, sources, items).
    Verified = at least 2 DIFFERENT sources report it (truth check)."""
    try:
        url = ("https://news.google.com/rss/search?q=" + quote_plus(topic) +
               "&hl=en&gl=US&ceid=US:en")
        r = requests.get(url, timeout=25,
                         headers={"User-Agent": "Mozilla/5.0"})
        if r.status_code != 200:
            return False, [], []
        root = ET.fromstring(r.content)
        items, sources = [], set()
        for item in root.findall(".//item"):
            title = (item.findtext("title") or "").strip()
            link = (item.findtext("link") or "").strip()
            src = (item.findtext("source") or "").strip()
            if not src and link:
                src = urlparse(link).netloc.replace("www.", "")
            if title and link:
                items.append({"title": title, "link": link, "source": src})
                if src:
                    sources.add(src.lower())
            if len(items) >= 8:
                break
        verified = len(sources) >= 2
        return verified, sorted(sources), items
    except Exception as e:
        log("warning", f"verify_news error: {e}")
        return False, [], []

# ---------------------------------------------------------------- Blogger
def blogger_publish(title, html_body, labels=None, bold=True, draft=False):
    """Publish an article to Blogger. Returns the post URL or None.
    bold=True (default) post-processes the HTML so headings are bold
    and the lead sentence is bold - the article looks organised and
    eye-catching on the blog, not plain text.
    draft=True saves the post as a Blogger DRAFT (never published) -
    the card's Draft-only mode. The user reviews and publishes it
    manually from Blogger."""
    title = clean_title(title)  # safety net: no '**' ever reaches Blogger
    if bold:
        html_body = bold_format_html(html_body)
    if not (BLOG_ID and BLOGGER_REFRESH_TOKEN and BLOGGER_CLIENT_ID
            and BLOGGER_CLIENT_SECRET):
        log("warning", "blogger_publish: Blogger credentials not configured")
        return None
    body = {"kind": "blogger#post", "blog": {"id": BLOG_ID},
            "title": title, "content": html_body,
            "labels": labels or ["News"]}
    if GOOGLE_AVAILABLE:
        try:
            creds = GoogleCredentials(
                token=None, refresh_token=BLOGGER_REFRESH_TOKEN,
                token_uri="https://oauth2.googleapis.com/token",
                client_id=BLOGGER_CLIENT_ID,
                client_secret=BLOGGER_CLIENT_SECRET,
                scopes=["https://www.googleapis.com/auth/blogger"])
            service = google_build("blogger", "v3", credentials=creds)
            post = service.posts().insert(blogId=BLOG_ID, body=body,
                                          isDraft=bool(draft)).execute()
            return post.get("url")
        except Exception as e:
            log("warning", f"blogger publish (sdk) failed: {e}")
    # REST fallback (no google library needed).
    try:
        tok = requests.post("https://oauth2.googleapis.com/token",
                            data={"client_id": BLOGGER_CLIENT_ID,
                                  "client_secret": BLOGGER_CLIENT_SECRET,
                                  "refresh_token": BLOGGER_REFRESH_TOKEN,
                                  "grant_type": "refresh_token"}, timeout=20)
        access = tok.json().get("access_token")
        if not access:
            log("warning", "blogger publish: could not refresh access token")
            return None
        r = requests.post(
            f"https://blogger.googleapis.com/v3/blogs/{BLOG_ID}/posts",
            params={"isDraft": "true"} if draft else {},
            json=body, headers={"Authorization": f"Bearer {access}"}, timeout=30)
        if r.status_code in (200, 201):
            return r.json().get("url")
        log("warning", f"blogger publish (rest) {r.status_code}: {r.text[:200]}")
    except Exception as e:
        log("warning", f"blogger publish (rest) failed: {e}")
    return None


def blogger_posts_today():
    """How many posts were published to Blogger today (for the daily cap)."""
    conn = db_connect()
    try:
        row = conn.execute(
            "SELECT COUNT(*) c FROM posts WHERE substr(created_at,1,10)=?",
            (today_str(),)).fetchone()
        return row["c"] if row else 0
    finally:
        conn.close()


# ---------------------------------------------------------------- Bluesky client
def bsky_login(handle, app_password):
    if not ATPROTO_AVAILABLE:
        log("warning", "bluesky: atproto library not installed")
        return None
    try:
        client = AtprotoClient()
        client.login(handle, app_password)
        return client
    except Exception as e:
        log("warning", f"bluesky login failed for {handle}: {e}")
        return None


def bluesky_post(client, text, image_path=None, image_alt=""):
    """Post to Bluesky (URL in the text becomes a clickable link).
    Returns (uri, url) or None."""
    try:
        if image_path and os.path.exists(image_path):
            with open(image_path, "rb") as f:
                img = f.read()
            resp = client.send_image(text=text, image=img, image_alt=image_alt or text[:100])
        else:
            resp = client.send_post(text=text)
        uri = getattr(resp, "uri", "") or ""
        # Build a public bsky.app URL from the uri.
        url = ""
        if uri:
            parts = uri.split("/")
            if len(parts) >= 5:
                did, rkey = parts[2], parts[4]
                url = f"https://bsky.app/profile/{did}/post/{rkey}"
        return uri, url
    except Exception as e:
        log("warning", f"bluesky post failed: {e}")
        return None


def bluesky_reply(client, text, parent_uri, parent_cid, root_uri=None, root_cid=None):
    """Reply to a Bluesky post. Returns the reply uri or None."""
    try:
        from atproto import models
        root_uri = root_uri or parent_uri
        root_cid = root_cid or parent_cid
        ref = models.AppBskyFeedPost.ReplyRef(
            parent=models.ComAtprotoRepoStrongRef.Main(uri=parent_uri, cid=parent_cid),
            root=models.ComAtprotoRepoStrongRef.Main(uri=root_uri, cid=root_cid))
        resp = client.send_post(text=text, reply_to=ref)
        return getattr(resp, "uri", "") or ""
    except Exception as e:
        log("warning", f"bluesky reply failed: {e}")
        return None


def bluesky_own_posts_with_replies(client, handle, limit=5, since=None,
                                   max_posts=None):
    """Our recent posts + their un-replied comments. Returns
    [{uri, cid, replies:[{uri, cid, author, text, created_at}]}].
    `since` (a datetime): only posts created at/after `since` are
    scanned - this is the card's comment lookback window, so comments
    on OLD posts are found too, not just the newest few. Posts come
    newest-first, so scanning stops once a post is older than `since`.
    A comment is skipped when we already replied to it (a nested reply
    in the thread authored by our own handle) - so a comment is never
    answered twice, even if the run state is lost."""
    out = []
    cap = int(max_posts or limit or 5)
    if cap <= 0:
        cap = 5
    cutoff = since
    cursor = None
    scanned = 0
    try:
        while scanned < cap:
            page = min(25, cap - scanned)
            try:
                feed = client.get_author_feed(actor=handle, limit=page,
                                              cursor=cursor)
            except TypeError:
                # Older atproto clients do not accept `cursor`.
                feed = client.get_author_feed(actor=handle, limit=page)
                cursor = None
            items = list(getattr(feed, "feed", None) or [])
            if not items:
                break
            stop_here = False
            for item in items:
                post = getattr(item, "post", None)
                if post is None:
                    continue
                # Post date: newest-first, so an old post ends the scan.
                created = getattr(getattr(post, "record", None),
                                  "created_at", "") or ""
                ts = None
                if created:
                    try:
                        ts = datetime.fromisoformat(
                            str(created).replace("Z", "+00:00"))
                        if ts.tzinfo is None:
                            ts = ts.replace(tzinfo=UTC)
                    except Exception:
                        ts = None
                if cutoff is not None and ts is not None and ts < cutoff:
                    stop_here = True
                    break
                scanned += 1
                uri, cid = post.uri, post.cid
                try:
                    thread = client.get_post_thread(uri=uri)
                    replies = []
                    for rep in (getattr(thread.thread, "replies", None) or []):
                        rp = getattr(rep, "post", None)
                        if rp is None:
                            continue
                        # Already answered? A nested reply by our own
                        # handle under this comment means: skip it.
                        answered = False
                        for nested in (getattr(rep, "replies", None) or []):
                            na = getattr(getattr(nested, "post", None),
                                         "author", None)
                            if getattr(na, "handle", "") == handle:
                                answered = True
                                break
                        if answered:
                            continue
                        rec = getattr(rp, "record", None)
                        replies.append({
                            "uri": rp.uri, "cid": rp.cid,
                            "author": getattr(getattr(rp, "author", None),
                                             "handle", ""),
                            "text": getattr(rec, "text", "") if rec else "",
                            "created_at": getattr(rec, "created_at", "")
                            if rec else "",
                        })
                    out.append({"uri": uri, "cid": cid, "replies": replies})
                except Exception as e:
                    log("warning", f"thread fetch failed for {uri}: {e}")
            if stop_here:
                break
            cursor = getattr(feed, "cursor", None)
            if not cursor:
                break
    except Exception as e:
        log("warning", f"author feed failed for {handle}: {e}")
    return out


def get_high_engagement_posts(limit=10):
    """Popular Bluesky posts worth replying to. Returns
    [{uri, cid, author, text, like_count, repost_count, reply_count}]."""
    posts = []
    # What's Hot feed is the best "high engagement" signal.
    try:
        feed_uri = ("at://did:plc:z72i7hdynmk6r22z27h6tvur/"
                    "app.bsky.feed.generator/whats-hot")
        r = requests.get(f"{BSKY_PUBLIC}/app.bsky.feed.getFeed",
                         params={"feed": feed_uri, "limit": 25}, timeout=20)
        if r.status_code == 200:
            for item in r.json().get("feed", []):
                p = item.get("post", {})
                posts.append({
                    "uri": p.get("uri", ""), "cid": p.get("cid", ""),
                    "author": (p.get("author") or {}).get("handle", ""),
                    "text": ((p.get("record") or {}).get("text") or "")[:200],
                    "like_count": p.get("likeCount", 0),
                    "repost_count": p.get("repostCount", 0),
                    "reply_count": p.get("replyCount", 0),
                })
    except Exception as e:
        log("warning", f"whats-hot feed error: {e}")
    if posts:
        posts.sort(key=lambda x: x["like_count"] + x["repost_count"] * 2,
                   reverse=True)
        return posts[:limit]
    # Fallback: search for popular posts.
    for p in search_bluesky_posts("breaking news", limit=limit):
        posts.append({"uri": p.get("uri", ""), "cid": p.get("cid", ""),
                      "author": (p.get("author") or {}).get("handle", ""),
                      "text": ((p.get("record") or {}).get("text") or "")[:200],
                      "like_count": p.get("likeCount", 0),
                      "repost_count": p.get("repostCount", 0),
                      "reply_count": p.get("replyCount", 0)})
    return posts


def get_fresh_comments(post_uri, minutes=5):
    """Comments on a post made within the last `minutes` minutes."""
    fresh = []
    try:
        r = requests.get(f"{BSKY_PUBLIC}/app.bsky.feed.getPostThread",
                         params={"uri": post_uri, "depth": 2}, timeout=20)
        if r.status_code != 200:
            return fresh
        cutoff = now_utc() - timedelta(minutes=minutes)
        thread = r.json().get("thread", {})
        for rep in thread.get("replies", []) or []:
            p = rep.get("post", {})
            rec = p.get("record", {})
            created = rec.get("createdAt", "")
            try:
                ts = datetime.fromisoformat(created.replace("Z", "+00:00"))
            except Exception:
                continue
            if ts >= cutoff:
                fresh.append({"uri": p.get("uri", ""), "cid": p.get("cid", ""),
                              "author": (p.get("author") or {}).get("handle", ""),
                              "text": (rec.get("text") or "")[:300],
                              "created_at": created})
    except Exception as e:
        log("warning", f"fresh comments error: {e}")
    return fresh


# ---------------------------------------------------------------- accounts
def list_accounts():
    """All Bluesky accounts: env secret first, then dashboard DB."""
    accounts = list(ENV_BLUESKY_ACCOUNTS)
    seen = {a["handle"] for a in accounts}
    try:
        conn = db_connect()
        try:
            rows = conn.execute(
                "SELECT handle, app_password, display_name FROM accounts "
                "WHERE active=1").fetchall()
        finally:
            conn.close()
        for r in rows:
            if r["handle"] not in seen:
                accounts.append({"handle": r["handle"],
                                 "app_password": r["app_password"],
                                 "display_name": r["display_name"] or ""})
                seen.add(r["handle"])
    except Exception:
        pass
    return accounts


# ---------------------------------------------------------------- article writing
ARTICLE_PROMPT = """You are a news writer for a news blog. Write a complete,
SEO-friendly news article in ENGLISH about this trending topic.

Topic: {topic}
Verified facts / sources:
{facts}

Style: {tone}
Length: {length}

Rules:
- Start with a STRONG hook in the first 2 lines (clickbait style, but honest).
- Headline first, on its own line, starting with "HEADLINE: ".
- Then the article: well organised with subheadings
  (use ## for subheadings), short paragraphs, bold key facts.
- BOLD FORMATTING (important - the article must look bold and
  eye-catching, not plain text): make the FIRST sentence of the article
  a bold lead sentence (wrap it in **...**). Use **bold** for key facts,
  names, numbers and important phrases in every section. Keep every
  subheading short and punchy. The reader must see bold text all
  through the article.
- Include a "Why it matters" section and a "What happens next" section.
- End with a "Sources:" line listing the source names.
- English only. No made-up quotes, numbers or claims - use only the facts
  given above. If a fact is unverified, say so.
"""

# Article length modes (per card). "auto" lets the AI judge the length
# from the story itself - a big story gets longer, a small one stays short.
ARTICLE_LENGTHS = {
    "auto": ("judge from the story itself - a big, important story gets a "
             "longer article (up to about 900 words); a small story stays "
             "short (about 350 words). Do not pad a small story.", 2000),
    "short": ("SHORT - about 300-400 words.", 1200),
    "medium": ("about 500-700 words.", 2000),
    "long": ("LONG - about 900-1200 words, with more detail and background.", 3200),
}

# Tone / style modes (per card). Used for the article AND for the
# Bluesky post text (the hook).
ARTICLE_TONES = {
    "dramatic": ("DRAMATIC and clickbait - a strong hook, punchy lines, "
                 "excitement - but stay honest and factual."),
    "serious": ("SERIOUS straight news - calm, factual, no hype."),
    "funny": ("LIGHT and funny - witty, playful lines - but keep the facts straight."),
    "simple": ("VERY SIMPLE plain English - short sentences, easy words, "
               "anyone can understand."),
}

BSKY_POST_PROMPT = """Write ONE clickbait Bluesky post in ENGLISH about this news.
It must be different from the others (unique wording and angle).
Keep it under 250 characters. End with the blog link on its own line.
Style: {tone}
News: {headline}
Blog link: {link}
"""

BSKY_PROMO_NEWS_PROMPT = """Write ONE short, exciting Bluesky post in ENGLISH about this news story, that makes people want to click the link below it. Sound like a real person sharing breaking news, not an ad. Keep it under 200 characters. Do NOT add the link or a call-to-action yourself - they are added after your text.
Style: {tone}
News: {headline}
Link: {link}
"""

REPLY_PROMPT = """Write ONE short, natural, relevant Bluesky reply in ENGLISH to
this comment. It must sound like a real person, not an ad. Do NOT repeat
the comment. Keep it under 200 characters. End with this link on its own
line: {link}

Comment: "{comment}"
Context (the post it was on): "{context}"
"""


def build_article_html(article_text, image_url, source_names):
    """Turn the Gemini article text into Blogger-ready HTML."""
    lines = [l.rstrip() for l in (article_text or "").splitlines()]
    html_parts = []
    for line in lines:
        if not line.strip():
            continue
        if line.startswith("HEADLINE:"):
            continue
        if line.startswith("## "):
            html_parts.append(f"<h2>{html_lib.escape(line[3:].strip())}</h2>")
        elif line.startswith("Sources:"):
            html_parts.append(
                f"<p><small><b>Sources:</b> {html_lib.escape(line[8:].strip())}</small></p>")
        else:
            # Bold **text** -> <b>text</b>
            esc = html_lib.escape(line)
            esc = re.sub(r"\*\*(.+?)\*\*", r"<b>\1</b>", esc)
            html_parts.append(f"<p>{esc}</p>")
    img = ""
    if image_url:
        img = (f'<p><img src="{html_lib.escape(image_url)}" alt="news photo" '
               f'style="width:100%;height:auto;" /></p>')
    return img + "\n".join(html_parts)


def clean_title(title):
    """Strip Markdown bold markers and prompt leakage from a headline.
    A published title must never contain '**', a stray '*', or a
    leading 'HEADLINE:'."""
    t = (title or "").strip()
    # Strip the markers FIRST: a title like "**HEADLINE:** Foo" starts
    # with asterisks, so the HEADLINE: prefix is only at the start
    # after the markers are gone.
    t = t.replace("**", "").replace("*", "")
    t = re.sub(r"^\s*HEADLINE\s*:\s*", "", t, flags=re.IGNORECASE)
    t = t.strip().strip('"').strip("'").strip()
    t = re.sub(r"\s+", " ", t)
    return t[:200] if t else "Breaking News"


def extract_headline(article_text):
    for line in (article_text or "").splitlines():
        if line.strip().startswith("HEADLINE:"):
            return clean_title(line.strip()[9:].strip())
    first = (article_text or "").splitlines()[0][:120] if article_text else "Breaking News"
    return clean_title(first)


def bold_format_html(html_body):
    """Post-process published article HTML so it looks bold and
    organised, not plain text. Headings get <strong>, the lead sentence
    (first real paragraph) gets <b>, and any leftover **markers**
    become <b>. Idempotent - safe to run twice."""
    if not html_body:
        return html_body
    body = html_body
    # 1) Headings bold: <h2>Text</h2> -> <h2><strong>Text</strong></h2>
    def _bold_heading(m):
        inner = m.group(2)
        if "<strong>" in inner or "<b>" in inner:
            return m.group(0)
        return f"<{m.group(1)}><strong>{inner}</strong></{m.group(1)}>"
    body = re.sub(r"<(h[123])>(.*?)</\1>", _bold_heading, body, flags=re.DOTALL)
    # 2) Any leftover **markers** -> <b>
    body = re.sub(r"\*\*(.+?)\*\*", r"<b>\1</b>", body)
    # 3) Lead sentence bold: first real paragraph (skips the photo
    #    paragraph and very short ones). If it already has bold, leave it.
    for m in re.finditer(r"<p>(.*?)</p>", body, flags=re.DOTALL):
        inner = m.group(1)
        if "<img" in inner:
            continue
        text = re.sub(r"<[^>]+>", "", inner).strip()
        if len(text) < 20:
            continue
        if "<b>" in inner or "<strong>" in inner:
            break
        sm = re.match(r"^(.*?[.!?])(\s+.*)?$", inner, flags=re.DOTALL)
        if sm:
            new = f"<p><b>{sm.group(1)}</b>{sm.group(2) or ''}</p>"
        else:
            new = f"<p><b>{inner}</b></p>"
        body = body[:m.start()] + new + body[m.end():]
        break
    return body


def card_bold_enabled(card):
    """Per-card 'Bold formatting' toggle (Blogger cards). True by
    default; falls back to the global blogger_bold_format setting."""
    v = card.get("bold_format") if isinstance(card, dict) else None
    if v is None:
        return str(get_setting("blogger_bold_format", "true")).strip().lower() != "false"
    if isinstance(v, bool):
        return v
    return str(v).strip().lower() not in ("false", "0", "no", "off", "")

# ---------------------------------------------------------------- worker
try:
    from zoneinfo import ZoneInfo
    USER_TZ = ZoneInfo("Asia/Dhaka")
except Exception:  # pragma: no cover
    USER_TZ = timezone(timedelta(hours=6))

OWN_REPLY_PROMPT = """Write ONE short, warm, natural Bluesky reply in ENGLISH
to this comment on MY post. Sound like a real person. Keep it under 150
characters. Do not add any link.

Comment: "{comment}"
"""

WORKER_RUNNING = False


def candidate_topics(state, limit=5, force_topic=None):
    """Trending topics from Bluesky FIRST (verified, not already posted).
    Falls back to RSS top stories if Bluesky trending is unavailable.
    force_topic: a per-card custom topic - it goes FIRST, ahead of
    trending."""
    cands = []
    posted = [t.lower() for t in state.get("posted_topics", [])]
    # Per-card custom topic (a card with source=custom) goes FIRST.
    # There is no global forced topic or blacklist any more: every
    # topic choice lives inside a card.
    if force_topic is not None:
        forced = str(force_topic or "").strip()
        if forced and forced.lower() not in posted:
            verified, sources, items = verify_news(forced)
            if verified:
                facts = "\n".join(f"- {i['title']} ({i['source']})" for i in items[:5])
                cands.append((forced, sources, facts))
                log("info", f"card topic queued: {forced}")
            else:
                log("info", f"card topic not verified (needs 2 sources): {forced}")
    for topic in get_bluesky_trending(limit=10):
        if topic.lower() in posted:
            continue
        verified, sources, items = verify_news(topic)
        if verified:
            facts = "\n".join(f"- {i['title']} ({i['source']})" for i in items[:5])
            cands.append((topic, sources, facts))
        else:
            log("info", f"topic not verified (needs 2 sources): {topic}")
        if len(cands) >= limit:
            break
    if cands:
        return cands
    # Fallback: Google News top stories.
    try:
        r = requests.get("https://news.google.com/rss?hl=en&gl=US&ceid=US:en",
                         timeout=25, headers={"User-Agent": "Mozilla/5.0"})
        if r.status_code == 200:
            root = ET.fromstring(r.content)
            for item in root.findall(".//item")[:10]:
                title = (item.findtext("title") or "").strip()
                if not title or title.lower() in posted:
                    continue
                verified, sources, items = verify_news(title)
                if verified:
                    facts = "\n".join(f"- {i['title']} ({i['source']})"
                                      for i in items[:5])
                    cands.append((title, sources, facts))
                if len(cands) >= limit:
                    break
    except Exception as e:
        log("warning", f"rss fallback error: {e}")
    return cands


def record_post(title, url, topic, source, image_url, status="published"):
    conn = db_connect()
    try:
        conn.execute(
            "INSERT INTO posts(title, url, topic, source, image_url, status, created_at) "
            "VALUES(?, ?, ?, ?, ?, ?, ?)",
            (title, url, topic, source, image_url, status, now_iso()))
        conn.commit()
    finally:
        conn.close()


def card_in_window(card):
    """True if now (Dhaka) is inside this card's posting window.
    Empty window_start/end = no window (always allowed)."""
    start = str(card.get("window_start") or "").strip()
    end = str(card.get("window_end") or "").strip()
    if not start or not end:
        return True
    try:
        sh, sm = [int(x) for x in start.split(":")]
        eh, em = [int(x) for x in end.split(":")]
    except Exception:
        return True
    now_local = now_utc().astimezone(USER_TZ)
    cur = now_local.hour * 60 + now_local.minute
    s = sh * 60 + sm
    e = eh * 60 + em
    if s <= e:
        return s <= cur <= e
    return cur >= s or cur <= e


def card_posts_per_run(card):
    """How many articles this card publishes per run (card 'count')."""
    try:
        return max(1, int(card.get("count") or 1))
    except Exception:
        return 1


# ---------------------------------------------------------------- rebuild #5
# ADVANCED card features: auto-spread posting times, run-interval vs
# posting gate, draft mode, days of week, jitter, labels, weekly/monthly
# caps, retry, replies-per-day cap, reply skip/allow lists, per-card
# Bluesky account, test runs, article length + tone, Bluesky image ratio.

def _fnv1a(text):
    """FNV-1a 32-bit hash - deterministic in Python AND in the dashboard
    JavaScript, so the worker and the dashboard compute the SAME jitter
    for the SAME card / day / slot."""
    h = 0x811C9DC5
    for b in str(text).encode("utf-8"):
        h ^= b
        h = (h * 0x01000193) & 0xFFFFFFFF
    return h


def card_spread_mode(card):
    m = str(card.get("spread_mode") or "even").strip().lower()
    return m if m in ("even", "best") else "even"


def card_length_mode(card):
    m = str(card.get("length_mode") or "auto").strip().lower()
    return m if m in ("auto", "short", "medium", "long") else "auto"


def card_tone(card):
    t = str(card.get("tone") or "dramatic").strip().lower()
    return t if t in ("dramatic", "serious", "funny", "simple") else "dramatic"


def card_draft_only(card):
    v = card.get("draft_only")
    if isinstance(v, bool):
        return v
    return str(v or "").strip().lower() not in ("", "false", "0", "no", "off")


def card_days_of_week(card):
    """Weekdays (Mon=0 .. Sun=6) this card runs on. Default: every day."""
    raw = card.get("days_of_week")
    days = set()
    if isinstance(raw, (list, tuple)):
        items = raw
    elif isinstance(raw, str):
        try:
            items = json.loads(raw)
            if not isinstance(items, list):
                items = [int(x) for x in raw.split(",") if x.strip() != ""]
        except Exception:
            items = [int(x) for x in raw.split(",") if x.strip() != ""]
    else:
        items = []
    for x in items:
        try:
            d = int(x)
            if 0 <= d <= 6:
                days.add(d)
        except Exception:
            continue
    return days if days else {0, 1, 2, 3, 4, 5, 6}


def card_jitter_minutes(card):
    """Rebuild #7: a MISSING jitter means 10 (the dashboard default) -
    the worker and the UI must agree, so a card saved without the field
    still jitters like the UI shows. An explicit 0 still means no jitter."""
    v = card.get("jitter_minutes")
    if v is None:
        return 10
    try:
        return max(0, min(30, int(v)))
    except Exception:
        return 10


def card_labels(card):
    """Blogger labels for this card's posts. Empty = ["News"]."""
    raw = card.get("labels") or ""
    if isinstance(raw, (list, tuple)):
        out = [str(x).strip() for x in raw if str(x).strip()]
    else:
        out = [x.strip() for x in str(raw).split(",") if x.strip()]
    return out or ["News"]


def card_max_posts_per_week(card):
    try:
        return max(0, int(card.get("max_posts_per_week") or 0))
    except Exception:
        return 0


def card_max_posts_per_month(card):
    try:
        return max(0, int(card.get("max_posts_per_month") or 0))
    except Exception:
        return 0


def card_retry_after_minutes(card):
    try:
        return max(1, int(card.get("retry_after_minutes") or 30))
    except Exception:
        return 30


def card_retry_max(card):
    """Rebuild #7: a MISSING retry_max means 2 (the dashboard default)
    - the worker and the UI must agree. An explicit 0 still means
    no retries."""
    v = card.get("retry_max")
    if v is None:
        return 2
    try:
        return max(0, int(v))
    except Exception:
        return 2


def card_replies_per_day(card):
    try:
        return max(0, int(card.get("replies_per_day") or 0))
    except Exception:
        return 0


def _parse_handle_list(raw):
    out = set()
    if isinstance(raw, (list, tuple)):
        items = raw
    else:
        items = str(raw or "").replace(",", " ").split()
    for h in items:
        h = str(h).strip().lstrip("@").lower()
        if h:
            out.add(h)
    return out


def card_reply_lists(card):
    """(never_reply_handles, only_reply_handles, skip_words).
    never: never reply to these accounts. only: if non-empty, reply
    ONLY to these accounts. skip_words: never reply to a comment
    containing any of these words (case-insensitive)."""
    never = _parse_handle_list(card.get("reply_never") or "")
    only = _parse_handle_list(card.get("reply_only") or "")
    words = [w.strip().lower() for w in
             str(card.get("reply_skip_words") or "").replace(",", " ").split()
             if w.strip()]
    return never, only, words


def card_bsky_image_ratio(card):
    r = str(card.get("bsky_image_ratio") or "16:9").strip()
    return r if r in ("16:9", "1:1", "4:5") else "16:9"


# Peak hours for "best times" auto-spread (Dhaka clock):
# morning 07:00-09:00, midday 12:00-13:00, evening 18:00-21:00.
PEAK_WINDOWS = [(7 * 60, 9 * 60), (12 * 60, 13 * 60), (18 * 60, 21 * 60)]


def _window_minutes(card):
    """This card's posting window as (start_min, end_min) minutes of day.
    Empty window = the whole day (0-1440). Overnight windows
    (end <= start) are normalised by adding 1440 to the end."""
    ws = str(card.get("window_start") or "").strip()
    we = str(card.get("window_end") or "").strip()
    if ws and we:
        try:
            sh, sm = [int(x) for x in ws.split(":")]
            eh, em = [int(x) for x in we.split(":")]
            start = sh * 60 + sm
            end = eh * 60 + em
            if end <= start:
                end += 24 * 60
            return start, end
        except Exception:
            pass
    return 0, 24 * 60


def auto_spread_slots(card, start_date):
    """Posting slots for ONE card for the Dhaka day starting at
    `start_date` (a date). Returns a list of (slot_index, datetime)
    in Dhaka time, jitter already applied (deterministic per card /
    day / slot, so the dashboard shows the same times the worker uses).
    - posts_per_day <= 0 (unlimited) -> [] (no slots; every run may post).
    - Fixed schedule_times (if set) win over auto-spread (exact times,
      no jitter).
    - "even": slots spread evenly across the window.
      Example: 12 posts in 07:00-23:00 (960 min) = every 80 min.
    - "best": slots spread across peak hours only (07-09, 12-13, 18-21
      Dhaka), clipped to the card's window when one is set."""
    per_day = card_posts_per_day(card)
    if per_day <= 0:
        return []
    fixed = _parse_schedule_times(card)
    day_start = datetime(start_date.year, start_date.month, start_date.day,
                         tzinfo=USER_TZ)
    if fixed:
        return [(i, day_start + timedelta(hours=hh, minutes=mm))
                for i, (hh, mm) in enumerate(fixed)]
    wstart, wend = _window_minutes(card)
    total = wend - wstart
    minutes = []
    if card_spread_mode(card) == "best":
        peak = []
        for a, b in PEAK_WINDOWS:
            peak.extend(range(a, b))
        # Clip peak minutes to the card's window (window may be overnight).
        clipped = []
        for m in peak:
            mm = m
            if mm < wstart:
                mm += 24 * 60
            if wstart <= mm < wend:
                clipped.append(mm)
        if clipped:
            n = len(clipped)
            for i in range(per_day):
                idx = int(round(i * n / per_day))
                minutes.append(clipped[min(idx, n - 1)])
        else:
            for i in range(per_day):
                minutes.append(int(wstart + i * total / per_day))
    else:
        for i in range(per_day):
            minutes.append(int(wstart + i * total / per_day))
    name = card.get("name", "")
    jit = card_jitter_minutes(card)
    date_str = start_date.isoformat()
    out = []
    for i, mins in enumerate(minutes):
        j = 0
        if jit > 0:
            span = 2 * jit + 1
            j = (_fnv1a(f"{name}|{date_str}|{i}") % span) - jit
        out.append((i, day_start + timedelta(minutes=mins + j)))
    out.sort(key=lambda x: x[1])
    return out


def card_post_due(card, state):
    """The POSTING gate. Returns (due, due_slots) where due_slots is a
    list of (date_str, slot_index) that are due RIGHT NOW and not used
    yet. A slot is due when its time has passed. Slots are checked for
    today AND yesterday (so an overnight window's early-morning slots
    still count). Unlimited cards (posts_per_day 0) have no slots and
    are ALWAYS due. Fixed schedule_times are used as-is (exact)."""
    name = card.get("name", "")
    if card_posts_per_day(card) <= 0:
        return True, []
    now_local = now_utc().astimezone(USER_TZ)
    used = state.get("file_card_post_slots", {}).get(name, {}) or {}
    due = []
    for delta in (0, 1):
        day = (now_local - timedelta(days=delta)).date()
        for idx, slot_dt in auto_spread_slots(card, day):
            # Only slots that fall on TODAY count. Yesterday's
            # computation matters only for overnight windows, whose
            # early-morning slots land on today - a stale slot from
            # yesterday evening must never trigger a post today.
            if slot_dt.date() != now_local.date():
                continue
            key = day.isoformat()
            if idx in (used.get(key) or []):
                continue
            if slot_dt <= now_local:
                due.append((key, idx))
    return (len(due) > 0), due


def mark_slots_used(state, name, slots):
    """Mark posting slots as used so they are never published twice."""
    if not slots:
        return
    store = state.setdefault("file_card_post_slots", {})
    per_card = store.setdefault(name, {})
    for date_str, idx in slots:
        lst = per_card.setdefault(date_str, [])
        if idx not in lst:
            lst.append(idx)
    # Prune slots older than 3 days.
    cutoff = (now_utc().astimezone(USER_TZ).date() - timedelta(days=3)).isoformat()
    for key in list(per_card.keys()):
        if key < cutoff:
            per_card.pop(key, None)


def _week_key(dt):
    iso = dt.isocalendar()
    return f"{iso[0]}-W{iso[1]:02d}"


def card_posts_today(state, name):
    """Articles THIS card actually published today (Dhaka day)."""
    counts = state.get("file_card_post_counts", {}).get(name, {}) or {}
    if counts.get("day") != now_utc().astimezone(USER_TZ).date().isoformat():
        return 0
    return int(counts.get("day_n") or 0)


def card_posts_this_week(state, name):
    counts = state.get("file_card_post_counts", {}).get(name, {}) or {}
    now_local = now_utc().astimezone(USER_TZ)
    if counts.get("week") != _week_key(now_local):
        return 0
    return int(counts.get("week_n") or 0)


def card_posts_this_month(state, name):
    counts = state.get("file_card_post_counts", {}).get(name, {}) or {}
    now_local = now_utc().astimezone(USER_TZ)
    if counts.get("month") != now_local.strftime("%Y-%m"):
        return 0
    return int(counts.get("month_n") or 0)


def record_card_post(state, name):
    """Count one published article for this card (day / week / month)."""
    now_local = now_utc().astimezone(USER_TZ)
    counts = state.setdefault("file_card_post_counts", {}).setdefault(name, {})
    day = now_local.date().isoformat()
    if counts.get("day") != day:
        counts["day"], counts["day_n"] = day, 0
    week = _week_key(now_local)
    if counts.get("week") != week:
        counts["week"], counts["week_n"] = week, 0
    month = now_local.strftime("%Y-%m")
    if counts.get("month") != month:
        counts["month"], counts["month_n"] = month, 0
    counts["day_n"] = int(counts.get("day_n") or 0) + 1
    counts["week_n"] = int(counts.get("week_n") or 0) + 1
    counts["month_n"] = int(counts.get("month_n") or 0) + 1


def card_caps_remaining(state, name, card):
    """Posts this card may still publish (day / week / month caps
    combined). None = no cap at all (all three are 0 = unlimited).
    0 or less = a cap is already reached."""
    rem = None
    cap = card_posts_per_day(card)
    if cap > 0:
        rem = cap - card_posts_today(state, name)
    wcap = card_max_posts_per_week(card)
    if wcap > 0:
        w = wcap - card_posts_this_week(state, name)
        rem = w if rem is None else min(rem, w)
    mcap = card_max_posts_per_month(card)
    if mcap > 0:
        m = mcap - card_posts_this_month(state, name)
        rem = m if rem is None else min(rem, m)
    return rem


def _card_caps_hit(state, name, card):
    """True if any of this card's post caps (day/week/month) is reached."""
    rem = card_caps_remaining(state, name, card)
    return rem is not None and rem <= 0


def card_replies_today(state, name):
    """Replies THIS card sent today (Dhaka day) - the per-day reply cap."""
    counts = state.get("file_card_reply_counts", {}).get(name, {}) or {}
    if counts.get("day") != now_utc().astimezone(USER_TZ).date().isoformat():
        return 0
    return int(counts.get("n") or 0)


def record_card_reply_today(state, name):
    counts = state.setdefault("file_card_reply_counts", {}).setdefault(name, {})
    day = now_utc().astimezone(USER_TZ).date().isoformat()
    if counts.get("day") != day:
        counts["day"], counts["n"] = day, 0
    counts["n"] = int(counts.get("n") or 0) + 1


def reply_allowed(author, text, card):
    """True if this comment may be replied to under the card's
    skip/allow lists: never-reply accounts, only-reply accounts, and
    skip words. Returns (allowed, reason)."""
    never, only, words = card_reply_lists(card)
    author_l = str(author or "").strip().lstrip("@").lower()
    if author_l and author_l in never:
        return False, f"author {author_l} is on the never-reply list"
    if only and author_l not in only:
        return False, f"author {author_l} is not on the only-reply list"
    text_l = str(text or "").lower()
    for w in words:
        if w and w in text_l:
            return False, f"comment contains skipped word '{w}'"
    return True, ""


def prepare_bsky_image(local_path, ratio=None):
    """Prepare a local image for Bluesky WITHOUT cropping: the photo
    is published in its ORIGINAL aspect ratio (user order 2026-11-23
    - whatever ratio the online photo has, that is the ratio it is
    published in). The card's image_ratio setting is accepted for
    backward compatibility but intentionally IGNORED - no centre
    crop to 16:9 / 1:1 / 4:5 ever happens. Only shrink (resize
    preserving ratio) until the file is <=950KB, because Bluesky
    rejects image blobs over 1 MB. The original ratio (WxH) and the
    published ratio are logged so the log proves no crop happened.
    If Pillow is missing or processing fails, the original file is
    used unchanged."""
    if not local_path or not os.path.exists(local_path):
        return local_path
    try:
        from PIL import Image
        img = Image.open(local_path)
        if img.mode in ("RGBA", "LA", "P"):
            img = img.convert("RGB")
        w, h = img.size
        log("info", f"prepare_bsky_image: original {w}x{h} "
                    f"(ratio {w / h:.2f}) - kept, no crop")
        if os.path.getsize(local_path) <= 950 * 1024:
            log("info", f"prepare_bsky_image: published {w}x{h} "
                        f"(ratio {w / h:.2f}) - unchanged")
            return local_path
        base, _ = os.path.splitext(local_path)
        out = f"{base}-shrunk.jpg"
        for _ in range(4):
            w2, h2 = img.size
            img = img.resize((max(1, w2 // 2), max(1, h2 // 2)))
            img.save(out, "JPEG", quality=80)
            if os.path.getsize(out) <= 950 * 1024:
                break
        w3, h3 = img.size
        log("info", f"prepare_bsky_image: published {w3}x{h3} "
                    f"(ratio {w3 / h3:.2f}) - shrunk to fit 950KB, "
                    "ratio preserved")
        return out
    except Exception as e:
        log("warning", f"prepare_bsky_image failed ({e}) - using original image")
        return local_path


def run_card_blogger(state, card, max_posts=None):
    """Write + publish articles for ONE Blogger card - the ONLY way
    the worker publishes to Blogger (card-only operation).
    Respects the card's own posts-per-day / per-week / per-month caps,
    posting window, posts-per-run, topic/source, bold toggle, labels
    and draft mode. max_posts caps how many articles this run may
    publish (the caller passes min(posts-per-run, due posting slots,
    remaining cap) - so one run can NEVER publish more than its due
    slots, and NEVER exceed the daily cap, even mid-run).
    PHOTO-FIRST order (hard rule): for each topic, fetch + verify a
    photo BEFORE the AI writes anything. No verified photo = the
    topic is dropped entirely, never text-only.
    Returns the LIST of published articles (empty list = nothing
    published this run). Published articles are also recorded in
    state.json (recent_articles) so Bluesky cards can promote them
    on GitHub Actions, where the SQLite DB is empty."""
    name = card.get("name", "")
    bold = card_bold_enabled(card)
    # Per-card caps - counted in PUBLISHED articles, not runs.
    if _card_caps_hit(state, name, card):
        log("info", f"card '{name}': post cap reached - skipping")
        return []
    if not card_in_window(card):
        log("info", f"card '{name}': outside its posting window - skipping")
        return []
    per_run = card_posts_per_run(card)
    limit = per_run if max_posts is None else max(0, int(max_posts))
    if limit <= 0:
        return []
    dry = is_dry_run()
    draft_only = card_draft_only(card)
    labels = card_labels(card)
    length_text, max_tokens = ARTICLE_LENGTHS[card_length_mode(card)]
    tone_text = ARTICLE_TONES[card_tone(card)]
    force = None
    if (card.get("source") or "trending") == "custom":
        force = (card.get("topic_override") or "").strip() or None
    published = []
    for topic, sources, facts in candidate_topics(
            state, limit=max(5, limit), force_topic=force)[:limit]:
        if len(published) >= limit:
            break
        # Re-check the caps before EVERY publish - the cap is counted
        # in published articles, so a run with posts-per-run 5 must
        # stop at the cap instead of publishing 5 past it.
        if _card_caps_hit(state, name, card):
            log("info", f"card '{name}': post cap reached mid-run - stopping")
            break
        if published:
            time.sleep(5)
        # PHOTO FIRST: fetch + verify the photo BEFORE writing.
        photo = fetch_verified_photo(topic)
        if not photo:
            state.setdefault("posted_topics", []).append(topic.lower())
            record_issue("warning", "no_photo",
                         f"card '{name}': topic dropped (no verified photo): {topic}")
            continue
        article_text = ai_write(ARTICLE_PROMPT.format(
            topic=topic, facts=facts, tone=tone_text, length=length_text),
            max_tokens=max_tokens)
        if not article_text:
            record_issue("warning", "ai_write",
                         f"card '{name}': article writing failed for '{topic}'")
            continue
        headline = extract_headline(article_text)
        html_body = build_article_html(article_text,
                                       photo.get("url", ""),
                                       ", ".join(sources))
        if dry:
            log("warning", f"[DRY RUN] card '{name}' would publish: {headline}")
            published.append({"title": headline, "url": "",
                              "image_path": photo.get("local_path", ""),
                              "image_url": photo.get("url", ""),
                              "topic": topic})
            continue
        url = retry_with_backoff(
            lambda: blogger_publish(headline, html_body, labels=labels,
                                    bold=bold, draft=draft_only),
            attempts=3, base_delay=10, label=f"blogger publish '{headline}'")
        if not url:
            record_issue("error", "blogger_publish",
                         f"card '{name}': blogger publish failed for '{headline}'")
            continue
        status = "draft" if draft_only else "published"
        record_post(headline, url, topic, ", ".join(sources),
                    photo.get("url", ""), status=status)
        record_card_post(state, name)
        state.setdefault("posted_urls", []).append(url)
        state.setdefault("posted_topics", []).append(topic.lower())
        # Remember the article in state.json (survives GitHub Actions).
        arts = state.setdefault("recent_articles", [])
        arts.insert(0, {"title": headline, "url": url,
                        "image_url": photo.get("url", ""), "topic": topic,
                        "created_at": now_iso()})
        del arts[20:]
        if draft_only:
            log("info", f"card '{name}' saved DRAFT (not published): {headline} -> {url}")
        else:
            log("info", f"card '{name}' published: {headline} -> {url}")
        published.append({"title": headline, "url": url,
                          "image_path": photo.get("local_path", ""),
                          "image_url": photo.get("url", ""), "topic": topic})
    if not published:
        log("info", f"card '{name}': no publishable topic this run (photo-first)")
    return published


def latest_article(state=None):
    """The newest published article (for Bluesky cards to promote).
    GitHub Actions runners are fresh VMs, so the SQLite DB is EMPTY
    there - fall back to the articles this worker recorded in
    state.json (they survive because state.json is committed back)."""
    conn = db_connect()
    try:
        row = conn.execute("SELECT title, url, image_url FROM posts "
                           "ORDER BY id DESC LIMIT 1").fetchone()
        if row:
            return dict(row)
    finally:
        conn.close()
    if isinstance(state, dict):
        arts = state.get("recent_articles") or []
        if arts:
            return dict(arts[0])
    return None


def _recent_articles(state, limit=10):
    """Recent published articles, newest first (DB first, then the
    state.json record - the DB is empty on GitHub Actions runners).
    Deduped by URL."""
    out, seen = [], set()
    conn = db_connect()
    try:
        rows = conn.execute(
            "SELECT title, url, image_url FROM posts ORDER BY id DESC LIMIT ?",
            (limit,)).fetchall()
        for r in rows:
            d = dict(r)
            if d.get("url") and d["url"] not in seen:
                seen.add(d["url"])
                out.append(d)
    finally:
        conn.close()
    if isinstance(state, dict):
        for a in state.get("recent_articles") or []:
            if isinstance(a, dict) and a.get("url") and a["url"] not in seen:
                seen.add(a["url"])
                out.append(dict(a))
    return out[:limit]


def _next_unposted_article(state, card):
    """The newest recent article this card has NOT posted to Bluesky
    yet. Returns an article dict or None (then the card has nothing
    new to post - it must NOT re-post the same article all day)."""
    name = card.get("name", "")
    posted = set((state.get("file_card_bsky_posts", {}) or {}).get(name, []) or [])
    for art in _recent_articles(state, limit=10):
        if art.get("url") and art["url"] not in posted:
            return art
    return None


def _mark_bsky_posted(state, name, url):
    """Remember that this card already posted this article URL."""
    if not url:
        return
    store = state.setdefault("file_card_bsky_posts", {})
    lst = store.setdefault(name, [])
    if url not in lst:
        lst.append(url)
    del lst[:-50]


def replies_today():
    conn = db_connect()
    try:
        row = conn.execute(
            "SELECT COUNT(*) c FROM replies WHERE substr(created_at,1,10)=?",
            (today_str(),)).fetchone()
        return row["c"] if row else 0
    finally:
        conn.close()


def record_reply(post_uri, comment_uri, reply_text, account_handle):
    conn = db_connect()
    try:
        conn.execute(
            "INSERT INTO replies(post_uri, comment_uri, reply_text, account_handle, "
            "status, created_at) VALUES(?, ?, ?, ?, 'sent', ?)",
            (post_uri, comment_uri, reply_text, account_handle, now_iso()))
        conn.commit()
    finally:
        conn.close()


def run_bluesky_cycle(state, article=None, reply_own=True, reply_others=True,
                      replies_per_run=0, lookback_days=7, card_name="",
                      account_handle="", replies_per_day=0,
                      reply_never="", reply_only="", reply_skip_words=""):
    """Reply to comments for ONE Bluesky card (card-only operation).
    Only the card's own account is used (account_handle, or the first
    account when empty). Posting itself is done by each card via
    _card_bluesky_post - this function only replies.
    - OWN posts: reply to EVERY unanswered comment (no per-run cap) -
      over runs the card answers all of them inside the lookback window.
    - OTHERS' posts: replies_per_run caps the replies per run (0 = no cap).
    - replies_per_day caps ALL replies this card sends in a day (0 = no cap).
    - reply_never / reply_only / reply_skip_words filter every comment.
    lookback_days = how far back (in days) the worker looks for comments
    on our OWN posts - old posts are scanned too, not just the newest
    one. Every reply is logged with the card name, so it shows up in
    that card's own log.
    Returns (own_replies_sent, others_replies_sent) - rebuild #7.3:
    the caller must know whether anything was actually sent, so the
    card's run is only logged as 'ok' when a post or a reply really
    happened."""
    accounts = list_accounts()
    if not accounts:
        log("info", "bluesky cycle: no accounts configured")
        return 0, 0
    # Per-card account: this card posts/replies as ONE account only.
    # NO silent fallback: if the card's account is missing, the card
    # does nothing (it must never reply as some other account).
    if account_handle:
        use_accounts = [a for a in accounts if a["handle"] == account_handle]
        if not use_accounts:
            log("warning", f"bluesky cycle: card '{card_name}' account "
                           f"'{account_handle}' not found - skipping replies "
                           "(add that account first)")
            return 0, 0
    else:
        use_accounts = accounts[:1]
    article = article or latest_article(state)
    if not article:
        log("info", "bluesky cycle: no article to link yet")
        return 0, 0
    dry = is_dry_run()
    try:
        per_run_replies = int(replies_per_run or 0)
    except Exception:
        per_run_replies = 0
    try:
        lb = int(lookback_days or 7)
    except Exception:
        lb = 7
    lb = max(1, min(30, lb))
    try:
        day_cap = int(replies_per_day or 0)
    except Exception:
        day_cap = 0
    tag = f"card '{card_name}': " if card_name else ""
    filter_card = {"reply_never": reply_never, "reply_only": reply_only,
                   "reply_skip_words": reply_skip_words}
    state.setdefault("replied_comments", [])
    own_done = 0
    others_done = 0

    def day_cap_reached():
        return day_cap > 0 and card_replies_today(state, card_name) >= day_cap

    def others_under_cap():
        return per_run_replies <= 0 or others_done < per_run_replies

    # --- 1) Replies to fresh comments on high-engagement posts (OTHERS).
    # Capped by replies_per_run per run AND by the replies-per-day cap.
    if reply_others is False:
        log("info", f"{tag}bluesky replies to others are OFF for this card - skipping")
    else:
        hot = get_high_engagement_posts(limit=5)
        acc_idx = 0
        for post in hot:
            if not others_under_cap() or day_cap_reached():
                break
            for comment in get_fresh_comments(post["uri"], minutes=5):
                if not others_under_cap() or day_cap_reached():
                    break
                if comment["uri"] in state["replied_comments"]:
                    continue
                ok, why = reply_allowed(comment["author"], comment["text"],
                                        filter_card)
                if not ok:
                    log("info", f"{tag}skipped reply to {comment['author']}: {why}")
                    continue
                acc = use_accounts[acc_idx % len(use_accounts)]
                acc_idx += 1
                if not account_enabled(acc["handle"]):
                    continue
                if dry:
                    log("warning", f"[DRY RUN] {tag}would reply to "
                                   f"{comment['author']} ({acc['handle']})")
                    continue
                client = bsky_login(acc["handle"], acc["app_password"])
                if not client:
                    continue
                reply_text = groq_text(REPLY_PROMPT.format(
                    link=article["url"], comment=comment["text"],
                    context=post["text"]), max_tokens=400)
                if not reply_text:
                    continue
                uri = retry_with_backoff(
                    lambda: bluesky_reply(client, reply_text, comment["uri"],
                                          comment["cid"], post["uri"], post["cid"]),
                    attempts=2, base_delay=5, label="bluesky reply (others)")
                if uri:
                    state["replied_comments"].append(comment["uri"])
                    record_reply(post["uri"], comment["uri"], reply_text, acc["handle"])
                    record_card_reply_today(state, card_name)
                    others_done += 1
                    log("info", f"{tag}replied to {comment['author']} "
                                f"(hot post by {post['author']}, "
                                f"comment: '{comment['text'][:60]}') "
                                f"as {acc['handle']}: '{reply_text[:80]}'")
                    time.sleep(2)
    # --- 2) Reply to comments on our OWN posts (ALL of them, lookback window).
    # No per-run cap: over runs the card answers every unanswered comment.
    # Old posts are scanned too - a comment left days ago still gets an
    # answer, as long as the post is inside the lookback window.
    if reply_own is False:
        log("info", f"{tag}bluesky replies to own posts are OFF for this card - skipping")
        return own_done, others_done
    own_cutoff = now_utc() - timedelta(days=lb)
    for acc in use_accounts:
        if day_cap_reached():
            break
        if not account_enabled(acc["handle"]):
            continue
        if dry:
            log("warning", f"[DRY RUN] {tag}would check own-post comments "
                           f"from the last {lb} days ({acc['handle']})")
            continue
        client = bsky_login(acc["handle"], acc["app_password"])
        if not client:
            continue
        own_posts = bluesky_own_posts_with_replies(
            client, acc["handle"], limit=25, since=own_cutoff, max_posts=25)
        pending = sum(len(o["replies"]) for o in own_posts)
        log("info", f"{tag}found {pending} un-replied comment(s) on "
                    f"{len(own_posts)} own post(s) from the last {lb} day(s) "
                    f"({acc['handle']})")
        for own in own_posts:
            for comment in own["replies"]:
                if day_cap_reached():
                    break
                if comment["uri"] in state["replied_comments"]:
                    continue
                if comment["author"] == acc["handle"]:
                    continue
                ok, why = reply_allowed(comment["author"], comment["text"],
                                        filter_card)
                if not ok:
                    log("info", f"{tag}skipped reply to {comment['author']}: {why}")
                    continue
                reply_text = groq_text(OWN_REPLY_PROMPT.format(comment=comment["text"]),
                                       max_tokens=300)
                if not reply_text:
                    continue
                uri = retry_with_backoff(
                    lambda: bluesky_reply(client, reply_text, comment["uri"],
                                          comment["cid"], own["uri"], own["cid"]),
                    attempts=2, base_delay=5, label="bluesky reply (own)")
                if uri:
                    state["replied_comments"].append(comment["uri"])
                    record_reply(own["uri"], comment["uri"], reply_text, acc["handle"])
                    record_card_reply_today(state, card_name)
                    own_done += 1
                    log("info", f"{tag}replied to {comment['author']} on your "
                                f"post (comment: '{comment['text'][:60]}') "
                                f"as {acc['handle']}: '{reply_text[:80]}'")
                    time.sleep(2)
    log("info", f"{tag}reply run done: {own_done} own + {others_done} others "
                f"replies sent (lookback {lb} day(s))")
    return own_done, others_done


def card_interval_minutes(card):
    """One card's interval in minutes: hours + minutes.
    (interval_hours is new; old cards only have interval_minutes.)"""
    try:
        hours = int(card.get("interval_hours") or 0)
    except Exception:
        hours = 0
    try:
        mins = int(card.get("interval_minutes") or 0)
    except Exception:
        mins = 0
    total = hours * 60 + mins
    return total if total > 0 else 30


def card_posts_per_day(card):
    """One card's posts-per-day cap. 0 = unlimited (no cap)."""
    try:
        return int(card.get("posts_per_day") or 0)
    except Exception:
        return 0


def _parse_schedule_times(card):
    raw = card.get("schedule_times") or []
    if isinstance(raw, str):
        try:
            raw = json.loads(raw)
        except Exception:
            raw = [t.strip() for t in raw.split(",") if t.strip()]
    times = []
    for t in (raw if isinstance(raw, list) else []):
        try:
            hh, mm = [int(x) for x in str(t).split(":")]
            if 0 <= hh <= 23 and 0 <= mm <= 59:
                times.append((hh, mm))
        except Exception:
            continue
    return sorted(set(times))


def next_runs_for_card(card, count=5, last_run_iso=None):
    """The next `count` RUN times for one card (aware datetimes, Dhaka).
    Runs are interval-based: last_run + interval, stepping forward
    until in the future. (Fixed schedule_times no longer drive runs -
    they are POSTING times now, handled by the auto-spread gate.)
    This is the SAME math the dashboard preview uses (in JS)."""
    now_local = now_utc().astimezone(USER_TZ)
    out = []
    interval = card_interval_minutes(card)
    base = None
    if last_run_iso:
        try:
            base = datetime.fromisoformat(last_run_iso)
            if base.tzinfo is None:
                base = base.replace(tzinfo=UTC)
            base = base.astimezone(USER_TZ)
        except Exception:
            base = None
    nxt = (base + timedelta(minutes=interval)) if base else now_local + timedelta(minutes=interval)
    while nxt <= now_local:
        nxt += timedelta(minutes=interval)
    for _ in range(count):
        out.append(nxt)
        nxt += timedelta(minutes=interval)
    return out


def next_post_times_for_card(card, count=5):
    """The next `count` POSTING times for one card (aware datetimes,
    Dhaka) - the auto-spread slots (or fixed schedule_times) that have
    not passed yet. Unlimited cards (posts_per_day 0) have no slots:
    every run may post, so this returns []."""
    if card_posts_per_day(card) <= 0 and not _parse_schedule_times(card):
        return []
    now_local = now_utc().astimezone(USER_TZ)
    out = []
    for delta in (0, 1, 2):
        day = (now_local + timedelta(days=delta)).date()
        for _idx, slot_dt in auto_spread_slots(card, day):
            if slot_dt > now_local:
                out.append(slot_dt)
            if len(out) >= count:
                return out[:count]
    return out[:count]


def next_run_for_card(card):
    nxt = next_runs_for_card(card, count=1)
    return nxt[0].astimezone(UTC).isoformat() if nxt else ""


def card_runs_today(state, key):
    """How many times this card has run today (same UTC day boundary
    the worker uses for its other daily counts)."""
    today = state.get("file_card_runs_today", {}).get(key, {})
    if today.get("date") != today_str():
        return 0
    return int(today.get("count") or 0)


def record_card_run_today(state, key):
    today = state.setdefault("file_card_runs_today", {})
    entry = today.get(key, {})
    if entry.get("date") != today_str():
        entry = {"date": today_str(), "count": 0}
    entry["count"] = int(entry.get("count") or 0) + 1
    today[key] = entry


CARDS_PATH = os.path.join(DATA_DIR, "cards.json")


def load_file_cards():
    """Cards from data/cards.json (edited via the dashboard / GitHub).
    This is the GitHub-only control panel - no server needed."""
    if not os.path.exists(CARDS_PATH):
        return []
    try:
        with open(CARDS_PATH, "r", encoding="utf-8") as f:
            data = json.load(f)
        if isinstance(data, list):
            return [c for c in data if isinstance(c, dict)]
    except Exception as e:
        log("warning", f"cards.json load failed: {e}")
    return []


def file_card_due(card, state):
    """Is a file-based card due for a RUN (reply checks + maybe a post)?
    - Card must be active.
    - Today (Dhaka) must be one of the card's days of week.
    - A failed run may retry early: if the card failed and retries are
      left and the retry time has passed, it is due even before the
      normal interval.
    - Otherwise: the run interval since the last run must have passed.
    NOTE: the posts-per-day cap does NOT gate runs - a card still runs
    (for replies) when its posting cap is hit; it just does not publish.
    Publishing itself is gated separately by card_post_due()."""
    name = card.get("name", "")
    today_wd = now_utc().astimezone(USER_TZ).weekday()
    if today_wd not in card_days_of_week(card):
        return False
    retries = (state.get("file_card_retries", {}) or {}).get(name, {}) or {}
    fails = int(retries.get("fails") or 0)
    if fails > 0 and fails <= card_retry_max(card):
        nxt = retries.get("next_retry") or ""
        if nxt:
            try:
                nxt_dt = datetime.fromisoformat(nxt)
                if nxt_dt.tzinfo is None:
                    nxt_dt = nxt_dt.replace(tzinfo=UTC)
                if now_utc() >= nxt_dt:
                    log("info", f"card '{name}': retry {fails}/{card_retry_max(card)} "
                                f"after failure - due now")
                    return True
            except Exception:
                pass
    runs = state.get("file_card_runs", {})
    last = runs.get(name, "")
    last_dt = None
    if last:
        try:
            last_dt = datetime.fromisoformat(last)
            if last_dt.tzinfo is None:
                last_dt = last_dt.replace(tzinfo=UTC)
        except Exception:
            last_dt = None
    if last_dt is None:
        return True
    return now_utc() >= last_dt + timedelta(minutes=card_interval_minutes(card))


def record_card_retry(state, name, card):
    """A run failed: count it and schedule the next retry (if any left)."""
    retries = state.setdefault("file_card_retries", {})
    entry = retries.setdefault(name, {"fails": 0, "next_retry": ""})
    entry["fails"] = int(entry.get("fails") or 0) + 1
    if entry["fails"] <= card_retry_max(card):
        nxt = now_utc() + timedelta(minutes=card_retry_after_minutes(card))
        entry["next_retry"] = nxt.isoformat()
        log("info", f"card '{name}': run failed ({entry['fails']}/"
                    f"{card_retry_max(card)} retries) - next retry at "
                    f"{nxt.astimezone(USER_TZ).strftime('%H:%M')} Dhaka")
    else:
        entry["next_retry"] = ""
        log("info", f"card '{name}': retries exhausted "
                    f"({card_retry_max(card)}) - waiting for the normal interval")


def clear_card_retries(state, name):
    """A run succeeded: forget past failures."""
    retries = state.get("file_card_retries", {}) or {}
    if name in retries:
        retries.pop(name, None)


def card_reply_settings(card):
    """Per-card Bluesky reply settings (reply_own / reply_others /
    replies_per_run / lookback_days). Returns a 4-tuple.
    Defaults depend on the card type: a reply card replies by default;
    a post/promo card only posts by default. lookback_days = how far
    back (in days) the worker looks for comments on our own posts:
    1-30, default 7."""

    def _lookback(v):
        try:
            n = int(v)
        except Exception:
            return 7
        if n <= 0:
            return 7
        return max(1, min(30, n))

    ctype = card.get("type", "")
    if ctype == "bluesky_reply":
        d_own, d_others = True, True
    else:
        d_own, d_others = False, False

    def _bool(v, default):
        if v is None:
            return default
        if isinstance(v, bool):
            return v
        return str(v).strip().lower() not in ("false", "0", "no", "off", "")

    try:
        rpr = int(card.get("replies_per_run") or 0)
    except Exception:
        rpr = 0
    return (_bool(card.get("reply_own"), d_own),
            _bool(card.get("reply_others"), d_others), rpr,
            _lookback(card.get("lookback_days")))


def _card_bluesky_post(card, state, article, promo=False):
    """Post ONE Bluesky card (post or promo). Returns True on success.
    Shared by bluesky_post and bluesky_promo cards. Only the card's
    own account posts (account_handle, or the first account).
    PHOTO-FIRST (hard rule): a verified photo is REQUIRED.
    - Article post: the article's image is downloaded + verified
      (content-type image/*) and cropped to the card's Bluesky image
      ratio (16:9 / 1:1 / 4:5). No image, or a download that fails =
      the post is SKIPPED ("no photo, skipped") - never text-only.
    - Promo (or a post card with a link): a FRESH news story is picked
      (rebuild #7.8 - ONLY USA political news and war news, rotating;
      NO fallback to other categories) and the photo is that story's
      REAL online image (the news article's og:image; text/logo/
      watermark is FINE; never Pollinations or stock). No verified
      real photo for that news = skipped, never link-only. The caption
      is written about THAT news story, so the same link gets a
      different caption every time. When the card has NO link, the
      story's own URL is the link in the caption (rebuild #7.8) - so
      a link-less card still posts fresh news instead of erroring.
    - The post text is ALWAYS a caption (hook + link), never the bare
      link: the card's custom text, else an AI hook about the news,
      else a built-in hook. Total text stays under 300 chars.
    - Per-topic / per-caption cooldown (rebuild #7.1, 24h): the same
      news story / caption is never reused within 24h. The LINK itself
      has no cooldown - it may post many times a day with different
      captions. A cooldown skip is a clean no-op (LAST_BSKY_SKIP).
    The photo is verified BEFORE logging in or writing any text, so a
    failed photo never wastes an AI call. The post text uses the
    card's tone."""
    global LAST_BSKY_SKIP
    LAST_BSKY_SKIP = None
    name = card.get("name", "")
    tone_text = ARTICLE_TONES[card_tone(card)]
    accs = [a for a in list_accounts()
            if not card.get("account_handle") or
            a["handle"] == card["account_handle"]]
    if not accs:
        log("warning", f"card '{name}': no usable Bluesky account - post skipped")
        return False
    link = (card.get("link") or "").strip()
    use_link = promo or bool(link)
    # Rebuild #7.8: the link that goes in the caption. The card's own
    # link when it has one; otherwise (link-less card, fresh news)
    # the picked story's own URL (set after the picker, from
    # photo["article_url"]) - so a card with NO link still posts
    # fresh news with a real link in the caption.
    effective_link = link
    if not use_link and not article:
        log("warning", f"card '{name}': no photo, skipped - nothing to post")
        return False
    # --- PHOTO-FIRST gate (before login, before any AI text) ---
    # Rebuild #7.1: a promo post's photo is a REAL image from online
    # news FOR THE NEWS STORY in its caption (picked fresh here, so
    # the caption and the image are always about the same story).
    image_path = None
    image_alt = ""
    news_topic = ""
    news_headline = ""
    if use_link:
        news_topic, news_headline, photo = _pick_fresh_promo_news(card, state)
        if not photo:
            # _pick_fresh_promo_news already logged why (LAST_BSKY_SKIP).
            log("warning", f"card '{name}': no photo, skipped - Bluesky post "
                           "needs a verified real news photo")
            return False
        if _is_pollinations_url(photo.get("url", "")):
            log("warning", f"card '{name}': no photo, skipped - promo photo "
                           "is AI-generated, not a real news image")
            LAST_BSKY_SKIP = "no_photo"
            return False
        # Rebuild #7.8: a link-less card posts the story with the
        # story's own URL (the picker carries it as article_url).
        effective_link = link or (photo.get("article_url") or "")
        # Defense in depth: the picker already skips used stories,
        # but never post a story that was used within 24h even if
        # the pick came from somewhere else.
        if _promo_topic_cooldown_left(state, news_headline) is not None:
            log("info", f"card '{name}': news story already used within "
                        f"24h - cooldown, skipping (event key "
                        f"'{_norm_news_key(news_headline)[:60]}')")
            LAST_BSKY_SKIP = "cooldown"
            return False
        if _promo_link_topic_cooldown_left(state, effective_link, news_headline) is not None:
            log("info", f"card '{name}': same link + same event within "
                        f"24h - cooldown, skipping (event key "
                        f"'{_norm_news_key(news_headline)[:60]}')")
            LAST_BSKY_SKIP = "cooldown"
            return False
        image_path = prepare_bsky_image(photo["local_path"],
                                        card_bsky_image_ratio(card))
        image_alt = photo.get("alt", "") or news_headline
    else:
        image_url = (article or {}).get("image_url", "")
        title = (article or {}).get("title", "") or "breaking news"
        if not image_url:
            log("warning", f"card '{name}': no photo, skipped - article has no image")
            return False
        # Rebuild #7.8: the article's own image must ALSO pass the
        # vision gate (it must show the person/subject in the article
        # title) - a publisher image can be the wrong photo. An
        # AI-generated or logo image, OR a vision NO, falls back to
        # a real-photo search for the title; if that fails, skip.
        need_replacement = (_is_pollinations_url(image_url)
                            or _is_logo_image_url(image_url))
        local = None
        if not need_replacement:
            local = download_image(image_url, title)
            if not local:
                log("warning", f"card '{name}': no photo, skipped - article image "
                               "could not be downloaded/verified")
                return False
            if _vision_gate(local, title, {"used": 0}) is False:
                log("info", f"card '{name}': article image failed the "
                            "vision check - searching for a real photo")
                need_replacement = True
                local = None
        if need_replacement:
            # Rebuild #7/#7.2: an AI-generated or LOGO article image
            # must never go to Bluesky - swap it for a real news image,
            # or skip.
            news = _news_photo(title, state)
            if not news:
                log("warning", f"card '{name}': no photo, skipped - article "
                               "image is AI-generated, a logo, or does not "
                               "match the story, and no real news image "
                               "was found")
                return False
            image_url = news["url"]
            local = download_image(image_url, title)
            if not local:
                log("warning", f"card '{name}': no photo, skipped - replacement "
                               "image could not be downloaded/verified")
                return False
        image_path = prepare_bsky_image(local, card_bsky_image_ratio(card))
        image_alt = article.get("title", "")
        log("info", f"card '{name}': Bluesky image prepared "
                    "(original ratio kept)")
    if is_dry_run():
        log("warning", f"[DRY RUN] card '{name}': would post "
                       f"({accs[0]['handle']}) with photo {image_path}")
        return True
    ok = False
    for acc in accs[:1]:
        if not account_enabled(acc["handle"]):
            continue
        limit = account_posts_limit(acc["handle"])
        if limit > 0 and posts_today_for_account(state, acc["handle"]) >= limit:
            continue
        client = bsky_login(acc["handle"], acc["app_password"])
        if not client:
            continue
        if use_link:
            # Rebuild #7.1: the caption is written about THIS post's
            # news story (news_headline from the fresh pick above),
            # so every post about the same link reads differently.
            text = (card.get("text") or "").strip()
            if not text:
                text = (ai_write(
                    BSKY_PROMO_NEWS_PROMPT.format(
                        headline=(news_headline or news_topic)[:150],
                        link=effective_link, tone=tone_text),
                    max_tokens=400) or "").strip()
            if not text or text == effective_link:
                # The AI failed (keys down / rate limit): use the
                # picked news HEADLINE itself - the caption must always
                # mention the actual news (rebuild #7.2, strict order).
                # A generic built-in hook is only used when there is
                # genuinely no headline at all - NEVER the bare link.
                if news_headline:
                    text = news_headline
                else:
                    hook = _promo_fallback_hook(card, effective_link, state)
                    if hook is None:
                        log("info", f"card '{name}': no fresh caption "
                                    "available within 24h - cooldown, skipping")
                        LAST_BSKY_SKIP = "cooldown"
                        return False
                    text = hook
            hook_text = text
            text = _fit_bsky_text(text, effective_link, _next_bsky_cta(state))
            # Per-caption cooldown (rebuild #7.1): the same caption
            # is never posted twice within 24h. The identity is the
            # caption WITHOUT the rotating CTA (#7.7) - the CTA is
            # decoration, and a rotated CTA must not make a reused
            # caption look new. The no-CTA form is also what
            # pre-#7.7 captions hashed to, so old state still matches.
            caption_id = _fit_bsky_text(hook_text, effective_link, cta="")
            if _promo_caption_cooldown_left(state, caption_id) is not None:
                log("info", f"card '{name}': caption already used "
                            "within 24h - cooldown, skipping")
                LAST_BSKY_SKIP = "cooldown"
                return False
            label = f"card promo ({acc['handle']})"
        else:
            text = (card.get("text") or "").strip()
            if not text:
                text = (ai_write(
                    BSKY_POST_PROMPT.format(headline=article["title"],
                                            link=article["url"], tone=tone_text),
                    max_tokens=400) or "").strip()
            if not text:
                text = article["title"]
            text = _fit_bsky_text(text, article["url"], _next_bsky_cta(state))
            label = f"card post ({acc['handle']})"
        if retry_with_backoff(
                lambda: bluesky_post(client, text, image_path=image_path,
                                     image_alt=image_alt or (article["title"] if article else "")),
                attempts=3, base_delay=5, label=label):
            record_bsky_post(state, acc["handle"])
            if use_link:
                # Rebuild #7.1: record the news story AND the exact
                # caption as used, so neither is reused within 24h.
                # Rebuild #7.5: also record the (link, event) pair,
                # and log the event key so the log proves the guard.
                # Rebuild #7.8: also record WHICH account posted this
                # event - the cooldown is global across accounts, and
                # this proves which account posted what.
                if news_headline:
                    _record_promo_topic_posted(state, news_headline)
                    _record_promo_link_topic_posted(
                        state, effective_link, news_headline)
                    _record_promo_account_posted(
                        state, news_headline, acc["handle"])
                    log("info", f"card '{name}': promo posted - event "
                                f"'{_norm_news_key(news_headline)[:60]}' on "
                                "24h cooldown (topic + link+event recorded, "
                                f"account {acc['handle']})")
                _record_promo_caption_posted(state, caption_id)
            ok = True
    return ok


def _post_bsky_card(card, state, due_slots):
    """The posting loop for bluesky_post / bluesky_promo cards.
    Returns (made, last_error). Respects, in order:
    - posts-per-run, the number of due posting slots (at most ONE post
      per slot, so spread stays even), and the day/week/month caps
      (a run can never push the card past its daily cap).
    A post card with a link posts the link; without a link it posts
    the newest article this card has not posted yet (rotation - the
    same article is never posted all day). Rebuild #7.8: when there
    is no article at all (Blogger API restricted), it falls back to
    FRESH Political/War news from the picker instead of erroring
    ("no article to post yet") - the news MUST publish. In dry-run/
    test mode nothing is counted and no slot is marked used.
    Rebuild #7.1: the same LINK may post many times a day (up to
    posts_per_day), but the same news topic / caption is never reused
    within 24h (posted_promo_topics + posted_promo_captions in
    state.json) - a cooldown skip is a clean no-op, not a failure.
    The card's UI settings are re-read fresh from data/cards.json
    BEFORE EACH POST and the effective settings are logged, so the
    workflow log proves the UI was checked for every single post."""
    global LAST_BSKY_SKIP
    name = card.get("name", "")
    dry = is_dry_run()
    made = 0
    cooldown_hit = False
    cap_hit = False
    # Rebuild #7.2: no bursts - a card that posted less than 5 minutes
    # ago (a concurrent run, or a Run-now right after a scheduled run)
    # does not post again this run. Checked once per RUN, not between
    # posts inside the run, so posts_per_run still works. Dry runs
    # neither check nor record the gap. Rebuild #7.8: the gap is keyed
    # by ACCOUNT handle (not card name), so two cards sharing one
    # account cannot burst-post to it.
    gap_key = _bsky_gap_key(card)
    if not dry and _bsky_gap_left(state, gap_key) is not None:
        log("info", f"card '{name}': posted less than "
                    f"{BSKY_MIN_POST_GAP_MINUTES} minutes ago - too soon, skipping")
        return 0, "too soon"
    while True:
        # Strict UI obedience (user order 2026-11-23): re-read the
        # card fresh from data/cards.json BEFORE EACH POST and log
        # its effective settings, so the workflow log proves the UI
        # was checked for every single post. Settings are never
        # cached across posts within a run - a UI change mid-run
        # (new link, lower cap, fewer posts/run) takes effect on
        # the very next post.
        card = _refresh_card(card)
        log_card_settings(card)
        # Caps re-derived from the FRESH settings.
        remaining = card_caps_remaining(state, name, card)
        if remaining is not None and remaining <= 0:
            log("info", f"card '{name}': post cap reached - skipping")
            cap_hit = True
            break
        if made >= card_posts_per_run(card):
            break
        if due_slots and made >= len(due_slots):
            break
        link = (card.get("link") or "").strip()
        if link:
            target, use_promo = None, True
        else:
            target = _next_unposted_article(state, card)
            if target:
                use_promo = False
            else:
                # Rebuild #7.8 (root cause of the live "no article to
                # post yet" error): a bluesky_post card with no link
                # used to die here because there is no Blogger article
                # (the Blogger API is restricted, so no article is
                # ever recorded). Fall back to FRESH Political/War
                # news instead of erroring - the news picker supplies
                # the story, the photo and (when the card has no link)
                # the story URL, so the post still goes out.
                log("info", f"card '{name}': no new article - falling "
                            "back to fresh news")
                target, use_promo = None, True
        try:
            posted = _card_bluesky_post(card, state, target, promo=use_promo)
        except Exception as e:
            # Rebuild #7.8: a single post attempt that CRASHES must
            # not wipe out a post that already went out this run
            # (the exception used to propagate to execute_card, which
            # marked the WHOLE run failed and burned a retry even
            # though a post was published). Log it and stop this
            # run's posting loop; the return value below still
            # reports what actually happened (made > 0 = ok).
            # LAST_BSKY_SKIP is reset so a crash is never misreported
            # as a clean skip.
            log("error", f"card '{name}': post attempt failed: {e}")
            LAST_BSKY_SKIP = None
            break
        if posted:
            made += 1
            if not dry:
                record_card_post(state, name)
                _record_bsky_post_at(state, gap_key)
                if target and target.get("url"):
                    _mark_bsky_posted(state, name, target["url"])
        else:
            if LAST_BSKY_SKIP == "cooldown":
                cooldown_hit = True
            break
    if made and not dry and due_slots:
        mark_slots_used(state, name, due_slots[:made])
    if cooldown_hit and made == 0:
        # A cooldown skip is a clean no-op, NOT a failure (no retry).
        return 0, "cooldown"
    if cap_hit and made == 0:
        return 0, "post cap reached"
    if made == 0 and LAST_BSKY_SKIP == "no_photo":
        # Rebuild #7.3: say the REAL reason in the run line, so the
        # card's final log reads 'skipped: no photo, skipped' instead
        # of the vague 'post failed or skipped'.
        return 0, "no photo, skipped"
    if made == 0 and LAST_BSKY_SKIP == "no_news":
        # Rebuild #7.8: no fresh Political/War news with a verified
        # people's photo - a clean skip, NOT a failure, no retry.
        return 0, "no fresh news"
    return made, ("" if made else "post failed or skipped")


def _update_card_stats(state, card, ok, last_error, post_only=False):
    """Per-card stats: success/fail counters + last error + last run.
    DB cards (Flask) update the cards table; file cards (data/cards.json)
    are tracked in state.json (committed back to the repo).
    Rebuild #7: a post-only run (slot-triggered) does NOT reset the
    card's interval clock (file_card_runs), so the next interval run
    - and its reply checks - still happens on schedule. The
    success/fail counters still update."""
    name = card.get("name", "")
    if card.get("id"):
        conn = db_connect()
        try:
            if ok:
                conn.execute(
                    "UPDATE cards SET done_count=done_count+1, "
                    "success_count=success_count+1, last_run=?, next_run=?, "
                    "error='', updated_at=? WHERE id=?",
                    (now_iso(), next_run_for_card(card), now_iso(), card["id"]))
            else:
                conn.execute(
                    "UPDATE cards SET fail_count=fail_count+1, last_run=?, "
                    "next_run=?, error=?, updated_at=? WHERE id=?",
                    (now_iso(), next_run_for_card(card), last_error, now_iso(),
                     card["id"]))
            conn.commit()
        finally:
            conn.close()
        record_card_run_today(state, f"db:{card['id']}")
    else:
        stats = state.setdefault("file_card_stats", {})
        s = stats.setdefault(name, {"success": 0, "fail": 0, "last_ok": True,
                                    "last_error": "", "last_run": ""})
        if ok:
            s["success"] = int(s.get("success", 0)) + 1
            s["last_ok"] = True
            s["last_error"] = ""
        else:
            s["fail"] = int(s.get("fail", 0)) + 1
            s["last_ok"] = False
            s["last_error"] = last_error
        s["last_run"] = now_iso()
        if not post_only:
            state.setdefault("file_card_runs", {})[name] = now_iso()
        record_card_run_today(state, name)


def execute_card(card, state, test_mode=False, post_only=False):
    """Run one card once. Returns True on success.
    RUN MODEL (rebuild #5, kept):
    - The card RUNS every `interval` (run every X minutes) to check
      replies. Replies (own + others) happen on EVERY run.
    - PUBLISHING happens ONLY at a scheduled posting time: the
      auto-spread slots computed from posts-per-day + posting window
      (or fixed schedule_times, or every run when posts-per-day is
      unlimited). Off-schedule runs do replies only and publish nothing.
    - test_mode=True: a TEST run - forces dry-run for THIS card only
      (the article is written and the photo is verified, but nothing
      is published and no reply is sent). The posting gate is bypassed
      so the test actually exercises the article path. Test runs do
      not touch the success/fail counters.
    - post_only=True (rebuild #7): this run was triggered by a DUE
      POSTING SLOT, not by the card's run interval. It publishes the
      due post and does NOT check replies (replies stay on the
      interval rhythm, so they never spam). It also does NOT reset
      the interval clock, so the next interval run still happens on
      schedule.
    PAUSE is per-card: pausing one card pauses ONLY that card (the
    caller skips paused cards). The global paused=true in config is
    only the emergency "Pause All" switch.
    A Bluesky card with NO usable account does NOT run at all: it is
    logged and skipped, and it does NOT burn retries (a missing
    account is a setup problem, not a transient failure).
    Per-card settings honoured here: topic override + source, bold,
    labels, draft mode, length + tone (Blogger), and reply toggles +
    caps + lists + account (Bluesky). Success / failure counters and
    the last error are stored per card."""
    global FORCE_DRY
    ctype = card["type"]
    name = card.get("name", "")
    last_error = ""
    ok = False
    no_account = False
    # Rebuild #7.3: what this run ACTUALLY did - the final log line
    # must say so truthfully. 'ran (ok)' is only logged when a post
    # or a reply really happened; a skip is logged as a skip.
    made = 0           # posts actually published this run
    replies_sent = 0   # replies actually sent this run
    # Master safety switches: a card never runs when its workflow is OFF.
    if ctype == "blogger_post" and not workflow_enabled("blogger"):
        log("info", f"card '{name}': Blogger workflow is OFF - skipping")
        return False
    if ctype in ("bluesky_post", "bluesky_promo") and not workflow_enabled("bsky"):
        log("info", f"card '{name}': Bluesky workflow is OFF - skipping")
        return False
    if ctype == "bluesky_reply" and not workflow_enabled("replies"):
        log("info", f"card '{name}': Bluesky replies are OFF - skipping")
        return False
    prev_dry = FORCE_DRY
    if test_mode:
        FORCE_DRY = True
        log("warning", f"TEST RUN card '{name}': dry-run forced - the article "
                       "will be written and the photo verified, but NOTHING "
                       "will be published and NO reply will be sent")
    # Rebuild #7: log the card's EFFECTIVE settings first, so the
    # workflow log proves the worker uses exactly the UI values.
    log_card_settings(card)
    if post_only:
        log("info", f"card '{name}': post-only run (a posting slot is due; "
                    "replies stay on the interval rhythm)")
    # The posting gate: is it a scheduled posting time right now?
    # (Bypassed for test runs so the test exercises the article path.)
    post_due, due_slots = card_post_due(card, state)
    if test_mode:
        post_due = True
        due_slots = []

    def _do_replies(article):
        """Replies for this card (own + others) - runs on EVERY run.
        Returns how many replies were actually sent (rebuild #7.3)."""
        if post_only:
            # Rebuild #7: a slot-triggered run never checks replies.
            return 0
        reply_own, reply_others, rpr, lb = card_reply_settings(card)
        if not (reply_own or reply_others):
            return 0
        if not workflow_enabled("replies"):
            return 0
        res = run_bluesky_cycle(state, article=article,
                                reply_own=reply_own,
                                reply_others=reply_others,
                                replies_per_run=rpr,
                                lookback_days=lb, card_name=name,
                                account_handle=card.get("account_handle") or "",
                                replies_per_day=card_replies_per_day(card),
                                reply_never=card.get("reply_never") or "",
                                reply_only=card.get("reply_only") or "",
                                reply_skip_words=card.get("reply_skip_words") or "")
        if isinstance(res, (tuple, list)) and len(res) == 2:
            return int(res[0] or 0) + int(res[1] or 0)
        return 0

    try:
        # A Bluesky card with NO account cannot run at all.
        if ctype in ("bluesky_post", "bluesky_promo", "bluesky_reply") \
                and not list_accounts():
            no_account = True
            last_error = "no Bluesky account added - add one first (Bluesky tab)"
            log("error", f"card '{name}': {last_error} - skipping, nothing posted")
            ok = False
        elif ctype == "blogger_post":
            # Card-only: the card's own settings drive everything.
            # Blogger cards have no replies - they only publish, and
            # only at a scheduled posting time.
            if not post_due:
                log("info", f"card '{name}': not a posting time - "
                            "nothing published this run (replies: n/a)")
                last_error = "not a posting time"
                ok = True
            else:
                remaining = card_caps_remaining(state, name, card)
                if remaining is not None and remaining <= 0:
                    log("info", f"card '{name}': post cap reached - skipping")
                    last_error = "post cap reached"
                else:
                    max_posts = card_posts_per_run(card)
                    if due_slots:
                        max_posts = min(max_posts, len(due_slots))
                    if remaining is not None:
                        max_posts = min(max_posts, remaining)
                    articles = run_card_blogger(state, card, max_posts=max_posts)
                    made = len(articles or [])
                    ok = bool(articles)
                    if ok:
                        mark_slots_used(state, name, due_slots[:len(articles)])
                    else:
                        last_error = "no article published this run"
        elif ctype == "bluesky_post":
            # Rebuild #7.8: the "no article to post yet" error is GONE.
            # Root cause: this branch depended on a Blogger article
            # existing, and there is none (the Blogger API is
            # restricted, so no article is ever recorded) - so the
            # card failed every run and burned retries. Bluesky
            # posting must NOT depend on a Blogger article: a
            # link-less card falls back to fresh Political/War news
            # in _post_bsky_card. Replies may use the card's link
            # when there is no article (the article dependency
            # blocked replies too).
            link = (card.get("link") or "").strip()
            article = latest_article(state) or (
                {"url": link, "title": name, "image_url": ""}
                if link else None)
            replies_sent = _do_replies(article)
            if not post_due:
                log("info", f"card '{name}': not a posting time - "
                            "replies only, nothing posted this run")
                last_error = "not a posting time"
                ok = True
            else:
                made, err = _post_bsky_card(card, state, due_slots)
                # Rebuild #7.8: a CLEAN SKIP is a successful run, not
                # a failure - no retry, no Error badge. Retries are
                # for transient failures (network/API), not for
                # "nothing fresh to post". last_error still carries
                # the skip reason, so the run log reads "skipped: ...".
                ok = made > 0 or err in (
                    "cooldown", "too soon", "no photo, skipped",
                    "post cap reached", "no fresh news")
                if ok:
                    last_error = err or ""
                else:
                    last_error = err or "post failed or skipped"
        elif ctype == "bluesky_promo":
            # Rebuild #7.8: a promo card with NO link no longer errors
            # ("no link to promote") - it falls back to fresh
            # Political/War news in _post_bsky_card (the picker
            # supplies the story URL as the link), so the news MUST
            # publish. Replies may use the card's link when there is
            # no article (the article dependency blocked replies too).
            link = (card.get("link") or "").strip()
            replies_sent = _do_replies(
                latest_article(state) or
                ({"url": link, "title": name, "image_url": ""}
                 if link else None))
            if not post_due:
                log("info", f"card '{name}': not a posting time - "
                            "replies only, nothing promoted this run")
                last_error = "not a posting time"
                ok = True
            else:
                made, err = _post_bsky_card(card, state, due_slots)
                # Clean skip = successful run (rebuild #7.8, see above).
                ok = made > 0 or err in (
                    "cooldown", "too soon", "no photo, skipped",
                    "post cap reached", "no fresh news")
                if ok:
                    last_error = err or ""
                else:
                    last_error = err or "promo failed or skipped"
        elif ctype == "bluesky_reply":
            if post_only:
                # Rebuild #7: a slot-triggered run never checks replies.
                log("info", f"card '{name}': post-only run - replies stay "
                            "on the interval rhythm")
                last_error = "not a posting time"
                ok = True
            else:
                # Rebuild #7.8: replies may use the card's link when
                # there is no article; no article AND no link is a
                # CLEAN SKIP (not a failure, no retry).
                link = (card.get("link") or "").strip()
                article = latest_article(state) or (
                    {"url": link, "title": name, "image_url": ""}
                    if link else None)
                if not article:
                    last_error = "no article yet"
                    ok = True
                else:
                    replies_sent = _do_replies(article)
                    ok = True
        else:
            log("warning", f"card '{name}': unknown type {ctype}")
            last_error = f"unknown type {ctype}"
    except Exception as e:
        log("error", f"card '{name}' failed: {e}")
        last_error = str(e)[:200]
        ok = False
    finally:
        FORCE_DRY = prev_dry
    if test_mode:
        # A test run never touches counters or retry state - its result
        # lives only in the card's log.
        log("info", f"TEST RUN card '{name}' finished "
                    f"({'ok' if ok else 'no-op'}) - nothing was published")
        return ok
    # --- retry bookkeeping: a failed run may retry early (per card).
    # A missing account is NOT retried (setup problem, not transient).
    if ok:
        clear_card_retries(state, name)
    elif not no_account:
        record_card_retry(state, name, card)
    _update_card_stats(state, card, ok, last_error, post_only=post_only)
    # Rebuild #7.3: the run line must say what REALLY happened.
    # 'ok' is only logged when a post or a reply actually happened;
    # a skip is logged as a skip (never as ok), so a run that posted
    # nothing can never again look like a success. (The stats/retry
    # bookkeeping above still treats a clean skip - cooldown, too
    # soon, cap - as a no-op that burns no retry; only the LOG is
    # made truthful here.)
    if made > 0:
        outcome = f"ok - posted {made}"
    elif replies_sent > 0:
        outcome = (f"ok - {replies_sent} "
                   f"repl{'y' if replies_sent == 1 else 'ies'} sent")
    elif last_error:
        outcome = f"skipped: {last_error}"
    else:
        outcome = "no-op"
    log("info", f"card '{name}' ran ({outcome})")
    return ok


def _card_workflow(card):
    """Which GitHub Actions workflow runs this card: 'blogger' for
    blogger_post, 'bluesky' for bluesky_* cards, None for unknown types.
    Blogger and Bluesky run as TWO separate workflows so each can be
    enabled/disabled on its own (the Blogger API is restricted while
    Bluesky still works)."""
    t = card.get("type", "")
    if t == "blogger_post":
        return "blogger"
    if t in ("bluesky_post", "bluesky_promo", "bluesky_reply"):
        return "bluesky"
    return None


def run_cards_cycle(state, only=None):
    """CARD-ONLY: the worker runs ONLY the cards in data/cards.json.
    No card due (or no cards at all) = nothing is published.
    only: 'blogger' runs Blogger cards only, 'bluesky' runs Bluesky
    cards only, None runs all (backward compatible). Pausing one card
    pauses ONLY that card - every other card still runs."""
    # "Run now" from the dashboard: a card name in state["run_card_now"].
    # Runs that card at once (even if not due), then clears the flag.
    # "Test" from the dashboard: state["test_card_now"] runs the card
    # once in dry-run mode (article + photo verified, nothing published,
    # no reply sent).
    file_cards = load_file_cards()
    ran_any = False
    # Rebuild #7.8: a card run via run-now must NOT run a second time
    # in the same worker run - the normal cycle below would execute it
    # AGAIN if its interval/slot is also due (same card, same run =
    # the "same post twice" bug). ran_names tracks the cards already
    # executed this run; the cycle skips them.
    ran_names = set()
    run_now = state.get("run_card_now") or ""
    if run_now:
        state["run_card_now"] = ""
        for card in file_cards:
            if card.get("name") == run_now and \
                    (card.get("status") or "active") == "active":
                if only and _card_workflow(card) != only:
                    log("info", f"run-now: card '{run_now}' is a "
                                f"{_card_workflow(card)} card - this is the "
                                f"{only} workflow, skipping")
                    break
                log("info", f"run-now requested for card '{run_now}'")
                execute_card(card, state)
                ran_any = True
                ran_names.add(run_now)
                break
        else:
            log("warning", f"run-now: card '{run_now}' not found or paused")
    test_now = state.get("test_card_now") or ""
    if test_now:
        state["test_card_now"] = ""
        for card in file_cards:
            if card.get("name") == test_now and \
                    (card.get("status") or "active") == "active":
                if only and _card_workflow(card) != only:
                    log("info", f"test: card '{test_now}' is a "
                                f"{_card_workflow(card)} card - this is the "
                                f"{only} workflow, skipping")
                    break
                log("info", f"test requested for card '{test_now}'")
                execute_card(card, state, test_mode=True)
                ran_any = True
                break
        else:
            log("warning", f"test: card '{test_now}' not found or paused")
    if not file_cards:
        log("info", "no cards configured (data/cards.json is empty) - nothing to do")
        return
    # File-based cards (data/cards.json) - the GitHub-only control panel.
    # Rebuild #7 (prompt posting): a card runs when EITHER its run
    # interval is due (replies + maybe a post) OR a posting slot is due
    # (post-only run: publish the due post, no replies). A slot-due run
    # only applies to cards that HAVE slots (posts_per_day > 0) - an
    # unlimited card (0 = unlimited) has no slots, so its interval
    # stays the only gate and it can never post on every workflow run.
    # With the Bluesky workflow on a 10-minute cadence, a due post now
    # waits at most ~10 minutes instead of a whole run interval.
    for card in file_cards:
        if (card.get("status") or "active") != "active":
            continue
        if card.get("name") in ran_names:
            # Rebuild #7.8: already executed this run via run-now -
            # never run the same card twice in one worker run.
            continue
        if only and _card_workflow(card) != only:
            continue
        interval_due = file_card_due(card, state)
        post_only = False
        if not interval_due and card.get("type") in (
                "bluesky_post", "bluesky_promo", "blogger_post"):
            if card_posts_per_day(card) > 0:
                slot_due, _slots = card_post_due(card, state)
                if slot_due:
                    post_only = True
        if not interval_due and not post_only:
            continue
        execute_card(card, state, post_only=post_only)
        ran_any = True
    if not ran_any:
        log("info", "no card due - nothing published this run")


# ---------------------------------------------------------------- robustness systems
# BACKUP PLAN: every risky step has a fallback, and every failure is
# recorded as a structured issue so the dashboard shows it in one place.
_ISSUES = []


def record_issue(level, code, message):
    """Record a structured problem (dashboard Problems panel).
    level: 'error' | 'warning' | 'info'. Duplicates are ignored."""
    entry = {"level": level, "code": code, "message": str(message)[:300],
             "time": now_iso()}
    for item in _ISSUES:
        if item.get("code") == code and item.get("message") == entry["message"]:
            return
    _ISSUES.append(entry)
    if len(_ISSUES) > 50:
        del _ISSUES[:-50]
    log(level if level in ("error", "warning", "info") else "info",
        f"[{code}] {message}")


def get_issues(state=None):
    """All current issues: previous runs' (state) + this run's. Deduped."""
    prev = []
    if isinstance(state, dict):
        prev = [i for i in state.get("issues", []) if isinstance(i, dict)]
    seen = set()
    out = []
    for item in prev + _ISSUES:
        key = (item.get("code"), item.get("message"))
        if key in seen:
            continue
        seen.add(key)
        out.append(item)
    return out[-50:]


def retry_with_backoff(fn, attempts=3, base_delay=5, label="operation"):
    """Run fn(); on failure retry with exponential backoff.
    Returns fn()'s result, or None after all attempts fail."""
    delay = base_delay
    for attempt in range(1, attempts + 1):
        try:
            result = fn()
            if result is not None and result is not False:
                return result
            if attempt < attempts:
                log("warning", f"{label}: empty result, retry {attempt}/{attempts} in {delay}s")
        except Exception as e:
            if attempt < attempts:
                log("warning", f"{label}: failed ({e}), retry {attempt}/{attempts} in {delay}s")
            else:
                record_issue("error", "retry_exhausted",
                             f"{label} failed after {attempts} attempts: {e}")
                return None
        time.sleep(delay)
        delay *= 2
    return None


def is_dry_run():
    """Test mode: log what WOULD be posted, post nothing.
    FORCE_DRY is set by a per-card TEST run (execute_card test_mode) -
    only that card runs dry, the rest of the worker is unaffected."""
    if globals().get("FORCE_DRY"):
        return True
    return str(get_setting("dry_run", str(DEFAULT_DRY_RUN))).strip().lower() == "true"


# Set to True while one card is running as a TEST (dry) run.
FORCE_DRY = False


def workflow_enabled(name):
    """Is a workflow cycle switched on? name: blogger|bsky|replies|cards."""
    key = {"blogger": "blogger_enabled", "bsky": "bsky_enabled",
           "replies": "replies_enabled", "cards": "cards_enabled"}.get(name)
    if not key:
        return True
    default = {"blogger": DEFAULT_BLOGGER_ENABLED, "bsky": DEFAULT_BSKY_ENABLED,
               "replies": DEFAULT_REPLIES_ENABLED,
               "cards": DEFAULT_CARDS_ENABLED}[name]
    return str(get_setting(key, default)).strip().lower() != "false"


ACCOUNT_SETTINGS_PATH = os.path.join(DATA_DIR, "accounts.json")


def get_account_settings():
    """Per-account settings from data/accounts.json (public, no passwords):
    [{handle, enabled, posts_per_day}]. Missing file = all enabled."""
    if not os.path.exists(ACCOUNT_SETTINGS_PATH):
        return {}
    try:
        with open(ACCOUNT_SETTINGS_PATH, "r", encoding="utf-8") as f:
            data = json.load(f)
        if isinstance(data, list):
            return {a["handle"]: a for a in data
                    if isinstance(a, dict) and a.get("handle")}
        if isinstance(data, dict):
            return data
    except Exception as e:
        log("warning", f"accounts.json load failed: {e}")
    return {}


def account_enabled(handle):
    cfg = get_account_settings().get(handle)
    if not cfg:
        return True
    return cfg.get("enabled", True) is not False


def account_posts_limit(handle):
    cfg = get_account_settings().get(handle)
    if not cfg:
        return 0
    try:
        return int(cfg.get("posts_per_day") or 0)
    except Exception:
        return 0


def record_bsky_post(state, handle):
    """Count a Bluesky post for this account today (per-account limits)."""
    counts = state.setdefault("bsky_post_counts", {})
    today = counts.setdefault(today_str(), {})
    today[handle] = int(today.get(handle, 0)) + 1
    # Prune old dates (keep 3 days).
    for d in list(counts.keys()):
        try:
            if (now_utc().date() - datetime.strptime(d, "%Y-%m-%d").date()).days > 3:
                counts.pop(d, None)
        except Exception:
            counts.pop(d, None)


def posts_today_for_account(state, handle):
    counts = state.get("bsky_post_counts", {})
    return int(counts.get(today_str(), {}).get(handle, 0))


def validate_config():
    """Check config values; record a warning issue for each bad one."""
    warnings = []
    def _int(key, default=0):
        try:
            return int(get_setting(key, str(default)) or default)
        except Exception:
            warnings.append(f"{key} is not a number - using {default}")
            return default
    for key in ("max_consecutive_failures", "card_default_interval_hours",
                "card_default_interval_minutes", "card_default_posts_per_day",
                "card_default_jitter_minutes", "card_default_retry_after_minutes",
                "card_default_retry_max"):
        _int(key, 0)
    for w in warnings:
        record_issue("warning", "config", w)
    return warnings


def health_check(state=None):
    """Fast config-level health report (no quota used). Real failures are
    also surfaced by the issues tracker during the actual cycles."""
    health = {}
    gemini_keys = _parse_api_keys(os.environ.get("GEMINI_API_KEYS") or "")
    groq_keys = _parse_api_keys(os.environ.get("GROQ_API_KEYS") or "")
    health["gemini"] = {
        "ok": bool(gemini_keys),
        "detail": f"{len(gemini_keys)} key(s) configured" if gemini_keys
                  else "no GEMINI_API_KEYS secret"}
    health["groq"] = {
        "ok": bool(groq_keys),
        "detail": f"{len(groq_keys)} key(s) configured" if groq_keys
                  else "no GROQ_API_KEYS secret"}
    health["blogger"] = {
        "ok": bool(os.environ.get("BLOGGER_REFRESH_TOKEN")),
        "detail": "refresh token present" if os.environ.get("BLOGGER_REFRESH_TOKEN")
                  else "no BLOGGER_REFRESH_TOKEN secret"}
    accounts = list_accounts()
    health["bluesky"] = {
        "ok": bool(accounts),
        "detail": f"{len(accounts)} account(s)" if accounts
                  else "no BLUESKY_ACCOUNTS secret"}
    health["pexels"] = {
        "ok": bool(os.environ.get("PEXELS_API_KEY")),
        "detail": "key present" if os.environ.get("PEXELS_API_KEY")
                  else "no key (fallback: Pixabay / Openverse / Pollinations)"}
    if not health["gemini"]["ok"]:
        record_issue("error", "health",
                     "Gemini keys missing - articles cannot be written")
    if not health["blogger"]["ok"]:
        record_issue("error", "health",
                     "Blogger refresh token missing - cannot publish")
    if not health["bluesky"]["ok"]:
        record_issue("warning", "health",
                     "No Bluesky accounts - posts and replies are skipped")
    return health


def _run_worker_once(only=None):
    """One worker run (inner). only: 'blogger' runs Blogger cards
    only, 'bluesky' runs Bluesky cards only, None runs all cards.
    The global paused=true in config is the emergency "Pause All"
    switch - it stops everything. Day-to-day pausing is PER CARD
    (each card's own Pause button); a paused card is skipped while
    every other card runs normally. Returns the state dict. This
    function must NOT print 'worker run finished' itself - the
    run_worker wrapper guarantees the finish flush (even on crash).
    Rebuild #7.3."""
    init_db()
    state = load_state()
    state["runs"] = state.get("runs", 0) + 1
    state["last_run"] = now_iso()
    log("info", f"worker run #{state['runs']} started"
                + (f" (--only {only})" if only else ""))
    # --- startup checks: config validation + health (no quota used) ---
    validate_config()
    health_check(state)
    # Rebuild #7.3: AI health check FIRST, before the card cycle -
    # the log must show why Gemini/Groq fail even when the photo
    # step fails and AI is never attempted for a caption.
    _ai_health_check()
    if is_dry_run():
        log("warning", "DRY RUN mode - nothing will be posted (dry_run=true)")
    # --- circuit breaker: stop after N fully-failed runs in a row ---
    max_fail = 5
    try:
        max_fail = int(get_setting("max_consecutive_failures",
                                   str(DEFAULT_MAX_CONSECUTIVE_FAILURES)) or 5)
    except Exception:
        max_fail = 5
    breaker_open = int(state.get("consecutive_failures", 0) or 0) >= max_fail
    if breaker_open:
        record_issue("error", "circuit_breaker",
                     f"{max_fail} runs failed in a row - automation stopped. "
                     "Fix the problem, then the next run resumes automatically "
                     "after a successful cycle.")
        log("error", f"circuit breaker OPEN ({max_fail} failed runs) - skipping cycles")
    paused = str(get_setting("paused", "false")).strip().lower() == "true"
    if paused:
        log("info", "automation is PAUSED (paused=true in config, emergency "
                    "Pause All) - skipping all cycles")
    elif breaker_open:
        pass
    else:
        failures = 0
        # CARD-ONLY: the worker runs nothing but the cards in
        # data/cards.json. There is no global Blogger or Bluesky cycle.
        if workflow_enabled("cards"):
            try:
                run_cards_cycle(state, only=only)
            except Exception as e:
                record_issue("error", "cards_cycle", f"cards cycle failed: {e}")
                failures += 1
        else:
            log("info", "cards workflow is OFF - skipping")
        if failures >= 3:
            state["consecutive_failures"] = int(state.get("consecutive_failures", 0) or 0) + 1
        else:
            state["consecutive_failures"] = 0
    # --- persist this run's issues so the dashboard shows them.
    # Issues are per-run: a fixed problem disappears on the next run.
    state["issues"] = list(_ISSUES)
    return state


def run_worker(only=None):
    """One worker run (wrapper). only: 'blogger' runs Blogger cards
    only, 'bluesky' runs Bluesky cards only, None runs all cards.
    Rebuild #7.3 - NEVER ends silently: state.json + logs.json +
    dashboard.json are flushed and 'worker run finished' is printed
    on EVERY run - posted, skipped, or crashed. A crash is printed
    as a traceback and logged, never swallowed."""
    global WORKER_RUNNING
    if WORKER_RUNNING:
        log("info", "worker already running - skipping")
        return
    WORKER_RUNNING = True
    state = None
    try:
        state = _run_worker_once(only)
    except Exception:
        import traceback
        print("worker run CRASHED:\n" + traceback.format_exc(),
              flush=True)
        try:
            log("error", "worker run crashed - state and logs are "
                         "still being saved (see traceback above)")
        except Exception:
            pass
    finally:
        # Never end silently: persist state + logs and print the
        # finish line even when the run crashed. (On the normal path
        # this just re-flushes what the inner run already saved -
        # append_logs_json is idempotent, so nothing duplicates.)
        try:
            if state is None:
                state = load_state()
            state["issues"] = list(_ISSUES)
            save_state(state)
        except Exception as e:
            print(f"worker finish: state save failed: {e}", flush=True)
        try:
            append_logs_json()
        except Exception as e:
            print(f"worker finish: logs.json write failed: {e}",
                  flush=True)
        try:
            write_dashboard_json(state)
        except Exception as e:
            print(f"worker finish: dashboard.json write failed: {e}",
                  flush=True)
        WORKER_RUNNING = False
        try:
            log("info", "worker run finished")
        except Exception:
            print("worker run finished", flush=True)
        try:
            append_logs_json()
        except Exception:
            pass


# ---------------------------------------------------------------- web routes
def require_login():
    if not session.get("authed"):
        return jsonify({"error": "login required"}), 401
    return None


@app.route("/")
def index():
    return send_from_directory(BASE_DIR, "index.html")


@app.route("/images/<path:filename>")
def serve_image(filename):
    return send_from_directory(IMAGES_DIR, filename)


@app.route("/health")
def health():
    return jsonify({"status": "ok", "time": now_iso()})


@app.route("/api/login", methods=["POST"])
def api_login():
    data = request.get_json(silent=True) or {}
    if str(data.get("password", "")) == ADMIN_PASSWORD:
        session["authed"] = True
        return jsonify({"ok": True})
    return jsonify({"error": "wrong password"}), 401


@app.route("/api/logout", methods=["POST"])
def api_logout():
    session.clear()
    return jsonify({"ok": True})


@app.route("/api/me")
def api_me():
    return jsonify({"authenticated": bool(session.get("authed"))})


@app.route("/api/status")
def api_status():
    err = require_login()
    if err:
        return err
    conn = db_connect()
    try:
        cards = [dict(r) for r in conn.execute(
            "SELECT * FROM cards ORDER BY id DESC").fetchall()]
        accounts = [dict(r) for r in conn.execute(
            "SELECT id, handle, display_name, active, created_at FROM accounts "
            "ORDER BY id").fetchall()]
        logs = [dict(r) for r in conn.execute(
            "SELECT level, message, created_at FROM logs ORDER BY id DESC LIMIT 50"
            ).fetchall()]
        total_posts = conn.execute("SELECT COUNT(*) c FROM posts").fetchone()["c"]
        total_replies = conn.execute("SELECT COUNT(*) c FROM replies").fetchone()["c"]
    finally:
        conn.close()
    state = load_state()
    settings = {k: get_setting(k, "") for k in
                ("blogger_bold_format", "card_default_interval_hours",
                 "card_default_interval_minutes", "card_default_posts_per_day")}
    return jsonify({
        "stats": {"blogger_today": blogger_posts_today(),
                  "replies_today": replies_today(),
                  "total_posts": total_posts, "total_replies": total_replies,
                  "accounts": len(list_accounts()),
                  "last_run": state.get("last_run", ""),
                  "runs": state.get("runs", 0)},
        "cards": cards, "accounts": accounts, "logs": logs,
        "settings": settings,
    })


@app.route("/api/trending")
def api_trending():
    err = require_login()
    if err:
        return err
    return jsonify({"topics": get_bluesky_trending(limit=10)})


@app.route("/api/cards", methods=["GET", "POST"])
def api_cards():
    err = require_login()
    if err:
        return err
    conn = db_connect()
    try:
        if request.method == "GET":
            rows = conn.execute("SELECT * FROM cards ORDER BY id DESC").fetchall()
            return jsonify({"cards": [dict(r) for r in rows]})
        data = request.get_json(silent=True) or {}
        name = (data.get("name") or "Card").strip()
        ctype = data.get("type") or "bluesky_post"
        if ctype not in ("bluesky_post", "bluesky_reply", "blogger_post", "bluesky_promo"):
            return jsonify({"error": "bad type"}), 400
        times = data.get("schedule_times") or []
        if isinstance(times, str):
            times = [t.strip() for t in times.split(",") if t.strip()]

        def _b(v, default=True):
            if v is None:
                return 1 if default else 0
            if isinstance(v, bool):
                return 1 if v else 0
            return 0 if str(v).strip().lower() in ("false", "0", "no", "off", "") else 1

        cur = conn.execute(
            "INSERT INTO cards(name, type, link, account_handle, count, "
            "interval_minutes, interval_hours, posts_per_day, schedule_times, "
            "text, status, source, topic_override, reply_own, reply_others, "
            "replies_per_run, lookback_days, bold_format, notes, color, window_start, "
            "window_end, spread_mode, length_mode, tone, draft_only, "
            "days_of_week, jitter_minutes, labels, max_posts_per_week, "
            "max_posts_per_month, retry_after_minutes, retry_max, "
            "replies_per_day, reply_never, reply_only, reply_skip_words, "
            "bsky_image_ratio, created_at, updated_at) "
            "VALUES(?, ?, ?, ?, ?, ?, ?, ?, ?, ?, 'active', ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?)",
            (name, ctype, data.get("link", ""), data.get("account_handle", ""),
             int(data.get("count") or 1), int(data.get("interval_minutes") or 30),
             int(data.get("interval_hours") or 0),
             int(data.get("posts_per_day") or 0),
             json.dumps(times), data.get("text", ""),
             data.get("source") or "trending", data.get("topic_override", ""),
             _b(data.get("reply_own"), ctype == "bluesky_reply"),
             _b(data.get("reply_others"), ctype == "bluesky_reply"),
             int(data.get("replies_per_run") or 0),
             max(1, min(30, int(data.get("lookback_days") or 7))),
             _b(data.get("bold_format"), True),
             data.get("notes", ""), data.get("color", ""),
             data.get("window_start", ""), data.get("window_end", ""),
             data.get("spread_mode") or "even",
             data.get("length_mode") or "auto",
             data.get("tone") or "dramatic",
             _b(data.get("draft_only"), False),
             json.dumps(data.get("days_of_week") or [0, 1, 2, 3, 4, 5, 6]),
             int(data.get("jitter_minutes") or 10),
             data.get("labels") if isinstance(data.get("labels"), str)
             else ", ".join(str(x) for x in (data.get("labels") or [])),
             int(data.get("max_posts_per_week") or 0),
             int(data.get("max_posts_per_month") or 0),
             int(data.get("retry_after_minutes") or 30),
             int(data.get("retry_max") or 2),
             int(data.get("replies_per_day") or 0),
             data.get("reply_never", ""), data.get("reply_only", ""),
             data.get("reply_skip_words", ""),
             data.get("bsky_image_ratio") or "16:9",
             now_iso(), now_iso()))
        conn.commit()
        return jsonify({"ok": True, "id": cur.lastrowid})
    finally:
        conn.close()


@app.route("/api/cards/<int:cid>", methods=["PUT", "DELETE"])
def api_card_one(cid):
    err = require_login()
    if err:
        return err
    conn = db_connect()
    try:
        if request.method == "DELETE":
            conn.execute("DELETE FROM cards WHERE id=?", (cid,))
            conn.commit()
            return jsonify({"ok": True})
        data = request.get_json(silent=True) or {}
        fields = {}
        for key in ("name", "type", "link", "account_handle", "text", "status",
                    "source", "topic_override", "notes", "color",
                    "window_start", "window_end",
                    "spread_mode", "length_mode", "tone",
                    "reply_never", "reply_only", "reply_skip_words",
                    "bsky_image_ratio"):
            if key in data:
                fields[key] = data[key]
        if "labels" in data:
            v = data["labels"]
            fields["labels"] = v if isinstance(v, str) else \
                ", ".join(str(x) for x in (v or []))
        if "days_of_week" in data:
            days = []
            raw = data["days_of_week"]
            if isinstance(raw, (list, tuple)):
                items = raw
            else:
                items = str(raw).split(",")
            for x in items:
                try:
                    d = int(x)
                    if 0 <= d <= 6 and d not in days:
                        days.append(d)
                except Exception:
                    pass
            fields["days_of_week"] = json.dumps(
                sorted(days) if days else [0, 1, 2, 3, 4, 5, 6])
        for key in ("count", "interval_minutes", "interval_hours",
                    "posts_per_day", "posts_per_run", "replies_per_run",
                    "lookback_days", "jitter_minutes", "max_posts_per_week",
                    "max_posts_per_month", "retry_after_minutes",
                    "retry_max", "replies_per_day"):
            if key in data:
                fields[key] = int(data[key] or 0)
        for key in ("reply_own", "reply_others", "bold_format", "draft_only"):
            if key in data:
                v = data[key]
                if isinstance(v, bool):
                    fields[key] = 1 if v else 0
                else:
                    fields[key] = 0 if str(v).strip().lower() in (
                        "false", "0", "no", "off", "") else 1
        if "schedule_times" in data:
            times = data["schedule_times"]
            if isinstance(times, str):
                times = [t.strip() for t in times.split(",") if t.strip()]
            fields["schedule_times"] = json.dumps(times)
        if not fields:
            return jsonify({"error": "nothing to update"}), 400
        fields["updated_at"] = now_iso()
        sets = ", ".join(f"{k}=?" for k in fields)
        conn.execute(f"UPDATE cards SET {sets} WHERE id=?",
                     (*fields.values(), cid))
        conn.commit()
        return jsonify({"ok": True})
    finally:
        conn.close()


@app.route("/api/cards/<int:cid>/run", methods=["POST"])
def api_card_run(cid):
    err = require_login()
    if err:
        return err
    conn = db_connect()
    try:
        row = conn.execute("SELECT * FROM cards WHERE id=?", (cid,)).fetchone()
        card = dict(row) if row else None
    finally:
        conn.close()
    if not card:
        return jsonify({"error": "card not found"}), 404
    if (card.get("status") or "active") != "active":
        return jsonify({"ok": False, "error": "card is paused"}), 409
    state = load_state()
    ok = execute_card(card, state)
    save_state(state)
    return jsonify({"ok": ok})


@app.route("/api/cards/<int:cid>/test", methods=["POST"])
def api_card_test(cid):
    """TEST a card once (dry-run): the article is written and the photo
    is verified, but NOTHING is published and NO reply is sent. The
    result shows in the card's log. Counters are not touched."""
    err = require_login()
    if err:
        return err
    conn = db_connect()
    try:
        row = conn.execute("SELECT * FROM cards WHERE id=?", (cid,)).fetchone()
        card = dict(row) if row else None
    finally:
        conn.close()
    if not card:
        return jsonify({"error": "card not found"}), 404
    if (card.get("status") or "active") != "active":
        return jsonify({"ok": False, "error": "card is paused"}), 409
    state = load_state()
    ok = execute_card(card, state, test_mode=True)
    save_state(state)
    return jsonify({"ok": ok, "test": True,
                    "message": "test run done - check the card log; "
                               "nothing was published"})


@app.route("/api/cards/<int:cid>/pause", methods=["POST"])
def api_card_pause(cid):
    err = require_login()
    if err:
        return err
    conn = db_connect()
    try:
        conn.execute("UPDATE cards SET status='paused', updated_at=? WHERE id=?",
                     (now_iso(), cid))
        conn.commit()
    finally:
        conn.close()
    return jsonify({"ok": True})


@app.route("/api/cards/<int:cid>/resume", methods=["POST"])
def api_card_resume(cid):
    err = require_login()
    if err:
        return err
    conn = db_connect()
    try:
        conn.execute("UPDATE cards SET status='active', updated_at=? WHERE id=?",
                     (now_iso(), cid))
        conn.commit()
    finally:
        conn.close()
    return jsonify({"ok": True})


@app.route("/api/cards/bulk", methods=["POST"])
def api_cards_bulk():
    """Bulk pause / resume / delete for DB cards.
    Body: {"action": "pause"|"resume"|"delete", "ids": [1, 2]}"""
    err = require_login()
    if err:
        return err
    data = request.get_json(silent=True) or {}
    action = data.get("action")
    ids = [int(i) for i in (data.get("ids") or []) if str(i).isdigit()]
    if action not in ("pause", "resume", "delete") or not ids:
        return jsonify({"error": "action + ids required"}), 400
    conn = db_connect()
    try:
        marks = ",".join("?" for _ in ids)
        if action == "delete":
            conn.execute(f"DELETE FROM cards WHERE id IN ({marks})", ids)
        else:
            status = "paused" if action == "pause" else "active"
            conn.execute(f"UPDATE cards SET status=?, updated_at=? WHERE id IN ({marks})",
                         (status, now_iso(), *ids))
        conn.commit()
    finally:
        conn.close()
    return jsonify({"ok": True, "count": len(ids)})


@app.route("/api/cards/<int:cid>/logs")
def api_card_logs(cid):
    """Per-card log viewer: log lines that mention this card's name."""
    err = require_login()
    if err:
        return err
    conn = db_connect()
    try:
        row = conn.execute("SELECT name FROM cards WHERE id=?", (cid,)).fetchone()
        if not row:
            return jsonify({"error": "card not found"}), 404
        name = row["name"]
        rows = conn.execute(
            "SELECT level, message, created_at FROM logs "
            "WHERE message LIKE ? ORDER BY id DESC LIMIT 50",
            (f"%{name}%",)).fetchall()
        return jsonify({"card": name, "logs": [dict(r) for r in rows]})
    finally:
        conn.close()


@app.route("/api/pause-all", methods=["POST"])
def api_pause_all():
    """Emergency "Pause All": pauses EVERY card (DB cards AND the file
    cards in data/cards.json, which is what the worker actually runs).
    Day-to-day pausing is PER CARD - this switch is only the emergency
    stop, and it must NOT be the default state."""
    err = require_login()
    if err:
        return err
    conn = db_connect()
    try:
        conn.execute("UPDATE cards SET status='paused', updated_at=?", (now_iso(),))
        conn.commit()
    finally:
        conn.close()
    try:
        file_cards = load_file_cards()
        for c in file_cards:
            c["status"] = "paused"
        with open(CARDS_PATH, "w", encoding="utf-8") as f:
            json.dump(file_cards, f, ensure_ascii=False, indent=2)
    except Exception as e:
        log("warning", f"pause-all (file cards) failed: {e}")
    log("info", "pause-all: every card paused (emergency switch)")
    return jsonify({"ok": True})


@app.route("/api/resume-all", methods=["POST"])
def api_resume_all():
    """Resume every card after an emergency Pause All."""
    err = require_login()
    if err:
        return err
    conn = db_connect()
    try:
        conn.execute("UPDATE cards SET status='active', updated_at=?", (now_iso(),))
        conn.commit()
    finally:
        conn.close()
    try:
        file_cards = load_file_cards()
        for c in file_cards:
            c["status"] = "active"
        with open(CARDS_PATH, "w", encoding="utf-8") as f:
            json.dump(file_cards, f, ensure_ascii=False, indent=2)
    except Exception as e:
        log("warning", f"resume-all (file cards) failed: {e}")
    log("info", "resume-all: every card resumed")
    return jsonify({"ok": True})


@app.route("/api/accounts", methods=["GET", "POST"])
def api_accounts():
    err = require_login()
    if err:
        return err
    conn = db_connect()
    try:
        if request.method == "GET":
            rows = conn.execute(
                "SELECT id, handle, display_name, active, created_at FROM accounts "
                "ORDER BY id").fetchall()
            return jsonify({"accounts": [dict(r) for r in rows]})
        data = request.get_json(silent=True) or {}
        handle = (data.get("handle") or "").strip()
        pw = (data.get("app_password") or "").strip()
        if not handle or not pw:
            return jsonify({"error": "handle and app password required"}), 400
        cur = conn.execute(
            "INSERT INTO accounts(handle, app_password, display_name, created_at) "
            "VALUES(?, ?, ?, ?) ON CONFLICT(handle) DO UPDATE SET "
            "app_password=excluded.app_password, display_name=excluded.display_name",
            (handle, pw, data.get("display_name", ""), now_iso()))
        conn.commit()
        return jsonify({"ok": True, "id": cur.lastrowid})
    finally:
        conn.close()


@app.route("/api/accounts/<int:aid>", methods=["DELETE"])
def api_account_delete(aid):
    err = require_login()
    if err:
        return err
    conn = db_connect()
    try:
        conn.execute("DELETE FROM accounts WHERE id=?", (aid,))
        conn.commit()
    finally:
        conn.close()
    return jsonify({"ok": True})


@app.route("/api/settings", methods=["GET", "POST"])
def api_settings():
    err = require_login()
    if err:
        return err
    # Card-only: the only remaining global settings are the safety
    # switches, dry-run, circuit breaker and card defaults.
    keys = ("dry_run", "max_consecutive_failures",
            "blogger_enabled", "bsky_enabled", "replies_enabled",
            "cards_enabled", "blogger_bold_format",
            "card_default_interval_hours", "card_default_interval_minutes",
            "card_default_posts_per_day", "card_default_reply_own",
            "card_default_reply_others", "card_default_lookback_days",
            "card_default_spread_mode", "card_default_length_mode",
            "card_default_tone", "card_default_jitter_minutes",
            "card_default_bsky_image_ratio",
            "card_default_retry_after_minutes", "card_default_retry_max")
    if request.method == "GET":
        return jsonify({k: get_setting(k, "") for k in keys})
    data = request.get_json(silent=True) or {}
    for k in keys:
        if k in data:
            set_setting(k, data[k])
    return jsonify({"ok": True})


@app.route("/api/run-worker", methods=["POST"])
def api_run_worker():
    err = require_login()
    if err:
        return err
    if WORKER_RUNNING:
        return jsonify({"ok": False, "error": "worker already running"})
    t = threading.Thread(target=run_worker, daemon=True)
    t.start()
    return jsonify({"ok": True, "message": "worker started"})


@app.route("/api/export")
def api_export():
    err = require_login()
    if err:
        return err
    conn = db_connect()
    try:
        cards = [dict(r) for r in conn.execute("SELECT * FROM cards").fetchall()]
        accounts = [dict(r) for r in conn.execute(
            "SELECT handle, display_name FROM accounts").fetchall()]
    finally:
        conn.close()
    settings = {k: get_setting(k, "") for k in
                ("dry_run", "max_consecutive_failures",
                 "blogger_enabled", "bsky_enabled", "replies_enabled",
                 "cards_enabled", "blogger_bold_format",
                 "card_default_interval_hours", "card_default_interval_minutes",
                 "card_default_posts_per_day", "card_default_reply_own",
                 "card_default_reply_others")}
    return jsonify({"cards": cards, "accounts": accounts, "settings": settings,
                    "exported_at": now_iso()})


# ---------------------------------------------------------------- entrypoint
init_db()

if __name__ == "__main__":
    if "--worker" in sys.argv:
        only = None
        if "--only" in sys.argv:
            idx = sys.argv.index("--only")
            if idx + 1 < len(sys.argv) and sys.argv[idx + 1] in ("blogger", "bluesky"):
                only = sys.argv[idx + 1]
        # Rebuild #7.3: last defense - a worker crash must be
        # visible (traceback + non-zero exit), never a silent
        # success. (run_worker itself already flushes state/logs
        # and prints 'worker run finished' in its finally block.)
        try:
            run_worker(only=only)
        except Exception:
            import traceback
            print("worker FAILED:\n" + traceback.format_exc(), flush=True)
            sys.exit(1)
    else:
        port = int(os.environ.get("PORT", "5000"))
        print(f"Automation Website running on http://0.0.0.0:{port}", flush=True)
        app.run(host="0.0.0.0", port=port)
