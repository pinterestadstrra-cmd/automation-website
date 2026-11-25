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
  REDDIT_ACCOUNTS        JSON list [{"username": "...", "password": "...",
                         "client_id": "...", "client_secret": "..."}]
                         (or single-account env vars REDDIT_CLIENT_ID /
                         REDDIT_CLIENT_SECRET / REDDIT_USERNAME /
                         REDDIT_PASSWORD)
  TUMBLR_ACCOUNTS        JSON list [{"blog": "...", "client_id": "...",
                         "client_secret": "...", "access_token": "...",
                         "refresh_token": "..."}] (OAuth2, scopes basic
                         write offline_access; free, no review -
                         register the app at tumblr.com/oauth/apps)
                         (or single-account env vars TUMBLR_BLOG /
                         TUMBLR_CLIENT_ID / TUMBLR_CLIENT_SECRET /
                         TUMBLR_ACCESS_TOKEN / TUMBLR_REFRESH_TOKEN)
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
from requests.auth import HTTPBasicAuth
from flask import Flask, request, jsonify, session, send_from_directory

# Nostr (platform 5 of 8): pynostr signs kind-1 text-note events
# (BIP-340 Schnorr over secp256k1, via coincurve) and broadcasts
# them to relays over wss. Guarded import: if the library is
# missing, Nostr functions log a plain warning and skip instead of
# crashing the worker (the worker installs it from requirements.txt).
try:
    from pynostr.event import Event as _NostrEvent
    from pynostr.key import PrivateKey as _NostrPrivateKey
    from pynostr.relay_manager import RelayManager as _NostrRelayManager
    _PYNOSTR_AVAILABLE = True
except Exception:
    _NostrEvent = None
    _NostrPrivateKey = None
    _NostrRelayManager = None
    _PYNOSTR_AVAILABLE = False

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

# Reddit accounts can come from the env secret (GitHub Actions) or from
# single-account env vars. Same sealed-box pattern as BLUESKY_ACCOUNTS:
# the dashboard encrypts the list into the REDDIT_ACCOUNTS secret.
def _load_env_reddit_accounts():
    raw = (os.environ.get("REDDIT_ACCOUNTS", "") or "").strip()
    accounts = []
    if raw:
        try:
            data = json.loads(raw)
            if isinstance(data, list):
                accounts = [a for a in data
                            if isinstance(a, dict) and a.get("username")
                            and a.get("password") and a.get("client_id")
                            and a.get("client_secret")]
        except Exception:
            accounts = []
    if not accounts:
        # Single account set directly as secrets (script-type app).
        cid = (os.environ.get("REDDIT_CLIENT_ID", "") or "").strip()
        csec = (os.environ.get("REDDIT_CLIENT_SECRET", "") or "").strip()
        user = (os.environ.get("REDDIT_USERNAME", "") or "").strip()
        pw = (os.environ.get("REDDIT_PASSWORD", "") or "").strip()
        if cid and csec and user and pw:
            accounts = [{"username": user, "password": pw,
                         "client_id": cid, "client_secret": csec}]
    return accounts

ENV_REDDIT_ACCOUNTS = _load_env_reddit_accounts()

# Tumblr accounts can come from the env secret (GitHub Actions) or
# from single-account env vars. Same sealed-box pattern as
# BLUESKY_ACCOUNTS / REDDIT_ACCOUNTS: the dashboard encrypts the
# list into the TUMBLR_ACCOUNTS secret. Auth is OAuth2 (scopes basic
# write offline_access): the access token lasts 42 minutes, the
# refresh token 42 days. The worker refreshes ONLY on a 401 (never
# speculatively) and keeps the refreshed tokens in memory for the
# rest of the run - a rotated refresh token is NEVER written to a
# repo file (state.json is committed back, so it must never hold a
# secret); see _tumblr_refresh.
def _load_env_tumblr_accounts():
    raw = (os.environ.get("TUMBLR_ACCOUNTS", "") or "").strip()
    accounts = []
    if raw:
        try:
            data = json.loads(raw)
            if isinstance(data, list):
                accounts = [a for a in data
                            if isinstance(a, dict) and a.get("blog")
                            and a.get("client_id")
                            and a.get("client_secret")
                            and a.get("access_token")
                            and a.get("refresh_token")]
        except Exception:
            accounts = []
    if not accounts:
        # Single account set directly as secrets.
        blog = (os.environ.get("TUMBLR_BLOG", "") or "").strip()
        cid = (os.environ.get("TUMBLR_CLIENT_ID", "") or "").strip()
        csec = (os.environ.get("TUMBLR_CLIENT_SECRET", "") or "").strip()
        atok = (os.environ.get("TUMBLR_ACCESS_TOKEN", "") or "").strip()
        rtok = (os.environ.get("TUMBLR_REFRESH_TOKEN", "") or "").strip()
        if blog and cid and csec and atok and rtok:
            accounts = [{"blog": blog, "client_id": cid,
                         "client_secret": csec, "access_token": atok,
                         "refresh_token": rtok}]
    return accounts

ENV_TUMBLR_ACCOUNTS = _load_env_tumblr_accounts()

# Threads accounts can come from the env secret (GitHub Actions) or
# from single-account env vars. Same sealed-box pattern as
# BLUESKY_ACCOUNTS / REDDIT_ACCOUNTS / TUMBLR_ACCOUNTS: the dashboard
# encrypts the list into the THREADS_ACCOUNTS secret. Auth is OAuth2
# (scopes threads_basic + threads_content_publish): the short-lived
# token lasts 1 hour, exchanged for a long-lived token (60 days).
# The worker refreshes a long-lived token ONLY when it is at least
# 24 hours old (and its age is known - token_obtained_at, recorded
# by the dashboard authorize helper) or on a 401, and keeps the
# refreshed token in memory for the rest of the run - a rotated
# token is NEVER written to a repo file (state.json is committed
# back, so it must never hold a secret); see _threads_refresh.
def _load_env_threads_accounts():
    raw = (os.environ.get("THREADS_ACCOUNTS", "") or "").strip()
    accounts = []
    if raw:
        try:
            data = json.loads(raw)
            if isinstance(data, list):
                accounts = [a for a in data
                            if isinstance(a, dict) and a.get("user_id")
                            and a.get("app_id")
                            and a.get("app_secret")
                            and a.get("access_token")]
        except Exception:
            accounts = []
    if not accounts:
        # Single account set directly as secrets.
        uid = (os.environ.get("THREADS_USER_ID", "") or "").strip()
        aid = (os.environ.get("THREADS_APP_ID", "") or "").strip()
        asec = (os.environ.get("THREADS_APP_SECRET", "") or "").strip()
        atok = (os.environ.get("THREADS_ACCESS_TOKEN", "") or "").strip()
        if uid and aid and asec and atok:
            accounts = [{"user_id": uid, "app_id": aid,
                         "app_secret": asec, "access_token": atok}]
    return accounts

ENV_THREADS_ACCOUNTS = _load_env_threads_accounts()

# Mastodon accounts can come from the env secret (GitHub Actions) or
# from single-account env vars. Same sealed-box pattern as
# BLUESKY_ACCOUNTS / REDDIT_ACCOUNTS / TUMBLR_ACCOUNTS /
# THREADS_ACCOUNTS: the dashboard encrypts the list into the
# MASTODON_ACCOUNTS secret. Auth is a plain access token from the
# instance web UI (Preferences -> Development -> New application,
# scopes write:statuses + write:media) - the token does NOT expire,
# so there is no refresh flow and a rotated token is never written
# to a repo file (state.json is committed back, so it must never
# hold a secret). "instance" is the instance host, e.g.
# mastodon.social (a full URL is accepted too and normalised).
def _load_env_mastodon_accounts():
    raw = (os.environ.get("MASTODON_ACCOUNTS", "") or "").strip()
    accounts = []
    if raw:
        try:
            data = json.loads(raw)
            if isinstance(data, list):
                accounts = [a for a in data
                            if isinstance(a, dict) and a.get("instance")
                            and a.get("access_token")]
        except Exception:
            accounts = []
    if not accounts:
        # Single account set directly as secrets.
        inst = (os.environ.get("MASTODON_INSTANCE", "") or "").strip()
        atok = (os.environ.get("MASTODON_ACCESS_TOKEN", "") or "").strip()
        user = (os.environ.get("MASTODON_USERNAME", "") or "").strip()
        if inst and atok:
            entry = {"instance": inst, "access_token": atok}
            if user:
                entry["username"] = user
            accounts = [entry]
    return accounts

ENV_MASTODON_ACCOUNTS = _load_env_mastodon_accounts()

# Telegram is a single bot token, not an account list: the user
# creates a bot with @BotFather (/newbot) and pastes the token into
# the TELEGRAM_BOT_TOKEN secret (the dashboard encrypts it with the
# same sealed-box pattern as the other platforms). The token never
# expires and there is no OAuth or refresh - a 401 means the stored
# token is wrong or revoked. The bot is added as a channel admin
# (Post Messages permission) and each card picks its own destination
# channel (card field "channel", e.g. @primotodaynews). Auth is just
# the token in the request URL: POST
# https://api.telegram.org/bot<token>/sendMessage (chat_id, text
# 1-4096 chars) and /sendPhoto (multipart photo upload, caption
# 0-1024 chars). Free, no review, no approval queue (verified
# 2026-11-25 against core.telegram.org/bots/api, Bot API 10.5).
def _load_env_telegram_bot_token():
    return (os.environ.get("TELEGRAM_BOT_TOKEN", "") or "").strip()

ENV_TELEGRAM_BOT_TOKEN = _load_env_telegram_bot_token()

# Nostr accounts can come from the env secret (GitHub Actions) or
# from single-account env vars. Same sealed-box pattern as
# BLUESKY_ACCOUNTS / REDDIT_ACCOUNTS / TUMBLR_ACCOUNTS /
# THREADS_ACCOUNTS / MASTODON_ACCOUNTS: the dashboard encrypts the
# list into the NOSTR_ACCOUNTS secret. There is NO account, NO
# registration, NO approval and NO review on Nostr: the nsec private
# key IS the account (secp256k1 keypair, NIP-01). Whoever holds the
# nsec controls the identity, so it is stored ONLY in the env secret
# - never logged, never written to a repo file, never in state.json.
# The dashboard also saves the matching npub (public key) alongside
# each nsec so it can label the key without doing crypto in the
# browser; the WORKER never trusts the stored npub - it derives the
# npub from the nsec and uses the derived value as the account key.
def _load_env_nostr_accounts():
    raw = (os.environ.get("NOSTR_ACCOUNTS", "") or "").strip()
    accounts = []
    if raw:
        try:
            data = json.loads(raw)
            if isinstance(data, list):
                accounts = [a for a in data
                            if isinstance(a, dict) and a.get("nsec")]
        except Exception:
            accounts = []
    if not accounts:
        # Single account set directly as secrets.
        nsec = (os.environ.get("NOSTR_NSEC", "") or "").strip()
        name = (os.environ.get("NOSTR_NAME", "") or "").strip()
        if nsec:
            entry = {"nsec": nsec}
            if name:
                entry["name"] = name
            accounts = [entry]
    return accounts


ENV_NOSTR_ACCOUNTS = _load_env_nostr_accounts()

# Lemmy accounts can come from the env secret (GitHub Actions) or
# from single-account env vars. Same sealed-box pattern as
# BLUESKY_ACCOUNTS / REDDIT_ACCOUNTS: the dashboard encrypts the
# list into the LEMMY_ACCOUNTS secret. No app registration exists
# on Lemmy - the user just has an account on an instance (e.g.
# lemmy.world) and the worker logs in with username + password.
def _load_env_lemmy_accounts():
    raw = (os.environ.get("LEMMY_ACCOUNTS", "") or "").strip()
    accounts = []
    if raw:
        try:
            data = json.loads(raw)
            if isinstance(data, list):
                accounts = [a for a in data
                            if isinstance(a, dict) and a.get("instance")
                            and a.get("username") and a.get("password")]
        except Exception:
            accounts = []
    if not accounts:
        # Single account set directly as secrets.
        inst = (os.environ.get("LEMMY_INSTANCE", "") or "").strip()
        user = (os.environ.get("LEMMY_USERNAME", "") or "").strip()
        pw = (os.environ.get("LEMMY_PASSWORD", "") or "").strip()
        if inst and user and pw:
            accounts = [{"instance": inst, "username": user,
                         "password": pw}]
    return accounts


ENV_LEMMY_ACCOUNTS = _load_env_lemmy_accounts()

# dev.to (platform 7 of 8): ONE API key, not an account list - the
# user creates a free dev.to account and generates the key at
# dev.to Settings > Extensions (Settings > Extensions > "DEV
# Community API Keys" > Generate API Key). The key is stored ONLY
# in the DEVTO_API_KEY env secret (the dashboard encrypts it with
# the same sealed-box pattern as the other platforms) - never
# logged, never in state.json, never in a repo file. Auth is one
# header: "api-key: <key>" (+ Accept:
# application/vnd.forem.api-v1+json). Free, no app registration, no
# review, no approval queue (verified 2026-11-25 against the
# official Forem API v1 reference at developers.forem.com/api/v1 -
# "Publish article" - and the dev.to API guides): POST
# https://dev.to/api/articles with {"article": {title,
# body_markdown, published, tags, main_image, canonical_url,
# description}} creates an article (201). Tags are a
# comma-separated string, max 4. canonical_url is OPTIONAL and is
# omitted when unknown (see _devto_canonical_url). main_image is
# the cover image URL. This is ARTICLE cross-posting, not a short
# post: the worker writes the FULL article (the same Gemini
# Markdown it writes for Blogger - see _devto_body_markdown) with
# the verified photo as the cover image. Audience is developers -
# this is an SEO/canonical play, not a news-feed play. dev.to v1
# is POST-ONLY: article comments exist on dev.to (POST
# /api/comments) but the comment-fetch loop was not built - see
# execute_card. Rate limit on article creation is 10 requests per
# 30 seconds - the worker's 5-minute gap per key is far inside it.
def _load_env_devto_api_key():
    return (os.environ.get("DEVTO_API_KEY", "") or "").strip()


ENV_DEVTO_API_KEY = _load_env_devto_api_key()

# Gemini models to try, in order.
# Rebuild #7.12 (quota fix, user order 2026-11-25: use only 2-3
# Gemini models): ONLY the models PROVEN to answer live. Health
# checks 2026-11-24/25 answered on gemini-4-hydrogen (fast) and
# gemini-3.5-flash-lite; gemini-4-argon 429s on EVERY key (the vision
# check burned all 6 of its attempts on argon and never reached a
# working model), and gemini-3.8-flash, gemini-3.1-flash-lite,
# gemini-2.5-flash, gemini-2.0-flash and gemini-2.5-flash-lite never
# answered live - so they are REMOVED. An unproven model name must
# never burn the attempt budget again. If a third model is ever
# proven live, add it here (and only here).
GEMINI_MODELS = ["gemini-4-hydrogen", "gemini-3.5-flash-lite",
                 "gemini-3.8-flash"]
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
DEFAULT_REDDIT_ENABLED = "true"       # Reddit cards on/off
DEFAULT_TUMBLR_ENABLED = "true"       # Tumblr cards on/off
DEFAULT_THREADS_ENABLED = "true"      # Threads cards on/off
DEFAULT_MASTODON_ENABLED = "true"     # Mastodon cards on/off
DEFAULT_TELEGRAM_ENABLED = "true"     # Telegram cards on/off
DEFAULT_NOSTR_ENABLED = "true"        # Nostr cards on/off
DEFAULT_LEMMY_ENABLED = "true"        # Lemmy cards on/off
DEFAULT_DEVTO_ENABLED = "true"        # dev.to cards on/off
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
        "reddit_enabled": str(DEFAULT_REDDIT_ENABLED),
        "tumblr_enabled": str(DEFAULT_TUMBLR_ENABLED),
        "threads_enabled": str(DEFAULT_THREADS_ENABLED),
        "mastodon_enabled": str(DEFAULT_MASTODON_ENABLED),
        "telegram_enabled": str(DEFAULT_TELEGRAM_ENABLED),
        "nostr_enabled": str(DEFAULT_NOSTR_ENABLED),
        "lemmy_enabled": str(DEFAULT_LEMMY_ENABLED),
        "devto_enabled": str(DEFAULT_DEVTO_ENABLED),
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
              "last_bsky_post_at", "last_reddit_post_at",
              "last_tumblr_post_at", "last_threads_post_at",
              "last_mastodon_post_at", "last_telegram_post_at",
              "last_nostr_post_at", "last_lemmy_post_at",
              "last_devto_post_at"):
        m = dict(remote.get(k) or {})
        for kk, vv in (local.get(k) or {}).items():
            if kk not in m or str(vv or "") >= str(m.get(kk) or ""):
                m[kk] = vv
        if m:
            merged[k] = m
    # Reddit per-account daily post counts: max per date+username wins
    # (a count must never go backwards on merge, or the daily cap
    # would silently reset and an account could over-post).
    _rc_remote = remote.get("reddit_post_counts") or {}
    _rc_local = local.get("reddit_post_counts") or {}
    _rc = {}
    for _d in set(_rc_remote) | set(_rc_local):
        _day = {}
        for _u in set((_rc_remote.get(_d) or {})) | set((_rc_local.get(_d) or {})):
            try:
                _day[_u] = max(int((_rc_remote.get(_d) or {}).get(_u) or 0),
                               int((_rc_local.get(_d) or {}).get(_u) or 0))
            except Exception:
                _day[_u] = ((_rc_remote.get(_d) or {}).get(_u)
                            or (_rc_local.get(_d) or {}).get(_u) or 0)
        if _day:
            _rc[_d] = _day
    if _rc:
        merged["reddit_post_counts"] = _rc
    # Tumblr per-blog daily post counts: same max-wins rule as Reddit.
    _tc_remote = remote.get("tumblr_post_counts") or {}
    _tc_local = local.get("tumblr_post_counts") or {}
    _tc = {}
    for _d in set(_tc_remote) | set(_tc_local):
        _day = {}
        for _u in set((_tc_remote.get(_d) or {})) | set((_tc_local.get(_d) or {})):
            try:
                _day[_u] = max(int((_tc_remote.get(_d) or {}).get(_u) or 0),
                               int((_tc_local.get(_d) or {}).get(_u) or 0))
            except Exception:
                _day[_u] = ((_tc_remote.get(_d) or {}).get(_u)
                            or (_tc_local.get(_d) or {}).get(_u) or 0)
        if _day:
            _tc[_d] = _day
    if _tc:
        merged["tumblr_post_counts"] = _tc
    # Threads per-user daily post counts: same max-wins rule as Reddit/Tumblr.
    _th_remote = remote.get("threads_post_counts") or {}
    _th_local = local.get("threads_post_counts") or {}
    _th = {}
    for _d in set(_th_remote) | set(_th_local):
        _day = {}
        for _u in set((_th_remote.get(_d) or {})) | set((_th_local.get(_d) or {})):
            try:
                _day[_u] = max(int((_th_remote.get(_d) or {}).get(_u) or 0),
                               int((_th_local.get(_d) or {}).get(_u) or 0))
            except Exception:
                _day[_u] = ((_th_remote.get(_d) or {}).get(_u)
                            or (_th_local.get(_d) or {}).get(_u) or 0)
        if _day:
            _th[_d] = _day
    if _th:
        merged["threads_post_counts"] = _th
    # Mastodon per-account daily post counts: same max-wins rule as Reddit/Tumblr/Threads.
    _ma_remote = remote.get("mastodon_post_counts") or {}
    _ma_local = local.get("mastodon_post_counts") or {}
    _ma = {}
    for _d in set(_ma_remote) | set(_ma_local):
        _day = {}
        for _u in set((_ma_remote.get(_d) or {})) | set((_ma_local.get(_d) or {})):
            try:
                _day[_u] = max(int((_ma_remote.get(_d) or {}).get(_u) or 0),
                               int((_ma_local.get(_d) or {}).get(_u) or 0))
            except Exception:
                _day[_u] = ((_ma_remote.get(_d) or {}).get(_u)
                            or (_ma_local.get(_d) or {}).get(_u) or 0)
        if _day:
            _ma[_d] = _day
    if _ma:
        merged["mastodon_post_counts"] = _ma
    # Telegram per-channel daily post counts: same max-wins rule as
    # Reddit/Tumblr/Threads/Mastodon (the key is the channel, e.g.
    # @primotodaynews - one bot can post to several channels).
    _tg_remote = remote.get("telegram_post_counts") or {}
    _tg_local = local.get("telegram_post_counts") or {}
    _tg = {}
    for _d in set(_tg_remote) | set(_tg_local):
        _day = {}
        for _u in set((_tg_remote.get(_d) or {})) | set((_tg_local.get(_d) or {})):
            try:
                _day[_u] = max(int((_tg_remote.get(_d) or {}).get(_u) or 0),
                               int((_tg_local.get(_d) or {}).get(_u) or 0))
            except Exception:
                _day[_u] = ((_tg_remote.get(_d) or {}).get(_u)
                            or (_tg_local.get(_d) or {}).get(_u) or 0)
        if _day:
            _tg[_d] = _day
    if _tg:
        merged["telegram_post_counts"] = _tg
    # Nostr per-key daily post counts: same max-wins rule as
    # Reddit/Tumblr/Threads/Mastodon/Telegram (the key is the npub -
    # the public key, never the nsec - so state.json stays secret-free).
    _no_remote = remote.get("nostr_post_counts") or {}
    _no_local = local.get("nostr_post_counts") or {}
    _no = {}
    for _d in set(_no_remote) | set(_no_local):
        _day = {}
        for _u in set((_no_remote.get(_d) or {})) | set((_no_local.get(_d) or {})):
            try:
                _day[_u] = max(int((_no_remote.get(_d) or {}).get(_u) or 0),
                               int((_no_local.get(_d) or {}).get(_u) or 0))
            except Exception:
                _day[_u] = ((_no_remote.get(_d) or {}).get(_u)
                            or (_no_local.get(_d) or {}).get(_u) or 0)
        if _day:
            _no[_d] = _day
    if _no:
        merged["nostr_post_counts"] = _no
    # Lemmy per-account daily post counts: same max-wins rule as
    # Reddit/Tumblr/Threads/Mastodon/Telegram/Nostr (the key is
    # "instance|username" - public, never a password or JWT).
    _le_remote = remote.get("lemmy_post_counts") or {}
    _le_local = local.get("lemmy_post_counts") or {}
    _le = {}
    for _d in set(_le_remote) | set(_le_local):
        _day = {}
        for _u in set((_le_remote.get(_d) or {})) | set((_le_local.get(_d) or {})):
            try:
                _day[_u] = max(int((_le_remote.get(_d) or {}).get(_u) or 0),
                               int((_le_local.get(_d) or {}).get(_u) or 0))
            except Exception:
                _day[_u] = ((_le_remote.get(_d) or {}).get(_u)
                            or (_le_local.get(_d) or {}).get(_u) or 0)
        if _day:
            _le[_d] = _day
    if _le:
        merged["lemmy_post_counts"] = _le
    # dev.to per-key daily post counts: same max-wins rule as
    # Reddit/Tumblr/Threads/Mastodon/Telegram/Nostr/Lemmy (the key
    # is "devto" - one API key, no account name, never the key
    # itself).
    _de_remote = remote.get("devto_post_counts") or {}
    _de_local = local.get("devto_post_counts") or {}
    _de = {}
    for _d in set(_de_remote) | set(_de_local):
        _day = {}
        for _u in set((_de_remote.get(_d) or {})) | set((_de_local.get(_d) or {})):
            try:
                _day[_u] = max(int((_de_remote.get(_d) or {}).get(_u) or 0),
                               int((_de_local.get(_d) or {}).get(_u) or 0))
            except Exception:
                _day[_u] = ((_de_remote.get(_d) or {}).get(_u)
                            or (_de_local.get(_d) or {}).get(_u) or 0)
        if _day:
            _de[_d] = _day
    if _de:
        merged["devto_post_counts"] = _de
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
    # Rebuild #7.11: the ready queue is owned by the worker (the
    # dashboard never touches it) - merge it per card, newest
    # prepared_at wins per headline, stale items dropped, capped at
    # READY_QUEUE_SIZE. Without this the queue would be LOST on every
    # commit-back (the remote state has no queue key) and a prepared
    # post would never survive to the next run.
    rq_remote = remote.get("ready_queue") or {}
    rq_local = local.get("ready_queue") or {}
    merged_rq = {}
    for _name in set(rq_remote) | set(rq_local):
        by_head = {}
        for _it in (rq_remote.get(_name) or []) + (rq_local.get(_name) or []):
            if not isinstance(_it, dict):
                continue
            if not _ready_item_fresh(_it):
                continue
            _key = _norm_news_key(_it.get("headline") or "")
            if not _key:
                continue
            _prev = by_head.get(_key)
            if _prev is None or str(_it.get("prepared_at") or "") >= str(_prev.get("prepared_at") or ""):
                by_head[_key] = _it
        _items = sorted(by_head.values(),
                        key=lambda it: str(it.get("prepared_at") or ""))
        if _items:
            merged_rq[_name] = _items[-READY_QUEUE_SIZE:]
    if merged_rq:
        merged["ready_queue"] = merged_rq
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
        reddit_accounts_detail = []
        for a in list_reddit_accounts():
            u = a["username"]
            reddit_accounts_detail.append({
                "username": u,
                "enabled": reddit_account_enabled(u),
                "posts_limit": reddit_account_posts_limit(u),
                "posts_today": posts_today_for_reddit_account(state, u),
            })
        tumblr_accounts_detail = []
        for a in list_tumblr_accounts():
            b = a["blog"]
            tumblr_accounts_detail.append({
                "blog": b,
                "enabled": tumblr_account_enabled(b),
                "posts_limit": tumblr_account_posts_limit(b),
                "posts_today": posts_today_for_tumblr_account(state, b),
            })
        threads_accounts_detail = []
        for a in list_threads_accounts():
            u = a["user_id"]
            threads_accounts_detail.append({
                "user_id": u,
                "username": a.get("username", ""),
                "enabled": threads_account_enabled(u),
                "posts_limit": threads_account_posts_limit(u),
                "posts_today": posts_today_for_threads_account(state, u),
            })
        mastodon_accounts_detail = []
        for a in list_mastodon_accounts():
            k = _mastodon_account_key(a)
            mastodon_accounts_detail.append({
                "key": k,
                "instance": _mastodon_instance_base(a),
                "username": a.get("username", ""),
                "enabled": mastodon_account_enabled(k),
                "posts_limit": mastodon_account_posts_limit(k),
                "posts_today": posts_today_for_mastodon_account(state, k),
            })
        telegram_accounts_detail = []
        for a in list_telegram_accounts():
            k = _telegram_account_key(a)
            telegram_accounts_detail.append({
                "key": k,
                "enabled": telegram_account_enabled(k),
                "posts_limit": telegram_account_posts_limit(k),
                "posts_today": posts_today_for_telegram_bot(state),
            })
        nostr_accounts_detail = []
        for a in list_nostr_accounts():
            k = _nostr_account_key(a)
            nostr_accounts_detail.append({
                "key": k,
                "npub": k,
                "name": a.get("name", ""),
                "enabled": nostr_account_enabled(k),
                "posts_limit": nostr_account_posts_limit(k),
                "posts_today": posts_today_for_nostr_account(state, k),
            })
        lemmy_accounts_detail = []
        for a in list_lemmy_accounts():
            k = _lemmy_account_key(a)
            lemmy_accounts_detail.append({
                "key": k,
                "instance": _lemmy_instance_base(a),
                "username": a.get("username", ""),
                "enabled": lemmy_account_enabled(k),
                "posts_limit": lemmy_account_posts_limit(k),
                "posts_today": posts_today_for_lemmy_account(state, k),
            })
        devto_accounts_detail = []
        for a in list_devto_accounts():
            k = _devto_account_key(a)
            devto_accounts_detail.append({
                "key": k,
                "name": a.get("name", "dev.to"),
                "enabled": devto_account_enabled(k),
                "posts_limit": devto_account_posts_limit(k),
                "posts_today": posts_today_for_devto_account(state, k),
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
                "subreddit": c.get("subreddit", ""),
                "community": c.get("community", ""),
                "channel": c.get("channel", ""),
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
                          "bsky_enabled", "reddit_enabled", "tumblr_enabled",
                          "threads_enabled", "mastodon_enabled",
                          "telegram_enabled", "nostr_enabled",
                          "lemmy_enabled", "devto_enabled",
                          "replies_enabled",
                          "cards_enabled",
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
            "reddit_accounts_detail": reddit_accounts_detail,
            "tumblr_accounts_detail": tumblr_accounts_detail,
            "threads_accounts_detail": threads_accounts_detail,
            "mastodon_accounts_detail": mastodon_accounts_detail,
            "telegram_accounts_detail": telegram_accounts_detail,
            "nostr_accounts_detail": nostr_accounts_detail,
            "lemmy_accounts_detail": lemmy_accounts_detail,
            "devto_accounts_detail": devto_accounts_detail,
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


def _gemini_attempt_order(keys, models):
    """(key, model) pairs in round-robin order. Rebuild #7.12 (quota
    fix, user order 2026-11-25): the old loops were MODEL-major (for
    model: for key:), so a dead first model burned every attempt
    before a working model was tried - live, vision spent all 6 of
    its attempts on gemini-4-argon (HTTP 429 on every key) and never
    reached gemini-4-hydrogen / gemini-3.5-flash-lite, the two models
    proven to answer. Round-robin alternates the model on every
    attempt while cycling the keys, so a dead model costs one attempt
    and a dead key costs one attempt; the first len(keys) pairs cover
    EVERY key (models alternating) and the full order covers every
    key x model pair exactly once. Keys are shuffled by the caller
    first, so the load spreads across projects. Returns a list of
    (key, model) tuples (empty when no keys or no models)."""
    keys = list(keys or [])
    models = list(models or [])
    if not keys or not models:
        return []
    pairs = []
    for offset in range(len(models)):
        for i, key in enumerate(keys):
            pairs.append((key, models[(i + offset) % len(models)]))
    return pairs


def gemini_text(prompt, max_tokens=1500):
    """Write with Gemini. Returns text or '' (never raises).
    Rebuild #7.2: on total failure, log the SPECIFIC reason (how many
    keys were found, which models were tried, the exact error per
    status) instead of failing silently - the workflow log must show
    WHY the AI is down. Key VALUES are never logged, only counts.
    Rebuild #7.12: attempts walk _gemini_attempt_order (round-robin,
    key + model alternating) so one dead model or one dead key never
    burns the whole budget - the first len(keys) attempts already
    cover every key. On 429, sleep 2s (per-minute backoff)."""
    if not GEMINI_KEYS:
        log("warning", "gemini_text: no GEMINI_API_KEYS configured (0 keys)")
        return ""
    keys = GEMINI_KEYS[:]
    random.shuffle(keys)
    seen = {}  # (code, detail) -> attempts
    for key, model in _gemini_attempt_order(keys, GEMINI_MODELS):
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
    any og:image that is a BARE logo / icon / generic graphic is
    rejected - a bare logo is never a 'real photo' (rebuild #7.10: a
    real photograph that carries a logo/text/watermark overlay is
    FINE and is accepted). Rebuild #7.6: when the caller
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
# Path words that are NEVER a real news photograph (a generic graphic
# / missing-image placeholder, not a photo at all). "logo" and "icon"
# are deliberately NOT in this list (rebuild #7.10, user order): a
# real news photo whose URL passes through a directory named "logo"
# or "icon" is still a photo, and a photo that carries a logo / text
# / watermark overlay is FINE.
LOGO_PATH_WORDS = ("favicon", "sprite", "placeholder", "no-image",
                   "default-image", "blank")
# Filename stems of a BARE logo/icon file (the file itself IS a logo,
# not a photograph). Checked against the file's base name only - a
# photo file is named after its subject, never "logo".
LOGO_FILE_STEMS = ("logo", "logos", "icon", "icons", "favicon",
                   "sprite", "placeholder", "no-image", "default-image",
                   "blank")

# Rebuild #7.12: signals that an image is a flag-only / cartoon /
# clipart / kids-story graphic - checked ONLY by the vision-down
# strict check (_photo_strict_when_vision_down). Live failures
# 2026-11-25: an Iranian flag on a Saudi/Yemen Hodeidah story and a
# "MORAL KIDS STORIES" cartoon on a US election story both passed
# the weak keyword check while the vision gate was down (Gemini 429).
# A real news photograph that happens to show a flag is still FINE
# when vision can judge it - these signals only apply when vision
# cannot run.
VISION_DOWN_FLAG_FILE_WORDS = ("flag", "flags")
VISION_DOWN_JUNK_FILE_WORDS = ("cartoon", "clipart", "clip-art",
                               "coloring", "colouring", "moral")
VISION_DOWN_JUNK_HOSTS = ("pngmart", "vecteezy", "pngtree", "clipart")
VISION_DOWN_JUNK_TITLE_PHRASES = ("cartoon", "clipart", "clip-art",
                                  "coloring", "colouring", "moral kids",
                                  "kids stories", "moral stories")


def _is_logo_image_url(url):
    """True if an image URL is a BARE logo / icon / generic graphic,
    not a real news photograph. Rebuild #7.10 (user order, strict):
    a REAL news photograph that carries a logo, text or watermark
    OVERLAY is FINE and must NOT be rejected - only an image that
    IS a logo (a bare logo file, not a photo at all) is rejected.
    So the check is filename-based: the FILE itself must be a
    logo/icon (its name is logo/favicon/sprite/...), or the host
    must be Google's (the Google News logo). A photo whose URL
    merely passes through a directory named "logo" or "icon" is a
    photo and passes, and a file named "iconic-..." is a photo too
    (the old token check rejected it). The vision gate is the
    backstop for a bare logo on a neutral URL (it does not show the
    story/person)."""
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
        # The FILE name only (not a directory): a bare logo/icon
        # file. "iconic-moment.jpg" is a photo - "icon" must match
        # exactly, or as a hyphen/underscore prefix, never a prefix
        # of a longer word.
        base = parsed.path.rsplit("/", 1)[-1]
        stem = base.rsplit(".", 1)[0] if "." in base else base
        stem = stem.strip().lower()
        if stem in LOGO_FILE_STEMS:
            return True
        if stem.startswith(("logo-", "logo_", "favicon", "sprite",
                            "icon-", "icon_")) or \
                stem.endswith(("-logo", "_logo")):
            return True
        return False
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
            gate = _vision_gate(local, topic, vision)
            if gate is False:
                log("info", f"photo candidate for '{topic}': "
                            f"'{(item.get('title') or '')[:50]}' - rejected "
                            "(vision: does not show the person/subject)")
                continue
            if gate is None:
                # Rebuild #7.12: vision down - the og:image must not
                # pass on the keyword check alone. Only the
                # junk-image signals apply here (fetch_og_image
                # already verified the page is about the story).
                ok, why = _photo_strict_when_vision_down(
                    img, link, None, "", topic, require_title=False)
                if not ok:
                    log("info", f"photo candidate for '{topic}': "
                                f"'{(item.get('title') or '')[:50]}' - "
                                f"rejected (vision down, strict check): "
                                f"{why}")
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
VISION_MAX_ATTEMPTS = 10        # max key/model attempts per vision check
                                # (round-robin: all 10 keys, models
                                # alternating - see _gemini_attempt_order)

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
    # Rebuild #7.10 (user order, strict): a logo, text, caption or
    # watermark OVERLAID on the photo is FINE - judge the photo
    # itself, not the overlay. Only a photo that does not show the
    # story/person is a NO.
    overlay_ok = ("A logo, text, caption or watermark overlaid on "
                  "the photo is fine - judge the photo itself, not "
                  "the overlay. ")
    if person_names:
        names = " and ".join(person_names[:2])
        return (f"News headline: \"{headline}\"\n"
                f"Does this photo clearly show {names}? "
                "Answer YES only if the named person is clearly visible "
                "in the photo. " + overlay_ok +
                "Answer NO if the photo shows someone else, "
                "a product, a cartoon, a chart, a poster, or anything "
                "unrelated. Reply with YES or NO first, then one short reason.")
    return (f"News headline: \"{headline}\"\n"
            "Does this photo show the people, place or event in this "
            "headline? Answer YES only if the photo clearly matches the "
            "headline. " + overlay_ok +
            "Answer NO if it shows a product, a cartoon, a "
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
    NEVER blocks a post by itself. Rebuild #7.12 (quota fix, user
    order 2026-11-25): ROOT CAUSE of the 2026-11-24/25 vision outage
    - the loop was MODEL-major (for model: for key:) and capped at 6
    attempts, so all 6 attempts burned on the FIRST model
    (gemini-4-argon, HTTP 429 on every key) and vision NEVER reached
    gemini-4-hydrogen / gemini-3.5-flash-lite, the two models proven
    to answer live. Attempts now walk _gemini_attempt_order
    (round-robin: every key, models alternating), bounded to
    VISION_MAX_ATTEMPTS, so a dead model costs one attempt and a dead
    key costs one attempt. On 429, sleep 2s (per-minute backoff).
    Never raises. Key values are never logged."""
    if not GEMINI_KEYS:
        return None, "no GEMINI_API_KEYS configured"
    if not image_b64:
        return None, "no image data to check"
    prompt = _vision_prompt(headline, person_names or [])
    keys = GEMINI_KEYS[:]
    random.shuffle(keys)
    attempts = 0
    seen = {}
    for key, model in _gemini_attempt_order(keys, GEMINI_MODELS):
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


def _photo_strict_when_vision_down(url, page_url, page_title, alt,
                                   headline, require_title=True):
    """Strict photo check used ONLY when the Gemini vision gate could
    not run (quota exhausted / API down) - a photo must NOT pass on a
    weak keyword match alone. Rebuild #7.12 (live failures 2026-11-25:
    an Iranian flag on a Saudi/Yemen Hodeidah story and a "MORAL KIDS
    STORIES" cartoon on a US election story both passed _photo_relevant
    on 2 generic words while vision was 429-down). Two bars: (1) the
    image must not be a flag-only / cartoon / clipart / kids-story
    graphic (image URL, host, alt text or page title signals); (2) the
    source page TITLE must contain at least 2 of the story's key
    entities - the page must be a news article ABOUT the story, not a
    page that merely mentions two words in its URL. When the page has
    no title, the URL alone must name 3 key entities. require_title
    is False for an article's own og:image (fetch_og_image already
    verified its page is about the story, so only the junk-image
    signals apply there). Returns (ok, reason). Never raises."""
    try:
        u = str(url or "").strip().lower()
        netloc = urlparse(u).netloc
        if any(h in netloc for h in VISION_DOWN_JUNK_HOSTS):
            return False, "image from a clipart/vector host"
        parsed = urlparse(u)
        stem = parsed.path.rsplit("/", 1)[-1]
        stem = stem.rsplit(".", 1)[0] if "." in stem else stem
        tokens = set(re.findall(r"[a-z0-9]+", stem.lower()))
        if tokens & set(VISION_DOWN_FLAG_FILE_WORDS):
            return False, "image file looks like a flag, not a news photo"
        if tokens & set(VISION_DOWN_JUNK_FILE_WORDS):
            return False, "image file looks like a cartoon/clipart"
        if "kids" in tokens and "stories" in tokens:
            return False, "image file looks like a kids-story graphic"
        hay = ((page_title or "") + " " + (alt or "")).lower()
        if any(p in hay for p in VISION_DOWN_JUNK_TITLE_PHRASES):
            return False, "source page/alt describes a cartoon/clipart"
    except Exception:
        pass
    if not require_title:
        return True, "vision down but image is not a flag/cartoon"
    words = _event_words(headline)
    if not words:
        return False, "no key entities in the headline"
    title = (page_title or "").strip()
    if title:
        hay_words = {_stem_word(w)
                     for w in re.findall(r"[a-z0-9]+", title.lower())}
        hits = [w for w in words if w in hay_words]
        need = min(2, len(words))
        if len(hits) < need:
            return False, (f"source page title names only {len(hits)} of "
                           f"{len(words)} key entities - not a news "
                           "article about the story")
    else:
        hay_words = {_stem_word(w) for w in re.findall(
            r"[a-z0-9]+", (page_url or "").lower())}
        hits = [w for w in words if w in hay_words]
        if len(hits) < 3:
            return False, (f"source page URL names only {len(hits)} key "
                           "entities - not a news article about the story")
    return True, "vision down but photo passes the strict check"


def _real_photo_for_topic(topic, vision=None):
    """A REAL photo for a topic from real-photo sources only
    (Pexels / Pixabay / Openverse / Wikimedia Commons / Google Images
    / Bing Images). Never AI-generated, never a BARE logo, never a
    generic icon (rebuild #7.10: a real photo that carries a logo /
    text / watermark overlay is FINE). Tries progressively shorter search queries and several
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
    Rebuild #7.11: when the topical search finds NOTHING, an
    ENTITY-based fallback runs - the named PERSON (or the leading
    entity) in the headline is searched instead. A portrait of the
    person IS the right photo for a story about them; relevance is
    relaxed to "the source page names the entity" and the vision
    gate still checks the photo shows that person / matches the
    story. The download budget covers both phases, so one story can
    never grind through dozens of downloads.
    Returns a photo dict with local_path, or None (with a summary log
    of what was tried)."""
    tried_downloads = 0
    # Phase 1: topical queries (full headline -> short keywords).
    for q in _photo_search_queries(topic):
        if tried_downloads >= MAX_REAL_PHOTO_DOWNLOADS:
            break
        photo, tried_downloads = _try_photo_query(
            q, topic, vision, tried_downloads,
            lambda pu, pt: _photo_relevant(pu, pt, topic))
        if photo:
            return photo
    # Phase 2 (rebuild #7.11): entity-based fallback - the named
    # person, or the leading entity, in the headline.
    if tried_downloads < MAX_REAL_PHOTO_DOWNLOADS:
        for entity in _photo_fallback_entities(topic):
            if tried_downloads >= MAX_REAL_PHOTO_DOWNLOADS:
                break
            log("info", f"photo: topical search found nothing for "
                        f"'{topic[:50]}' - trying entity search "
                        f"'{entity}'")
            photo, tried_downloads = _try_photo_query(
                entity, topic, vision, tried_downloads,
                lambda pu, pt, e=entity: _page_names_entity(pu, pt, e))
            if photo:
                return photo
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
# Rebuild #7.10: the try-next-story loop. A post attempt tries up to
# this many FRESH stories (each gets a full photo attempt: the
# article's own og:image, then a real-photo search) before it skips
# - a story with no photo never ends the run on its own. Only when
# ALL tried stories lack a photo does the run skip cleanly.
PICK_MAX_STORIES = 6           # max fresh stories tried per promo pick
# Rebuild #7.11: a wider story pool (8 -> 12 items per category) so
# the try-next-story loop has more visual stories to try - the old
# pool was exhausted by non-visual survey/analysis pieces. verify_news
# now returns up to 12 items per topic to match.
PICK_MAX_ITEMS_PER_TOPIC = 12   # news items examined per category

# Rebuild #7.11: the READY QUEUE (user order 2026-11-24 - a post must
# happen ON TIME, the photo WILL be collected). The worker prepares
# the next post(s) AHEAD of time - news + verified photo + caption -
# and stores them in state (ready_queue, per card). When a post slot
# is due, the ready post goes out at once instead of starting a fresh
# news/photo search that can fail and skip the slot. A ready post is
# fresh for READY_MAX_AGE_HOURS; older items are discarded and
# re-prepared. The photo's remote URL is stored (NOT the local file -
# each workflow run is a fresh runner, so the file is gone; the URL
# is re-downloaded at post time, which is fast and re-verified).
READY_QUEUE_SIZE = 2            # ready posts kept per card
READY_MAX_AGE_HOURS = 3         # a ready post older than this is stale
READY_PREPARE_WINDOW_MINUTES = 15  # prepare when a post slot is due within this

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
        # Rebuild #7.9: a link too long for Bluesky makes the fitted
        # caption None - this hook can never post, try the next one.
        caption_id = _fit_bsky_text(hook, link, cta="")
        if caption_id is None:
            continue
        if _promo_caption_cooldown_left(state, caption_id) is None:
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


# ---------------------------------------------------------------- rebuild #7.9
# GRAPHEME-AWARE LENGTH (Bluesky counts GRAPHEMES, not code points).
# Root cause of run #33 (2026-11-24 02:44 UTC): a Google News story
# URL can be 570+ chars (the CBM token grows with the publisher URL;
# the live feed shows 570/578-char story URLs), and the old
# _fit_bsky_text returned such a link WHOLE ("return link" when the
# tail did not fit) - a 570-grapheme "caption" that Bluesky rejects
# with 400 InvalidRequest "grapheme too big (maximum 300, got 570)".
# The old cap also counted Python len() (code points); an emoji /
# ZWJ / flag cluster is several code points but ONE grapheme, so
# len() and Bluesky disagreed. Everything below counts graphemes.
try:
    import grapheme as _grapheme_lib
except Exception:  # package not installed - use the fallback segmenter
    _grapheme_lib = None
import unicodedata as _unicodedata


def _grapheme_clusters(text):
    """Split text into extended grapheme clusters (UAX #29).
    Uses the `grapheme` package when installed (reference
    implementation, also in requirements.txt); otherwise a
    conservative built-in segmenter that merges a base character
    with following combining marks, variation selectors, skin-tone
    modifiers, ZWJ-joined parts, regional-indicator pairs (flags)
    and keycap sequences - the cases that occur in a caption. The
    fallback never splits a cluster it merges, and code-point
    length is the safe upper bound, so the cap below is always on
    the safe side."""
    text = text or ""
    if _grapheme_lib is not None:
        return list(_grapheme_lib.graphemes(text))
    clusters = []
    cur = ""
    prev_ri = False   # previous char was a lone regional indicator
    prev_zwj = False  # previous char was ZWJ (next char joins it)
    for ch in text:
        o = ord(ch)
        joins = (
            _unicodedata.combining(ch) != 0
            or o in (0xFE0E, 0xFE0F)          # variation selectors
            or 0x1F3FB <= o <= 0x1F3FF        # skin-tone modifiers
            or o == 0x200D                    # ZWJ joins both sides
            or o == 0x20E3                    # combining enclosing keycap
            or prev_zwj
            or (0x1F1E6 <= o <= 0x1F1FF and prev_ri)  # flag pair
        )
        if cur and joins:
            cur += ch
            prev_ri = False
            prev_zwj = o == 0x200D
        else:
            if cur:
                clusters.append(cur)
            cur = ch
            prev_ri = 0x1F1E6 <= o <= 0x1F1FF
            prev_zwj = o == 0x200D
    if cur:
        clusters.append(cur)
    return clusters


def _bsky_grapheme_len(text):
    """Bluesky grapheme count of text (what the 300 limit counts)."""
    return len(_grapheme_clusters(text))


def _bsky_grapheme_slice(text, max_graphemes):
    """The first at most max_graphemes grapheme clusters of text -
    never splits a cluster, so an emoji/flag/ZWJ sequence stays whole."""
    if max_graphemes <= 0:
        return ""
    return "".join(_grapheme_clusters(text)[:max_graphemes])


def _cap_bsky_text(text):
    """HARD cap at the single send point (rebuild #7.9): no Bluesky
    post or reply may exceed 300 graphemes, whatever path built it.
    Trims the text to 300 graphemes, keeping a trailing CTA + link
    intact when the text ends with them (caption format is hook +
    CTA + link, one per line) - the hook is trimmed, the link never
    is. Logs when it had to trim, so a bypass of _fit_bsky_text is
    visible in the run log. Returns the (possibly trimmed) text."""
    text = text or ""
    total = _bsky_grapheme_len(text)
    if total <= BSKY_MAX_CHARS:
        return text
    lines = text.split("\n")
    tail_lines = []
    if lines and lines[-1].strip().startswith("http"):
        tail_lines.append(lines.pop())
        if lines and lines[-1].strip():
            tail_lines.insert(0, lines.pop())
    tail = "\n".join(tail_lines)
    tail_len = _bsky_grapheme_len(tail)
    if tail_len >= BSKY_MAX_CHARS:
        # Even the link alone does not fit: hard-truncate (last resort).
        capped = _bsky_grapheme_slice(text, BSKY_MAX_CHARS)
        log("warning", "caption truncated to "
                       f"{BSKY_MAX_CHARS} graphemes (was {total}) - "
                       "link may be cut")
        return capped
    room = BSKY_MAX_CHARS - tail_len - 1
    head = "\n".join(lines)
    if _bsky_grapheme_len(head) > room:
        if room <= 1:
            head = _bsky_grapheme_slice(head, room)
        else:
            head = _bsky_grapheme_slice(head, room - 1).rstrip() + "\u2026"
    capped = f"{head}\n{tail}" if head and tail else (head or tail)
    log("warning", f"caption truncated to {_bsky_grapheme_len(capped)} "
                   f"graphemes (was {total})")
    return capped


def _fit_bsky_text(hook, link, cta=None):
    """Combine a hook, a call-to-action and a link into ONE Bluesky
    post (max 300 graphemes). Rebuild #7.7: the caption ALWAYS ends
    with CTA + link - the CTA and the link are NEVER truncated, the
    hook is trimmed to fit, so the final text always ends with the
    CTA and then the link, and the link appears exactly once.
    cta defaults to the first variant; the caller passes the
    rotated variant via _next_bsky_cta(state).
    Rebuild #7.9: counts GRAPHEMES (what Bluesky counts), not
    len() (code points) - an emoji/ZWJ/flag cluster is several code
    points but one grapheme. And a link that cannot fit in a post
    at all (a Google News story URL can be 570+ chars) now returns
    None instead of the old behaviour of returning the bare link
    untrimmed - that bare 570-char link is exactly what Bluesky
    rejected in run #33 ("grapheme too big, got 570"). The caller
    must skip the post when this returns None. Never returns just
    the bare link unless the link alone already fills the post AND
    fits in 300 graphemes."""
    hook = (hook or "").strip()
    link = (link or "").strip()
    if cta is None:
        cta = BSKY_CTA_VARIANTS[0]
    cta = (cta or "").strip()
    # Drop a link the AI already appended, so it is not doubled.
    if link and link in hook:
        hook = hook.replace(link, "").strip()
    # Rebuild #7.9: a link longer than the whole post cannot fit at
    # all - check FIRST, before spending a fallback hook on it.
    if link and _bsky_grapheme_len(link) > BSKY_MAX_CHARS:
        log("warning", f"caption: link too long for Bluesky "
                       f"({_bsky_grapheme_len(link)} graphemes) - "
                       "story cannot be posted with this link")
        return None
    if not hook:
        hook = _promo_fallback_hook(None, link)
    if not link:
        return _bsky_grapheme_slice(hook, BSKY_MAX_CHARS)
    # CTA + link always fit (both are short); only the hook is trimmed.
    # cta="" means NO call-to-action (used for the caption-dedup
    # identity - see _card_bluesky_post): the tail is then just the link.
    tail = f"{cta}\n{link}" if cta else link
    tail_len = _bsky_grapheme_len(tail)
    if tail_len >= BSKY_MAX_CHARS:
        # CTA + link fill the post: the link itself fits (checked
        # above), so the bare link is a valid caption.
        return link
    room = BSKY_MAX_CHARS - tail_len - 1
    if room < 10:
        return tail
    if _bsky_grapheme_len(hook) > room:
        hook = _bsky_grapheme_slice(hook, room - 1).rstrip() + "\u2026"
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


# Rebuild #7.10 (user order): collect news AND photos from BIG
# news outlets. A story counts as "big outlet" when its Google News
# RSS <source> name or its link host matches one of these. Big-outlet
# stories are tried FIRST in the picker, and the outlet's own article
# page is fetched for its og:image before any image search runs.
# (name fragment in the RSS source, host fragment in the link)
BIG_OUTLETS = (
    ("reuters", "reuters.com"),
    ("associated press", "apnews.com"),
    ("ap news", "apnews.com"),
    ("bbc", "bbc.com"),
    ("cnn", "cnn.com"),
    ("al jazeera", "aljazeera.com"),
    ("new york times", "nytimes.com"),
    ("washington post", "washingtonpost.com"),
    ("guardian", "theguardian.com"),
    ("fox news", "foxnews.com"),
    ("nbc news", "nbcnews.com"),
    ("nbc", "nbcnews.com"),
    ("cbs news", "cbsnews.com"),
    ("abc news", "abcnews.go.com"),
    ("npr", "npr.org"),
    ("bloomberg", "bloomberg.com"),
    ("the hill", "thehill.com"),
    ("politico", "politico.com"),
    ("wall street journal", "wsj.com"),
    ("usa today", "usatoday.com"),
    ("axios", "axios.com"),
    ("sky news", "news.sky.com"),
    ("france 24", "france24.com"),
    ("euronews", "euronews.com"),
    ("deutsche welle", "dw.com"),
)


def _big_outlet_rank(source, link):
    """Sort key for a news item: 0 = a major news outlet (tried
    first), 1 = any other source. Matches the RSS <source> name or
    the link host against BIG_OUTLETS. Never raises."""
    s = (source or "").strip().lower()
    try:
        host = (urlparse(link or "").netloc or "").lower()
    except Exception:
        host = ""
    for name, h in BIG_OUTLETS:
        if name and name in s:
            return 0
        if h and h in host:
            return 0
    return 1


def _resolve_article_url(link):
    """Resolve a Google News link to the publisher's article URL, so
    a big outlet's OWN article page can be fetched for its og:image.
    Returns the publisher URL, or the original link when it cannot
    be resolved (a non-Google-News link is returned unchanged).
    Follows the HTTP redirect when there is one, else the
    meta-refresh / canonical / outbound anchor on the Google News
    page (_extract_redirect_url). Never raises."""
    if not link:
        return link
    try:
        if "news.google.com" not in (urlparse(link).netloc or "").lower():
            return link
    except Exception:
        return link
    try:
        r = requests.get(link, timeout=20, allow_redirects=True,
                         headers={"User-Agent": "Mozilla/5.0"})
        if r.status_code == 200:
            final_host = (urlparse(r.url).netloc or "").lower()
            if "news.google.com" not in final_host:
                return r.url
            target = _extract_redirect_url(r.text, r.url)
            if target:
                return target
    except Exception:
        pass
    return link


# ---------------------------------------------------------------- rebuild #7.11
# NON-VISUAL STORIES: survey / poll / analysis / opinion headlines
# almost NEVER carry a real news photo (a Pew survey, a trust-in-media
# poll, an "anyone's guess" analysis). The live 2026-11-24 failure
# burned the whole 6-story budget on exactly these. They are skipped
# EARLY - before the item/story budget - so the budget is spent on
# stories that can actually have photos. Cheap headline-keyword
# detection: whole words for the survey words ("poll" matches,
# "polling" does NOT - an election-day polling station IS visual),
# phrases for the survey patterns ("Majority of Americans Say...").
_NON_VISUAL_HEADLINE_WORDS = frozenset(
    "survey surveys poll analysis opinion editorial explainer explained "
    "column".split())
_NON_VISUAL_HEADLINE_PHRASES = (
    "americans say", "americans think", "majority of americans",
    "most americans", "trust in", "approval rating", "favorability",
    "polls show", "new poll", "study finds", "study shows",
    "report finds", "what it means", "what to know", "what we know",
    "what happens next", "anyone's guess", "the political map",
)


def _is_non_visual_headline(headline):
    """True when a headline is a survey / poll / analysis / opinion
    piece that almost never carries a real news photo. A heuristic
    (cheap keyword match) - a missed one only costs a photo attempt,
    a wrongly skipped one is never posted from this pick (the next
    pick can still use it). Never raises."""
    h = (headline or "").lower()
    if not h:
        return False
    if any(p in h for p in _NON_VISUAL_HEADLINE_PHRASES):
        return True
    words = set(re.findall(r"[a-z0-9]+", h))
    return bool(words & _NON_VISUAL_HEADLINE_WORDS)


# ---------------------------------------------------------------- rebuild #7.11
# READY QUEUE (user order 2026-11-24 - a post must happen ON TIME):
# the worker prepares the next post(s) AHEAD of time (news + verified
# photo + caption) and stores them in state["ready_queue"] (per card).
# A ready item is {topic, headline, photo_url, photo_source, photo_alt,
# article_url, hook, prepared_at}. The photo's remote URL is stored,
# NOT the local file - each workflow run is a fresh runner, so the
# file is gone; the URL is re-downloaded (and re-verified) at post
# time. A ready item is fresh for READY_MAX_AGE_HOURS; older items
# are discarded and re-prepared. The queue is the reservation: the
# picker never steals a story that is already prepared and waiting.
def _ready_queue(state):
    """The ready queue store: {card_name: [ready_item, ...]}."""
    q = (state or {}).get("ready_queue")
    if not isinstance(q, dict):
        q = {}
        if isinstance(state, dict):
            state["ready_queue"] = q
    return q


def _ready_item_fresh(item):
    """True when a ready item was prepared within READY_MAX_AGE_HOURS.
    An item with no (or unparseable) prepared_at is never fresh."""
    try:
        dt = datetime.fromisoformat(str((item or {}).get("prepared_at") or ""))
    except Exception:
        return False
    if dt.tzinfo is None:
        dt = dt.replace(tzinfo=UTC)
    return (now_utc() - dt) <= timedelta(hours=READY_MAX_AGE_HOURS)


def _prune_ready_queue(state, name=None):
    """Drop stale ready items (and cap each card at READY_QUEUE_SIZE).
    Returns the pruned store."""
    q = _ready_queue(state)
    names = [name] if name else list(q.keys())
    for n in names:
        items = [it for it in (q.get(n) or []) if isinstance(it, dict)
                 and _ready_item_fresh(it)]
        if len(items) > READY_QUEUE_SIZE:
            items = items[-READY_QUEUE_SIZE:]
        if items:
            q[n] = items
        elif n in q:
            del q[n]
    return q


def _ready_queue_headline_keys(state):
    """Event keys of every FRESH ready item (all cards) - the picker
    must not steal a story that is already prepared and waiting to
    post. Never raises."""
    keys = set()
    try:
        for items in _ready_queue(state).values():
            for it in (items or []):
                if isinstance(it, dict) and _ready_item_fresh(it):
                    k = _norm_news_key(it.get("headline") or "")
                    if k:
                        keys.add(k)
    except Exception:
        pass
    return keys


def _headline_in_ready_queue(state, headline):
    """True when this headline's event is already prepared in the
    ready queue (any card) - the picker must not steal it for another
    post. Fuzzy event match, like the 24h cooldown (rebuild #7.5)."""
    words = _norm_news_key(headline).split()
    if not words:
        return False
    for key in _ready_queue_headline_keys(state):
        if _event_keys_match(words, key.split()):
            return True
    return False


def _discard_ready_item(card, state, headline):
    """Remove a ready item by headline (fuzzy event match)."""
    name = card.get("name", "")
    q = _ready_queue(state)
    items = q.get(name) or []
    words = _norm_news_key(headline).split()
    kept = [it for it in items
            if not (isinstance(it, dict) and words and
                    _event_keys_match(words, _norm_news_key(
                        it.get("headline") or "").split()))]
    if kept:
        q[name] = kept
    elif name in q:
        del q[name]


def _consume_ready_item(card, state, headline):
    """Remove a ready item after it was successfully posted."""
    _discard_ready_item(card, state, headline)


def _prepare_ready_item(card, state):
    """Prepare ONE ready post for a card: pick a fresh story + verified
    photo (the expensive part) and write its caption, then store it in
    the ready queue. Returns True when an item was queued. The picker
    already skips stories in the queue (reservation), so a second
    prepare in the same run picks a DIFFERENT story. A failed prepare
    (no photo) returns False - the caller must not retry at once (the
    news pool has not changed). Never raises."""
    name = card.get("name", "")
    try:
        topic, headline, photo = _pick_fresh_promo_news(card, state)
    except Exception as e:
        log("warning", f"ready queue: prepare failed for card '{name}': {e}")
        return False
    if not photo:
        return False
    link = (card.get("link") or "").strip()
    effective_link = link or (photo.get("article_url") or "")
    hook = ""
    try:
        hook = (ai_write(BSKY_PROMO_NEWS_PROMPT.format(
            headline=(headline or topic)[:150],
            link=effective_link,
            tone=ARTICLE_TONES[card_tone(card)]),
            max_tokens=400) or "").strip()
    except Exception:
        hook = ""
    if not hook or hook == effective_link:
        # The AI failed: the headline itself is the caption (same
        # fallback as post time, rebuild #7.2) - never the bare link.
        hook = headline or ""
    q = _ready_queue(state)
    items = [it for it in (q.get(name) or []) if _ready_item_fresh(it)]
    items.append({
        "topic": topic,
        "headline": headline,
        "photo_url": photo.get("url", ""),
        "photo_source": photo.get("source") or "news",
        "photo_alt": photo.get("alt") or headline,
        "article_url": photo.get("article_url") or "",
        "hook": hook,
        "prepared_at": now_iso(),
    })
    q[name] = items[-READY_QUEUE_SIZE:]
    log("info", f"prepared ready post: '{headline[:60]}' for card "
                f"'{name}' (queue now {len(q[name])})")
    return True


def _ensure_ready_queue(card, state):
    """Top up a card's ready queue when a post slot is due within
    READY_PREPARE_WINDOW_MINUTES (or already due): prepare ahead so
    the post goes out ON TIME with a verified story + photo + caption
    already in hand. Nothing is prepared when no slot is near (the
    item would go stale). At most one failed prepare per run - a
    failure means the news pool has no photo right now, and retrying
    at once would just repeat the same search. Never raises."""
    name = card.get("name", "")
    try:
        _prune_ready_queue(state, name)
        q = _ready_queue(state)
        if len(q.get(name) or []) >= READY_QUEUE_SIZE:
            return
        due_soon = False
        if card_posts_per_day(card) <= 0 and not _parse_schedule_times(card):
            # Unlimited card: every run may post - keep the queue
            # topped up.
            due_soon = True
        else:
            try:
                due, _slots = card_post_due(card, state)
            except Exception:
                due = False
            if due:
                due_soon = True
            else:
                nxt = next_post_times_for_card(card, count=1)
                if nxt:
                    mins = (nxt[0] - now_utc().astimezone(USER_TZ)
                            ).total_seconds() / 60.0
                    if 0 <= mins <= READY_PREPARE_WINDOW_MINUTES:
                        due_soon = True
        if not due_soon:
            return
        while len(q.get(name) or []) < READY_QUEUE_SIZE:
            if not _prepare_ready_item(card, state):
                break
    except Exception as e:
        log("warning", f"ready queue: ensure failed for card '{name}': {e}")


def _take_ready_item(card, state):
    """Take the OLDEST fresh ready item for a card, ready to post NOW.
    Validates it again at post time (the story may have been posted by
    another path since it was prepared): freshness, topic cooldown,
    link+topic cooldown, caption cooldown, and the photo re-downloads
    (the file from prepare time is gone - each workflow run is a fresh
    runner, so the photo URL is stored and re-downloaded here, fast
    and re-verified). A failed validation DISCARDS the item and returns
    None (the caller falls back to preparing on the spot). Returns a
    dict with the ready item + local_path, or None. Does NOT remove
    the item - the caller removes it only after a successful post
    (_consume_ready_item), so a transient post failure keeps it for
    the next run. Never raises."""
    name = card.get("name", "")
    try:
        _prune_ready_queue(state, name)
        items = _ready_queue(state).get(name) or []
        if not items:
            return None
        item = items[0]
        headline = (item.get("headline") or "").strip()
        link = (card.get("link") or "").strip()
        effective_link = link or (item.get("article_url") or "")

        def _drop(reason):
            log("info", f"ready queue: discarding '{headline[:60]}' for "
                        f"card '{name}' - {reason}")
            _discard_ready_item(card, state, headline)

        if not headline:
            _drop("no headline stored")
            return None
        if _promo_topic_cooldown_left(state, headline) is not None:
            _drop("story posted since it was prepared (topic cooldown)")
            return None
        if _promo_link_topic_cooldown_left(state, effective_link,
                                           headline) is not None:
            _drop("story posted since it was prepared (link+topic cooldown)")
            return None
        hook = (item.get("hook") or "").strip()
        if hook:
            caption_id = _fit_bsky_text(hook, effective_link, cta="")
            if caption_id is None:
                _drop("stored caption's link is too long for Bluesky")
                return None
            if _promo_caption_cooldown_left(state, caption_id) is not None:
                _drop("caption posted since it was prepared (caption cooldown)")
                return None
        photo_url = (item.get("photo_url") or "").strip()
        if not photo_url:
            _drop("no photo URL stored")
            return None
        local = download_image(photo_url, headline)
        if not local:
            _drop("stored photo URL no longer downloads/verifies")
            return None
        out = dict(item)
        out["local_path"] = local
        return out
    except Exception as e:
        log("warning", f"ready queue: take failed for card '{name}': {e}")
        return None


# ---------------------------------------------------------------- rebuild #7.11
# ENTITY-BASED PHOTO FALLBACK: when no page about the exact event has
# a photo, search for the NAMED PERSON (or the leading entity) in the
# headline. A portrait of the person IS the right photo for a story
# about them, even when no page about the exact event carries one.
def _page_names_entity(page_url, page_title, entity):
    """Is the ENTITY (a person or place) the subject of the source
    page? The page's title/URL must contain the entity's words
    (stemmed). Returns (relevant, reason)."""
    words = {_stem_word(w) for w in re.findall(r"[a-z0-9]+",
                                               (entity or "").lower())}
    if not words:
        return False, "no entity to match"
    hay = ((page_title or "") + " " + (page_url or "")).lower()
    hay_words = {_stem_word(w) for w in re.findall(r"[a-z0-9]+", hay)}
    if words <= hay_words:
        return True, f"page names the entity ({entity})"
    return False, f"page does not name the entity ({entity})"


# Words that are never a photo entity: quote/adverb/filler words that
# commonly START a headline ("'Hopefully things get done'...") but
# name nothing a photo could show. Verbs are covered separately
# (_HEADLINE_VERB_STEMS, below) - a verb is never an entity either.
_ENTITY_JUNK_WORDS = frozenset(
    "hopefully wait breaking just watch live update updates updated "
    "exclusive finally actually really here there stunning shocking "
    "incredible amazing huge major big new top first latest urgent "
    "things thing done way ways time times day days week weeks year "
    "years month months today yesterday tomorrow now still back "
    "majority minority most many few several some all every each both".split())
_HEADLINE_VERB_STEMS = frozenset(
    _stem_word(v) for v in _HEADLINE_VERBS)


def _is_headline_verb(word):
    """True when a headline word is a verb - base form ("get", "say",
    "take") or 3rd-person form ("gets", "says", "takes"). A verb is
    never a photo entity."""
    low = (word or "").lower()
    if not low:
        return False
    if low in _HEADLINE_VERBS:
        return True
    if _stem_word(low) in _HEADLINE_VERB_STEMS:
        return True
    return low + "s" in _HEADLINE_VERBS or low + "es" in _HEADLINE_VERBS


def _photo_fallback_entities(topic):
    """Entities to search for a photo when the topical search fails:
    the named PERSON(s) in the headline first (a portrait of the
    person IS the right photo for a story about them), else the
    leading key entity (the first headline keyword that is not a
    junk word or a verb - usually a country, capital, institution
    or leader's surname). Returns up to 2 entity strings."""
    names = _headline_person_names(topic)
    if names:
        return names[:2]
    for w in re.split(r"[^A-Za-z0-9]+", topic or ""):
        if len(w) < 3:
            continue
        low = w.lower()
        if low in _PHOTO_QUERY_STOPWORDS:
            continue
        if low in _ENTITY_JUNK_WORDS:
            continue
        if _is_headline_verb(w):
            continue
        return [w]
    return []


def _try_photo_query(query, topic, vision, tried_downloads, relevance):
    """One photo-search query across all real-photo sources
    (Pexels / Pixabay / Openverse / Wikimedia / Google Images / Bing
    Images). relevance(page_url, page_title) -> (bool, reason) decides
    whether a candidate's source page is about the story. Every
    candidate still passes the real-photo check (valid JPEG/PNG,
    >=400px wide, not a bare logo) in download_image, and the Gemini
    vision gate. Returns (photo_dict_or_None, tried_downloads). Never
    raises."""
    cands = []
    for fn in (_pexels_photo, _pixabay_photo):
        try:
            found = fn(query)
        except Exception:
            found = None
        if found:
            cands.append(found)
    try:
        cands.extend(_openverse_photos(query, limit=PICK_MAX_PHOTO_CANDIDATES))
    except Exception:
        pass
    try:
        cands.extend(_wikimedia_photos(query, limit=PICK_MAX_PHOTO_CANDIDATES))
    except Exception:
        pass
    try:
        cands.extend(_google_images_photos(query, limit=4))
    except Exception:
        pass
    try:
        cands.extend(_bing_images_photos(query, limit=4))
    except Exception:
        pass
    for cand in cands:
        url = (cand or {}).get("url", "")
        if not url or _is_pollinations_url(url):
            continue
        if _is_logo_image_url(url):
            log("info", f"photo: rejected (logo/icon URL): {url[:100]}")
            continue
        page = ((cand.get("page_url") or "") + " | " +
                (cand.get("page_title") or "")).strip(" |")
        try:
            rel, rel_reason = relevance(cand.get("page_url"),
                                        cand.get("page_title"))
        except Exception:
            rel, rel_reason = False, "relevance check failed"
        if not rel:
            log("info", f"photo: rejected (irrelevant to "
                        f"'{topic[:50]}'): {url[:100]} "
                        f"(page: {page[:100]} - {rel_reason})")
            continue
        if tried_downloads >= MAX_REAL_PHOTO_DOWNLOADS:
            log("info", "photo: download budget reached "
                        f"({MAX_REAL_PHOTO_DOWNLOADS}) - stopping")
            return None, tried_downloads
        tried_downloads += 1
        local = download_image(url, topic)
        if local:
            gate = _vision_gate(local, topic, vision)
            if gate is False:
                log("info", f"photo: rejected (vision NO): {url[:100]}")
                continue
            if gate is None:
                # Rebuild #7.12: vision could not run (quota down) -
                # do NOT accept on the weak keyword match alone. A
                # flag / cartoon / clipart, or a photo whose source
                # page is not a news article about the story, is
                # rejected here; the next candidate is tried.
                ok, why = _photo_strict_when_vision_down(
                    url, cand.get("page_url"), cand.get("page_title"),
                    cand.get("alt"), topic)
                if not ok:
                    log("info", f"photo: rejected (vision down, strict "
                                f"check): {url[:100]} - {why}")
                    continue
            log("info", f"photo: ACCEPTED relevant photo for "
                        f"'{topic[:60]}': {url[:100]} "
                        f"(from {cand.get('source') or 'stock'}, "
                        f"query '{query}', page: {page[:100]} - "
                        f"{rel_reason})")
            return {"url": url, "source": cand.get("source") or "stock",
                    "alt": cand.get("alt") or topic, "local_path": local,
                    "page_url": cand.get("page_url") or "",
                    "page_title": cand.get("page_title") or ""}, tried_downloads
        log("info", f"photo: candidate rejected (download/verify failed): {url[:100]}")
    return None, tried_downloads


def _pick_fresh_promo_news(card, state):
    """Pick a FRESH news story for a promo post: (topic, headline, photo).
    Candidates: ONLY the user's two news categories (Rebuild #7.8,
    user order 2026-11-24 - USA political news and war news, rotating
    the starting category per post). The card's topic_override is the
    ONLY other allowed topic (an explicit user instruction). There is
    NO fallback to custom text, Bluesky trending or "breaking news".
    Rebuild #7.10 (user order): when a story has no usable photo,
    the picker tries the NEXT fresh story at once - up to 6 fresh
    stories per post attempt (PICK_MAX_STORIES), each with a full
    photo attempt (the article's own og:image, then a real-photo
    search). Only when ALL tried stories lack a photo does the run
    SKIP posting (a clean skip, logged) - a wrong-category post is
    worse than no post. Big-outlet stories are tried first, and a
    big outlet's own article page is fetched for its og:image. A
    real photo that carries a logo/text/watermark overlay is FINE.
    A story is fresh only
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
    gate must verify the photo shows that person. Rebuild #7.11:
    NON-VISUAL stories (survey/poll/analysis/opinion) are skipped
    EARLY, before the item/story budget - they almost never carry a
    photo, and the live 2026-11-24 failure burned the whole 6-story
    budget on Pew survey pieces; the pool is wider now (12 items per
    topic); a story already prepared in the ready queue is RESERVED
    and never stolen for another post; and the real-photo search falls
    back to the named PERSON / leading entity when the topical search
    finds nothing. Every candidate
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
    stories_tried = 0    # Rebuild #7.10: FRESH stories given a full
    # photo attempt this pick (og:image + optional fallback search).
    # The pick stops at PICK_MAX_STORIES - a story with no photo
    # never ends the run, only the budget does.
    tried_story_keys = set()  # canonical event keys already tried
    # this pick (the same story can appear in both categories' feeds
    # under different links) - never re-try one.
    for topic in topics:
        try:
            _verified, _sources, items = verify_news(topic)
        except Exception:
            continue
        if items:
            had_items = True
        seen = set()
        # Rebuild #7.10: big-outlet stories first (stable sort, so
        # RSS order is kept inside each group), and more items per
        # topic so the try-next-story loop has enough fresh stories.
        items = sorted(items or [],
                       key=lambda it: _big_outlet_rank(it.get("source"),
                                                       it.get("link")))
        for item in items[:PICK_MAX_ITEMS_PER_TOPIC]:
            if tried >= PICK_MAX_ITEMS:
                log("info", "promo: candidate budget reached "
                            f"({PICK_MAX_ITEMS} items) - stopping the search")
                break
            link = (item.get("link") or "").strip()
            if not link or link in seen:
                continue
            seen.add(link)
            headline = (item.get("title") or "").strip() or topic
            # Rebuild #7.11: a NON-VISUAL story (survey / poll /
            # analysis / opinion) almost never carries a real news
            # photo - skip it EARLY, before the item budget, so the
            # budget is spent on stories that can actually have
            # photos (the live 2026-11-24 failure burned the whole
            # 6-story budget on Pew survey pieces).
            if _is_non_visual_headline(headline):
                log("info", f"photo candidate: '{headline[:60]}' - "
                            "skipped (non-visual story: survey/poll/"
                            "analysis/opinion - no photo expected)")
                continue
            tried += 1
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
            # Rebuild #7.11: a story already prepared in the ready
            # queue is RESERVED - the picker must not steal it for
            # another post (it is waiting for its own slot).
            if _headline_in_ready_queue(state, headline):
                log("info", f"photo candidate: '{headline[:60]}' - "
                            "skipped (already prepared in the ready queue)")
                continue
            # Rebuild #7.10: the try-next-story loop. A FRESH story
            # (past both cooldowns) gets a full photo attempt and
            # counts against the story budget; the same event is
            # never tried twice in one pick.
            story_key = _norm_news_key(headline)
            if story_key in tried_story_keys:
                log("info", f"photo candidate: '{headline[:60]}' - "
                            "skipped (same story already tried this pick)")
                continue
            tried_story_keys.add(story_key)
            stories_tried += 1
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
            # Rebuild #7.10: a BIG-OUTLET story's own article page is
            # fetched for its og:image FIRST - resolve the Google
            # News link to the publisher's article, then read the
            # og:image from that page. Other stories use the link as
            # before (fetch_og_image resolves when it can).
            if _big_outlet_rank(src, link) == 0:
                article_url = _resolve_article_url(link)
                if article_url != link:
                    log("info", f"photo candidate: '{headline[:60]}' - "
                                f"big outlet ({src}), resolved to "
                                f"{urlparse(article_url).netloc}")
                img = fetch_og_image(article_url, topic=headline)
            else:
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
                    gate = _vision_gate(local, headline, vision)
                    if gate is False:
                        seen_imgs.add(img)
                        log("info", f"photo candidate: '{headline[:60]}' - "
                                    "rejected (vision NO - photo does not "
                                    "match the story)")
                    elif gate is None:
                        # Rebuild #7.12: vision down - the og:image
                        # must not pass on the keyword check alone.
                        # Only the junk-image signals apply here
                        # (fetch_og_image already verified the page
                        # is about the story).
                        ok, why = _photo_strict_when_vision_down(
                            img, link, None, "", headline,
                            require_title=False)
                        if not ok:
                            seen_imgs.add(img)
                            log("info", f"photo candidate: "
                                        f"'{headline[:60]}' - rejected "
                                        f"(vision down, strict check): "
                                        f"{why}")
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
            # Rebuild #7.10: this fresh story had no usable photo -
            # log it and move on to the NEXT story (the loop keeps
            # going until the story budget is used up - a no-photo
            # story never skips the run on its own).
            log("info", f"promo: story {stories_tried}/"
                        f"{PICK_MAX_STORIES} tried: '{headline[:60]}' - "
                        "no usable photo, trying the next story")
            fresh_no_photo = True
            if stories_tried >= PICK_MAX_STORIES:
                log("info", "promo: story budget reached "
                            f"({PICK_MAX_STORIES} fresh stories) - "
                            "stopping the search")
                break
        if tried >= PICK_MAX_ITEMS or stories_tried >= PICK_MAX_STORIES:
            break
    log("info", f"promo: photo search done - {tried} candidate(s) tried, "
                f"{stories_tried} fresh stor"
                f"{'y' if stories_tried == 1 else 'ies'} with a photo "
                f"attempt, {fallback_tries} real-photo search(es), "
                "no usable photo")
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
    extra = ""
    if card.get("type") == "reddit_post":
        extra = (" subreddit=r/" +
                 (card.get("subreddit") or "").strip().lstrip("r/"))
    if card.get("type") == "tumblr_post":
        extra = (" blog=" + (card.get("account_handle") or "").strip())
    if card.get("type") == "threads_post":
        extra = (" user_id=" + (card.get("account_handle") or "").strip())
    if card.get("type") == "mastodon_post":
        extra = (" instance=" + (card.get("account_handle") or "").strip())
    if card.get("type") == "telegram_post":
        extra = (" channel=" + (card.get("channel") or "").strip())
    if card.get("type") == "nostr_post":
        extra = (" npub=" + (card.get("account_handle") or "").strip())
    if card.get("type") == "lemmy_post":
        extra = (" community=c/" +
                 (card.get("community") or "").strip().lstrip("!").lstrip("c/"))
    if card.get("type") == "devto_post":
        extra = (" tags=" + ",".join(_devto_tags(card, "")) +
                 (" canonical=set" if _devto_canonical_url(card)
                  else " canonical=not-set"))
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
                f"replies/day={card_replies_per_day(card)}{extra}")


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
            # Rebuild #7.11: 12 items, not 8 - the wider story pool
            # (PICK_MAX_ITEMS_PER_TOPIC) needs the feed to actually
            # carry 12 stories per category.
            if len(items) >= 12:
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
    Returns (uri, url) or None. Rebuild #7.9: the text is hard-capped
    to 300 graphemes HERE, at the single send point, so no path can
    ever send an over-long post (run #33 died on a 570-grapheme
    caption that bypassed the fitter)."""
    text = _cap_bsky_text(text)
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
    """Reply to a Bluesky post. Returns the reply uri or None.
    Rebuild #7.9: same hard 300-grapheme cap as bluesky_post - a
    reply is a post too, and an uncapped AI reply (up to 400 tokens)
    would hit the same 400."""
    text = _cap_bsky_text(text)
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


# ---------------------------------------------------------------- Reddit
# Reddit posting + replies, same model as Bluesky (user order 2026-11-24).
# Reddit HAS a free OAuth API (script-type app): POST
# https://www.reddit.com/api/v1/access_token with HTTP Basic auth
# (client_id:client_secret), grant_type=password, username + password.
# The token lives 1 hour; re-auth on 401. Posts go INTO a subreddit
# (the card specifies which); each subreddit has its own rules, and
# repeatedly posting the same link is spam-risky - so every post uses
# a fresh Political/War story (same picker model as Bluesky) with a
# different title, and the per-card daily caps apply. Quora was NOT
# built: it has no public API (confirmed).
# Rate limit: 100 queries/min per OAuth client ID. New apps need
# approval under Reddit's Responsible Builder Policy.
REDDIT_TOKEN_URL = "https://www.reddit.com/api/v1/access_token"
REDDIT_API_BASE = "https://oauth.reddit.com"
REDDIT_MIN_POST_GAP_MINUTES = 5
# In-memory OAuth token cache: username -> (token, expires_at).
# Tokens live 1 hour; the cache is per run (the worker is short-lived).
_REDDIT_TOKENS = {}

LAST_REDDIT_SKIP = None


def list_reddit_accounts():
    """All Reddit accounts: the REDDIT_ACCOUNTS env secret (JSON list)
    or the single-account env vars. (The dashboard saves accounts
    encrypted into the secret, same sealed-box pattern as Bluesky.)"""
    return list(ENV_REDDIT_ACCOUNTS)


def _reddit_user_agent(username):
    # Reddit requires a descriptive User-Agent (not the default
    # python-requests one) or the API rejects the call.
    return f"automation-website/1.0 (by /u/{username})"


def _reddit_token(account):
    """OAuth access token for a Reddit account (script-type app).
    Returns the token string or None. Cached until shortly before
    expiry; a failed result is never cached. Logs only success or
    failure - never the token or any credential value."""
    username = (account or {}).get("username", "")
    cached = _REDDIT_TOKENS.get(username)
    if cached:
        token, expires_at = cached
        if expires_at > now_utc() + timedelta(seconds=30):
            return token
    try:
        r = requests.post(
            REDDIT_TOKEN_URL,
            auth=HTTPBasicAuth(account.get("client_id", ""),
                               account.get("client_secret", "")),
            data={"grant_type": "password",
                  "username": username,
                  "password": account.get("password", "")},
            headers={"User-Agent": _reddit_user_agent(username)},
            timeout=20)
    except Exception as e:
        log("warning", f"reddit token request failed for u/{username}: {e}")
        return None
    if r.status_code != 200:
        log("warning", f"reddit token request failed for u/{username}: "
                       f"HTTP {r.status_code}")
        return None
    try:
        data = r.json()
    except Exception:
        log("warning", f"reddit token response not JSON for u/{username}")
        return None
    token = data.get("access_token", "")
    if not token:
        log("warning", f"reddit token request returned no token for u/{username}")
        return None
    try:
        expires_in = int(data.get("expires_in") or 3600)
    except Exception:
        expires_in = 3600
    _REDDIT_TOKENS[username] = (
        token, now_utc() + timedelta(seconds=max(60, expires_in - 60)))
    log("info", f"reddit: got access token for u/{username}")
    return token


def reddit_request(account, method, path, **kwargs):
    """One authenticated Reddit API call. Returns the Response or None.
    On a 401 the cached token is dropped and the call is retried once
    with a fresh token. kwargs pass through to requests (params/data)."""
    username = (account or {}).get("username", "")
    headers = dict(kwargs.pop("headers", {}) or {})
    headers["User-Agent"] = _reddit_user_agent(username)
    url = REDDIT_API_BASE + path
    for attempt in (1, 2):
        token = _reddit_token(account)
        if not token:
            return None
        headers["Authorization"] = f"bearer {token}"
        try:
            r = requests.request(method, url, headers=headers, timeout=25,
                                 **kwargs)
        except Exception as e:
            log("warning", f"reddit {method} {path} failed: {e}")
            return None
        if r.status_code == 401 and attempt == 1:
            _REDDIT_TOKENS.pop(username, None)
            log("info", f"reddit: token expired for u/{username} - re-authenticating")
            continue
        return r
    return None


def reddit_submit(account, subreddit, title, url=None, text=None):
    """Submit a Reddit post. A link post (title + url) when url is
    given, else a text post (title + text). The title is hard-capped
    at 300 chars at this single send point. Returns
    (fullname, post_url) or None."""
    sub = (subreddit or "").strip().lstrip("r/").strip()
    if not sub:
        return None
    title = (title or "").strip()[:300]
    if not title:
        return None
    if url:
        payload = {"sr": sub, "kind": "link", "title": title,
                   "url": (url or "").strip()}
    else:
        payload = {"sr": sub, "kind": "self", "title": title,
                   "text": (text or "")[:10000]}
    r = reddit_request(account, "POST", "/api/submit", data=payload)
    if r is None or r.status_code != 200:
        log("warning", "reddit submit failed (HTTP "
                       f"{r.status_code if r is not None else 'no response'})")
        return None
    try:
        data = (r.json().get("json") or {})
    except Exception:
        log("warning", "reddit submit response not JSON")
        return None
    errors = data.get("errors") or []
    if errors:
        log("warning", f"reddit submit rejected: {errors[0][:2] if errors else errors}")
        return None
    d = data.get("data") or {}
    fullname = d.get("name", "")
    post_url = d.get("url", "")
    if not fullname:
        log("warning", "reddit submit returned no post id")
        return None
    log("info", f"reddit: posted to r/{sub}: {post_url or fullname}")
    return fullname, post_url


def reddit_comment(account, thing_id, text):
    """Reply to a Reddit post/comment (thing_id = fullname t3_/t1_).
    Text is hard-capped at 10,000 chars. Returns the comment
    fullname or None."""
    text = (text or "").strip()[:10000]
    if not text or not thing_id:
        return None
    r = reddit_request(account, "POST", "/api/comment",
                       data={"thing_id": thing_id, "text": text})
    if r is None or r.status_code != 200:
        log("warning", "reddit comment failed (HTTP "
                       f"{r.status_code if r is not None else 'no response'})")
        return None
    try:
        data = (r.json().get("json") or {})
    except Exception:
        log("warning", "reddit comment response not JSON")
        return None
    errors = data.get("errors") or []
    if errors:
        log("warning", f"reddit comment rejected: {errors[0][:2] if errors else errors}")
        return None
    d = data.get("data") or {}
    for thing in (d.get("things") or []):
        name = ((thing or {}).get("data") or {}).get("name", "")
        if name:
            return name
    return None


def reddit_own_posts_with_comments(account, username, subreddit, limit=25,
                                   since=None):
    """Our recent posts in a subreddit + their un-replied comments.
    Returns [{id, fullname, replies:[{id, fullname, author, text}]}].
    A comment is skipped when we already replied to it (a nested reply
    in the thread authored by our own username) - so a comment is never
    answered twice, even if the run state is lost. Mirrors
    bluesky_own_posts_with_replies."""
    sub = (subreddit or "").strip().lstrip("r/").strip()
    out = []
    if not sub:
        return out
    try:
        cap = int(limit or 25)
    except Exception:
        cap = 25
    cap = max(1, min(25, cap))
    r = reddit_request(account, "GET", f"/user/{username}/submitted",
                       params={"limit": 25})
    if r is None or r.status_code != 200:
        log("warning", "reddit own-posts fetch failed")
        return out
    try:
        children = (r.json().get("data") or {}).get("children") or []
    except Exception:
        return out
    scanned = 0
    for child in children:
        d = (child or {}).get("data") or {}
        if (d.get("subreddit") or "").lower() != sub.lower():
            continue
        created = d.get("created_utc") or 0
        try:
            ts = datetime.fromtimestamp(float(created), tz=UTC)
        except Exception:
            ts = None
        if since is not None and ts is not None and ts < since:
            continue
        scanned += 1
        if scanned > cap:
            break
        post_id = d.get("id", "")
        fullname = d.get("name", "")
        replies = []
        try:
            cr = reddit_request(account, "GET",
                                f"/r/{sub}/comments/{post_id}",
                                params={"depth": 2, "limit": 100})
            if cr is not None and cr.status_code == 200:
                listing = cr.json()
                comments = []
                if isinstance(listing, list) and len(listing) > 1:
                    comments = ((listing[1] or {}).get("data") or {}).get("children") or []
                for c in comments:
                    cd = (c or {}).get("data") or {}
                    if cd.get("author") == username:
                        continue
                    # Already answered? A nested reply by our username.
                    answered = False
                    nested = cd.get("replies")
                    if isinstance(nested, dict):
                        for rep in ((nested.get("data") or {}).get("children") or []):
                            rd = (rep or {}).get("data") or {}
                            if rd.get("author") == username:
                                answered = True
                                break
                    if answered:
                        continue
                    replies.append({"id": cd.get("id", ""),
                                    "fullname": cd.get("name", ""),
                                    "author": cd.get("author", ""),
                                    "text": (cd.get("body") or "")[:300]})
        except Exception as e:
            log("warning", f"reddit comments fetch failed for {post_id}: {e}")
        out.append({"id": post_id, "fullname": fullname, "replies": replies})
    return out


def reddit_hot_posts(subreddit, limit=10):
    """Hot posts in a subreddit, highest score first. Returns
    [{id, fullname, author, title, score, num_comments}]. Mirrors
    get_high_engagement_posts (hot posts are public - any login works,
    so the first Reddit account is used)."""
    sub = (subreddit or "").strip().lstrip("r/").strip()
    posts = []
    accounts = list_reddit_accounts()
    if not sub or not accounts:
        return posts
    r = reddit_request(accounts[0], "GET", f"/r/{sub}/hot",
                       params={"limit": 25})
    if r is None or r.status_code != 200:
        log("warning", f"reddit hot posts fetch failed for r/{sub}")
        return posts
    try:
        children = (r.json().get("data") or {}).get("children") or []
    except Exception:
        return posts
    for child in children:
        d = (child or {}).get("data") or {}
        try:
            score = int(d.get("score") or 0)
        except Exception:
            score = 0
        try:
            ncom = int(d.get("num_comments") or 0)
        except Exception:
            ncom = 0
        posts.append({"id": d.get("id", ""), "fullname": d.get("name", ""),
                      "author": d.get("author", ""),
                      "title": (d.get("title") or "")[:200],
                      "score": score, "num_comments": ncom})
    posts.sort(key=lambda x: x["score"], reverse=True)
    try:
        lim = int(limit or 10)
    except Exception:
        lim = 10
    return posts[:max(1, lim)]


def reddit_fresh_comments(account, subreddit, post_id, minutes=5):
    """Top-level comments on a post made within the last `minutes`
    minutes. Mirrors get_fresh_comments."""
    sub = (subreddit or "").strip().lstrip("r/").strip()
    fresh = []
    if not sub or not post_id:
        return fresh
    r = reddit_request(account, "GET", f"/r/{sub}/comments/{post_id}",
                       params={"depth": 1, "limit": 100})
    if r is None or r.status_code != 200:
        return fresh
    try:
        listing = r.json()
        comments = []
        if isinstance(listing, list) and len(listing) > 1:
            comments = ((listing[1] or {}).get("data") or {}).get("children") or []
    except Exception:
        return fresh
    cutoff = now_utc() - timedelta(minutes=minutes)
    for c in comments:
        d = (c or {}).get("data") or {}
        try:
            ts = datetime.fromtimestamp(float(d.get("created_utc") or 0), tz=UTC)
        except Exception:
            continue
        if ts >= cutoff:
            fresh.append({"id": d.get("id", ""),
                          "fullname": d.get("name", ""),
                          "author": d.get("author", ""),
                          "text": (d.get("body") or "")[:300]})
    return fresh


REDDIT_REPLY_PROMPT = """Write ONE short, natural, relevant Reddit reply in ENGLISH to
this comment. It must sound like a real person, not an ad. Do NOT repeat
the comment. Do NOT add any link. Keep it under 200 characters.

Comment: "{comment}"
Context (the post it was on): "{context}"
"""

REDDIT_OWN_REPLY_PROMPT = """Write ONE short, warm, natural Reddit reply in ENGLISH to
this comment on my post. It must sound like a real person, not an ad.
Do NOT repeat the comment. Do NOT add any link. Keep it under 200
characters.

Comment: "{comment}"
"""

REDDIT_TITLE_PROMPT = """Write ONE short, exciting Reddit post title in ENGLISH about this news story, that makes people want to click it. Sound like a real person sharing breaking news, not an ad. Keep it under 200 characters. Do NOT add a link.

News: {headline}
"""


def run_reddit_cycle(state, subreddit, reply_own=True, reply_others=True,
                     replies_per_run=0, lookback_days=7, card_name="",
                     account_username="", replies_per_day=0,
                     reply_never="", reply_only="", reply_skip_words=""):
    """Reply to comments for ONE Reddit card (same model as
    run_bluesky_cycle). Only the card's own account is used.
    - OWN posts: reply to EVERY unanswered comment (no per-run cap) -
      over runs the card answers all of them inside the lookback window.
    - OTHERS' posts: replies_per_run caps the replies per run (0 = no cap).
    - replies_per_day caps ALL replies this card sends in a day (0 = no cap).
    - Reddit replies NEVER carry the promo link (a link dropped in a
      reply reads as spam to subreddit moderators and risks a ban) -
      the link lives on the card's own posts. The card's link is not
      needed at all here, so no article is required either.
    Returns (own_replies_sent, others_replies_sent)."""
    accounts = list_reddit_accounts()
    if not accounts:
        log("info", "reddit cycle: no accounts configured")
        return 0, 0
    sub = (subreddit or "").strip().lstrip("r/").strip()
    if not sub:
        log("info", f"card '{card_name}': no subreddit set - skipping replies")
        return 0, 0
    if account_username:
        use_accounts = [a for a in accounts
                        if a["username"] == account_username]
        if not use_accounts:
            log("warning", f"reddit cycle: card '{card_name}' account "
                           f"'u/{account_username}' not found - skipping replies "
                           "(add that account first)")
            return 0, 0
    else:
        use_accounts = accounts[:1]
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

    # --- 1) Replies to fresh comments on hot posts (OTHERS).
    if reply_others is False:
        log("info", f"{tag}reddit replies to others are OFF for this card - skipping")
    else:
        hot = reddit_hot_posts(sub, limit=5)
        acc_idx = 0
        for post in hot:
            if not others_under_cap() or day_cap_reached():
                break
            acc = use_accounts[acc_idx % len(use_accounts)]
            acc_idx += 1
            if not reddit_account_enabled(acc["username"]):
                continue
            for comment in reddit_fresh_comments(acc, sub, post["id"], minutes=5):
                if not others_under_cap() or day_cap_reached():
                    break
                if comment["fullname"] in state["replied_comments"]:
                    continue
                ok, why = reply_allowed(comment["author"], comment["text"],
                                        filter_card)
                if not ok:
                    log("info", f"{tag}skipped reply to {comment['author']}: {why}")
                    continue
                if dry:
                    log("warning", f"[DRY RUN] {tag}would reply to "
                                   f"{comment['author']} (u/{acc['username']})")
                    continue
                reply_text = groq_text(REDDIT_REPLY_PROMPT.format(
                    comment=comment["text"], context=post["title"]),
                    max_tokens=400)
                if not reply_text:
                    continue
                uri = retry_with_backoff(
                    lambda: reddit_comment(acc, comment["fullname"], reply_text),
                    attempts=2, base_delay=5, label="reddit reply (others)")
                if uri:
                    state["replied_comments"].append(comment["fullname"])
                    record_reply(post["fullname"], comment["fullname"],
                                 reply_text, acc["username"])
                    record_card_reply_today(state, card_name)
                    others_done += 1
                    log("info", f"{tag}replied to {comment['author']} "
                                f"(hot post in r/{sub}, "
                                f"comment: '{comment['text'][:60]}') "
                                f"as u/{acc['username']}: '{reply_text[:80]}'")
                    time.sleep(2)
    # --- 2) Reply to comments on our OWN posts (ALL of them, lookback window).
    if reply_own is False:
        log("info", f"{tag}reddit replies to own posts are OFF for this card - skipping")
        return own_done, others_done
    own_cutoff = now_utc() - timedelta(days=lb)
    for acc in use_accounts:
        if day_cap_reached():
            break
        if not reddit_account_enabled(acc["username"]):
            continue
        if dry:
            log("warning", f"[DRY RUN] {tag}would check own-post comments "
                           f"from the last {lb} days (u/{acc['username']})")
            continue
        own_posts = reddit_own_posts_with_comments(
            acc, acc["username"], sub, limit=25, since=own_cutoff)
        pending = sum(len(o["replies"]) for o in own_posts)
        log("info", f"{tag}found {pending} un-replied comment(s) on "
                    f"{len(own_posts)} own post(s) from the last {lb} day(s) "
                    f"(u/{acc['username']})")
        for own in own_posts:
            for comment in own["replies"]:
                if day_cap_reached():
                    break
                if comment["fullname"] in state["replied_comments"]:
                    continue
                if comment["author"] == acc["username"]:
                    continue
                ok, why = reply_allowed(comment["author"], comment["text"],
                                        filter_card)
                if not ok:
                    log("info", f"{tag}skipped reply to {comment['author']}: {why}")
                    continue
                reply_text = groq_text(REDDIT_OWN_REPLY_PROMPT.format(
                    comment=comment["text"]), max_tokens=300)
                if not reply_text:
                    continue
                uri = retry_with_backoff(
                    lambda: reddit_comment(acc, comment["fullname"], reply_text),
                    attempts=2, base_delay=5, label="reddit reply (own)")
                if uri:
                    state["replied_comments"].append(comment["fullname"])
                    record_reply(own["fullname"], comment["fullname"],
                                 reply_text, acc["username"])
                    record_card_reply_today(state, card_name)
                    own_done += 1
                    log("info", f"{tag}replied to {comment['author']} on your "
                                f"post (comment: '{comment['text'][:60]}') "
                                f"as u/{acc['username']}: '{reply_text[:80]}'")
                    time.sleep(2)
    log("info", f"{tag}reply run done: {own_done} own + {others_done} others "
                f"replies sent (lookback {lb} day(s))")
    return own_done, others_done


def _pick_fresh_reddit_news(card, state):
    """Pick a FRESH news story for a Reddit post: (topic, headline,
    article_url). Same categories as the Bluesky promo picker (ONLY USA
    political news and war news, rotating; the card's topic_override is
    the only other allowed topic) and the same 24h per-topic / per-link
    cooldowns - but NO photo is needed (a Reddit link post is a title
    + a link, no image), so a story is picked as soon as it is fresh.
    Non-visual stories are skipped early (same as the Bluesky picker).
    Returns (None, None, None) when no fresh story exists;
    LAST_REDDIT_SKIP says why ("cooldown" or "no_news")."""
    global LAST_REDDIT_SKIP
    LAST_REDDIT_SKIP = None
    cat_topics = _rotated_promo_categories(state)
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
    tried_story_keys = set()
    for topic in topics:
        try:
            _verified, _sources, items = verify_news(topic)
        except Exception:
            continue
        if items:
            had_items = True
        seen = set()
        items = sorted(items or [],
                       key=lambda it: _big_outlet_rank(it.get("source"),
                                                       it.get("link")))
        for item in items[:PICK_MAX_ITEMS_PER_TOPIC]:
            link = (item.get("link") or "").strip()
            if not link or link in seen:
                continue
            seen.add(link)
            headline = (item.get("title") or "").strip() or topic
            if _is_non_visual_headline(headline):
                continue
            if _promo_topic_cooldown_left(state, headline) is not None:
                continue
            if _promo_link_topic_cooldown_left(
                    state, (card.get("link") or ""), headline) is not None:
                continue
            if _headline_in_ready_queue(state, headline):
                continue
            story_key = _norm_news_key(headline)
            if story_key in tried_story_keys:
                continue
            tried_story_keys.add(story_key)
            return topic, headline, link
    if not had_items:
        LAST_REDDIT_SKIP = "no_news"
        log("info", "reddit: no news available in Political / War - skipping")
    else:
        LAST_REDDIT_SKIP = "cooldown"
        log("info", "reddit: every fresh news story was already used "
                    "within 24h - cooldown, skipping")
    return None, None, None


def _reddit_gap_key(card):
    """The key the 5-minute no-burst gap is stored under: the Reddit
    username, not the card name (same rule as Bluesky - two cards
    sharing one account must not burst-post to it)."""
    if isinstance(card, dict):
        return (card.get("account_handle") or "").strip() or card.get("name", "")
    return str(card or "")


def _reddit_gap_left(state, username):
    """Time left on the 5-minute no-burst gap for a Reddit account,
    or None when it may post again."""
    last = (state.get("last_reddit_post_at") or {}).get(username or "")
    if not last:
        return None
    try:
        dt = datetime.fromisoformat(last)
        if dt.tzinfo is None:
            dt = dt.replace(tzinfo=UTC)
    except Exception:
        return None
    left = dt + timedelta(minutes=REDDIT_MIN_POST_GAP_MINUTES) - now_utc()
    return left if left.total_seconds() > 0 else None


def _record_reddit_post_at(state, username):
    """Remember that this Reddit account posted now (state.json, so
    the gap survives across worker runs)."""
    state.setdefault("last_reddit_post_at", {})[username or ""] = now_iso()


def record_reddit_post(state, username):
    """Count a Reddit post for this account today (per-account limits)."""
    counts = state.setdefault("reddit_post_counts", {})
    today = counts.setdefault(today_str(), {})
    today[username] = int(today.get(username, 0)) + 1
    for d in list(counts.keys()):
        try:
            if (now_utc().date() - datetime.strptime(d, "%Y-%m-%d").date()).days > 3:
                counts.pop(d, None)
        except Exception:
            counts.pop(d, None)


def posts_today_for_reddit_account(state, username):
    counts = state.get("reddit_post_counts", {})
    return int(counts.get(today_str(), {}).get(username, 0))


def _card_reddit_post(card, state):
    """Post ONE Reddit card. Returns True on success.
    The post is a LINK post to the card's subreddit: the title is an
    AI hook about a fresh Political/War news story (the headline
    itself when the AI is down, the card's own text when set) and the
    URL is the card's link (or the story's own URL when the card has
    no link). No photo is needed. Same 24h per-topic / per-link
    cooldowns as Bluesky (shared stores - the same story never goes
    to both Bluesky and Reddit on the same day) and the same 5-minute
    no-burst gap per account. A cooldown / no-news / no-subreddit
    skip is a clean no-op (LAST_REDDIT_SKIP)."""
    global LAST_REDDIT_SKIP
    LAST_REDDIT_SKIP = None
    name = card.get("name", "")
    sub = (card.get("subreddit") or "").strip().lstrip("r/").strip()
    if not sub:
        log("warning", f"card '{name}': no subreddit set - post skipped")
        LAST_REDDIT_SKIP = "no_subreddit"
        return False
    accs = [a for a in list_reddit_accounts()
            if not card.get("account_handle") or
            a["username"] == card["account_handle"]]
    if not accs:
        log("warning", f"card '{name}': no usable Reddit account - post skipped")
        return False
    link = (card.get("link") or "").strip()
    topic, headline, article_url = _pick_fresh_reddit_news(card, state)
    if not headline:
        log("warning", f"card '{name}': no fresh news - Reddit post skipped")
        return False
    effective_link = link or article_url
    if _promo_topic_cooldown_left(state, headline) is not None:
        log("info", f"card '{name}': news story already used within "
                    f"24h - cooldown, skipping")
        LAST_REDDIT_SKIP = "cooldown"
        return False
    if _promo_link_topic_cooldown_left(state, effective_link, headline) is not None:
        log("info", f"card '{name}': same link + same event within "
                    f"24h - cooldown, skipping")
        LAST_REDDIT_SKIP = "cooldown"
        return False
    title = (card.get("text") or "").strip()
    if not title:
        try:
            title = (ai_write(REDDIT_TITLE_PROMPT.format(headline=headline),
                              max_tokens=200) or "").strip()
        except Exception:
            title = ""
        if not title:
            title = headline
    title = title[:300]
    if is_dry_run():
        log("warning", f"[DRY RUN] card '{name}': would post to r/{sub} "
                       f"(u/{accs[0]['username']}) '{title[:60]}' -> "
                       f"{effective_link[:60]}")
        return True
    ok = False
    for acc in accs[:1]:
        if not reddit_account_enabled(acc["username"]):
            continue
        limit = reddit_account_posts_limit(acc["username"])
        if limit > 0 and posts_today_for_reddit_account(state, acc["username"]) >= limit:
            log("info", f"card '{name}': account u/{acc['username']} daily "
                        "limit reached - skipping")
            continue
        res = retry_with_backoff(
            lambda: reddit_submit(acc, sub, title, url=effective_link),
            attempts=2, base_delay=5, label="reddit submit")
        if res:
            fullname, post_url = res
            _record_promo_topic_posted(state, headline)
            _record_promo_link_topic_posted(state, effective_link, headline)
            _record_promo_account_posted(state, headline, acc["username"])
            record_reddit_post(state, acc["username"])
            _record_reddit_post_at(state, acc["username"])
            log("info", f"card '{name}': posted to r/{sub} as "
                        f"u/{acc['username']}: {post_url or fullname}")
            ok = True
            break
        log("warning", f"card '{name}': reddit submit failed")
    return ok


def _post_reddit_card(card, state, due_slots):
    """The posting loop for reddit_post cards. Returns (made, last_error).
    Mirrors _post_bsky_card: 5-minute gap per account, posts-per-run,
    due slots, day/week/month caps. Clean skips (cooldown, too soon,
    cap, no fresh news, no subreddit) are no-ops, not failures."""
    global LAST_REDDIT_SKIP
    name = card.get("name", "")
    dry = is_dry_run()
    made = 0
    cooldown_hit = False
    cap_hit = False
    gap_key = _reddit_gap_key(card)
    if not dry and _reddit_gap_left(state, gap_key) is not None:
        log("info", f"card '{name}': posted less than "
                    f"{REDDIT_MIN_POST_GAP_MINUTES} minutes ago - too soon, skipping")
        return 0, "too soon"
    while True:
        card = _refresh_card(card)
        log_card_settings(card)
        remaining = card_caps_remaining(state, name, card)
        if remaining is not None and remaining <= 0:
            log("info", f"card '{name}': post cap reached - skipping")
            cap_hit = True
            break
        if made >= card_posts_per_run(card):
            break
        if due_slots and made >= len(due_slots):
            break
        try:
            posted = _card_reddit_post(card, state)
        except Exception as e:
            log("error", f"card '{name}': post attempt failed: {e}")
            LAST_REDDIT_SKIP = None
            break
        if posted:
            made += 1
            if not dry:
                record_card_post(state, name)
                _record_reddit_post_at(state, gap_key)
        else:
            if LAST_REDDIT_SKIP == "cooldown":
                cooldown_hit = True
            break
    if made and not dry and due_slots:
        mark_slots_used(state, name, due_slots[:made])
    if cooldown_hit and made == 0:
        return 0, "cooldown"
    if cap_hit and made == 0:
        return 0, "post cap reached"
    if made == 0 and LAST_REDDIT_SKIP == "no_news":
        return 0, "no fresh news"
    if made == 0 and LAST_REDDIT_SKIP == "no_subreddit":
        return 0, "no subreddit set"
    return made, ("" if made else "post failed or skipped")


# ---------------------------------------------------------------- Tumblr
# Free, no review (verified 2026-11-25 against Tumblr's own API docs,
# github.com/tumblr/docs api.md, plus Breakreach's Oct 2026 check of
# the same docs): register an app at tumblr.com/oauth/apps, OAuth2
# scopes basic write offline_access, POST /v2/blog/{blog}/posts with
# the post in NPF (Neue Post Format) blocks. Photos upload in the
# SAME request as multipart/form-data: a "json" part first, then one
# file part per media identifier. A remote image URL does NOT work
# for a new photo (the docs only document media URLs for files
# already on Tumblr) - the worker uploads the verified photo bytes
# it already downloaded. Access tokens last 42 minutes (2,520s);
# each refresh returns a NEW access token AND a new refresh token
# (42 days). Rate: 1,000 calls/hour and 5,000/day per consumer key,
# 250 posts/day per user. The worker refreshes ONLY on a 401, never
# speculatively, and keeps refreshed tokens in memory for the rest
# of the run - a rotated refresh token is NEVER written to a repo
# file (state.json is committed back, so it must never hold a
# secret). If the stored refresh token stops working after a
# rotation, the log + health check say plainly to re-authorize in
# the Tumblr tab. Tumblr has NO public comment-reply API, so
# Tumblr cards post only - there is no reply cycle (unlike Reddit).
TUMBLR_TOKEN_URL = "https://api.tumblr.com/v2/oauth2/token"
TUMBLR_API_BASE = "https://api.tumblr.com"
TUMBLR_MIN_POST_GAP_MINUTES = 5
# In-memory OAuth2 token cache: blog -> (access_token, refresh_token,
# expires_at). Tokens live 42 minutes; the cache is per run (the
# worker is short-lived). Blogs whose refresh token rotated during
# this run (the new token differs from the stored one).
_TUMBLR_TOKENS = {}
_TUMBLR_ROTATED = set()

LAST_TUMBLR_SKIP = None


def list_tumblr_accounts():
    """All Tumblr accounts: the TUMBLR_ACCOUNTS env secret (JSON list)
    or the single-account env vars. (The dashboard saves accounts
    encrypted into the secret, same sealed-box pattern as Bluesky.)"""
    return list(ENV_TUMBLR_ACCOUNTS)


def _tumblr_user_agent():
    # Tumblr requires a consistent User-Agent per app (it can
    # suspend apps whose User-Agent changes) - one fixed value.
    return "automation-website/1.0"


def _tumblr_blog_key(account):
    return ((account or {}).get("blog") or "").strip()


def _tumblr_token(account):
    """Current access token for a Tumblr account: the cached
    (refreshed) token while it is valid, else the stored token from
    the secret. Returns the token string or ''. Never logs a token."""
    blog = _tumblr_blog_key(account)
    cached = _TUMBLR_TOKENS.get(blog)
    if cached:
        token, _refresh, expires_at = cached
        if token and expires_at > now_utc() + timedelta(seconds=30):
            return token
    return (account or {}).get("access_token", "") or ""


def _tumblr_refresh(account):
    """Refresh a Tumblr account's access token (grant_type=
    refresh_token). Returns the new access token or None. The new
    refresh token is cached in memory for the rest of this run (so
    later posts in the same run reuse it) and NEVER written to disk:
    state.json is committed back to the repo, so it must never hold
    a secret. When Tumblr issues a different refresh token than the
    one stored, the blog is marked rotated and the log says plainly
    that the stored refresh token may stop working - re-authorize
    in the Tumblr tab if the next run fails to refresh. Logs only
    success or failure - never any token or credential value."""
    blog = _tumblr_blog_key(account)
    cached = _TUMBLR_TOKENS.get(blog)
    refresh_token = ""
    if cached and cached[1]:
        refresh_token = cached[1]
    if not refresh_token:
        refresh_token = (account or {}).get("refresh_token", "") or ""
    if not refresh_token:
        log("warning", f"tumblr: no refresh token for blog '{blog}' - "
                       "re-authorize in the Tumblr tab")
        return None
    try:
        r = requests.post(
            TUMBLR_TOKEN_URL,
            data={"grant_type": "refresh_token",
                  "client_id": account.get("client_id", ""),
                  "client_secret": account.get("client_secret", ""),
                  "refresh_token": refresh_token},
            headers={"User-Agent": _tumblr_user_agent()},
            timeout=20)
    except Exception as e:
        log("warning", f"tumblr token refresh failed for blog '{blog}': {e}")
        return None
    if r.status_code != 200:
        try:
            err = (r.json() or {}).get("error", "")
        except Exception:
            err = ""
        log("warning", f"tumblr token refresh failed for blog '{blog}': "
                       f"HTTP {r.status_code}"
                       + (" (invalid_grant - the stored refresh token "
                          "no longer works, re-authorize in the Tumblr tab)"
                          if err == "invalid_grant" else ""))
        return None
    try:
        data = r.json()
    except Exception:
        log("warning", f"tumblr token refresh response not JSON for blog '{blog}'")
        return None
    token = data.get("access_token", "")
    if not token:
        log("warning", f"tumblr token refresh returned no token for blog '{blog}'")
        return None
    new_refresh = data.get("refresh_token", "") or refresh_token
    try:
        expires_in = int(data.get("expires_in") or 2520)
    except Exception:
        expires_in = 2520
    _TUMBLR_TOKENS[blog] = (
        token, new_refresh,
        now_utc() + timedelta(seconds=max(60, expires_in - 60)))
    if new_refresh != refresh_token:
        _TUMBLR_ROTATED.add(blog)
        log("warning", f"tumblr: Tumblr issued a new refresh token for "
                       f"blog '{blog}' - the stored refresh token may "
                       "stop working; if the next run fails to refresh, "
                       "re-authorize in the Tumblr tab")
    log("info", f"tumblr: refreshed access token for blog '{blog}'")
    return token


def tumblr_request(account, method, path, **kwargs):
    """One authenticated Tumblr API call. Returns the Response or None.
    On a 401 the token is refreshed and the call is retried once with
    the fresh token. kwargs pass through to requests (params/data/
    files). The User-Agent is fixed per app (Tumblr suspends apps
    whose User-Agent changes)."""
    blog = _tumblr_blog_key(account)
    headers = dict(kwargs.pop("headers", {}) or {})
    headers["User-Agent"] = _tumblr_user_agent()
    url = TUMBLR_API_BASE + path
    for attempt in (1, 2):
        token = _tumblr_token(account)
        if not token:
            return None
        headers["Authorization"] = f"Bearer {token}"
        try:
            r = requests.request(method, url, headers=headers, timeout=25,
                                 **kwargs)
        except Exception as e:
            log("warning", f"tumblr {method} {path} failed: {e}")
            return None
        if r.status_code == 401 and attempt == 1:
            _TUMBLR_TOKENS.pop(blog, None)
            log("info", f"tumblr: token expired for blog '{blog}' - refreshing")
            if not _tumblr_refresh(account):
                return None
            continue
        return r
    return None


def _tumblr_tags(topic):
    """NPF tags for a post, from the picker's category topic:
    Political news -> news, politics, usa; war news -> news, war.
    Returned as one comma-separated string, without '#'."""
    t = (topic or "").lower()
    if "war" in t:
        return "news, war"
    return "news, politics, usa"


def _tumblr_npf_body(headline, hook, link, image_mime, topic=""):
    """The NPF post body for POST /v2/blog/{blog}/posts: a heading
    text block (the headline), an image block (media identifier
    'photo1', matched by the multipart file part), the hook as a text
    block, and a link block to the story. Pure function (no I/O) -
    unit-tested. Caps are enforced here, at this single send point:
    headline 300 chars, hook 400 chars (Tumblr allows 4,096 code
    points per text block)."""
    headline = (headline or "").strip()[:300]
    hook = (hook or "").strip()[:400]
    link = (link or "").strip()
    content = []
    if headline:
        content.append({"type": "text", "subtype": "heading1",
                        "text": headline})
    content.append({"type": "image", "media": [
        {"type": image_mime or "image/jpeg", "identifier": "photo1"}]})
    if hook:
        content.append({"type": "text", "text": hook})
    if link:
        content.append({"type": "link", "url": link, "title": headline})
    body = {"content": content, "state": "published",
            "tags": _tumblr_tags(topic)}
    if link:
        body["source_url"] = link
    return body


def tumblr_submit(account, blog, headline, hook, link, image_path,
                  topic=""):
    """Publish one Tumblr post: NPF content + the verified photo
    bytes as multipart/form-data (json part first, then the 'photo1'
    file part). Returns (post_id, post_url) or None. The photo must
    already be downloaded + verified (download_image only ever
    produces .jpg/.png, both accepted by Tumblr)."""
    blog = (blog or "").strip()
    if not blog:
        return None
    if not image_path or not os.path.exists(image_path):
        log("warning", "tumblr submit failed: no verified photo file")
        return None
    mime = "image/png" if str(image_path).lower().endswith(".png") \
        else "image/jpeg"
    try:
        with open(image_path, "rb") as f:
            img_bytes = f.read()
    except Exception as e:
        log("warning", f"tumblr submit failed: cannot read photo: {e}")
        return None
    if len(img_bytes) < 1000:
        log("warning", "tumblr submit failed: photo file too small")
        return None
    body = _tumblr_npf_body(headline, hook, link, mime, topic)
    fname = os.path.basename(image_path) or "photo.jpg"
    files = {"json": (None, json.dumps(body), "application/json"),
             "photo1": (fname, img_bytes, mime)}
    r = tumblr_request(account, "POST", f"/v2/blog/{blog}/posts",
                       files=files)
    if r is None or r.status_code != 201:
        log("warning", "tumblr submit failed (HTTP "
                       f"{r.status_code if r is not None else 'no response'})")
        return None
    try:
        data = r.json()
    except Exception:
        log("warning", "tumblr submit response not JSON")
        return None
    post_id = str(((data or {}).get("response") or {}).get("id", ""))
    if not post_id:
        log("warning", "tumblr submit returned no post id")
        return None
    post_url = ""
    if "." not in blog and not blog.startswith("t:"):
        post_url = f"https://{blog}.tumblr.com/post/{post_id}"
    log("info", f"tumblr: posted to {blog}: {post_url or post_id}")
    return post_id, post_url


TUMBLR_ACCOUNT_SETTINGS_PATH = os.path.join(DATA_DIR, "tumblr_accounts.json")


def get_tumblr_account_settings():
    """Per-account settings from data/tumblr_accounts.json (public, no
    passwords): [{blog, enabled, posts_per_day}]. Missing file = all
    enabled. Kept in its own file (not accounts.json) so saving
    Bluesky/Reddit controls can never wipe Tumblr entries and vice
    versa - the dashboard writes this file from the Tumblr tab."""
    if not os.path.exists(TUMBLR_ACCOUNT_SETTINGS_PATH):
        return {}
    try:
        with open(TUMBLR_ACCOUNT_SETTINGS_PATH, "r", encoding="utf-8") as f:
            data = json.load(f)
        if isinstance(data, list):
            return {a["blog"]: a for a in data
                    if isinstance(a, dict) and a.get("blog")}
        if isinstance(data, dict):
            return data
    except Exception as e:
        log("warning", f"tumblr_accounts.json load failed: {e}")
    return {}


def tumblr_account_enabled(blog):
    cfg = get_tumblr_account_settings().get(blog)
    if not cfg:
        return True
    return cfg.get("enabled", True) is not False


def tumblr_account_posts_limit(blog):
    cfg = get_tumblr_account_settings().get(blog)
    if not cfg:
        return 0
    try:
        return int(cfg.get("posts_per_day") or 0)
    except Exception:
        return 0


TUMBLR_CAPTION_PROMPT = """Write ONE short, exciting Tumblr post in ENGLISH about this news story, that makes people want to click the link below it. Sound like a real person sharing breaking news, not an ad. Keep it under 400 characters. Do NOT add the link or a call-to-action yourself - they are added after your text.
Style: {tone}
News: {headline}
Link: {link}
"""


def _tumblr_gap_key(card):
    """The key the 5-minute no-burst gap is stored under: the Tumblr
    blog, not the card name (same rule as Bluesky/Reddit - two cards
    sharing one blog must not burst-post to it)."""
    if isinstance(card, dict):
        return (card.get("account_handle") or "").strip() or card.get("name", "")
    return str(card or "")


def _tumblr_gap_left(state, blog):
    """Time left on the 5-minute no-burst gap for a Tumblr blog,
    or None when it may post again."""
    last = (state.get("last_tumblr_post_at") or {}).get(blog or "")
    if not last:
        return None
    try:
        dt = datetime.fromisoformat(last)
        if dt.tzinfo is None:
            dt = dt.replace(tzinfo=UTC)
    except Exception:
        return None
    left = dt + timedelta(minutes=TUMBLR_MIN_POST_GAP_MINUTES) - now_utc()
    return left if left.total_seconds() > 0 else None


def _record_tumblr_post_at(state, blog):
    """Remember that this Tumblr blog posted now (state.json, so
    the gap survives across worker runs)."""
    state.setdefault("last_tumblr_post_at", {})[blog or ""] = now_iso()


def record_tumblr_post(state, blog):
    """Count a Tumblr post for this blog today (per-blog limits)."""
    counts = state.setdefault("tumblr_post_counts", {})
    today = counts.setdefault(today_str(), {})
    today[blog] = int(today.get(blog, 0)) + 1
    for d in list(counts.keys()):
        try:
            if (now_utc().date() - datetime.strptime(d, "%Y-%m-%d").date()).days > 3:
                counts.pop(d, None)
        except Exception:
            counts.pop(d, None)


def posts_today_for_tumblr_account(state, blog):
    counts = state.get("tumblr_post_counts", {})
    return int(counts.get(today_str(), {}).get(blog, 0))


def _card_tumblr_post(card, state):
    """Post ONE Tumblr card. Returns True on success.
    The post is an NPF post to the card's blog: a heading (the fresh
    story's headline), the story's VERIFIED real photo (uploaded as
    multipart bytes - Tumblr does not take a remote image URL), a
    hook caption, and a link block to the story (the card's link, or
    the story's own URL when the card has no link). The story comes
    from the SAME picker as Bluesky (_pick_fresh_promo_news) and the
    SAME shared 24h per-topic / per-link cooldown stores are
    recorded, so the same story never goes to Bluesky, Reddit and
    Tumblr on the same day. No verified photo = skip (LAST_TUMBLR_SKIP
    'no_photo'), never text-only. Same 5-minute no-burst gap per
    blog. A cooldown / no-news / no-photo skip is a clean no-op."""
    global LAST_TUMBLR_SKIP
    LAST_TUMBLR_SKIP = None
    name = card.get("name", "")
    accs = [a for a in list_tumblr_accounts()
            if not card.get("account_handle") or
            a["blog"] == card["account_handle"]]
    if not accs:
        log("warning", f"card '{name}': no usable Tumblr account - post skipped")
        return False
    link = (card.get("link") or "").strip()
    topic, headline, photo = _pick_fresh_promo_news(card, state)
    if not photo:
        # _pick_fresh_promo_news already logged why (LAST_BSKY_SKIP).
        log("warning", f"card '{name}': no photo, skipped - Tumblr post "
                       "needs a verified real news photo")
        LAST_TUMBLR_SKIP = {"no_photo": "no_photo", "no_news": "no_news"}.get(
            LAST_BSKY_SKIP, "cooldown")
        return False
    headline = headline or topic
    effective_link = link or (photo.get("article_url") or "")
    if _promo_topic_cooldown_left(state, headline) is not None:
        log("info", f"card '{name}': news story already used within "
                    f"24h - cooldown, skipping")
        LAST_TUMBLR_SKIP = "cooldown"
        return False
    if _promo_link_topic_cooldown_left(state, effective_link, headline) is not None:
        log("info", f"card '{name}': same link + same event within "
                    f"24h - cooldown, skipping")
        LAST_TUMBLR_SKIP = "cooldown"
        return False
    image_path = (photo or {}).get("local_path", "")
    if not image_path or not os.path.exists(image_path):
        log("warning", f"card '{name}': no photo, skipped - verified photo "
                       "file is missing")
        LAST_TUMBLR_SKIP = "no_photo"
        return False
    tone_text = ARTICLE_TONES[card_tone(card)]
    text = (card.get("text") or "").strip()
    if not text:
        try:
            text = (ai_write(
                TUMBLR_CAPTION_PROMPT.format(
                    headline=headline[:150], link=effective_link,
                    tone=tone_text), max_tokens=400) or "").strip()
        except Exception:
            text = ""
        if not text:
            text = headline
    text = text[:400]
    if is_dry_run():
        log("warning", f"[DRY RUN] card '{name}': would post to "
                       f"{accs[0]['blog']} '{headline[:60]}' -> "
                       f"{effective_link[:60]}")
        return True
    ok = False
    for acc in accs[:1]:
        blog = acc["blog"]
        if not tumblr_account_enabled(blog):
            continue
        limit = tumblr_account_posts_limit(blog)
        if limit > 0 and posts_today_for_tumblr_account(state, blog) >= limit:
            log("info", f"card '{name}': blog {blog} daily limit "
                        "reached - skipping")
            continue
        res = retry_with_backoff(
            lambda: tumblr_submit(acc, blog, headline, text,
                                  effective_link, image_path, topic),
            attempts=2, base_delay=5, label="tumblr submit")
        if res:
            post_id, post_url = res
            _record_promo_topic_posted(state, headline)
            _record_promo_link_topic_posted(state, effective_link, headline)
            _record_promo_account_posted(state, headline, blog)
            record_tumblr_post(state, blog)
            _record_tumblr_post_at(state, blog)
            if blog in _TUMBLR_ROTATED:
                # Timestamp only (never a token value): the dashboard
                # can show that this blog's refresh token rotated.
                state.setdefault("tumblr_refresh_rotated_at", {})[blog] = now_iso()
            log("info", f"card '{name}': posted to {blog}: "
                        f"{post_url or post_id}")
            ok = True
            break
        log("warning", f"card '{name}': tumblr submit failed")
    return ok


def _post_tumblr_card(card, state, due_slots):
    """The posting loop for tumblr_post cards. Returns (made, last_error).
    Mirrors _post_reddit_card: 5-minute gap per blog, posts-per-run,
    due slots, day/week/month caps. Clean skips (cooldown, too soon,
    cap, no fresh news, no photo) are no-ops, not failures."""
    global LAST_TUMBLR_SKIP
    name = card.get("name", "")
    dry = is_dry_run()
    made = 0
    cooldown_hit = False
    cap_hit = False
    gap_key = _tumblr_gap_key(card)
    if not dry and _tumblr_gap_left(state, gap_key) is not None:
        log("info", f"card '{name}': posted less than "
                    f"{TUMBLR_MIN_POST_GAP_MINUTES} minutes ago - too soon, skipping")
        return 0, "too soon"
    while True:
        card = _refresh_card(card)
        log_card_settings(card)
        remaining = card_caps_remaining(state, name, card)
        if remaining is not None and remaining <= 0:
            log("info", f"card '{name}': post cap reached - skipping")
            cap_hit = True
            break
        if made >= card_posts_per_run(card):
            break
        if due_slots and made >= len(due_slots):
            break
        try:
            posted = _card_tumblr_post(card, state)
        except Exception as e:
            log("error", f"card '{name}': post attempt failed: {e}")
            LAST_TUMBLR_SKIP = None
            break
        if posted:
            made += 1
            if not dry:
                record_card_post(state, name)
                _record_tumblr_post_at(state, gap_key)
        else:
            if LAST_TUMBLR_SKIP == "cooldown":
                cooldown_hit = True
            break
    if made and not dry and due_slots:
        mark_slots_used(state, name, due_slots[:made])
    if cooldown_hit and made == 0:
        return 0, "cooldown"
    if cap_hit and made == 0:
        return 0, "post cap reached"
    if made == 0 and LAST_TUMBLR_SKIP == "no_photo":
        return 0, "no photo, skipped"
    if made == 0 and LAST_TUMBLR_SKIP == "no_news":
        return 0, "no fresh news"
    return made, ("" if made else "post failed or skipped")


# ---------------------------------------------------------------- Threads
# Free, no review for your OWN account (verified 2026-11-25 against
# Meta's own Threads API docs, developers.facebook.com/documentation/
# threads/get-started + /posts): create a Meta app with the Threads
# use case (use the THREADS app ID + secret, not the app's main
# ones), permissions threads_basic + threads_content_publish. Until
# the app passes App Review, only Threads testers on the app can
# grant the permissions - the user adds themself as a Threads tester
# (App Dashboard > App roles > Roles > Add People > Threads Tester)
# and accepts the invite in Threads settings, so NO App Review is
# needed for their own account. OAuth: authorize window at
# threads.com/oauth/authorize -> 1h short-lived token -> exchange
# for a 60-day long-lived token (GET /access_token with
# grant_type=th_exchange_token). Publishing is TWO calls, same shape
# as Instagram: (1) POST /v1.0/{user-id}/threads creates a media
# container (media_type TEXT/IMAGE, text, image_url), (2) POST
# /v1.0/{user-id}/threads_publish with creation_id publishes it.
# Meta recommends waiting ~30s between the two so the container is
# processed (the worker polls the container status and publishes as
# soon as it is FINISHED, falling back to the full wait). Limits:
# 500 characters per post, max 5 links, 250 posts per profile per
# 24h. Media: Threads downloads the image from a PUBLIC URL - the
# worker uses the photo's ORIGINAL public URL (the news article's
# og:image / search-result URL it downloaded from), never uploads
# the image anywhere itself. If no public URL is available the post
# goes out TEXT-only (never a skipped run for that reason alone).
# The worker refreshes a long-lived token ONLY when it is at least
# 24 hours old (age from token_obtained_at, recorded by the
# dashboard authorize helper) or on a 401, and keeps refreshed
# tokens in memory for the rest of the run - a rotated token is
# NEVER written to a repo file (state.json is committed back, so it
# must never hold a secret). If the stored token stops working
# after a rotation, the log + health check say plainly to
# re-authorize in the Threads tab. Threads HAS reply endpoints
# (threads_read_replies / threads_manage_replies), but they need two
# extra permissions and a per-post reply-fetch loop - v1 is
# POST-ONLY, like Tumblr (no reply API was built for it either).
# Replies are a possible follow-up, not part of this build.
THREADS_API_BASE = "https://graph.threads.net"
THREADS_MIN_POST_GAP_MINUTES = 5
THREADS_MAX_TEXT_CHARS = 500
THREADS_CONTAINER_WAIT_SECONDS = 30
THREADS_TOKEN_MIN_AGE_TO_REFRESH_HOURS = 24
THREADS_TOKEN_LIFETIME_SECONDS = 5184000  # 60 days
# In-memory OAuth token cache: user_id -> (access_token, expires_at,
# obtained_at). Tokens live 60 days; the cache is per run (the
# worker is short-lived). User IDs whose token rotated during this
# run, and user IDs already age-checked this run (the 24h refresh
# must fire at most once per run per account).
_THREADS_TOKENS = {}
_THREADS_ROTATED = set()
_THREADS_AGE_CHECKED = set()

LAST_THREADS_SKIP = None


def list_threads_accounts():
    """All Threads accounts: the THREADS_ACCOUNTS env secret (JSON list)
    or the single-account env vars. (The dashboard saves accounts
    encrypted into the secret, same sealed-box pattern as Bluesky.)"""
    return list(ENV_THREADS_ACCOUNTS)


def _threads_user_key(account):
    return ((account or {}).get("user_id") or "").strip()


def _threads_token_age_hours(account):
    """Age in hours of the stored long-lived token, from the
    token_obtained_at the dashboard authorize helper recorded - or
    None when the age is unknown (token pasted by hand: refresh only
    on a 401, never speculatively)."""
    raw = (account or {}).get("token_obtained_at", "") or ""
    if not raw:
        return None
    try:
        dt = datetime.fromisoformat(str(raw))
        if dt.tzinfo is None:
            dt = dt.replace(tzinfo=UTC)
    except Exception:
        return None
    return (now_utc() - dt).total_seconds() / 3600.0


def _threads_token(account):
    """Current access token for a Threads account: the cached
    (refreshed) token while it is valid, else the stored token from
    the secret. Returns the token string or ''. Never logs a token."""
    uid = _threads_user_key(account)
    cached = _THREADS_TOKENS.get(uid)
    if cached:
        token, expires_at, _obtained = cached
        if token and expires_at > now_utc() + timedelta(seconds=30):
            return token
    return (account or {}).get("access_token", "") or ""


def _threads_refresh(account):
    """Refresh a Threads account's long-lived token (GET
    /refresh_access_token with grant_type=th_refresh_token). Returns
    the new access token or None. The new token is cached in memory
    for the rest of this run (so later posts in the same run reuse
    it) and NEVER written to disk: state.json is committed back to
    the repo, so it must never hold a secret. When Threads issues a
    different token than the one stored, the user is marked rotated
    and the log says plainly that the stored token may stop working
    - re-authorize in the Threads tab if the next run fails. Logs
    only success or failure - never any token or credential value."""
    uid = _threads_user_key(account)
    cached = _THREADS_TOKENS.get(uid)
    current = ""
    if cached and cached[0]:
        current = cached[0]
    if not current:
        current = (account or {}).get("access_token", "") or ""
    if not current:
        log("warning", f"threads: no access token for user '{uid}' - "
                       "re-authorize in the Threads tab")
        return None
    try:
        r = requests.get(
            THREADS_API_BASE + "/refresh_access_token",
            params={"grant_type": "th_refresh_token",
                    "access_token": current},
            timeout=20)
    except Exception as e:
        log("warning", f"threads token refresh failed for user '{uid}': {e}")
        return None
    if r.status_code != 200:
        try:
            err = (r.json() or {}).get("error", {})
            err = err.get("message", "") if isinstance(err, dict) else str(err)
        except Exception:
            err = ""
        log("warning", f"threads token refresh failed for user '{uid}': "
                       f"HTTP {r.status_code}"
                       + (" (the stored token no longer works, "
                          "re-authorize in the Threads tab)"
                          if r.status_code in (400, 401) else ""))
        return None
    try:
        data = r.json()
    except Exception:
        log("warning", f"threads token refresh response not JSON for user '{uid}'")
        return None
    token = data.get("access_token", "")
    if not token:
        log("warning", f"threads token refresh returned no token for user '{uid}'")
        return None
    try:
        expires_in = int(data.get("expires_in") or THREADS_TOKEN_LIFETIME_SECONDS)
    except Exception:
        expires_in = THREADS_TOKEN_LIFETIME_SECONDS
    _THREADS_TOKENS[uid] = (
        token, now_utc() + timedelta(seconds=max(60, expires_in - 60)),
        now_utc())
    if token != current:
        _THREADS_ROTATED.add(uid)
        log("warning", f"threads: Threads issued a new access token for "
                       f"user '{uid}' - the stored token may stop "
                       "working; if the next run fails to refresh, "
                       "re-authorize in the Threads tab")
    log("info", f"threads: refreshed access token for user '{uid}'")
    return token


def _threads_refresh_if_old(account):
    """Refresh the token when it is at least 24 hours old (and its
    age is known), at most once per run per account. Returns True
    when a refresh was attempted. A failed refresh never blocks the
    post - the stored token may still work until its 60 days end."""
    uid = _threads_user_key(account)
    if uid in _THREADS_AGE_CHECKED:
        return False
    _THREADS_AGE_CHECKED.add(uid)
    age = _threads_token_age_hours(account)
    if age is None or age < THREADS_TOKEN_MIN_AGE_TO_REFRESH_HOURS:
        return False
    log("info", f"threads: token for user '{uid}' is "
                f"{int(age)}h old - refreshing")
    _threads_refresh(account)
    return True


def threads_request(account, method, path, **kwargs):
    """One authenticated Threads API call. Returns the Response or None.
    The access token is sent exactly as Meta's docs show it - as the
    access_token request parameter (POST data / GET query) - never as
    a Bearer header. On a 401 the token is refreshed and the call is
    retried once with the fresh token. kwargs pass through to
    requests (params/data). A token at least 24h old is refreshed
    once per run before the first call (see _threads_refresh_if_old)."""
    uid = _threads_user_key(account)
    _threads_refresh_if_old(account)
    url = THREADS_API_BASE + path
    for attempt in (1, 2):
        token = _threads_token(account)
        if not token:
            return None
        if (method or "GET").upper() == "GET":
            params = dict(kwargs.pop("params", {}) or {})
            params["access_token"] = token
            kwargs["params"] = params
        else:
            data = dict(kwargs.pop("data", {}) or {})
            data["access_token"] = token
            kwargs["data"] = data
        try:
            r = requests.request(method, url, timeout=25, **kwargs)
        except Exception as e:
            log("warning", f"threads {method} {path} failed: {e}")
            return None
        if r.status_code == 401 and attempt == 1:
            _THREADS_TOKENS.pop(uid, None)
            log("info", f"threads: token expired for user '{uid}' - refreshing")
            if not _threads_refresh(account):
                return None
            continue
        return r
    return None


def _fit_threads_text(hook, link):
    """The Threads post text: hook + link, hard-capped at 500
    characters at this single send point (Threads' limit; the link
    is never cut - the hook is trimmed to make room). Pure function
    (no I/O) - unit-tested."""
    hook = (hook or "").strip()
    link = (link or "").strip()
    if not link:
        return hook[:THREADS_MAX_TEXT_CHARS]
    text = hook + "\n" + link if hook else link
    if len(text) <= THREADS_MAX_TEXT_CHARS:
        return text
    room = THREADS_MAX_TEXT_CHARS - len(link) - 1
    if room <= 0:
        return link[:THREADS_MAX_TEXT_CHARS]
    return hook[:room].rstrip() + "\n" + link


def threads_create_container(account, user_id, text, image_url=None):
    """Create a Threads media container: POST /v1.0/{user-id}/threads.
    IMAGE + the photo's original PUBLIC url when one is available
    (Threads downloads it), else TEXT. Returns the container id or
    None."""
    user_id = (user_id or "").strip()
    if not user_id:
        return None
    text = (text or "").strip()
    if image_url:
        data = {"media_type": "IMAGE", "text": text,
                "image_url": (image_url or "").strip()}
    else:
        data = {"media_type": "TEXT", "text": text}
    r = threads_request(account, "POST", f"/v1.0/{user_id}/threads",
                        data=data)
    if r is None or r.status_code != 200:
        log("warning", "threads container create failed (HTTP "
                       f"{r.status_code if r is not None else 'no response'})")
        return None
    try:
        data = r.json()
    except Exception:
        log("warning", "threads container create response not JSON")
        return None
    cid = str((data or {}).get("id", ""))
    if not cid:
        log("warning", "threads container create returned no id")
        return None
    return cid


def threads_container_status(account, container_id):
    """The processing status of a media container (FINISHED / IN_PROGRESS
    / ERROR / EXPIRED), or None when the status cannot be read (the
    caller then falls back to waiting the full delay)."""
    r = threads_request(account, "GET", f"/v1.0/{container_id}",
                        params={"fields": "status"})
    if r is None or r.status_code != 200:
        return None
    try:
        return ((r.json() or {}).get("status") or "").strip() or None
    except Exception:
        return None


def threads_publish_container(account, user_id, creation_id):
    """Publish a finished media container: POST
    /v1.0/{user-id}/threads_publish with creation_id. Returns the
    published post (media) id or None."""
    user_id = (user_id or "").strip()
    if not user_id or not creation_id:
        return None
    r = threads_request(account, "POST",
                        f"/v1.0/{user_id}/threads_publish",
                        data={"creation_id": str(creation_id)})
    if r is None or r.status_code != 200:
        log("warning", "threads publish failed (HTTP "
                       f"{r.status_code if r is not None else 'no response'})")
        return None
    try:
        data = r.json()
    except Exception:
        log("warning", "threads publish response not JSON")
        return None
    post_id = str((data or {}).get("id", ""))
    if not post_id:
        log("warning", "threads publish returned no post id")
        return None
    return post_id


def threads_submit(account, user_id, text, image_url=None,
                   wait_seconds=THREADS_CONTAINER_WAIT_SECONDS):
    """Publish one Threads post: create the media container, wait for
    it to finish processing (poll the container status, at most
    wait_seconds; Meta recommends ~30s), then publish it. Returns
    the published post id or None. wait_seconds=0 publishes at once
    (used by tests - never by the worker)."""
    user_id = (user_id or "").strip()
    if not user_id or not (text or "").strip():
        return None
    cid = threads_create_container(account, user_id, text, image_url)
    if not cid:
        return None
    if wait_seconds and wait_seconds > 0:
        waited = 0
        while waited < wait_seconds:
            status = threads_container_status(account, cid)
            if status == "FINISHED":
                break
            if status in ("ERROR", "EXPIRED"):
                log("warning", f"threads container {cid} status {status} - "
                               "not publishing")
                return None
            step = min(5, wait_seconds - waited)
            time.sleep(step)
            waited += step
    post_id = threads_publish_container(account, user_id, cid)
    if not post_id:
        return None
    log("info", f"threads: posted for user {user_id}: {post_id}")
    return post_id


THREADS_ACCOUNT_SETTINGS_PATH = os.path.join(DATA_DIR, "threads_accounts.json")


def get_threads_account_settings():
    """Per-account settings from data/threads_accounts.json (public, no
    passwords): [{user_id, enabled, posts_per_day}]. Missing file =
    all enabled. Kept in its own file (not accounts.json) so saving
    Bluesky/Reddit/Tumblr controls can never wipe Threads entries
    and vice versa - the dashboard writes this file from the Threads
    tab."""
    if not os.path.exists(THREADS_ACCOUNT_SETTINGS_PATH):
        return {}
    try:
        with open(THREADS_ACCOUNT_SETTINGS_PATH, "r", encoding="utf-8") as f:
            data = json.load(f)
        if isinstance(data, list):
            return {a["user_id"]: a for a in data
                    if isinstance(a, dict) and a.get("user_id")}
        if isinstance(data, dict):
            return data
    except Exception as e:
        log("warning", f"threads_accounts.json load failed: {e}")
    return {}


def threads_account_enabled(user_id):
    cfg = get_threads_account_settings().get(user_id)
    if not cfg:
        return True
    return cfg.get("enabled", True) is not False


def threads_account_posts_limit(user_id):
    cfg = get_threads_account_settings().get(user_id)
    if not cfg:
        return 0
    try:
        return int(cfg.get("posts_per_day") or 0)
    except Exception:
        return 0


THREADS_CAPTION_PROMPT = """Write ONE short, exciting Threads post in ENGLISH about this news story, that makes people want to click the link below it. Sound like a real person sharing breaking news, not an ad. Keep it under 400 characters. Do NOT add the link or a call-to-action yourself - they are added after your text.
Style: {tone}
News: {headline}
Link: {link}
"""


def _threads_gap_key(card):
    """The key the 5-minute no-burst gap is stored under: the Threads
    user ID, not the card name (same rule as Bluesky/Reddit/Tumblr -
    two cards sharing one account must not burst-post to it)."""
    if isinstance(card, dict):
        return (card.get("account_handle") or "").strip() or card.get("name", "")
    return str(card or "")


def _threads_gap_left(state, user_id):
    """Time left on the 5-minute no-burst gap for a Threads account,
    or None when it may post again."""
    last = (state.get("last_threads_post_at") or {}).get(user_id or "")
    if not last:
        return None
    try:
        dt = datetime.fromisoformat(last)
        if dt.tzinfo is None:
            dt = dt.replace(tzinfo=UTC)
    except Exception:
        return None
    left = dt + timedelta(minutes=THREADS_MIN_POST_GAP_MINUTES) - now_utc()
    return left if left.total_seconds() > 0 else None


def _record_threads_post_at(state, user_id):
    """Remember that this Threads account posted now (state.json, so
    the gap survives across worker runs)."""
    state.setdefault("last_threads_post_at", {})[user_id or ""] = now_iso()


def record_threads_post(state, user_id):
    """Count a Threads post for this account today (per-account limits)."""
    counts = state.setdefault("threads_post_counts", {})
    today = counts.setdefault(today_str(), {})
    today[user_id] = int(today.get(user_id, 0)) + 1
    for d in list(counts.keys()):
        try:
            if (now_utc().date() - datetime.strptime(d, "%Y-%m-%d").date()).days > 3:
                counts.pop(d, None)
        except Exception:
            counts.pop(d, None)


def posts_today_for_threads_account(state, user_id):
    counts = state.get("threads_post_counts", {})
    return int(counts.get(today_str(), {}).get(user_id, 0))


def _card_threads_post(card, state):
    """Post ONE Threads card. Returns True on success.
    The post is a fresh Political/War story from the SAME picker as
    Bluesky (_pick_fresh_promo_news) with the SAME shared 24h
    per-topic / per-link cooldown stores recorded, so the same story
    never goes to Bluesky, Reddit, Tumblr and Threads on the same
    day. The photo is posted with its ORIGINAL public URL (Threads
    downloads it) - the worker never uploads an image anywhere. When
    the story has no usable photo, the post still goes out TEXT-only
    (a fresh story from _pick_fresh_reddit_news, which needs no
    photo) - a missing photo never ends the run. Text = hook + link,
    hard-capped at 500 chars by _fit_threads_text. Same 5-minute
    no-burst gap per account. A cooldown / no-news skip is a clean
    no-op."""
    global LAST_THREADS_SKIP
    LAST_THREADS_SKIP = None
    name = card.get("name", "")
    accs = [a for a in list_threads_accounts()
            if not card.get("account_handle") or
            a["user_id"] == card["account_handle"]]
    if not accs:
        log("warning", f"card '{name}': no usable Threads account - post skipped")
        return False
    link = (card.get("link") or "").strip()
    topic, headline, photo = _pick_fresh_promo_news(card, state)
    image_url = (photo or {}).get("url", "") if photo else ""
    article_url = (photo or {}).get("article_url", "") if photo else ""
    if not photo:
        # No verified photo for any fresh story - fall back to a
        # fresh story that needs no photo and post TEXT-only (the
        # picker already logged why; LAST_BSKY_SKIP says no_photo).
        topic2, headline2, url2 = _pick_fresh_reddit_news(card, state)
        if not headline2:
            log("warning", f"card '{name}': no fresh news - Threads post "
                           "skipped")
            LAST_THREADS_SKIP = {"cooldown": "cooldown",
                                 "no_news": "no_news"}.get(
                LAST_REDDIT_SKIP, "no_news")
            return False
        log("info", f"card '{name}': no public photo URL - posting "
                     "text-only to Threads")
        topic, headline = topic2, headline2
        article_url = url2 or ""
        image_url = ""
    headline = headline or topic
    effective_link = link or article_url
    if _promo_topic_cooldown_left(state, headline) is not None:
        log("info", f"card '{name}': news story already used within "
                    f"24h - cooldown, skipping")
        LAST_THREADS_SKIP = "cooldown"
        return False
    if _promo_link_topic_cooldown_left(state, effective_link, headline) is not None:
        log("info", f"card '{name}': same link + same event within "
                    f"24h - cooldown, skipping")
        LAST_THREADS_SKIP = "cooldown"
        return False
    tone_text = ARTICLE_TONES[card_tone(card)]
    text = (card.get("text") or "").strip()
    if not text:
        try:
            text = (ai_write(
                THREADS_CAPTION_PROMPT.format(
                    headline=headline[:150], link=effective_link,
                    tone=tone_text), max_tokens=400) or "").strip()
        except Exception:
            text = ""
        if not text:
            text = headline
    post_text = _fit_threads_text(text, effective_link)
    if is_dry_run():
        log("warning", f"[DRY RUN] card '{name}': would post to Threads "
                       f"(user {accs[0]['user_id']}) '{headline[:60]}' -> "
                       f"{effective_link[:60]}")
        return True
    ok = False
    for acc in accs[:1]:
        uid = acc["user_id"]
        if not threads_account_enabled(uid):
            continue
        limit = threads_account_posts_limit(uid)
        if limit > 0 and posts_today_for_threads_account(state, uid) >= limit:
            log("info", f"card '{name}': Threads user {uid} daily limit "
                        "reached - skipping")
            continue
        res = retry_with_backoff(
            lambda: threads_submit(acc, uid, post_text,
                                   image_url or None),
            attempts=2, base_delay=5, label="threads submit")
        if res:
            _record_promo_topic_posted(state, headline)
            _record_promo_link_topic_posted(state, effective_link, headline)
            _record_promo_account_posted(state, headline, uid)
            record_threads_post(state, uid)
            _record_threads_post_at(state, uid)
            if uid in _THREADS_ROTATED:
                # Timestamp only (never a token value): the dashboard
                # can show that this user's token rotated.
                state.setdefault("threads_refresh_rotated_at", {})[uid] = now_iso()
            log("info", f"card '{name}': posted to Threads (user {uid}): "
                        f"{res}")
            ok = True
            break
        log("warning", f"card '{name}': threads submit failed")
    return ok


def _post_threads_card(card, state, due_slots):
    """The posting loop for threads_post cards. Returns (made, last_error).
    Mirrors _post_tumblr_card: 5-minute gap per account, posts-per-run,
    due slots, day/week/month caps. Clean skips (cooldown, too soon,
    cap, no fresh news) are no-ops, not failures. There is no
    'no photo' skip: a story without a public photo URL posts
    text-only instead."""
    global LAST_THREADS_SKIP
    name = card.get("name", "")
    dry = is_dry_run()
    made = 0
    cooldown_hit = False
    cap_hit = False
    gap_key = _threads_gap_key(card)
    if not dry and _threads_gap_left(state, gap_key) is not None:
        log("info", f"card '{name}': posted less than "
                    f"{THREADS_MIN_POST_GAP_MINUTES} minutes ago - too soon, skipping")
        return 0, "too soon"
    while True:
        card = _refresh_card(card)
        log_card_settings(card)
        remaining = card_caps_remaining(state, name, card)
        if remaining is not None and remaining <= 0:
            log("info", f"card '{name}': post cap reached - skipping")
            cap_hit = True
            break
        if made >= card_posts_per_run(card):
            break
        if due_slots and made >= len(due_slots):
            break
        try:
            posted = _card_threads_post(card, state)
        except Exception as e:
            log("error", f"card '{name}': post attempt failed: {e}")
            LAST_THREADS_SKIP = None
            break
        if posted:
            made += 1
            if not dry:
                record_card_post(state, name)
                _record_threads_post_at(state, gap_key)
        else:
            if LAST_THREADS_SKIP == "cooldown":
                cooldown_hit = True
            break
    if made and not dry and due_slots:
        mark_slots_used(state, name, due_slots[:made])
    if cooldown_hit and made == 0:
        return 0, "cooldown"
    if cap_hit and made == 0:
        return 0, "post cap reached"
    if made == 0 and LAST_THREADS_SKIP == "no_news":
        return 0, "no fresh news"
    return made, ("" if made else "post failed or skipped")


# ---------------------------------------------------------------- Mastodon
# Free, no review, no approval queue (verified 2026-11-25 against
# Mastodon's own API docs, docs.joinmastodon.org/methods/statuses +
# /methods/media): the API is per-instance - every request goes to
# https://{instance_host}/api/v1/... . For the user's OWN account
# the simple path is the instance web UI: log in, Preferences ->
# Development -> New application -> copy the access token (scopes
# write:statuses + write:media). The API path (POST /api/v1/apps to
# register an app, then OAuth) is a follow-up, not required for the
# user's own account. Auth is a Bearer <access token> header; tokens
# do NOT expire, so there is no refresh flow - a 401 means the stored
# token is wrong or revoked, and the log says plainly to check the
# token in the Mastodon tab. Publishing is TWO calls: (1) POST
# /api/v2/media uploads the photo as multipart (200 = processed,
# 202 = still processing, then GET /api/v1/media/:id is polled until
# the url appears), (2) POST /api/v1/statuses with status text,
# media_ids[] and visibility public. 500 characters default (varies
# by instance - text is capped at 500 to be safe). Rate ~300
# requests per 5 minutes per account. The photo comes from the shared
# Bluesky picker and is UPLOADED as bytes (Mastodon does not take a
# remote image URL); when no verified photo is available the post
# goes out TEXT-only (never a skipped run for that reason alone).
# Mastodon v1 is POST-ONLY, like Tumblr/Threads: replies ARE
# possible on Mastodon (GET /api/v1/statuses/:id/context +
# in_reply_to_id), but need a per-post reply-fetch loop and posted-id
# tracking, and were not built - a follow-up, not part of this build.
MASTODON_MIN_POST_GAP_MINUTES = 5
MASTODON_MAX_TEXT_CHARS = 500
MASTODON_MEDIA_WAIT_SECONDS = 30

LAST_MASTODON_SKIP = None


def _mastodon_instance_base(account):
    """The instance base URL for a Mastodon account: https://host.
    Accepts 'mastodon.social', 'https://mastodon.social' or a pasted
    profile URL - scheme, path and trailing slash are stripped."""
    raw = ((account or {}).get("instance") or "").strip()
    if not raw:
        return ""
    if "://" not in raw:
        raw = "https://" + raw
    try:
        host = (urlparse(raw).netloc or "").strip().lower()
    except Exception:
        host = ""
    if not host:
        return ""
    return "https://" + host


def _mastodon_account_key(account):
    """The per-account key for counts/gaps/settings: the instance
    host, plus /@username when one is stored (two accounts on one
    instance must not share a daily cap)."""
    base = _mastodon_instance_base(account)
    host = base.replace("https://", "", 1) if base else ""
    user = ((account or {}).get("username") or "").strip().lstrip("@")
    if host and user:
        return host + "/@" + user
    return host


def list_mastodon_accounts():
    """All Mastodon accounts: the MASTODON_ACCOUNTS env secret (JSON
    list) or the single-account env vars. (The dashboard saves
    accounts encrypted into the secret, same sealed-box pattern as
    Bluesky/Reddit/Tumblr/Threads.)"""
    return list(ENV_MASTODON_ACCOUNTS)


def _mastodon_token(account):
    """The access token for a Mastodon account, or ''. Never logged."""
    return ((account or {}).get("access_token") or "").strip()


def mastodon_request(account, method, path, **kwargs):
    """One authenticated Mastodon API call against the account's own
    instance. Returns the Response or None. The token travels as a
    Bearer header, exactly as Mastodon's docs show it. Tokens do not
    expire, so there is no refresh: a 401 means the stored token is
    wrong or revoked - the log says so plainly (never the token
    value) and the call is NOT retried. kwargs pass through to
    requests (params/data/files/headers)."""
    base = _mastodon_instance_base(account)
    if not base:
        log("warning", "mastodon: no instance set for this account - "
                       "add one in the Mastodon tab")
        return None
    token = _mastodon_token(account)
    if not token:
        log("warning", f"mastodon: no access token for instance "
                       f"'{_mastodon_account_key(account)}' - add one "
                       "in the Mastodon tab")
        return None
    headers = dict(kwargs.pop("headers", {}) or {})
    headers["Authorization"] = f"Bearer {token}"
    url = base + path
    try:
        r = requests.request(method, url, headers=headers, timeout=25,
                             **kwargs)
    except Exception as e:
        log("warning", f"mastodon {method} {path} failed: {e}")
        return None
    if r.status_code == 401:
        log("warning", f"mastodon: access token rejected (401) for "
                       f"instance '{_mastodon_account_key(account)}' - "
                       "check the access token in the Mastodon tab "
                       "(Preferences -> Development -> New application)")
    return r


def _fit_mastodon_text(hook, link):
    """The Mastodon post text: hook + link, hard-capped at 500
    characters at this single send point (Mastodon's default limit;
    the link is never cut - the hook is trimmed to make room). Pure
    function (no I/O) - unit-tested."""
    hook = (hook or "").strip()
    link = (link or "").strip()
    if not link:
        return hook[:MASTODON_MAX_TEXT_CHARS]
    text = hook + "\n" + link if hook else link
    if len(text) <= MASTODON_MAX_TEXT_CHARS:
        return text
    room = MASTODON_MAX_TEXT_CHARS - len(link) - 1
    if room <= 0:
        return link[:MASTODON_MAX_TEXT_CHARS]
    return hook[:room].rstrip() + "\n" + link


def mastodon_upload_media(account, image_path,
                          wait_seconds=MASTODON_MEDIA_WAIT_SECONDS):
    """Upload one photo to the account's instance: POST /api/v2/media
    as multipart. Returns the media attachment id or None. A 200
    means processed at once; a 202 means still processing, so GET
    /api/v1/media/:id is polled (206 = still processing) until the
    url appears, at most wait_seconds. The photo must already be
    downloaded + verified (download_image only ever produces
    .jpg/.png, both accepted by Mastodon)."""
    if not image_path or not os.path.exists(image_path):
        log("warning", "mastodon media upload failed: no verified photo file")
        return None
    mime = "image/png" if str(image_path).lower().endswith(".png") \
        else "image/jpeg"
    try:
        with open(image_path, "rb") as f:
            img_bytes = f.read()
    except Exception as e:
        log("warning", f"mastodon media upload failed: cannot read photo: {e}")
        return None
    if len(img_bytes) < 1000:
        log("warning", "mastodon media upload failed: photo file too small")
        return None
    fname = os.path.basename(image_path) or "photo.jpg"
    files = {"file": (fname, img_bytes, mime)}
    r = mastodon_request(account, "POST", "/api/v2/media", files=files)
    if r is None or r.status_code not in (200, 202):
        log("warning", "mastodon media upload failed (HTTP "
                       f"{r.status_code if r is not None else 'no response'})")
        return None
    try:
        data = r.json()
    except Exception:
        log("warning", "mastodon media upload response not JSON")
        return None
    media_id = str((data or {}).get("id", ""))
    if not media_id:
        log("warning", "mastodon media upload returned no id")
        return None
    if r.status_code == 200:
        return media_id
    # 202: still processing - poll until the url appears.
    waited = 0
    while waited < wait_seconds:
        r2 = mastodon_request(account, "GET", f"/api/v1/media/{media_id}")
        if r2 is not None and r2.status_code == 200:
            try:
                if (r2.json() or {}).get("url"):
                    return media_id
            except Exception:
                pass
        elif r2 is not None and r2.status_code not in (200, 206):
            log("warning", "mastodon media status check failed (HTTP "
                           f"{r2.status_code})")
            return None
        step = min(2, wait_seconds - waited)
        time.sleep(step)
        waited += step
    log("warning", f"mastodon media {media_id} still processing after "
                   f"{wait_seconds}s - posting without it")
    return None


def mastodon_submit(account, text, image_path=None,
                    wait_seconds=MASTODON_MEDIA_WAIT_SECONDS):
    """Publish one Mastodon status: upload the photo first (when one
    is given), then POST /api/v1/statuses with the text, media_ids[]
    and visibility public. Returns the published status id or None.
    A failed media upload does NOT fail the post - it goes out
    TEXT-only instead (logged plainly). An Idempotency-Key header
    guards against a retried request double-posting."""
    text = (text or "").strip()
    if not text:
        return None
    media_ids = []
    if image_path:
        media_id = mastodon_upload_media(account, image_path,
                                         wait_seconds=wait_seconds)
        if media_id:
            media_ids = [media_id]
        else:
            log("info", "mastodon: media upload failed - posting text-only")
    data = {"status": text, "visibility": "public"}
    if media_ids:
        data["media_ids[]"] = media_ids
    key = (f"mastodon-{int(time.time())}-"
           f"{random.randint(0, 999999)}")
    r = mastodon_request(account, "POST", "/api/v1/statuses",
                         data=data,
                         headers={"Idempotency-Key": key})
    if r is None or r.status_code not in (200, 201):
        log("warning", "mastodon status post failed (HTTP "
                       f"{r.status_code if r is not None else 'no response'})")
        return None
    try:
        data = r.json()
    except Exception:
        log("warning", "mastodon status post response not JSON")
        return None
    post_id = str((data or {}).get("id", ""))
    if not post_id:
        log("warning", "mastodon status post returned no post id")
        return None
    log("info", f"mastodon: posted to "
                f"{_mastodon_account_key(account)}: {post_id}")
    return post_id


MASTODON_ACCOUNT_SETTINGS_PATH = os.path.join(DATA_DIR, "mastodon_accounts.json")


def get_mastodon_account_settings():
    """Per-account settings from data/mastodon_accounts.json (public, no
    passwords): [{instance, username, enabled, posts_per_day}].
    Missing file = all enabled. Kept in its own file (not
    accounts.json) so saving Bluesky/Reddit/Tumblr/Threads controls
    can never wipe Mastodon entries and vice versa - the dashboard
    writes this file from the Mastodon tab."""
    if not os.path.exists(MASTODON_ACCOUNT_SETTINGS_PATH):
        return {}
    try:
        with open(MASTODON_ACCOUNT_SETTINGS_PATH, "r", encoding="utf-8") as f:
            data = json.load(f)
        if isinstance(data, list):
            out = {}
            for a in data:
                if not isinstance(a, dict):
                    continue
                key = a.get("key") or _mastodon_account_key(a)
                if key:
                    out[key] = a
            return out
        if isinstance(data, dict):
            return data
    except Exception as e:
        log("warning", f"mastodon_accounts.json load failed: {e}")
    return {}


def mastodon_account_enabled(key):
    cfg = get_mastodon_account_settings().get(key)
    if not cfg:
        return True
    return cfg.get("enabled", True) is not False


def mastodon_account_posts_limit(key):
    cfg = get_mastodon_account_settings().get(key)
    if not cfg:
        return 0
    try:
        return int(cfg.get("posts_per_day") or 0)
    except Exception:
        return 0


MASTODON_CAPTION_PROMPT = """Write ONE short, exciting Mastodon post in ENGLISH about this news story, that makes people want to click the link below it. Sound like a real person sharing breaking news, not an ad. Keep it under 400 characters. Do NOT add the link or a call-to-action yourself - they are added after your text.
Style: {tone}
News: {headline}
Link: {link}
"""


def _mastodon_gap_key(card):
    """The key the 5-minute no-burst gap is stored under: the
    Mastodon account key (instance host), not the card name (same
    rule as Bluesky/Reddit/Tumblr/Threads - two cards sharing one
    account must not burst-post to it)."""
    if isinstance(card, dict):
        return (card.get("account_handle") or "").strip() or card.get("name", "")
    return str(card or "")


def _mastodon_gap_left(state, key):
    """Time left on the 5-minute no-burst gap for a Mastodon account,
    or None when it may post again."""
    last = (state.get("last_mastodon_post_at") or {}).get(key or "")
    if not last:
        return None
    try:
        dt = datetime.fromisoformat(last)
        if dt.tzinfo is None:
            dt = dt.replace(tzinfo=UTC)
    except Exception:
        return None
    left = dt + timedelta(minutes=MASTODON_MIN_POST_GAP_MINUTES) - now_utc()
    return left if left.total_seconds() > 0 else None


def _record_mastodon_post_at(state, key):
    """Remember that this Mastodon account posted now (state.json, so
    the gap survives across worker runs)."""
    state.setdefault("last_mastodon_post_at", {})[key or ""] = now_iso()


def record_mastodon_post(state, key):
    """Count a Mastodon post for this account today (per-account limits)."""
    counts = state.setdefault("mastodon_post_counts", {})
    today = counts.setdefault(today_str(), {})
    today[key] = int(today.get(key, 0)) + 1
    for d in list(counts.keys()):
        try:
            if (now_utc().date() - datetime.strptime(d, "%Y-%m-%d").date()).days > 3:
                counts.pop(d, None)
        except Exception:
            counts.pop(d, None)


def posts_today_for_mastodon_account(state, key):
    counts = state.get("mastodon_post_counts", {})
    return int(counts.get(today_str(), {}).get(key, 0))


def _card_mastodon_post(card, state):
    """Post ONE Mastodon card. Returns True on success.
    The post is a fresh Political/War story from the SAME picker as
    Bluesky (_pick_fresh_promo_news) with the SAME shared 24h
    per-topic / per-link cooldown stores recorded, so the same story
    never goes to Bluesky, Reddit, Tumblr, Threads and Mastodon on
    the same day. The photo is UPLOADED as bytes to the account's own
    instance (POST /api/v2/media, then POST /api/v1/statuses with
    media_ids[]). When the story has no usable photo, the post still
    goes out TEXT-only (a fresh story from _pick_fresh_reddit_news,
    which needs no photo) - a missing photo never ends the run.
    Text = hook + link, hard-capped at 500 chars by
    _fit_mastodon_text. Same 5-minute no-burst gap per account. A
    cooldown / no-news skip is a clean no-op."""
    global LAST_MASTODON_SKIP
    LAST_MASTODON_SKIP = None
    name = card.get("name", "")
    accs = [a for a in list_mastodon_accounts()
            if not card.get("account_handle") or
            _mastodon_account_key(a) == card["account_handle"]]
    if not accs:
        log("warning", f"card '{name}': no usable Mastodon account - post skipped")
        return False
    link = (card.get("link") or "").strip()
    topic, headline, photo = _pick_fresh_promo_news(card, state)
    image_path = ""
    if photo:
        image_path = (photo or {}).get("local_path", "") or ""
        if image_path and not os.path.exists(image_path):
            image_path = ""
    article_url = (photo or {}).get("article_url", "") if photo else ""
    if not photo or not image_path:
        # No verified photo for any fresh story - fall back to a
        # fresh story that needs no photo and post TEXT-only (the
        # picker already logged why; LAST_BSKY_SKIP says no_photo).
        topic2, headline2, url2 = _pick_fresh_reddit_news(card, state)
        if not headline2:
            log("warning", f"card '{name}': no fresh news - Mastodon post "
                           "skipped")
            LAST_MASTODON_SKIP = {"cooldown": "cooldown",
                                  "no_news": "no_news"}.get(
                LAST_REDDIT_SKIP, "no_news")
            return False
        log("info", f"card '{name}': no verified photo - posting "
                     "text-only to Mastodon")
        topic, headline = topic2, headline2
        article_url = url2 or ""
        image_path = ""
    headline = headline or topic
    effective_link = link or article_url
    if _promo_topic_cooldown_left(state, headline) is not None:
        log("info", f"card '{name}': news story already used within "
                    f"24h - cooldown, skipping")
        LAST_MASTODON_SKIP = "cooldown"
        return False
    if _promo_link_topic_cooldown_left(state, effective_link, headline) is not None:
        log("info", f"card '{name}': same link + same event within "
                    f"24h - cooldown, skipping")
        LAST_MASTODON_SKIP = "cooldown"
        return False
    tone_text = ARTICLE_TONES[card_tone(card)]
    text = (card.get("text") or "").strip()
    if not text:
        try:
            text = (ai_write(
                MASTODON_CAPTION_PROMPT.format(
                    headline=headline[:150], link=effective_link,
                    tone=tone_text), max_tokens=400) or "").strip()
        except Exception:
            text = ""
        if not text:
            text = headline
    post_text = _fit_mastodon_text(text, effective_link)
    if is_dry_run():
        log("warning", f"[DRY RUN] card '{name}': would post to Mastodon "
                       f"(instance {_mastodon_account_key(accs[0])}) "
                       f"'{headline[:60]}' -> {effective_link[:60]}")
        return True
    ok = False
    for acc in accs[:1]:
        key = _mastodon_account_key(acc)
        if not mastodon_account_enabled(key):
            continue
        limit = mastodon_account_posts_limit(key)
        if limit > 0 and posts_today_for_mastodon_account(state, key) >= limit:
            log("info", f"card '{name}': Mastodon account {key} daily limit "
                        "reached - skipping")
            continue
        res = retry_with_backoff(
            lambda: mastodon_submit(acc, post_text,
                                    image_path or None),
            attempts=2, base_delay=5, label="mastodon submit")
        if res:
            _record_promo_topic_posted(state, headline)
            _record_promo_link_topic_posted(state, effective_link, headline)
            _record_promo_account_posted(state, headline, key)
            record_mastodon_post(state, key)
            _record_mastodon_post_at(state, key)
            log("info", f"card '{name}': posted to Mastodon ({key}): {res}")
            ok = True
            break
        log("warning", f"card '{name}': mastodon submit failed")
    return ok


def _post_mastodon_card(card, state, due_slots):
    """The posting loop for mastodon_post cards. Returns (made, last_error).
    Mirrors _post_threads_card: 5-minute gap per account, posts-per-run,
    due slots, day/week/month caps. Clean skips (cooldown, too soon,
    cap, no fresh news) are no-ops, not failures. There is no
    'no photo' skip: a story without a verified photo posts
    text-only instead."""
    global LAST_MASTODON_SKIP
    name = card.get("name", "")
    dry = is_dry_run()
    made = 0
    cooldown_hit = False
    cap_hit = False
    gap_key = _mastodon_gap_key(card)
    if not dry and _mastodon_gap_left(state, gap_key) is not None:
        log("info", f"card '{name}': posted less than "
                    f"{MASTODON_MIN_POST_GAP_MINUTES} minutes ago - too soon, skipping")
        return 0, "too soon"
    while True:
        card = _refresh_card(card)
        log_card_settings(card)
        remaining = card_caps_remaining(state, name, card)
        if remaining is not None and remaining <= 0:
            log("info", f"card '{name}': post cap reached - skipping")
            cap_hit = True
            break
        if made >= card_posts_per_run(card):
            break
        if due_slots and made >= len(due_slots):
            break
        try:
            posted = _card_mastodon_post(card, state)
        except Exception as e:
            log("error", f"card '{name}': post attempt failed: {e}")
            LAST_MASTODON_SKIP = None
            break
        if posted:
            made += 1
            if not dry:
                record_card_post(state, name)
                _record_mastodon_post_at(state, gap_key)
        else:
            if LAST_MASTODON_SKIP == "cooldown":
                cooldown_hit = True
            break
    if made and not dry and due_slots:
        mark_slots_used(state, name, due_slots[:made])
    if cooldown_hit and made == 0:
        return 0, "cooldown"
    if cap_hit and made == 0:
        return 0, "post cap reached"
    if made == 0 and LAST_MASTODON_SKIP == "no_news":
        return 0, "no fresh news"
    return made, ("" if made else "post failed or skipped")


# ---------------------------------------------------------------- Telegram
# Free, no review, no approval queue (verified 2026-11-25 against
# core.telegram.org/bots/api, Bot API 10.5): the user creates a bot
# with @BotFather (/newbot) and gets ONE token - that token IS the
# auth (no OAuth, no refresh, no expiry). The bot is added as a
# channel admin with Post Messages permission, and each card picks
# its own destination channel (card field "channel", e.g.
# @primotodaynews). Publishing is ONE call: POST
# https://api.telegram.org/bot<token>/sendMessage with chat_id +
# text (1-4096 chars), or /sendPhoto with the photo as multipart
# bytes + caption (0-1024 chars, hook + link, link never cut).
# The photo comes from the shared Bluesky picker and is UPLOADED as
# bytes (the worker already has it as a local file); when no
# verified photo is available the post goes out TEXT-only via
# sendMessage (never a skipped run for that reason alone). Rate is
# ~1 message per second per chat - a short wait spaces sends.
# This posts to a CHANNEL: the audience must join the channel
# first, it is not a discovery feed. Telegram v1 is POST-ONLY:
# channel posts have no reply cycle in the Bot API sense (channel
# comments live in a linked discussion group), so no replies were
# built - a follow-up, not part of this build.
TELEGRAM_API_BASE = "https://api.telegram.org"
TELEGRAM_MIN_POST_GAP_MINUTES = 5
TELEGRAM_MAX_TEXT_CHARS = 4096
TELEGRAM_MAX_CAPTION_CHARS = 1024
TELEGRAM_MIN_SEND_INTERVAL_SECONDS = 1.1

LAST_TELEGRAM_SKIP = None

_TELEGRAM_LAST_SEND_AT = 0.0


def _telegram_account_key(account=None):
    """The per-bot key for counts/gaps/settings: there is ONE bot,
    so every Telegram card shares this key. The per-channel split
    lives in the daily counts and the gap (keyed by channel)."""
    return "telegram-bot"


def list_telegram_accounts():
    """The Telegram bot: the TELEGRAM_BOT_TOKEN env secret (one
    token, from @BotFather). An empty list means no bot is
    configured - a Telegram card cannot run at all then."""
    token = (ENV_TELEGRAM_BOT_TOKEN or "").strip()
    if not token:
        return []
    return [{"bot_token": token}]


def _telegram_token(account):
    """The bot token for a Telegram account, or ''. Never logged -
    the token is part of the request URL, so no URL is ever logged
    either (only the method name)."""
    return ((account or {}).get("bot_token") or "").strip()


def _telegram_channel(card):
    """The destination channel for a Telegram card: the card's
    "channel" field, normalised to @channelusername (a bare name
    gets the @; a numeric chat id is kept as-is)."""
    raw = ((card or {}).get("channel") or "").strip()
    if not raw:
        return ""
    if raw.startswith("@") or raw.startswith("-") \
            or raw.lstrip("-").isdigit():
        return raw
    return "@" + raw


def _telegram_rate_wait():
    """Space sends ~1.1s apart per chat (Telegram's ~1 message/sec
    per chat limit). Only sleeps the remainder since the last send,
    so a first send never waits."""
    global _TELEGRAM_LAST_SEND_AT
    elapsed = time.time() - _TELEGRAM_LAST_SEND_AT
    wait = TELEGRAM_MIN_SEND_INTERVAL_SECONDS - elapsed
    if wait > 0:
        time.sleep(wait)


def _telegram_note_sent():
    """Remember a send just happened (for _telegram_rate_wait)."""
    global _TELEGRAM_LAST_SEND_AT
    _TELEGRAM_LAST_SEND_AT = time.time()


def telegram_api(token, method, **kwargs):
    """One Telegram Bot API call: POST
    https://api.telegram.org/bot<token>/<method>. Returns the
    Response or None. The token travels in the URL (that is how the
    Bot API works), so the URL is NEVER logged - only the method
    name and the status. A 401 means the stored token is wrong or
    revoked; a 403 means the bot is not an admin of the channel
    (or was blocked); a 400 is usually a bad channel name - the log
    says so plainly (never the token value) and the call is NOT
    retried. kwargs pass through to requests (json/data/files)."""
    token = (token or "").strip()
    if not token:
        log("warning", "telegram: no bot token - add one in the "
                       "Telegram tab")
        return None
    url = TELEGRAM_API_BASE + "/bot" + token + "/" + method
    try:
        r = requests.request("POST", url, timeout=25, **kwargs)
    except Exception as e:
        log("warning", f"telegram {method} failed: {e}")
        return None
    if r.status_code == 401:
        log("warning", "telegram: bot token rejected (401) - check "
                       "the bot token in the Telegram tab")
    elif r.status_code == 403:
        log("warning", "telegram: bot is not allowed here (403) - "
                       "add the bot as a channel admin with Post "
                       "Messages permission")
    elif r.status_code == 400:
        try:
            desc = (r.json() or {}).get("description", "")
        except Exception:
            desc = ""
        log("warning", "telegram " + method + " rejected (400)" +
                       (f": {desc}" if desc else
                        " - check the channel name"))
    return r


def _fit_telegram_text(hook, link):
    """The Telegram text message: hook + link, hard-capped at 4096
    characters at this single send point (sendMessage's limit; the
    link is never cut - the hook is trimmed to make room). Pure
    function (no I/O) - unit-tested."""
    hook = (hook or "").strip()
    link = (link or "").strip()
    if not link:
        return hook[:TELEGRAM_MAX_TEXT_CHARS]
    text = hook + "\n" + link if hook else link
    if len(text) <= TELEGRAM_MAX_TEXT_CHARS:
        return text
    room = TELEGRAM_MAX_TEXT_CHARS - len(link) - 1
    if room <= 0:
        return link[:TELEGRAM_MAX_TEXT_CHARS]
    return hook[:room].rstrip() + "\n" + link


def _fit_telegram_caption(hook, link):
    """The Telegram photo caption: hook + link, hard-capped at 1024
    characters at this single send point (sendPhoto's caption
    limit; the link is never cut - the hook is trimmed to make
    room). Pure function (no I/O) - unit-tested."""
    hook = (hook or "").strip()
    link = (link or "").strip()
    if not link:
        return hook[:TELEGRAM_MAX_CAPTION_CHARS]
    text = hook + "\n" + link if hook else link
    if len(text) <= TELEGRAM_MAX_CAPTION_CHARS:
        return text
    room = TELEGRAM_MAX_CAPTION_CHARS - len(link) - 1
    if room <= 0:
        return link[:TELEGRAM_MAX_CAPTION_CHARS]
    return hook[:room].rstrip() + "\n" + link


def _telegram_message_id(r):
    """The message_id from a Telegram send response, or ''. A
    non-JSON or ok:false response logs plainly and yields ''."""
    if r is None or r.status_code != 200:
        return ""
    try:
        data = r.json()
    except Exception:
        log("warning", "telegram send response not JSON")
        return ""
    if not (data or {}).get("ok"):
        return ""
    mid = str(((data or {}).get("result") or {}).get("message_id", ""))
    if not mid:
        log("warning", "telegram send returned no message id")
    return mid


def telegram_send_message(token, chat_id, text):
    """Send one text message to a channel: POST /sendMessage with
    chat_id + text (1-4096 chars, fitted by _fit_telegram_text
    before this is called). Returns the message_id or None."""
    text = (text or "").strip()
    if not text:
        return None
    _telegram_rate_wait()
    r = telegram_api(token, "sendMessage",
                     json={"chat_id": chat_id, "text": text})
    _telegram_note_sent()
    if r is None or r.status_code != 200:
        log("warning", "telegram message post failed (HTTP "
                       f"{r.status_code if r is not None else 'no response'})")
        return None
    return _telegram_message_id(r) or None


def telegram_send_photo(token, chat_id, image_path, caption):
    """Send one photo to a channel: POST /sendPhoto with the photo
    as multipart bytes + caption (0-1024 chars). Returns the
    message_id or None. The photo must already be downloaded +
    verified (download_image only ever produces .jpg/.png)."""
    if not image_path or not os.path.exists(image_path):
        log("warning", "telegram photo send failed: no verified photo file")
        return None
    mime = "image/png" if str(image_path).lower().endswith(".png") \
        else "image/jpeg"
    try:
        with open(image_path, "rb") as f:
            img_bytes = f.read()
    except Exception as e:
        log("warning", f"telegram photo send failed: cannot read photo: {e}")
        return None
    if len(img_bytes) < 1000:
        log("warning", "telegram photo send failed: photo file too small")
        return None
    fname = os.path.basename(image_path) or "photo.jpg"
    files = {"photo": (fname, img_bytes, mime)}
    _telegram_rate_wait()
    r = telegram_api(token, "sendPhoto",
                     data={"chat_id": chat_id, "caption": caption or ""},
                     files=files)
    _telegram_note_sent()
    if r is None or r.status_code != 200:
        log("warning", "telegram photo post failed (HTTP "
                       f"{r.status_code if r is not None else 'no response'})")
        return None
    return _telegram_message_id(r) or None


def telegram_submit(token, channel, hook, link, image_path=None):
    """Publish one Telegram channel post: with a photo, sendPhoto
    (caption = hook + link, capped at 1024); without one,
    sendMessage (text = hook + link, capped at 4096). Returns the
    published message_id or None. A failed photo send does NOT
    fail the post - it goes out TEXT-only instead (logged
    plainly)."""
    hook = (hook or "").strip()
    link = (link or "").strip()
    if not hook and not link:
        return None
    if image_path:
        mid = telegram_send_photo(
            token, channel, image_path,
            _fit_telegram_caption(hook, link))
        if mid:
            log("info", f"telegram: posted photo to {channel}: {mid}")
            return mid
        log("info", "telegram: photo send failed - posting text-only")
    mid = telegram_send_message(token, channel,
                                _fit_telegram_text(hook, link))
    if mid:
        log("info", f"telegram: posted to {channel}: {mid}")
    else:
        log("warning", "telegram message post failed")
    return mid


TELEGRAM_ACCOUNT_SETTINGS_PATH = os.path.join(DATA_DIR, "telegram_accounts.json")


def get_telegram_account_settings():
    """Per-bot settings from data/telegram_accounts.json (public, no
    passwords): [{key: "telegram-bot", enabled, posts_per_day}].
    Missing file = all enabled. Kept in its own file (not
    accounts.json) so saving Bluesky/Reddit/Tumblr/Threads/Mastodon
    controls can never wipe Telegram entries and vice versa - the
    dashboard writes this file from the Telegram tab."""
    if not os.path.exists(TELEGRAM_ACCOUNT_SETTINGS_PATH):
        return {}
    try:
        with open(TELEGRAM_ACCOUNT_SETTINGS_PATH, "r", encoding="utf-8") as f:
            data = json.load(f)
        if isinstance(data, list):
            out = {}
            for a in data:
                if not isinstance(a, dict):
                    continue
                key = a.get("key") or _telegram_account_key()
                if key:
                    out[key] = a
            return out
        if isinstance(data, dict):
            return data
    except Exception as e:
        log("warning", f"telegram_accounts.json load failed: {e}")
    return {}


def telegram_account_enabled(key):
    cfg = get_telegram_account_settings().get(key)
    if not cfg:
        return True
    return cfg.get("enabled", True) is not False


def telegram_account_posts_limit(key):
    cfg = get_telegram_account_settings().get(key)
    if not cfg:
        return 0
    try:
        return int(cfg.get("posts_per_day") or 0)
    except Exception:
        return 0


TELEGRAM_CAPTION_PROMPT = """Write ONE short, exciting Telegram channel post in ENGLISH about this news story, that makes people want to click the link below it. Sound like a real person sharing breaking news, not an ad. Keep it under 900 characters. Do NOT add the link or a call-to-action yourself - they are added after your text.
Style: {tone}
News: {headline}
Link: {link}
"""


def _telegram_gap_key(card):
    """The key the 5-minute no-burst gap is stored under: the
    destination CHANNEL (same rule as Bluesky/Reddit/Tumblr/
    Threads/Mastodon - two cards sharing one channel must not
    burst-post to it)."""
    if isinstance(card, dict):
        return _telegram_channel(card) or card.get("name", "")
    return str(card or "")


def _telegram_gap_left(state, key):
    """Time left on the 5-minute no-burst gap for a Telegram
    channel, or None when it may post again."""
    last = (state.get("last_telegram_post_at") or {}).get(key or "")
    if not last:
        return None
    try:
        dt = datetime.fromisoformat(last)
        if dt.tzinfo is None:
            dt = dt.replace(tzinfo=UTC)
    except Exception:
        return None
    left = dt + timedelta(minutes=TELEGRAM_MIN_POST_GAP_MINUTES) - now_utc()
    return left if left.total_seconds() > 0 else None


def _record_telegram_post_at(state, key):
    """Remember that this Telegram channel posted now (state.json,
    so the gap survives across worker runs)."""
    state.setdefault("last_telegram_post_at", {})[key or ""] = now_iso()


def record_telegram_post(state, channel):
    """Count a Telegram post for this channel today (per-channel
    daily counts)."""
    counts = state.setdefault("telegram_post_counts", {})
    today = counts.setdefault(today_str(), {})
    today[channel] = int(today.get(channel, 0)) + 1
    for d in list(counts.keys()):
        try:
            if (now_utc().date() - datetime.strptime(d, "%Y-%m-%d").date()).days > 3:
                counts.pop(d, None)
        except Exception:
            counts.pop(d, None)


def posts_today_for_telegram_channel(state, channel):
    counts = state.get("telegram_post_counts", {})
    return int(counts.get(today_str(), {}).get(channel, 0))


def posts_today_for_telegram_bot(state):
    """All Telegram posts today across every channel (the bot's
    daily total - the per-bot posts_per_day cap counts this)."""
    counts = state.get("telegram_post_counts", {})
    return sum(int(v or 0)
               for v in (counts.get(today_str(), {}) or {}).values())


def _card_telegram_post(card, state):
    """Post ONE Telegram card. Returns True on success.
    The post is a fresh Political/War story from the SAME picker as
    Bluesky (_pick_fresh_promo_news) with the SAME shared 24h
    per-topic / per-link cooldown stores recorded, so the same story
    never goes to Bluesky, Reddit, Tumblr, Threads, Mastodon and
    Telegram on the same day. The photo is UPLOADED as bytes to the
    channel (POST /sendPhoto with a 1024-char caption). When the
    story has no usable photo, the post still goes out TEXT-only
    via /sendMessage (a fresh story from _pick_fresh_reddit_news,
    which needs no photo) - a missing photo never ends the run.
    Same 5-minute no-burst gap per channel. A cooldown / no-news
    skip is a clean no-op. The bot token is never logged."""
    global LAST_TELEGRAM_SKIP
    LAST_TELEGRAM_SKIP = None
    name = card.get("name", "")
    accs = list_telegram_accounts()
    if not accs:
        log("warning", f"card '{name}': no Telegram bot token - post skipped")
        return False
    channel = _telegram_channel(card)
    if not channel:
        log("warning", f"card '{name}': no Telegram channel set - post "
                       "skipped")
        LAST_TELEGRAM_SKIP = "no_channel"
        return False
    link = (card.get("link") or "").strip()
    topic, headline, photo = _pick_fresh_promo_news(card, state)
    image_path = ""
    if photo:
        image_path = (photo or {}).get("local_path", "") or ""
        if image_path and not os.path.exists(image_path):
            image_path = ""
    article_url = (photo or {}).get("article_url", "") if photo else ""
    if not photo or not image_path:
        # No verified photo for any fresh story - fall back to a
        # fresh story that needs no photo and post TEXT-only (the
        # picker already logged why; LAST_BSKY_SKIP says no_photo).
        topic2, headline2, url2 = _pick_fresh_reddit_news(card, state)
        if not headline2:
            log("warning", f"card '{name}': no fresh news - Telegram post "
                           "skipped")
            LAST_TELEGRAM_SKIP = {"cooldown": "cooldown",
                                  "no_news": "no_news"}.get(
                LAST_REDDIT_SKIP, "no_news")
            return False
        log("info", f"card '{name}': no verified photo - posting "
                     "text-only to Telegram")
        topic, headline = topic2, headline2
        article_url = url2 or ""
        image_path = ""
    headline = headline or topic
    effective_link = link or article_url
    if _promo_topic_cooldown_left(state, headline) is not None:
        log("info", f"card '{name}': news story already used within "
                    f"24h - cooldown, skipping")
        LAST_TELEGRAM_SKIP = "cooldown"
        return False
    if _promo_link_topic_cooldown_left(state, effective_link, headline) is not None:
        log("info", f"card '{name}': same link + same event within "
                    f"24h - cooldown, skipping")
        LAST_TELEGRAM_SKIP = "cooldown"
        return False
    tone_text = ARTICLE_TONES[card_tone(card)]
    text = (card.get("text") or "").strip()
    if not text:
        try:
            text = (ai_write(
                TELEGRAM_CAPTION_PROMPT.format(
                    headline=headline[:150], link=effective_link,
                    tone=tone_text), max_tokens=400) or "").strip()
        except Exception:
            text = ""
        if not text:
            text = headline
    if is_dry_run():
        log("warning", f"[DRY RUN] card '{name}': would post to Telegram "
                       f"(channel {channel}) "
                       f"'{headline[:60]}' -> {effective_link[:60]}")
        return True
    ok = False
    for acc in accs[:1]:
        key = _telegram_account_key(acc)
        if not telegram_account_enabled(key):
            continue
        limit = telegram_account_posts_limit(key)
        if limit > 0 and posts_today_for_telegram_bot(state) >= limit:
            log("info", f"card '{name}': Telegram bot daily limit "
                        "reached - skipping")
            continue
        token = _telegram_token(acc)
        res = retry_with_backoff(
            lambda: telegram_submit(token, channel, text,
                                    effective_link,
                                    image_path or None),
            attempts=2, base_delay=5, label="telegram submit")
        if res:
            _record_promo_topic_posted(state, headline)
            _record_promo_link_topic_posted(state, effective_link, headline)
            _record_promo_account_posted(state, headline, key)
            record_telegram_post(state, channel)
            _record_telegram_post_at(state, channel)
            log("info", f"card '{name}': posted to Telegram ({channel}): {res}")
            ok = True
            break
        log("warning", f"card '{name}': telegram submit failed")
    return ok


def _post_telegram_card(card, state, due_slots):
    """The posting loop for telegram_post cards. Returns (made, last_error).
    Mirrors _post_mastodon_card: 5-minute gap per channel, posts-per-run,
    due slots, day/week/month caps. Clean skips (cooldown, too soon,
    cap, no fresh news, no channel set) are no-ops, not failures.
    There is no 'no photo' skip: a story without a verified photo posts
    text-only instead."""
    global LAST_TELEGRAM_SKIP
    name = card.get("name", "")
    dry = is_dry_run()
    made = 0
    cooldown_hit = False
    cap_hit = False
    gap_key = _telegram_gap_key(card)
    if not dry and _telegram_gap_left(state, gap_key) is not None:
        log("info", f"card '{name}': posted less than "
                    f"{TELEGRAM_MIN_POST_GAP_MINUTES} minutes ago - too soon, skipping")
        return 0, "too soon"
    while True:
        card = _refresh_card(card)
        log_card_settings(card)
        remaining = card_caps_remaining(state, name, card)
        if remaining is not None and remaining <= 0:
            log("info", f"card '{name}': post cap reached - skipping")
            cap_hit = True
            break
        if made >= card_posts_per_run(card):
            break
        if due_slots and made >= len(due_slots):
            break
        try:
            posted = _card_telegram_post(card, state)
        except Exception as e:
            log("error", f"card '{name}': post attempt failed: {e}")
            LAST_TELEGRAM_SKIP = None
            break
        if posted:
            made += 1
            if not dry:
                record_card_post(state, name)
                _record_telegram_post_at(state, gap_key)
        else:
            if LAST_TELEGRAM_SKIP == "cooldown":
                cooldown_hit = True
            break
    if made and not dry and due_slots:
        mark_slots_used(state, name, due_slots[:made])
    if cooldown_hit and made == 0:
        return 0, "cooldown"
    if cap_hit and made == 0:
        return 0, "post cap reached"
    if made == 0 and LAST_TELEGRAM_SKIP == "no_news":
        return 0, "no fresh news"
    if made == 0 and LAST_TELEGRAM_SKIP == "no_channel":
        return 0, "no channel set"
    return made, ("" if made else "post failed or skipped")


# ---------------------------------------------------------------- Nostr
# Free, no account, no approval, no review (verified 2026-11-25
# against NIP-01, github.com/nostr-protocol/nips/blob/master/01.md,
# and pynostr 0.7.0 on PyPI): Nostr is a PROTOCOL, not a service -
# there is no account to create and nobody to approve you. The user
# already has (or makes) a keypair in any Nostr client (Primal,
# Damus, Amethyst): the nsec private key IS the account, the npub
# public key is the public identity. Publishing is ONE signed
# kind-1 text-note event per post, broadcast over wss to public
# relays (relay.damus.io, relay.nostr.band, nos.lol,
# relay.snort.social): the worker sends ["EVENT", {...}] and waits
# for ["OK", id, true, ""] - success is AT LEAST ONE relay acking.
# Event fields per NIP-01: pubkey (hex), created_at (unix seconds),
# kind 1, tags [], content; id = SHA-256 of the [0, pubkey,
# created_at, kind, tags, content] serialization; sig = BIP-340
# Schnorr signature of the id. Signing + broadcast use pynostr
# (maintained fork of python-nostr, coincurve secp256k1) - no
# hand-rolled crypto anywhere. The photo is NOT uploaded anywhere:
# a kind-1 note is text, so the verified photo's PUBLIC URL goes in
# the content as its own line (Nostr clients render image URLs
# inline); a story with no photo URL posts text-only instead - there
# is no 'no photo' skip. Nostr v1 is POST-ONLY: replies ARE possible
# on Nostr (a kind-1 note with e/p tags per NIP-10), but need a
# per-post reply-fetch loop (REQ subscription + EOSE) and posted-id
# tracking, and were not built - see execute_card. Posting only.
# The nsec is NEVER logged, never in state.json, never in a repo
# file - only in the NOSTR_ACCOUNTS env secret. Counts and gaps are
# keyed by the npub (public), which is safe to log and store.
NOSTR_RELAYS = ["wss://relay.damus.io", "wss://relay.nostr.band",
                "wss://nos.lol", "wss://relay.snort.social"]
NOSTR_MIN_POST_GAP_MINUTES = 5
NOSTR_MAX_TEXT_CHARS = 10000
NOSTR_RELAY_TIMEOUT_SECONDS = 8

LAST_NOSTR_SKIP = None


def _nostr_private_key(account):
    """The pynostr PrivateKey for a Nostr account, or None. Accepts
    an nsec1... bech32 key (what Nostr clients show) or a 64-char
    hex key. A bad key logs a plain warning - the key VALUE is never
    logged, not even in part."""
    if not _PYNOSTR_AVAILABLE:
        return None
    raw = ((account or {}).get("nsec") or "").strip()
    if not raw:
        return None
    try:
        if raw.lower().startswith("nsec1"):
            return _NostrPrivateKey.from_nsec(raw)
        return _NostrPrivateKey.from_hex(raw)
    except Exception:
        log("warning", "nostr: an account key could not be read - "
                       "check the nsec in the Nostr tab")
        return None


def _nostr_account_key(account):
    """The per-account key for counts/gaps/settings: the npub
    (bech32 public key) DERIVED from the nsec. Public, safe to log
    and store. A pasted npub is never trusted on its own - the
    derived value always wins when the nsec can be read. "" when
    the key is unreadable."""
    sk = _nostr_private_key(account)
    if sk is not None:
        try:
            return sk.public_key.bech32()
        except Exception:
            return ""
    return ((account or {}).get("npub") or "").strip()


def list_nostr_accounts():
    """The Nostr accounts: the NOSTR_ACCOUNTS env secret (a JSON
    list of {name?, npub?, nsec}). Each entry gains its DERIVED
    npub (from the nsec) and keeps its nsec IN MEMORY ONLY for
    signing. An unreadable nsec is skipped with a plain warning (no
    key material in the log). An empty list means no key is
    configured - a Nostr card cannot run at all then. The nsec NEVER
    leaves this function except into the signing call - it is never
    logged, never in state.json, never in a repo file."""
    if not _PYNOSTR_AVAILABLE:
        log("warning", "nostr: pynostr is not installed - add it to "
                       "requirements.txt and reinstall")
        return []
    out = []
    for acc in (ENV_NOSTR_ACCOUNTS or []):
        if not isinstance(acc, dict):
            continue
        npub = _nostr_account_key(acc)
        if not npub:
            log("warning", "nostr: skipping an account whose key "
                           "could not be read - check the nsec in "
                           "the Nostr tab")
            continue
        entry = {"nsec": (acc.get("nsec") or "").strip(),
                 "npub": npub}
        if (acc.get("name") or "").strip():
            entry["name"] = (acc.get("name") or "").strip()
        out.append(entry)
    return out


def _fit_nostr_text(hook, link, image_url=None):
    """The Nostr note text: hook, then the photo's public URL on its
    own line when there is one (Nostr clients render image URLs
    inline), then the link on its own line. Hard-capped at 10000
    characters at this single send point (the Nostr note limit);
    the link is never cut - the hook is trimmed to make room, and
    the image URL is dropped before the link ever is. Pure function
    (no I/O) - unit-tested."""
    hook = (hook or "").strip()
    link = (link or "").strip()
    image_url = (image_url or "").strip()
    lines = [hook] if hook else []
    if image_url:
        lines.append(image_url)
    if link:
        lines.append(link)
    text = "\n".join(lines)
    if len(text) <= NOSTR_MAX_TEXT_CHARS:
        return text
    tail = "\n".join([l for l in [image_url, link] if l])
    room = NOSTR_MAX_TEXT_CHARS - len(tail) - (1 if tail else 0)
    if room <= 0:
        return tail[:NOSTR_MAX_TEXT_CHARS]
    return hook[:room].rstrip() + ("\n" + tail if tail else "")


def _nostr_build_event(account, text):
    """Build + sign one kind-1 text-note event for an account.
    Returns the signed pynostr Event, or None. The event id is the
    NIP-01 SHA-256 of [0, pubkey, created_at, kind, tags, content]
    and the signature is a BIP-340 Schnorr signature of the id -
    both computed inside pynostr (coincurve), never here."""
    if not _PYNOSTR_AVAILABLE:
        return None
    text = (text or "").strip()
    if not text:
        return None
    sk = _nostr_private_key(account)
    if sk is None:
        return None
    try:
        event = _NostrEvent(content=text, tags=[])
        event.sign(sk.hex())
        return event
    except Exception as e:
        log("warning", f"nostr: could not sign the event: {e}")
        return None


def _nostr_count_oks(manager, event_id):
    """Drain the relay manager's OK notices for one event id and
    count the relays that ACCEPTED it (["OK", id, true, ...]).
    Returns (accepted_count, [relay urls that accepted]). A relay
    that rejected the event (ok=false, e.g. rate-limited) is NOT
    counted - but a "duplicate:" ack still counts as accepted (the
    event IS on that relay). Pure helper, no I/O."""
    accepted = []
    try:
        pool = manager.message_pool
        while pool.has_ok_notices():
            notice = pool.get_ok_notice()
            ok = notice.ok
            if isinstance(ok, str):
                ok = ok.strip().lower() == "true"
            if notice.event_id == event_id and ok:
                accepted.append(notice.url)
    except Exception:
        pass
    return len(accepted), accepted


def nostr_publish(account, text, relays=None):
    """Publish one Nostr kind-1 note: sign it with the account's
    nsec and broadcast it to the public relays, waiting for
    ["OK", ...] acks. Returns the published event id (hex) or None.
    Success is AT LEAST ONE relay acking - a dead relay never fails
    the post, and a dead relay never hangs the worker: the relay
    run is bounded by NOSTR_RELAY_TIMEOUT_SECONDS + 5s. The nsec is
    never logged (only the public event id and the accepting relay
    urls are)."""
    if not _PYNOSTR_AVAILABLE:
        log("warning", "nostr: pynostr is not installed - the post "
                       "was skipped")
        return None
    event = _nostr_build_event(account, text)
    if event is None:
        return None
    urls = list(relays or NOSTR_RELAYS)
    manager = _NostrRelayManager(timeout=NOSTR_RELAY_TIMEOUT_SECONDS)
    for url in urls:
        try:
            manager.add_relay(url)
        except Exception:
            pass

    def _run():
        try:
            manager.publish_event(event)
            manager.run_sync()
        except Exception as e:
            log("warning", f"nostr: relay broadcast failed: {e}")

    worker = threading.Thread(target=_run, daemon=True)
    worker.start()
    worker.join(NOSTR_RELAY_TIMEOUT_SECONDS + 5)
    try:
        manager.close_all_relay_connections()
    except Exception:
        pass
    count, accepted = _nostr_count_oks(manager, event.id)
    if count:
        log("info", f"nostr: published {event.id[:16]}... to "
                    f"{count} relay(s): {', '.join(accepted)}")
        return event.id
    log("warning", "nostr: no relay accepted the event "
                   f"({event.id[:16]}...) - post failed")
    return None


NOSTR_ACCOUNT_SETTINGS_PATH = os.path.join(DATA_DIR, "nostr_accounts.json")


def get_nostr_account_settings():
    """Per-key settings from data/nostr_accounts.json (public, no
    secrets): [{key: <npub>, enabled, posts_per_day}]. Missing file
    = all enabled. Kept in its own file (not accounts.json) so
    saving Bluesky/Reddit/Tumblr/Threads/Mastodon/Telegram controls
    can never wipe Nostr entries and vice versa - the dashboard
    writes this file from the Nostr tab. The key is the npub
    (public) - the nsec is never stored here."""
    if not os.path.exists(NOSTR_ACCOUNT_SETTINGS_PATH):
        return {}
    try:
        with open(NOSTR_ACCOUNT_SETTINGS_PATH, "r", encoding="utf-8") as f:
            data = json.load(f)
        if isinstance(data, list):
            out = {}
            for a in data:
                if not isinstance(a, dict):
                    continue
                key = a.get("key") or ""
                if key:
                    out[key] = a
            return out
        if isinstance(data, dict):
            return data
    except Exception as e:
        log("warning", f"nostr_accounts.json load failed: {e}")
    return {}


def nostr_account_enabled(key):
    cfg = get_nostr_account_settings().get(key)
    if not cfg:
        return True
    return cfg.get("enabled", True) is not False


def nostr_account_posts_limit(key):
    cfg = get_nostr_account_settings().get(key)
    if not cfg:
        return 0
    try:
        return int(cfg.get("posts_per_day") or 0)
    except Exception:
        return 0


NOSTR_CAPTION_PROMPT = """Write ONE short, exciting Nostr post in ENGLISH about this news story, that makes people want to click the link below it. Sound like a real person sharing breaking news, not an ad. Keep it under 400 characters. Do NOT add the link or a call-to-action yourself - they are added after your text.
Style: {tone}
News: {headline}
Link: {link}
"""


def _nostr_gap_key(card):
    """The key the 5-minute no-burst gap is stored under: the
    account's npub (card field account_handle, the public key) -
    two cards sharing one key must not burst-post as it."""
    if isinstance(card, dict):
        return (card.get("account_handle") or "").strip() or card.get("name", "")
    return str(card or "")


def _nostr_gap_left(state, key):
    """Time left on the 5-minute no-burst gap for a Nostr key, or
    None when it may post again."""
    last = (state.get("last_nostr_post_at") or {}).get(key or "")
    if not last:
        return None
    try:
        dt = datetime.fromisoformat(last)
        if dt.tzinfo is None:
            dt = dt.replace(tzinfo=UTC)
    except Exception:
        return None
    left = dt + timedelta(minutes=NOSTR_MIN_POST_GAP_MINUTES) - now_utc()
    return left if left.total_seconds() > 0 else None


def _record_nostr_post_at(state, key):
    """Remember that this Nostr key posted now (state.json, so the
    gap survives across worker runs). The key is the npub - never
    the nsec."""
    state.setdefault("last_nostr_post_at", {})[key or ""] = now_iso()


def record_nostr_post(state, key):
    """Count a Nostr post for this key today (per-key daily
    counts)."""
    counts = state.setdefault("nostr_post_counts", {})
    today = counts.setdefault(today_str(), {})
    today[key] = int(today.get(key, 0)) + 1
    for d in list(counts.keys()):
        try:
            if (now_utc().date() - datetime.strptime(d, "%Y-%m-%d").date()).days > 3:
                counts.pop(d, None)
        except Exception:
            counts.pop(d, None)


def posts_today_for_nostr_account(state, key):
    counts = state.get("nostr_post_counts", {})
    return int(counts.get(today_str(), {}).get(key, 0))


def _card_nostr_post(card, state):
    """Post ONE Nostr card. Returns True on success.
    The post is a fresh Political/War story from the SAME picker as
    Bluesky (_pick_fresh_promo_news) with the SAME shared 24h
    per-topic / per-link cooldown stores recorded, so the same story
    never goes to Bluesky, Reddit, Tumblr, Threads, Mastodon,
    Telegram and Nostr on the same day. The verified photo's PUBLIC
    URL goes in the note as its own line (Nostr clients render
    image URLs inline) - nothing is uploaded. When the story has no
    usable photo, the post still goes out TEXT-only (a fresh story
    from _pick_fresh_reddit_news, which needs no photo) - a missing
    photo never ends the run. Text = hook + photo URL + link,
    hard-capped at 10000 chars by _fit_nostr_text. Same 5-minute
    no-burst gap per key. A cooldown / no-news skip is a clean
    no-op. The nsec is never logged."""
    global LAST_NOSTR_SKIP
    LAST_NOSTR_SKIP = None
    name = card.get("name", "")
    accs = [a for a in list_nostr_accounts()
            if not card.get("account_handle") or
            _nostr_account_key(a) == card["account_handle"]]
    if not accs:
        log("warning", f"card '{name}': no usable Nostr key - post skipped")
        return False
    link = (card.get("link") or "").strip()
    topic, headline, photo = _pick_fresh_promo_news(card, state)
    image_url = ""
    if photo:
        image_url = (photo or {}).get("url", "") or ""
        if image_url and not image_url.lower().startswith("http"):
            image_url = ""
    article_url = (photo or {}).get("article_url", "") if photo else ""
    if not photo:
        # No verified photo for any fresh story - fall back to a
        # fresh story that needs no photo and post TEXT-only (the
        # picker already logged why; LAST_BSKY_SKIP says no_photo).
        topic2, headline2, url2 = _pick_fresh_reddit_news(card, state)
        if not headline2:
            log("warning", f"card '{name}': no fresh news - Nostr post "
                           "skipped")
            LAST_NOSTR_SKIP = {"cooldown": "cooldown",
                               "no_news": "no_news"}.get(
                LAST_REDDIT_SKIP, "no_news")
            return False
        log("info", f"card '{name}': no verified photo - posting "
                     "text-only to Nostr")
        topic, headline = topic2, headline2
        article_url = url2 or ""
        image_url = ""
    headline = headline or topic
    effective_link = link or article_url
    if _promo_topic_cooldown_left(state, headline) is not None:
        log("info", f"card '{name}': news story already used within "
                    f"24h - cooldown, skipping")
        LAST_NOSTR_SKIP = "cooldown"
        return False
    if _promo_link_topic_cooldown_left(state, effective_link, headline) is not None:
        log("info", f"card '{name}': same link + same event within "
                    f"24h - cooldown, skipping")
        LAST_NOSTR_SKIP = "cooldown"
        return False
    tone_text = ARTICLE_TONES[card_tone(card)]
    text = (card.get("text") or "").strip()
    if not text:
        try:
            text = (ai_write(
                NOSTR_CAPTION_PROMPT.format(
                    headline=headline[:150], link=effective_link,
                    tone=tone_text), max_tokens=400) or "").strip()
        except Exception:
            text = ""
        if not text:
            text = headline
    post_text = _fit_nostr_text(text, effective_link,
                                image_url or None)
    if is_dry_run():
        log("warning", f"[DRY RUN] card '{name}': would post to Nostr "
                       f"(npub {_nostr_account_key(accs[0])[:16]}...) "
                       f"'{headline[:60]}' -> {effective_link[:60]}")
        return True
    ok = False
    for acc in accs[:1]:
        key = _nostr_account_key(acc)
        if not key:
            continue
        if not nostr_account_enabled(key):
            continue
        limit = nostr_account_posts_limit(key)
        if limit > 0 and posts_today_for_nostr_account(state, key) >= limit:
            log("info", f"card '{name}': Nostr key {key[:16]}... daily "
                        "limit reached - skipping")
            continue
        res = retry_with_backoff(
            lambda: nostr_publish(acc, post_text),
            attempts=2, base_delay=5, label="nostr publish")
        if res:
            _record_promo_topic_posted(state, headline)
            _record_promo_link_topic_posted(state, effective_link, headline)
            _record_promo_account_posted(state, headline, key)
            record_nostr_post(state, key)
            _record_nostr_post_at(state, key)
            log("info", f"card '{name}': posted to Nostr ({key[:16]}...): "
                        f"{res[:16]}...")
            ok = True
            break
        log("warning", f"card '{name}': nostr publish failed")
    return ok


def _post_nostr_card(card, state, due_slots):
    """The posting loop for nostr_post cards. Returns (made, last_error).
    Mirrors _post_mastodon_card: 5-minute gap per key, posts-per-run,
    due slots, day/week/month caps. Clean skips (cooldown, too soon,
    cap, no fresh news) are no-ops, not failures. There is no
    'no photo' skip: a story without a verified photo posts
    text-only instead (the photo URL line is simply absent)."""
    global LAST_NOSTR_SKIP
    name = card.get("name", "")
    dry = is_dry_run()
    made = 0
    cooldown_hit = False
    cap_hit = False
    gap_key = _nostr_gap_key(card)
    if not dry and _nostr_gap_left(state, gap_key) is not None:
        log("info", f"card '{name}': posted less than "
                    f"{NOSTR_MIN_POST_GAP_MINUTES} minutes ago - too soon, skipping")
        return 0, "too soon"
    while True:
        card = _refresh_card(card)
        log_card_settings(card)
        remaining = card_caps_remaining(state, name, card)
        if remaining is not None and remaining <= 0:
            log("info", f"card '{name}': post cap reached - skipping")
            cap_hit = True
            break
        if made >= card_posts_per_run(card):
            break
        if due_slots and made >= len(due_slots):
            break
        try:
            posted = _card_nostr_post(card, state)
        except Exception as e:
            log("error", f"card '{name}': post attempt failed: {e}")
            LAST_NOSTR_SKIP = None
            break
        if posted:
            made += 1
            if not dry:
                record_card_post(state, name)
                _record_nostr_post_at(state, gap_key)
        else:
            if LAST_NOSTR_SKIP == "cooldown":
                cooldown_hit = True
            break
    if made and not dry and due_slots:
        mark_slots_used(state, name, due_slots[:made])
    if cooldown_hit and made == 0:
        return 0, "cooldown"
    if cap_hit and made == 0:
        return 0, "post cap reached"
    if made == 0 and LAST_NOSTR_SKIP == "no_news":
        return 0, "no fresh news"
    return made, ("" if made else "post failed or skipped")


# ---------------------------------------------------------------- Lemmy
# Free, open API, no app registration, no review (verified 2026-11-25
# against join-lemmy.org/docs/contributors/04-api.html - Lemmy's own
# API page, which links the OpenAPI spec + lemmy-js-client - and the
# lemmy_api_common 0.16.7 CreatePost struct {name, community_id, url,
# body, auth}): any user account on any Lemmy instance (e.g.
# lemmy.world) can log in with username + password and post. There
# is no app to register and no approval to wait for - that is the
# door that was closed for Reddit and open here.
# Login: POST /api/v3/user/login {username_or_email, password} ->
# {"jwt": ...}. The JWT is cached in memory and sent as the "auth"
# field of every later JSON body (POST) or query param (GET); a 401
# drops the cached JWT and retries once with a fresh login. Create
# post: POST /api/v3/post {community_id, name, url, body, auth}.
# The post goes INTO a community, which has its own rules - the card
# names the community (REQUIRED, like Reddit's subreddit) and the
# worker resolves the name to a community_id first via
# GET /api/v3/community?name=<name> (cached in memory per
# account+name). Title is hard-capped at 200 chars (Lemmy's
# post-name limit). url = the card's Smartlink, body = the hook
# text. NO photo is needed (a link post carries the link's own
# preview). Repeated Smartlink = spam/ban risk - same mitigation as
# Reddit: fresh story per post, varied titles, per-card caps, shared
# cooldowns. Lemmy v1 is POST-ONLY: replies ARE possible
# (POST /api/v3/comment with a parent_id), but need a per-post
# reply-fetch loop and posted-id tracking, and were not built - see
# execute_card. Posting only. The JWT and password are NEVER logged,
# never in state.json, never in a repo file - only in the
# LEMMY_ACCOUNTS env secret. Counts and gaps are keyed by
# "instance|username", which is safe to log and store. Lemmy
# rate-limits per IP, so the worker's shared GitHub Actions IP can
# hit limits on a busy instance - a 429 is a clean skip, not a retry.
LEMMY_MIN_POST_GAP_MINUTES = 5
LEMMY_MAX_TITLE_CHARS = 200
LEMMY_MAX_BODY_CHARS = 10000

LAST_LEMMY_SKIP = None
_LEMMY_JWTS = {}
_LEMMY_COMMUNITIES = {}


def _lemmy_instance_base(account):
    """The instance base URL for a Lemmy account, e.g.
    "https://lemmy.world". A bare host ("lemmy.world") gains the
    https:// scheme; a trailing slash is stripped. "" when no
    instance is set."""
    raw = ((account or {}).get("instance") or "").strip().rstrip("/")
    if not raw:
        return ""
    if not raw.lower().startswith(("http://", "https://")):
        raw = "https://" + raw
    return raw


def _lemmy_account_key(account):
    """The per-account key for counts/gaps/settings/controls:
    "instance|username" (e.g. "lemmy.world|testuser"). Public, safe
    to log and store - it holds no password and no JWT. "" when the
    instance or username is missing."""
    base = _lemmy_instance_base(account)
    host = base.split("://", 1)[-1].strip("/").lower() if base else ""
    username = ((account or {}).get("username") or "").strip()
    if not host or not username:
        return ""
    return f"{host}|{username}"


def list_lemmy_accounts():
    """All Lemmy accounts: the LEMMY_ACCOUNTS env secret (JSON list)
    or the single-account env vars. (The dashboard saves accounts
    encrypted into the secret, same sealed-box pattern as Bluesky.)"""
    return list(ENV_LEMMY_ACCOUNTS)


def _lemmy_clean_community(name):
    """Normalise a community as typed on the card: strip whitespace,
    a leading '!' (the !community@instance form) and a leading 'c/'
    (the c/community form). "news@lemmy.world" passes through as-is
    - Lemmy resolves federated communities by that handle."""
    c = (name or "").strip()
    c = c.lstrip("!").strip()
    if c.lower().startswith("c/"):
        c = c[2:].strip()
    return c


def _lemmy_login(account):
    """The JWT for a Lemmy account (POST /api/v3/user/login).
    Cached in memory until a 401 drops it; a failed result is never
    cached. Logs only success or failure - never the JWT or the
    password."""
    key = _lemmy_account_key(account)
    if not key:
        return None
    cached = _LEMMY_JWTS.get(key)
    if cached:
        return cached
    base = _lemmy_instance_base(account)
    if not base:
        return None
    username = (account or {}).get("username", "")
    try:
        r = requests.post(
            base + "/api/v3/user/login",
            json={"username_or_email": username,
                  "password": account.get("password", "")},
            timeout=20)
    except Exception as e:
        log("warning", f"lemmy login failed for {key}: {e}")
        return None
    if r.status_code != 200:
        log("warning", f"lemmy login failed for {key}: HTTP {r.status_code}")
        return None
    try:
        data = r.json()
    except Exception:
        log("warning", f"lemmy login response not JSON for {key}")
        return None
    token = data.get("jwt", "")
    if not token:
        log("warning", f"lemmy login returned no token for {key}")
        return None
    _LEMMY_JWTS[key] = token
    log("info", f"lemmy: logged in as {key}")
    return token


def lemmy_request(account, method, path, **kwargs):
    """One authenticated Lemmy API call. Returns the Response or
    None. The JWT goes in the JSON body as "auth" (POST) or in the
    query params (GET), per the Lemmy API v3 convention. On a 401
    the cached JWT is dropped and the call is retried once with a
    fresh login. kwargs pass through to requests (params/json)."""
    key = _lemmy_account_key(account)
    base = _lemmy_instance_base(account)
    if not key or not base:
        return None
    url = base + path
    for attempt in (1, 2):
        token = _lemmy_login(account)
        if not token:
            return None
        kw = dict(kwargs)
        if method.upper() == "GET":
            params = dict(kw.pop("params", {}) or {})
            params["auth"] = token
            kw["params"] = params
        else:
            body = dict(kw.pop("json", {}) or {})
            body["auth"] = token
            kw["json"] = body
        try:
            r = requests.request(method, url, timeout=25, **kw)
        except Exception as e:
            log("warning", f"lemmy {method} {path} failed: {e}")
            return None
        if r.status_code == 401 and attempt == 1:
            _LEMMY_JWTS.pop(key, None)
            log("info", f"lemmy: token expired for {key} - re-authenticating")
            continue
        return r
    return None


def lemmy_resolve_community(account, name):
    """Resolve a community NAME to its numeric community_id (cached
    in memory per account+name, so a card does not re-resolve on
    every post). Returns the id or None. The name is given as the
    user typed it on the card (e.g. news, or news@lemmy.world for a
    federated community)."""
    comm = _lemmy_clean_community(name)
    if not comm:
        return None
    key = _lemmy_account_key(account)
    cache_key = (key, comm.lower())
    if cache_key in _LEMMY_COMMUNITIES:
        return _LEMMY_COMMUNITIES[cache_key]
    r = lemmy_request(account, "GET", "/api/v3/community",
                      params={"name": comm})
    if r is None or r.status_code != 200:
        log("warning", f"lemmy: community c/{comm} lookup failed (HTTP "
                       f"{r.status_code if r is not None else 'no response'})")
        return None
    try:
        cid = (((r.json().get("community_view") or {}).get("community")
                or {}).get("id"))
    except Exception:
        log("warning", f"lemmy: community c/{comm} lookup not JSON")
        return None
    if not cid:
        log("warning", f"lemmy: community c/{comm} not found on "
                       f"{_lemmy_instance_base(account)}")
        return None
    _LEMMY_COMMUNITIES[cache_key] = cid
    return cid


def lemmy_submit(account, community, title, url=None, body=None):
    """Create a Lemmy post in a community. A link post (title + url
    + hook body). The title is hard-capped at 200 chars (Lemmy's
    post-name limit) and the body at 10,000 chars at this single
    send point. Returns (post_id, post_url) or None."""
    comm = _lemmy_clean_community(community)
    if not comm:
        return None
    title = (title or "").strip()[:LEMMY_MAX_TITLE_CHARS]
    if not title:
        return None
    community_id = lemmy_resolve_community(account, comm)
    if not community_id:
        log("warning", f"lemmy: community c/{comm} could not be resolved")
        return None
    payload = {"community_id": community_id, "name": title}
    if url:
        payload["url"] = (url or "").strip()
    if body:
        payload["body"] = (body or "").strip()[:LEMMY_MAX_BODY_CHARS]
    r = lemmy_request(account, "POST", "/api/v3/post", json=payload)
    if r is None or r.status_code != 200:
        log("warning", "lemmy submit failed (HTTP "
                       f"{r.status_code if r is not None else 'no response'})")
        return None
    try:
        post = ((r.json().get("post_view") or {}).get("post") or {})
    except Exception:
        log("warning", "lemmy submit response not JSON")
        return None
    post_id = post.get("id")
    if not post_id:
        log("warning", "lemmy submit returned no post id")
        return None
    post_url = post.get("ap_id", "") or ""
    log("info", f"lemmy: posted to c/{comm}: {post_url or post_id}")
    return post_id, post_url


LEMMY_TITLE_PROMPT = """Write ONE short, exciting Lemmy post title in ENGLISH about this news story, that makes people want to click it. Sound like a real person sharing breaking news, not an ad. Keep it under 200 characters. Do NOT add a link.

News: {headline}
"""

LEMMY_HOOK_PROMPT = """Write ONE short, exciting hook in ENGLISH about this news story, that makes people want to click the link. Sound like a real person sharing breaking news, not an ad. Keep it under 400 characters. Do NOT add the link or a call-to-action yourself - they are added after your text.

News: {headline}
"""


def _pick_fresh_lemmy_news(card, state):
    """Pick a FRESH news story for a Lemmy post: (topic, headline,
    article_url). Reuses the Reddit picker verbatim - the same
    categories (ONLY USA political news and war news, rotating; the
    card's topic_override is the only other allowed topic) and the
    same 24h per-topic / per-link cooldowns, and NO photo is needed
    (a Lemmy link post is a title + a link + a hook body), so a
    story is picked as soon as it is fresh. Returns
    (None, None, None) when no fresh story exists;
    LAST_LEMMY_SKIP says why ("cooldown" or "no_news") - copied
    from LAST_REDDIT_SKIP, which the shared picker sets."""
    global LAST_LEMMY_SKIP
    topic, headline, url = _pick_fresh_reddit_news(card, state)
    LAST_LEMMY_SKIP = LAST_REDDIT_SKIP
    return topic, headline, url


def _lemmy_gap_key(card):
    """The key the 5-minute no-burst gap is stored under: the Lemmy
    account key ("instance|username"), not the card name (same rule
    as Bluesky - two cards sharing one account must not burst-post
    to it)."""
    if isinstance(card, dict):
        return (card.get("account_handle") or "").strip() or card.get("name", "")
    return str(card or "")


def _lemmy_gap_left(state, key):
    """Time left on the 5-minute no-burst gap for a Lemmy account,
    or None when it may post again."""
    last = (state.get("last_lemmy_post_at") or {}).get(key or "")
    if not last:
        return None
    try:
        dt = datetime.fromisoformat(last)
        if dt.tzinfo is None:
            dt = dt.replace(tzinfo=UTC)
    except Exception:
        return None
    left = dt + timedelta(minutes=LEMMY_MIN_POST_GAP_MINUTES) - now_utc()
    return left if left.total_seconds() > 0 else None


def _record_lemmy_post_at(state, key):
    """Remember that this Lemmy account posted now (state.json, so
    the gap survives across worker runs)."""
    state.setdefault("last_lemmy_post_at", {})[key or ""] = now_iso()


def record_lemmy_post(state, key):
    """Count a Lemmy post for this account today (per-account limits)."""
    counts = state.setdefault("lemmy_post_counts", {})
    today = counts.setdefault(today_str(), {})
    today[key] = int(today.get(key, 0)) + 1
    for d in list(counts.keys()):
        try:
            if (now_utc().date() - datetime.strptime(d, "%Y-%m-%d").date()).days > 3:
                counts.pop(d, None)
        except Exception:
            counts.pop(d, None)


def posts_today_for_lemmy_account(state, key):
    counts = state.get("lemmy_post_counts", {})
    return int(counts.get(today_str(), {}).get(key, 0))


LEMMY_ACCOUNT_SETTINGS_PATH = os.path.join(DATA_DIR, "lemmy_accounts.json")


def get_lemmy_account_settings():
    """Per-account settings from data/lemmy_accounts.json (public, no
    passwords): [{key, enabled, posts_per_day}] keyed by
    "instance|username". Missing file = all enabled. Kept in its own
    file (not accounts.json) so saving Lemmy controls can never wipe
    another platform's entries - the dashboard writes this file from
    the Lemmy tab."""
    if not os.path.exists(LEMMY_ACCOUNT_SETTINGS_PATH):
        return {}
    try:
        with open(LEMMY_ACCOUNT_SETTINGS_PATH, "r", encoding="utf-8") as f:
            data = json.load(f)
        if isinstance(data, list):
            return {a["key"]: a for a in data
                    if isinstance(a, dict) and a.get("key")}
        if isinstance(data, dict):
            return data
    except Exception as e:
        log("warning", f"lemmy_accounts.json load failed: {e}")
    return {}


def lemmy_account_enabled(key):
    cfg = get_lemmy_account_settings().get(key)
    if not cfg:
        return True
    return cfg.get("enabled", True) is not False


def lemmy_account_posts_limit(key):
    cfg = get_lemmy_account_settings().get(key)
    if not cfg:
        return 0
    try:
        return int(cfg.get("posts_per_day") or 0)
    except Exception:
        return 0


def _card_lemmy_post(card, state):
    """Post ONE Lemmy card. Returns True on success.
    The post is a LINK post to the card's community: the title is an
    AI hook about a fresh Political/War news story (the headline
    itself when the AI is down, the card's own text when set), the
    URL is the card's link (or the story's own URL when the card has
    no link) and the body is a short AI hook about the same story.
    No photo is needed. Same 24h per-topic / per-link cooldowns as
    Bluesky (shared stores - the same story never goes to both
    Bluesky and Lemmy on the same day) and the same 5-minute
    no-burst gap per account. A cooldown / no-news / no-community
    skip is a clean no-op (LAST_LEMMY_SKIP)."""
    global LAST_LEMMY_SKIP
    LAST_LEMMY_SKIP = None
    name = card.get("name", "")
    community = _lemmy_clean_community(card.get("community") or "")
    if not community:
        log("warning", f"card '{name}': no community set - post skipped")
        LAST_LEMMY_SKIP = "no_community"
        return False
    accs = [a for a in list_lemmy_accounts()
            if not card.get("account_handle") or
            _lemmy_account_key(a) == card["account_handle"]]
    if not accs:
        log("warning", f"card '{name}': no usable Lemmy account - post skipped")
        return False
    link = (card.get("link") or "").strip()
    topic, headline, article_url = _pick_fresh_lemmy_news(card, state)
    if not headline:
        # No fresh story (the picker already said why - "cooldown"
        # or "no_news"; an absent reason defaults to no_news, same
        # rule as Nostr).
        if not LAST_LEMMY_SKIP:
            LAST_LEMMY_SKIP = "no_news"
        log("warning", f"card '{name}': no fresh news - Lemmy post skipped")
        return False
    effective_link = link or article_url
    if _promo_topic_cooldown_left(state, headline) is not None:
        log("info", f"card '{name}': news story already used within "
                    f"24h - cooldown, skipping")
        LAST_LEMMY_SKIP = "cooldown"
        return False
    if _promo_link_topic_cooldown_left(state, effective_link, headline) is not None:
        log("info", f"card '{name}': same link + same event within "
                    f"24h - cooldown, skipping")
        LAST_LEMMY_SKIP = "cooldown"
        return False
    title = (card.get("text") or "").strip()
    if not title:
        try:
            title = (ai_write(LEMMY_TITLE_PROMPT.format(headline=headline),
                              max_tokens=200) or "").strip()
        except Exception:
            title = ""
        if not title:
            title = headline
    title = title[:LEMMY_MAX_TITLE_CHARS]
    try:
        body = (ai_write(LEMMY_HOOK_PROMPT.format(headline=headline),
                         max_tokens=400) or "").strip()
    except Exception:
        body = ""
    if not body:
        body = headline
    body = body[:LEMMY_MAX_BODY_CHARS]
    if is_dry_run():
        log("warning", f"[DRY RUN] card '{name}': would post to c/{community} "
                       f"({_lemmy_account_key(accs[0])}) '{title[:60]}' -> "
                       f"{effective_link[:60]}")
        return True
    ok = False
    for acc in accs[:1]:
        key = _lemmy_account_key(acc)
        if not key:
            continue
        if not lemmy_account_enabled(key):
            continue
        limit = lemmy_account_posts_limit(key)
        if limit > 0 and posts_today_for_lemmy_account(state, key) >= limit:
            log("info", f"card '{name}': Lemmy account {key} daily "
                        "limit reached - skipping")
            continue
        res = retry_with_backoff(
            lambda: lemmy_submit(acc, community, title,
                                 url=effective_link, body=body),
            attempts=2, base_delay=5, label="lemmy submit")
        if res:
            post_id, post_url = res
            _record_promo_topic_posted(state, headline)
            _record_promo_link_topic_posted(state, effective_link, headline)
            _record_promo_account_posted(state, headline, key)
            record_lemmy_post(state, key)
            _record_lemmy_post_at(state, key)
            log("info", f"card '{name}': posted to c/{community} as "
                        f"{key}: {post_url or post_id}")
            ok = True
            break
        log("warning", f"card '{name}': lemmy submit failed")
    return ok


def _post_lemmy_card(card, state, due_slots):
    """The posting loop for lemmy_post cards. Returns (made, last_error).
    Mirrors _post_reddit_card: 5-minute gap per account, posts-per-run,
    due slots, day/week/month caps. Clean skips (cooldown, too soon,
    cap, no fresh news, no community) are no-ops, not failures."""
    global LAST_LEMMY_SKIP
    name = card.get("name", "")
    dry = is_dry_run()
    made = 0
    cooldown_hit = False
    cap_hit = False
    gap_key = _lemmy_gap_key(card)
    if not dry and _lemmy_gap_left(state, gap_key) is not None:
        log("info", f"card '{name}': posted less than "
                    f"{LEMMY_MIN_POST_GAP_MINUTES} minutes ago - too soon, skipping")
        return 0, "too soon"
    while True:
        card = _refresh_card(card)
        log_card_settings(card)
        remaining = card_caps_remaining(state, name, card)
        if remaining is not None and remaining <= 0:
            log("info", f"card '{name}': post cap reached - skipping")
            cap_hit = True
            break
        if made >= card_posts_per_run(card):
            break
        if due_slots and made >= len(due_slots):
            break
        try:
            posted = _card_lemmy_post(card, state)
        except Exception as e:
            log("error", f"card '{name}': post attempt failed: {e}")
            LAST_LEMMY_SKIP = None
            break
        if posted:
            made += 1
            if not dry:
                record_card_post(state, name)
                _record_lemmy_post_at(state, gap_key)
        else:
            if LAST_LEMMY_SKIP == "cooldown":
                cooldown_hit = True
            break
    if made and not dry and due_slots:
        mark_slots_used(state, name, due_slots[:made])
    if cooldown_hit and made == 0:
        return 0, "cooldown"
    if cap_hit and made == 0:
        return 0, "post cap reached"
    if made == 0 and LAST_LEMMY_SKIP == "no_news":
        return 0, "no fresh news"
    if made == 0 and LAST_LEMMY_SKIP == "no_community":
        return 0, "no community set"
    return made, ("" if made else "post failed or skipped")


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


# ---------------------------------------------------------------- dev.to
# Free, full REST API, no app registration, no review, no approval
# (verified 2026-11-25 against the official Forem API v1 reference
# at developers.forem.com/api/v1 - "Publish article" - plus the
# dev.to API guides): POST https://dev.to/api/articles with
# {"article": {title, body_markdown, published, tags, main_image,
# canonical_url, description}} creates an article (201). Auth is
# ONE header, "api-key: <key>" (+ Accept:
# application/vnd.forem.api-v1+json); the key is generated at
# dev.to Settings > Extensions. Tags are a comma-separated string,
# max 4. Rate limit on article creation: 10 requests per 30s.
#
# TWO DESIGN DECISIONS (stated plainly, not buried):
# 1. CANONICAL URL: the canonical_url should point at the Blogger
#    post - but the Blogger API is restricted and posts go up via
#    the browser, so the worker does NOT know the Blogger post URL
#    at post time. RULE: post WITHOUT canonical_url when the worker
#    does not know it (dev.to allows the field to be omitted) and
#    log plainly that the canonical link should be set once the
#    Blogger post is live. The card carries an OPTIONAL
#    canonical_url field the user can fill per post; the default is
#    "omit when unknown". The worker NEVER fabricates a URL and
#    NEVER points canonical_url at the blog homepage.
# 2. BODY FORMAT: generate the article in Markdown DIRECTLY (option
#    b) - no HTML->Markdown converter. The worker's Gemini article
#    text IS already Markdown (## subheadings, **bold** - see
#    ARTICLE_PROMPT); build_article_html converts it to HTML only
#    for Blogger. For dev.to the raw article text is used as-is
#    (only the HEADLINE: line is dropped - it becomes the title).
#    The verified photo's public URL goes in as main_image (the
#    cover image), not embedded in the body.
# Audience is developers - this is an SEO/canonical play, not a
# news-feed play. dev.to v1 is POST-ONLY: article comments exist
# (POST /api/comments) but the comment-fetch loop was not built -
# see execute_card. The API key is NEVER logged, never in
# state.json, never in a repo file - only in the DEVTO_API_KEY env
# secret. Counts and gaps are keyed by "devto" (one key - there is
# no account name, and the key itself never appears in state).
DEVTO_MIN_POST_GAP_MINUTES = 5
DEVTO_MAX_TITLE_CHARS = 200
DEVTO_MAX_BODY_CHARS = 100000
DEVTO_API_URL = "https://dev.to/api/articles"

LAST_DEVTO_SKIP = None


def devto_api_key():
    """The dev.to API key from the DEVTO_API_KEY env secret.
    Empty when not configured - a dev.to card cannot run then.
    The key value is NEVER logged."""
    return ENV_DEVTO_API_KEY


def list_devto_accounts():
    """The dev.to 'account': the single API key (one key, from
    dev.to Settings > Extensions). An empty list means no key is
    configured - a dev.to card cannot run at all then."""
    if not devto_api_key():
        return []
    return [{"api_key": devto_api_key(), "name": "dev.to"}]


def _devto_account_key(account=None):
    """The per-key key for counts/gaps/settings/controls: always
    "devto" (one API key - there is no account name, and the key
    itself never appears in state or logs)."""
    return "devto"


def _devto_clean_tags(raw):
    """Normalise tags (a list or a comma string) for dev.to: up to
    4, lowercase, no spaces (spaces become '-'), only a-z, 0-9 and
    '-'. Duplicates dropped, order kept."""
    if isinstance(raw, str):
        parts = raw.split(",")
    elif isinstance(raw, (list, tuple)):
        parts = list(raw)
    else:
        parts = []
    out = []
    for p in parts:
        t = re.sub(r"[^a-z0-9\-]", "",
                   str(p or "").strip().lower().replace(" ", "-"))
        if t and t not in out:
            out.append(t)
    return out[:4]


def _devto_tags(card, topic):
    """The tags for a dev.to article (max 4). The card's own tags
    win when set; otherwise war news gets news+world and everything
    else (political news, a custom topic) gets news+politics."""
    tags = _devto_clean_tags((card or {}).get("tags"))
    if tags:
        return tags
    if (topic or "").strip().lower() == "war news":
        return ["news", "world"]
    return ["news", "politics"]


def _devto_canonical_url(card):
    """The card's optional Canonical URL (the Blogger post URL, once
    it is live). Empty when unknown - the worker NEVER guesses a URL
    and NEVER points it at the blog homepage: dev.to allows
    canonical_url to be omitted, and _card_devto_post logs plainly
    when it posts without one."""
    raw = ((card or {}).get("canonical_url") or "").strip()
    if not raw or not raw.lower().startswith("http"):
        return ""
    return raw


def card_devto_published(card):
    """Publish immediately (True) or save as a draft (False)? The
    card's devto_published field decides; the default is True -
    a scheduled dev.to card publishes, like every other card."""
    v = (card or {}).get("devto_published")
    if v is None:
        return True
    if isinstance(v, str):
        return v.strip().lower() != "false"
    return bool(v)


def _devto_body_markdown(article_text):
    """The dev.to article body, in Markdown, from the Gemini article
    text. The text IS already Markdown (## subheadings, **bold** -
    see ARTICLE_PROMPT), so it is used as-is: only the HEADLINE:
    line is dropped (it becomes the title) and leading/trailing
    blank lines are trimmed. No HTML is involved at all - that is
    the whole point (option b: generate in Markdown directly)."""
    lines = []
    for line in (article_text or "").splitlines():
        if line.strip().startswith("HEADLINE:"):
            continue
        lines.append(line.rstrip())
    while lines and not lines[0].strip():
        lines.pop(0)
    while lines and not lines[-1].strip():
        lines.pop()
    return "\n".join(lines)


def devto_submit(title, body_markdown, tags, main_image=None,
                 canonical_url=None, published=True):
    """Create a dev.to article: POST /api/articles with
    {"article": {...}}. The title is hard-capped at 200 chars and
    the body at 100,000 chars at this single send point. Tags go as
    the comma-separated string the official spec wants (max 4).
    main_image is the cover image URL; canonical_url is only sent
    when known (omitted otherwise - never fabricated, never the
    homepage). Returns (article_id, article_url) or None. The API
    key is NEVER logged (only the status and the article URL)."""
    key = devto_api_key()
    if not key:
        log("warning", "dev.to submit failed: no API key configured")
        return None
    title = (title or "").strip()[:DEVTO_MAX_TITLE_CHARS]
    body_markdown = (body_markdown or "").strip()[:DEVTO_MAX_BODY_CHARS]
    if not title or not body_markdown:
        return None
    article = {"title": title, "body_markdown": body_markdown,
               "published": bool(published)}
    tag_list = _devto_clean_tags(tags)
    if tag_list:
        article["tags"] = ",".join(tag_list)
    if main_image:
        article["main_image"] = (main_image or "").strip()
    if canonical_url:
        article["canonical_url"] = (canonical_url or "").strip()
    # description: the first real paragraph, plain text, <= 150 chars.
    first_para = ""
    for line in body_markdown.splitlines():
        text = re.sub(r"[#*_`>\[\]()]", "", line).strip()
        if len(text) >= 40:
            first_para = text
            break
    if first_para:
        article["description"] = first_para[:150]
    try:
        r = requests.post(
            DEVTO_API_URL, json={"article": article},
            headers={"api-key": key,
                     "Accept": "application/vnd.forem.api-v1+json",
                     "Content-Type": "application/json"},
            timeout=25)
    except Exception as e:
        log("warning", f"dev.to submit failed: {e}")
        return None
    if r.status_code not in (200, 201):
        log("warning", f"dev.to submit failed (HTTP {r.status_code})")
        return None
    try:
        data = r.json()
    except Exception:
        log("warning", "dev.to submit response not JSON")
        return None
    art_id = data.get("id")
    if not art_id:
        log("warning", "dev.to submit returned no article id")
        return None
    art_url = data.get("url", "") or ""
    log("info", f"dev.to: posted '{title[:60]}': {art_url or art_id}")
    return art_id, art_url


def _pick_fresh_devto_news(card, state):
    """Pick a FRESH news story for a dev.to article: (topic,
    headline, article_url). Reuses the Reddit picker verbatim - the
    same categories (ONLY USA political news and war news, rotating;
    the card's topic_override is the only other allowed topic) and
    the same 24h per-topic / per-link cooldowns, so the same story
    never goes to two platforms the same day. Returns
    (None, None, None) when no fresh story exists; LAST_DEVTO_SKIP
    says why ("cooldown" or "no_news") - copied from
    LAST_REDDIT_SKIP, which the shared picker sets."""
    global LAST_DEVTO_SKIP
    topic, headline, url = _pick_fresh_reddit_news(card, state)
    LAST_DEVTO_SKIP = LAST_REDDIT_SKIP
    return topic, headline, url


def _devto_gap_key(card):
    """The key the 5-minute no-burst gap is stored under: "devto"
    (one API key - two cards sharing the key must not burst-post)."""
    return "devto"


def _devto_gap_left(state, key):
    """Time left on the 5-minute no-burst gap for the dev.to key,
    or None when it may post again."""
    last = (state.get("last_devto_post_at") or {}).get(key or "")
    if not last:
        return None
    try:
        dt = datetime.fromisoformat(last)
        if dt.tzinfo is None:
            dt = dt.replace(tzinfo=UTC)
    except Exception:
        return None
    left = dt + timedelta(minutes=DEVTO_MIN_POST_GAP_MINUTES) - now_utc()
    return left if left.total_seconds() > 0 else None


def _record_devto_post_at(state, key):
    """Remember that dev.to posted now (state.json, so the gap
    survives across worker runs)."""
    state.setdefault("last_devto_post_at", {})[key or ""] = now_iso()


def record_devto_post(state, key):
    """Count a dev.to post for today (per-key daily counts)."""
    counts = state.setdefault("devto_post_counts", {})
    today = counts.setdefault(today_str(), {})
    today[key] = int(today.get(key, 0)) + 1
    for d in list(counts.keys()):
        try:
            if (now_utc().date() - datetime.strptime(d, "%Y-%m-%d").date()).days > 3:
                counts.pop(d, None)
        except Exception:
            counts.pop(d, None)


def posts_today_for_devto_account(state, key):
    counts = state.get("devto_post_counts", {})
    return int(counts.get(today_str(), {}).get(key, 0))


DEVTO_ACCOUNT_SETTINGS_PATH = os.path.join(DATA_DIR, "devto_accounts.json")


def get_devto_account_settings():
    """Per-key settings from data/devto_accounts.json (public, no
    key): [{key: "devto", enabled, posts_per_day}]. Missing file =
    all enabled. Kept in its own file (not accounts.json) so saving
    dev.to controls can never wipe another platform's entries - the
    dashboard writes this file from the dev.to tab."""
    if not os.path.exists(DEVTO_ACCOUNT_SETTINGS_PATH):
        return {}
    try:
        with open(DEVTO_ACCOUNT_SETTINGS_PATH, "r", encoding="utf-8") as f:
            data = json.load(f)
        if isinstance(data, list):
            out = {}
            for a in data:
                if not isinstance(a, dict):
                    continue
                key = a.get("key") or _devto_account_key()
                if key:
                    out[key] = a
            return out
        if isinstance(data, dict):
            return data
    except Exception as e:
        log("warning", f"devto_accounts.json load failed: {e}")
    return {}


def devto_account_enabled(key):
    cfg = get_devto_account_settings().get(key)
    if not cfg:
        return True
    return cfg.get("enabled", True) is not False


def devto_account_posts_limit(key):
    cfg = get_devto_account_settings().get(key)
    if not cfg:
        return 0
    try:
        return int(cfg.get("posts_per_day") or 0)
    except Exception:
        return 0


def _card_devto_post(card, state):
    """Post ONE dev.to article. Returns True on success.
    The article is a FULL article about a fresh Political/War news
    story (the same picker + shared cooldowns as Bluesky, so the
    same story never goes to two platforms the same day), written
    by Gemini in Markdown and posted with the verified photo as the
    cover image (main_image). PHOTO FIRST (strict rule): no
    verified photo = the story is dropped, never text-only - a
    dev.to article without a cover image is not posted. The
    canonical_url is the card's optional field, sent only when the
    user filled it (the Blogger post URL, once live); when it is
    empty the article posts WITHOUT canonical_url and the log says
    so plainly. Same 5-minute no-burst gap per key. A cooldown /
    no-news / no-photo skip is a clean no-op (LAST_DEVTO_SKIP)."""
    global LAST_DEVTO_SKIP
    LAST_DEVTO_SKIP = None
    name = card.get("name", "")
    key = _devto_account_key()
    if not devto_api_key():
        log("warning", f"card '{name}': no dev.to API key - post skipped")
        LAST_DEVTO_SKIP = "no_key"
        return False
    if not devto_account_enabled(key):
        log("info", f"card '{name}': dev.to key is disabled - skipping")
        return False
    limit = devto_account_posts_limit(key)
    if limit > 0 and posts_today_for_devto_account(state, key) >= limit:
        log("info", f"card '{name}': dev.to daily limit reached - skipping")
        return False
    topic, headline, article_url = _pick_fresh_devto_news(card, state)
    if not headline:
        # No fresh story (the picker already said why - "cooldown"
        # or "no_news"; an absent reason defaults to no_news, same
        # rule as Nostr/Lemmy).
        if not LAST_DEVTO_SKIP:
            LAST_DEVTO_SKIP = "no_news"
        log("warning", f"card '{name}': no fresh news - dev.to post skipped")
        return False
    link = (card.get("link") or "").strip()
    effective_link = link or article_url
    if _promo_topic_cooldown_left(state, headline) is not None:
        log("info", f"card '{name}': news story already used within "
                    f"24h - cooldown, skipping")
        LAST_DEVTO_SKIP = "cooldown"
        return False
    if _promo_link_topic_cooldown_left(state, effective_link, headline) is not None:
        log("info", f"card '{name}': same link + same event within "
                    f"24h - cooldown, skipping")
        LAST_DEVTO_SKIP = "cooldown"
        return False
    # PHOTO FIRST: fetch + verify the photo BEFORE the AI writes
    # anything - a dev.to article without a cover image is not
    # posted (strict no-post-without-a-photo rule).
    photo = fetch_verified_photo(topic)
    if not photo:
        log("warning", f"card '{name}': no photo, skipped - dev.to "
                       f"article needs a verified real photo (cover image)")
        LAST_DEVTO_SKIP = "no_photo"
        return False
    verified, sources, items = verify_news(topic)
    if not verified:
        log("warning", f"card '{name}': topic not verified (needs 2 "
                       f"sources) - dev.to post skipped")
        LAST_DEVTO_SKIP = "no_news"
        return False
    facts = "\n".join(f"- {i['title']} ({i['source']})" for i in items[:5])
    length_text, max_tokens = ARTICLE_LENGTHS[card_length_mode(card)]
    tone_text = ARTICLE_TONES[card_tone(card)]
    article_text = ai_write(ARTICLE_PROMPT.format(
        topic=topic, facts=facts, tone=tone_text, length=length_text),
        max_tokens=max_tokens)
    if not article_text:
        log("warning", f"card '{name}': article writing failed for '{topic}'")
        return False
    title = extract_headline(article_text)
    body = _devto_body_markdown(article_text)
    if not body:
        log("warning", f"card '{name}': empty article body for '{topic}'")
        return False
    tags = _devto_tags(card, topic)
    canonical = _devto_canonical_url(card)
    if not canonical:
        log("info", f"card '{name}': no canonical URL set - posting "
                    f"WITHOUT canonical_url; set the card's Canonical "
                    f"URL once the Blogger post is live (never guessed, "
                    f"never the homepage)")
    main_image = (photo.get("url") or "").strip()
    if is_dry_run():
        log("warning", f"[DRY RUN] card '{name}': would post to dev.to "
                       f"'{title[:60]}' tags={','.join(tags)}"
                       f"{' canonical=' + canonical if canonical else ' (no canonical_url)'}")
        return True
    res = retry_with_backoff(
        lambda: devto_submit(title, body, tags, main_image=main_image,
                             canonical_url=canonical,
                             published=card_devto_published(card)),
        attempts=2, base_delay=5, label="dev.to submit")
    if res:
        art_id, art_url = res
        _record_promo_topic_posted(state, headline)
        _record_promo_link_topic_posted(state, effective_link, headline)
        _record_promo_account_posted(state, headline, key)
        record_devto_post(state, key)
        _record_devto_post_at(state, key)
        log("info", f"card '{name}': posted to dev.to: {art_url or art_id}")
        return True
    log("warning", f"card '{name}': dev.to submit failed")
    return False


def _post_devto_card(card, state, due_slots):
    """The posting loop for devto_post cards. Returns (made, last_error).
    Mirrors _post_lemmy_card: 5-minute gap per key, posts-per-run,
    due slots, day/week/month caps. Clean skips (cooldown, too soon,
    cap, no fresh news, no photo) are no-ops, not failures."""
    global LAST_DEVTO_SKIP
    name = card.get("name", "")
    dry = is_dry_run()
    made = 0
    cooldown_hit = False
    cap_hit = False
    gap_key = _devto_gap_key(card)
    if not dry and _devto_gap_left(state, gap_key) is not None:
        log("info", f"card '{name}': posted less than "
                    f"{DEVTO_MIN_POST_GAP_MINUTES} minutes ago - too soon, skipping")
        return 0, "too soon"
    while True:
        card = _refresh_card(card)
        log_card_settings(card)
        remaining = card_caps_remaining(state, name, card)
        if remaining is not None and remaining <= 0:
            log("info", f"card '{name}': post cap reached - skipping")
            cap_hit = True
            break
        if made >= card_posts_per_run(card):
            break
        if due_slots and made >= len(due_slots):
            break
        try:
            posted = _card_devto_post(card, state)
        except Exception as e:
            log("error", f"card '{name}': post attempt failed: {e}")
            LAST_DEVTO_SKIP = None
            break
        if posted:
            made += 1
            if not dry:
                record_card_post(state, name)
                _record_devto_post_at(state, gap_key)
        else:
            if LAST_DEVTO_SKIP == "cooldown":
                cooldown_hit = True
            break
    if made and not dry and due_slots:
        mark_slots_used(state, name, due_slots[:made])
    if cooldown_hit and made == 0:
        return 0, "cooldown"
    if cap_hit and made == 0:
        return 0, "post cap reached"
    if made == 0 and LAST_DEVTO_SKIP == "no_news":
        return 0, "no fresh news"
    if made == 0 and LAST_DEVTO_SKIP == "no_photo":
        return 0, "no photo, skipped"
    if made == 0 and LAST_DEVTO_SKIP == "no_key":
        return 0, "no api key"
    return made, ("" if made else "post failed or skipped")


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
    - Rebuild #7.11: a READY post (prepared ahead in the ready queue
    - story + verified photo + caption) is used FIRST, so the post
    goes out ON TIME; only when the queue is empty is the post
    prepared on the spot (the behaviour above). A ready post is
    consumed only after it is successfully posted, so a transient
    failure keeps it for the next run.
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
    # Rebuild #7.11: the ready queue (prepared ahead: story + verified
    # photo + caption). from_queue = this post uses a ready item.
    from_queue = False
    hook_ready = ""
    if use_link:
        # Rebuild #7.11: a ready post (prepared ahead, story + verified
        # photo + caption) is used FIRST - the post goes out ON TIME.
        # If the queue is empty, prepare on the spot (current behavior).
        ready = _take_ready_item(card, state)
        if ready is not None:
            news_topic = ready.get("topic") or ""
            news_headline = ready.get("headline") or ""
            photo = {"url": ready.get("photo_url", ""),
                     "source": ready.get("photo_source") or "news",
                     "alt": ready.get("photo_alt") or news_headline,
                     "local_path": ready["local_path"],
                     "article_url": ready.get("article_url") or ""}
            hook_ready = (ready.get("hook") or "").strip()
            from_queue = True
            log("info", f"card '{name}': posted from ready queue - "
                        f"'{news_headline[:60]}'")
        else:
            news_topic, news_headline, photo = _pick_fresh_promo_news(card, state)
            if not photo:
                # _pick_fresh_promo_news already logged why (LAST_BSKY_SKIP).
                log("warning", f"card '{name}': no photo, skipped - Bluesky post "
                               "needs a verified real news photo")
                return False
        if _is_pollinations_url(photo.get("url", "")):
            log("warning", f"card '{name}': no photo, skipped - promo photo "
                           "is AI-generated, not a real news image")
            if from_queue:
                _discard_ready_item(card, state, news_headline)
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
            if from_queue:
                _discard_ready_item(card, state, news_headline)
            LAST_BSKY_SKIP = "cooldown"
            return False
        if _promo_link_topic_cooldown_left(state, effective_link, news_headline) is not None:
            log("info", f"card '{name}': same link + same event within "
                        f"24h - cooldown, skipping (event key "
                        f"'{_norm_news_key(news_headline)[:60]}')")
            if from_queue:
                _discard_ready_item(card, state, news_headline)
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
            if not text and from_queue and hook_ready:
                # Rebuild #7.11: the caption was written when the post
                # was prepared (ready queue) - use it, no AI call at
                # post time. A card's own custom text still wins.
                text = hook_ready
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
            if text is None:
                # Rebuild #7.9: the story link itself is too long for
                # a Bluesky post (a Google News URL can be 570+
                # chars) - skip cleanly, never send the bare long
                # link (Bluesky rejects it with 400).
                log("info", f"card '{name}': story link too long for "
                            "Bluesky - skipping")
                if from_queue:
                    _discard_ready_item(card, state, news_headline)
                LAST_BSKY_SKIP = "link_too_long"
                return False
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
                if from_queue:
                    _discard_ready_item(card, state, news_headline)
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
            if text is None:
                # Rebuild #7.9: the article link itself is too long
                # for a Bluesky post - skip cleanly, never send it.
                log("info", f"card '{name}': article link too long for "
                            "Bluesky - skipping")
                LAST_BSKY_SKIP = "link_too_long"
                return False
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
                if from_queue:
                    # Rebuild #7.11: the ready post went out - remove
                    # it from the queue so it is never posted twice.
                    _consume_ready_item(card, state, news_headline)
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
    if made == 0 and LAST_BSKY_SKIP == "link_too_long":
        # Rebuild #7.9: the story's URL alone exceeds Bluesky's
        # 300-grapheme post limit - a clean skip, NOT a failure
        # (retrying the same long link would fail identically).
        return 0, "link too long, skipped"
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
    if ctype == "reddit_post" and not workflow_enabled("reddit"):
        log("info", f"card '{name}': Reddit workflow is OFF - skipping")
        return False
    if ctype == "tumblr_post" and not workflow_enabled("tumblr"):
        log("info", f"card '{name}': Tumblr workflow is OFF - skipping")
        return False
    if ctype == "threads_post" and not workflow_enabled("threads"):
        log("info", f"card '{name}': Threads workflow is OFF - skipping")
        return False
    if ctype == "mastodon_post" and not workflow_enabled("mastodon"):
        log("info", f"card '{name}': Mastodon workflow is OFF - skipping")
        return False
    if ctype == "telegram_post" and not workflow_enabled("telegram"):
        log("info", f"card '{name}': Telegram workflow is OFF - skipping")
        return False
    if ctype == "nostr_post" and not workflow_enabled("nostr"):
        log("info", f"card '{name}': Nostr workflow is OFF - skipping")
        return False
    if ctype == "lemmy_post" and not workflow_enabled("lemmy"):
        log("info", f"card '{name}': Lemmy workflow is OFF - skipping")
        return False
    if ctype == "devto_post" and not workflow_enabled("devto"):
        log("info", f"card '{name}': dev.to workflow is OFF - skipping")
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
        if ctype == "reddit_post":
            # Reddit replies never carry the link (spam risk) and need
            # no article - the subreddit is the only extra input.
            res = run_reddit_cycle(
                state, subreddit=card.get("subreddit") or "",
                reply_own=reply_own, reply_others=reply_others,
                replies_per_run=rpr, lookback_days=lb, card_name=name,
                account_username=card.get("account_handle") or "",
                replies_per_day=card_replies_per_day(card),
                reply_never=card.get("reply_never") or "",
                reply_only=card.get("reply_only") or "",
                reply_skip_words=card.get("reply_skip_words") or "")
            if isinstance(res, (tuple, list)) and len(res) == 2:
                return int(res[0] or 0) + int(res[1] or 0)
            return 0
        if ctype == "tumblr_post":
            # Tumblr has NO public comment-reply API (notes are
            # likes/reblogs; there is no endpoint to post a reply to
            # a comment), so a Tumblr card never sends replies -
            # posting only. This is a platform limit, not a bug.
            log("info", f"card '{name}': Tumblr has no reply API - "
                        "replies skipped, posting only")
            return 0
        if ctype == "threads_post":
            # Threads v1 is POST-ONLY (same call as Tumblr): the
            # reply endpoints (threads_read_replies /
            # threads_manage_replies) need two extra permissions and
            # a per-post reply-fetch loop, and were not built - see
            # the Threads section header. Posting only.
            log("info", f"card '{name}': Threads replies are not built - "
                        "replies skipped, posting only")
            return 0
        if ctype == "mastodon_post":
            # Mastodon v1 is POST-ONLY (same call as Tumblr/Threads):
            # replies ARE possible on Mastodon (status context +
            # in_reply_to_id), but need a per-post reply-fetch loop
            # and posted-id tracking, and were not built - see the
            # Mastodon section header. Posting only.
            log("info", f"card '{name}': Mastodon replies are not built - "
                        "replies skipped, posting only")
            return 0
        if ctype == "telegram_post":
            # Telegram v1 is POST-ONLY (same call as Tumblr/Threads/
            # Mastodon): channel posts have no reply cycle in the
            # Bot API sense (channel comments live in a linked
            # discussion group), so no replies were built - see the
            # Telegram section header. Posting only.
            log("info", f"card '{name}': Telegram replies are not built - "
                        "replies skipped, posting only")
            return 0
        if ctype == "nostr_post":
            # Nostr v1 is POST-ONLY (same call as Tumblr/Threads/
            # Mastodon/Telegram): replies ARE possible on Nostr
            # (kind-1 with e/p tags per NIP-10), but need a per-post
            # reply-fetch loop and posted-id tracking, and were not
            # built - see the Nostr section header. Posting only.
            log("info", f"card '{name}': Nostr replies are not built - "
                        "replies skipped, posting only")
            return 0
        if ctype == "lemmy_post":
            # Lemmy v1 is POST-ONLY (same call as Tumblr/Threads/
            # Mastodon/Telegram/Nostr): replies ARE possible on Lemmy
            # (POST /api/v3/comment with a parent_id), but need a
            # per-post reply-fetch loop and posted-id tracking, and
            # were not built - see the Lemmy section header.
            # Posting only.
            log("info", f"card '{name}': Lemmy replies are not built - "
                        "replies skipped, posting only")
            return 0
        if ctype == "devto_post":
            # dev.to v1 is POST-ONLY (same call as Tumblr/Threads/
            # Mastodon/Telegram/Nostr/Lemmy): article comments ARE
            # possible on dev.to (POST /api/comments), but need a
            # per-article reply-fetch loop and posted-id tracking,
            # and were not built - see the dev.to section header.
            # Posting only.
            log("info", f"card '{name}': dev.to replies are not built - "
                        "replies skipped, posting only")
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
        elif ctype == "reddit_post" and not list_reddit_accounts():
            # A Reddit card with NO account cannot run at all.
            no_account = True
            last_error = "no Reddit account added - add one first (Reddit tab)"
            log("error", f"card '{name}': {last_error} - skipping, nothing posted")
            ok = False
        elif ctype == "tumblr_post" and not list_tumblr_accounts():
            # A Tumblr card with NO account cannot run at all.
            no_account = True
            last_error = "no Tumblr account added - add one first (Tumblr tab)"
            log("error", f"card '{name}': {last_error} - skipping, nothing posted")
            ok = False
        elif ctype == "threads_post" and not list_threads_accounts():
            # A Threads card with NO account cannot run at all.
            no_account = True
            last_error = "no Threads account added - add one first (Threads tab)"
            log("error", f"card '{name}': {last_error} - skipping, nothing posted")
            ok = False
        elif ctype == "mastodon_post" and not list_mastodon_accounts():
            # A Mastodon card with NO account cannot run at all.
            no_account = True
            last_error = "no Mastodon account added - add one first (Mastodon tab)"
            log("error", f"card '{name}': {last_error} - skipping, nothing posted")
            ok = False
        elif ctype == "telegram_post" and not list_telegram_accounts():
            # A Telegram card with NO bot token cannot run at all.
            no_account = True
            last_error = "no Telegram bot token added - add one first (Telegram tab)"
            log("error", f"card '{name}': {last_error} - skipping, nothing posted")
            ok = False
        elif ctype == "nostr_post" and not list_nostr_accounts():
            # A Nostr card with NO key cannot run at all.
            no_account = True
            last_error = "no Nostr key added - add one first (Nostr tab)"
            log("error", f"card '{name}': {last_error} - skipping, nothing posted")
            ok = False
        elif ctype == "lemmy_post" and not list_lemmy_accounts():
            # A Lemmy card with NO account cannot run at all.
            no_account = True
            last_error = "no Lemmy account added - add one first (Lemmy tab)"
            log("error", f"card '{name}': {last_error} - skipping, nothing posted")
            ok = False
        elif ctype == "devto_post" and not list_devto_accounts():
            # A dev.to card with NO API key cannot run at all.
            no_account = True
            last_error = "no dev.to API key added - add one first (dev.to tab)"
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
                # Rebuild #7.9: "link too long, skipped" is a clean
                # skip too (the story URL cannot fit in a post).
                ok = made > 0 or err in (
                    "cooldown", "too soon", "no photo, skipped",
                    "post cap reached", "no fresh news",
                    "link too long, skipped")
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
                # Rebuild #7.9: "link too long, skipped" is a clean
                # skip too (the story URL cannot fit in a post).
                ok = made > 0 or err in (
                    "cooldown", "too soon", "no photo, skipped",
                    "post cap reached", "no fresh news",
                    "link too long, skipped")
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
        elif ctype == "reddit_post":
            # Reddit posts need no article and no photo: a link post
            # (title + link) to the card's subreddit. Replies never
            # carry the link (spam risk on Reddit) and need no article.
            replies_sent = _do_replies(None)
            if not post_due:
                log("info", f"card '{name}': not a posting time - "
                            "replies only, nothing posted this run")
                last_error = "not a posting time"
                ok = True
            else:
                made, err = _post_reddit_card(card, state, due_slots)
                # Clean skip = successful run (same rule as Bluesky).
                ok = made > 0 or err in (
                    "cooldown", "too soon", "no fresh news",
                    "post cap reached", "no subreddit set")
                if ok:
                    last_error = err or ""
                else:
                    last_error = err or "post failed or skipped"
        elif ctype == "tumblr_post":
            # Tumblr posts need a verified photo (uploaded as NPF
            # multipart) and a fresh Political/War story from the
            # SAME picker + shared cooldowns as Bluesky, so the same
            # story never goes to two platforms the same day. Tumblr
            # has no reply API - _do_replies logs that and sends 0.
            replies_sent = _do_replies(None)
            if not post_due:
                log("info", f"card '{name}': not a posting time - "
                            "nothing posted this run")
                last_error = "not a posting time"
                ok = True
            else:
                made, err = _post_tumblr_card(card, state, due_slots)
                # Clean skip = successful run (same rule as Bluesky).
                ok = made > 0 or err in (
                    "cooldown", "too soon", "no fresh news",
                    "post cap reached", "no photo, skipped")
                if ok:
                    last_error = err or ""
                else:
                    last_error = err or "post failed or skipped"
        elif ctype == "threads_post":
            # Threads posts need a fresh Political/War story from the
            # SAME picker + shared cooldowns as Bluesky, so the same
            # story never goes to two platforms the same day. The
            # photo posts with its original public URL (Threads
            # downloads it); a story with no public photo URL posts
            # TEXT-only instead - there is no 'no photo' skip.
            # Threads v1 is post-only - _do_replies logs that.
            replies_sent = _do_replies(None)
            if not post_due:
                log("info", f"card '{name}': not a posting time - "
                            "nothing posted this run")
                last_error = "not a posting time"
                ok = True
            else:
                made, err = _post_threads_card(card, state, due_slots)
                # Clean skip = successful run (same rule as Bluesky).
                ok = made > 0 or err in (
                    "cooldown", "too soon", "no fresh news",
                    "post cap reached")
                if ok:
                    last_error = err or ""
                else:
                    last_error = err or "post failed or skipped"
        elif ctype == "mastodon_post":
            # Mastodon posts need a fresh Political/War story from the
            # SAME picker + shared cooldowns as Bluesky, so the same
            # story never goes to two platforms the same day. The
            # photo is UPLOADED to the account's own instance; a
            # story with no verified photo posts TEXT-only instead -
            # there is no 'no photo' skip. Mastodon v1 is post-only
            # - _do_replies logs that.
            replies_sent = _do_replies(None)
            if not post_due:
                log("info", f"card '{name}': not a posting time - "
                            "nothing posted this run")
                last_error = "not a posting time"
                ok = True
            else:
                made, err = _post_mastodon_card(card, state, due_slots)
                # Clean skip = successful run (same rule as Bluesky).
                ok = made > 0 or err in (
                    "cooldown", "too soon", "no fresh news",
                    "post cap reached")
                if ok:
                    last_error = err or ""
                else:
                    last_error = err or "post failed or skipped"
        elif ctype == "telegram_post":
            # Telegram posts need a fresh Political/War story from the
            # SAME picker + shared cooldowns as Bluesky, so the same
            # story never goes to two platforms the same day. The
            # photo is UPLOADED as bytes to the card's channel
            # (sendPhoto, 1024-char caption); a story with no
            # verified photo posts TEXT-only via sendMessage instead
            # (4096-char cap) - there is no 'no photo' skip.
            # Telegram v1 is post-only - _do_replies logs that.
            replies_sent = _do_replies(None)
            if not post_due:
                log("info", f"card '{name}': not a posting time - "
                            "nothing posted this run")
                last_error = "not a posting time"
                ok = True
            else:
                made, err = _post_telegram_card(card, state, due_slots)
                # Clean skip = successful run (same rule as Bluesky).
                ok = made > 0 or err in (
                    "cooldown", "too soon", "no fresh news",
                    "post cap reached", "no channel set")
                if ok:
                    last_error = err or ""
                else:
                    last_error = err or "post failed or skipped"
        elif ctype == "nostr_post":
            # Nostr posts need a fresh Political/War story from the
            # SAME picker + shared cooldowns as Bluesky, so the same
            # story never goes to two platforms the same day. The
            # verified photo's PUBLIC URL goes in the note as its own
            # line (Nostr clients render image URLs inline); a story
            # with no verified photo posts TEXT-only instead - there
            # is no 'no photo' skip. Nostr v1 is post-only -
            # _do_replies logs that.
            replies_sent = _do_replies(None)
            if not post_due:
                log("info", f"card '{name}': not a posting time - "
                            "nothing posted this run")
                last_error = "not a posting time"
                ok = True
            else:
                made, err = _post_nostr_card(card, state, due_slots)
                # Clean skip = successful run (same rule as Bluesky).
                ok = made > 0 or err in (
                    "cooldown", "too soon", "no fresh news",
                    "post cap reached")
                if ok:
                    last_error = err or ""
                else:
                    last_error = err or "post failed or skipped"
        elif ctype == "lemmy_post":
            # Lemmy posts need a fresh Political/War story from the
            # SAME picker + shared cooldowns as Bluesky, so the same
            # story never goes to two platforms the same day. NO
            # photo is needed: a Lemmy link post is a title + a link
            # + a hook body, posted INTO the card's community - there
            # is no 'no photo' skip. Lemmy v1 is post-only -
            # _do_replies logs that.
            replies_sent = _do_replies(None)
            if not post_due:
                log("info", f"card '{name}': not a posting time - "
                            "nothing posted this run")
                last_error = "not a posting time"
                ok = True
            else:
                made, err = _post_lemmy_card(card, state, due_slots)
                # Clean skip = successful run (same rule as Bluesky).
                ok = made > 0 or err in (
                    "cooldown", "too soon", "no fresh news",
                    "post cap reached", "no community set")
                if ok:
                    last_error = err or ""
                else:
                    last_error = err or "post failed or skipped"
        elif ctype == "devto_post":
            # dev.to posts are FULL articles about a fresh
            # Political/War story from the SAME picker + shared
            # cooldowns as Bluesky, so the same story never goes to
            # two platforms the same day. A verified photo is
            # REQUIRED (it is the cover image) - no photo is a clean
            # skip. The canonical_url is the card's optional field,
            # omitted when unknown. dev.to v1 is post-only -
            # _do_replies logs that.
            replies_sent = _do_replies(None)
            if not post_due:
                log("info", f"card '{name}': not a posting time - "
                            "nothing posted this run")
                last_error = "not a posting time"
                ok = True
            else:
                made, err = _post_devto_card(card, state, due_slots)
                # Clean skip = successful run (same rule as Bluesky).
                ok = made > 0 or err in (
                    "cooldown", "too soon", "no fresh news",
                    "post cap reached", "no photo, skipped")
                if ok:
                    last_error = err or ""
                else:
                    last_error = err or "post failed or skipped"
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
    blogger_post, 'bluesky' for bluesky_* AND reddit_post cards, None
    for unknown types. Blogger and Bluesky run as TWO separate
    workflows so each can be enabled/disabled on its own (the Blogger
    API is restricted while Bluesky still works). Reddit cards run in
    the Bluesky workflow (same 10-minute cadence, same --only bluesky
    flag) - no separate schedule is needed, and the Reddit workflow
    toggle (reddit_enabled) gates them inside that run. Tumblr cards
    run in the Bluesky workflow too (same cadence, same --only
    bluesky flag), gated by the tumblr_enabled toggle. Threads cards
    run in the Bluesky workflow too (same cadence, same --only
    bluesky flag), gated by the threads_enabled toggle. Mastodon cards
    run in the Bluesky workflow too (same cadence, same --only
    bluesky flag), gated by the mastodon_enabled toggle. Telegram
    cards run in the Bluesky workflow too (same cadence, same --only
    bluesky flag), gated by the telegram_enabled toggle. Nostr cards
    run in the Bluesky workflow too (same cadence, same --only
    bluesky flag), gated by the nostr_enabled toggle. Lemmy cards
    run in the Bluesky workflow too (same cadence, same --only
    bluesky flag), gated by the lemmy_enabled toggle. dev.to cards
    run in the Bluesky workflow too (same cadence, same --only
    bluesky flag), gated by the devto_enabled toggle."""
    t = card.get("type", "")
    if t == "blogger_post":
        return "blogger"
    if t in ("bluesky_post", "bluesky_promo", "bluesky_reply",
             "reddit_post", "tumblr_post", "threads_post",
             "mastodon_post", "telegram_post", "nostr_post",
             "lemmy_post", "devto_post"):
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
        # Rebuild #7.11: READY QUEUE - prepare the next post AHEAD of
        # time (news + verified photo + caption) when a post slot is
        # due within ~15 min, so the post goes out ON TIME. This runs
        # even when the card's interval is not due yet (the slot may
        # be due before the next interval run). _ensure_ready_queue
        # itself does nothing when no slot is near, and never prepares
        # for a card whose workflow is OFF.
        if card.get("type") in ("bluesky_post", "bluesky_promo") and \
                workflow_enabled("bsky"):
            _ensure_ready_queue(card, state)
        interval_due = file_card_due(card, state)
        post_only = False
        if not interval_due and card.get("type") in (
                "bluesky_post", "bluesky_promo", "blogger_post",
                "reddit_post", "tumblr_post", "threads_post",
                "mastodon_post", "telegram_post", "nostr_post",
                "lemmy_post", "devto_post"):
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
           "reddit": "reddit_enabled", "tumblr": "tumblr_enabled",
           "threads": "threads_enabled", "mastodon": "mastodon_enabled",
           "telegram": "telegram_enabled", "nostr": "nostr_enabled",
           "lemmy": "lemmy_enabled", "devto": "devto_enabled",
           "replies": "replies_enabled", "cards": "cards_enabled"}.get(name)
    if not key:
        return True
    default = {"blogger": DEFAULT_BLOGGER_ENABLED, "bsky": DEFAULT_BSKY_ENABLED,
               "reddit": DEFAULT_REDDIT_ENABLED,
               "tumblr": DEFAULT_TUMBLR_ENABLED,
               "threads": DEFAULT_THREADS_ENABLED,
               "mastodon": DEFAULT_MASTODON_ENABLED,
               "telegram": DEFAULT_TELEGRAM_ENABLED,
               "nostr": DEFAULT_NOSTR_ENABLED,
               "lemmy": DEFAULT_LEMMY_ENABLED,
               "devto": DEFAULT_DEVTO_ENABLED,
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


REDDIT_ACCOUNT_SETTINGS_PATH = os.path.join(DATA_DIR, "reddit_accounts.json")


def get_reddit_account_settings():
    """Per-account settings from data/reddit_accounts.json (public, no
    passwords): [{username, enabled, posts_per_day}]. Missing file =
    all enabled. Kept in its own file (not accounts.json) so saving
    Bluesky controls can never wipe Reddit entries and vice versa -
    the dashboard writes this file from the Reddit tab."""
    if not os.path.exists(REDDIT_ACCOUNT_SETTINGS_PATH):
        return {}
    try:
        with open(REDDIT_ACCOUNT_SETTINGS_PATH, "r", encoding="utf-8") as f:
            data = json.load(f)
        if isinstance(data, list):
            return {a["username"]: a for a in data
                    if isinstance(a, dict) and a.get("username")}
        if isinstance(data, dict):
            return data
    except Exception as e:
        log("warning", f"reddit_accounts.json load failed: {e}")
    return {}


def reddit_account_enabled(username):
    cfg = get_reddit_account_settings().get(username)
    if not cfg:
        return True
    return cfg.get("enabled", True) is not False


def reddit_account_posts_limit(username):
    cfg = get_reddit_account_settings().get(username)
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
    reddit_accounts = list_reddit_accounts()
    health["reddit"] = {
        "ok": bool(reddit_accounts),
        "detail": f"{len(reddit_accounts)} account(s)" if reddit_accounts
                  else "no REDDIT_ACCOUNTS secret"}
    tumblr_accounts = list_tumblr_accounts()
    health["tumblr"] = {
        "ok": bool(tumblr_accounts),
        "detail": f"{len(tumblr_accounts)} account(s)" if tumblr_accounts
                  else "no TUMBLR_ACCOUNTS secret"}
    threads_accounts = list_threads_accounts()
    health["threads"] = {
        "ok": bool(threads_accounts),
        "detail": f"{len(threads_accounts)} account(s)" if threads_accounts
                  else "no THREADS_ACCOUNTS secret"}
    mastodon_accounts = list_mastodon_accounts()
    health["mastodon"] = {
        "ok": bool(mastodon_accounts),
        "detail": f"{len(mastodon_accounts)} account(s)" if mastodon_accounts
                  else "no MASTODON_ACCOUNTS secret"}
    telegram_accounts = list_telegram_accounts()
    health["telegram"] = {
        "ok": bool(telegram_accounts),
        "detail": "bot token set" if telegram_accounts
                  else "no TELEGRAM_BOT_TOKEN secret"}
    lemmy_accounts = list_lemmy_accounts()
    health["lemmy"] = {
        "ok": bool(lemmy_accounts),
        "detail": f"{len(lemmy_accounts)} account(s)" if lemmy_accounts
                  else "no LEMMY_ACCOUNTS secret"}
    devto_accounts = list_devto_accounts()
    health["devto"] = {
        "ok": bool(devto_accounts),
        "detail": "API key set" if devto_accounts
                  else "no DEVTO_API_KEY secret"}
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
    # A Reddit card with no Reddit account is a setup problem (same as
    # Bluesky) - but no warning when the user simply does not use Reddit.
    try:
        if not reddit_accounts and any(
                c.get("type") == "reddit_post" for c in load_file_cards()):
            record_issue("warning", "health",
                         "Reddit card(s) exist but no Reddit account - "
                         "add one in the Reddit tab")
    except Exception:
        pass
    # A Tumblr card with no Tumblr account is a setup problem (same as
    # Bluesky/Reddit) - but no warning when the user simply does not
    # use Tumblr.
    try:
        if not tumblr_accounts and any(
                c.get("type") == "tumblr_post" for c in load_file_cards()):
            record_issue("warning", "health",
                         "Tumblr card(s) exist but no Tumblr account - "
                         "add one in the Tumblr tab")
    except Exception:
        pass
    # A Threads card with no Threads account is a setup problem (same
    # as Bluesky/Reddit/Tumblr) - but no warning when the user simply
    # does not use Threads.
    try:
        if not threads_accounts and any(
                c.get("type") == "threads_post" for c in load_file_cards()):
            record_issue("warning", "health",
                         "Threads card(s) exist but no Threads account - "
                         "add one in the Threads tab")
    except Exception:
        pass
    # A Mastodon card with no Mastodon account is a setup problem (same
    # as Bluesky/Reddit/Tumblr/Threads) - but no warning when the user
    # simply does not use Mastodon.
    try:
        if not mastodon_accounts and any(
                c.get("type") == "mastodon_post" for c in load_file_cards()):
            record_issue("warning", "health",
                         "Mastodon card(s) exist but no Mastodon account - "
                         "add one in the Mastodon tab")
    except Exception:
        pass
    # A Telegram card with no bot token is a setup problem (same
    # as Bluesky/Reddit/Tumblr/Threads/Mastodon) - but no warning
    # when the user simply does not use Telegram.
    try:
        if not telegram_accounts and any(
                c.get("type") == "telegram_post" for c in load_file_cards()):
            record_issue("warning", "health",
                         "Telegram card(s) exist but no Telegram bot token - "
                         "add one in the Telegram tab")
    except Exception:
        pass
    # A dev.to card with no API key is a setup problem (same as
    # Bluesky/Reddit/Tumblr/Threads/Mastodon/Telegram) - but no
    # warning when the user simply does not use dev.to.
    try:
        if not devto_accounts and any(
                c.get("type") == "devto_post" for c in load_file_cards()):
            record_issue("warning", "health",
                         "dev.to card(s) exist but no dev.to API key - "
                         "add one in the dev.to tab")
    except Exception:
        pass
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
            "blogger_enabled", "bsky_enabled", "reddit_enabled",
            "mastodon_enabled", "telegram_enabled", "nostr_enabled",
            "replies_enabled",
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
