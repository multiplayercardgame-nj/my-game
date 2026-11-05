import json
import os
import random
import re
import secrets
import socket
import sys
import threading
import time
from http.server import BaseHTTPRequestHandler, ThreadingHTTPServer
from urllib.parse import parse_qs, urlparse

# ---------------------------------------------------------------- cards ----
SUITS = "SHDC"
SUIT_SYMBOL = {"S": "♠", "H": "♥", "D": "♦", "C": "♣"}
SUIT_NAME = {"S": "spades", "H": "hearts", "D": "diamonds", "C": "clubs"}
RANK_NAME = {11: "J", 12: "Q", 13: "K", 14: "A"}
PLACES = ["First", "Second", "Third", "Fourth", "Fifth",
          "Sixth", "Seventh", "Eighth", "Ninth", "Tenth"]
MAX_PLAYERS = len(PLACES)


def suit(card):
    return card[0]


def rank(card):
    return int(card[1:])


def sort_key(card):
    return (SUITS.index(card[0]), int(card[1:]))


def card_text(card):
    """'S14' -> the ace of spades as it is shown on screen."""
    return SUIT_SYMBOL[suit(card)] + RANK_NAME.get(rank(card), str(rank(card)))


def deal(k, rng=random):
    """Deal a 52 card deck to k players."""
    cards = [s + str(n) for s in SUITS for n in range(2, 15)]
    hands = [[] for _ in range(k)]
    for i in range(52):
        c = rng.choice(cards)
        cards.remove(c)
        hands[i % k].append(c)
    return [sorted(h, key=sort_key) for h in hands]


# ---------------------------------------------------------------- rules ----
class DonkeyGame:
    """The rules of the game.  Players are numbered from 0."""

    def __init__(self, k, hands=None, rng=random, names=None):
        if not 2 <= k <= MAX_PLAYERS:
            raise ValueError("2 to %d players" % MAX_PLAYERS)
        self.k = k
        self.names = list(names) if names else ["Player %d" % (i + 1) for i in range(k)]
        self.hands = hands if hands is not None else deal(k, rng)
        self.places = {}                      # player -> "First", "Second", ...
        self.out_order = []                   # players in the order they went out
        self.donkey = None
        self.last_round = None
        self.round_number = 0
        self._free_places = list(PLACES[:k])
        self._just_out = []
        self.leader = next(i for i, h in enumerate(self.hands) if "S14" in h)
        self.first_round = True
        self._start_round()

    @property
    def current_player(self):
        return self.order[self.turn] if self.state == "playing" else None

    def legal_cards(self):
        """The cards the current player is allowed to play."""
        if self.state != "playing":
            return []
        hand = self.hands[self.order[self.turn]]
        if self.turn == 0:
            return list(hand)
        same = [c for c in hand if suit(c) == self.lead]
        return same if same else list(hand)

    def must_follow(self):
        """True if the current player holds the suit that was led."""
        if self.state != "playing" or self.turn == 0:
            return False
        return any(suit(c) == self.lead for c in self.hands[self.order[self.turn]])

    def result_text(self):
        if self.state != "game_over":
            return ""
        if self.donkey is None:
            return "Everyone finished at the same time: it is a draw!"
        return "%s is the donkey!" % self.names[self.donkey]

    def _start_round(self):
        k = self.k
        u = self.leader
        while not self.hands[u]:              # leader already out: next player
            u = (u + 1) % k
        self.order = [(u + i) % k for i in range(k) if self.hands[(u + i) % k]]
        self.turn = 0
        self.pile = []                        # (player, card) in the order played
        self.lead = None
        self.best = None
        self.best_rank = 0
        self.round_number += 1
        self.state = "playing"
        if self.first_round:                  # the ace of spades must open the game
            self.first_round = False
            self.play("S14")

    def play(self, card):
        if card not in self.legal_cards():
            raise ValueError("%s is not a legal card now" % card)
        p = self.order[self.turn]
        had_suit = self.turn == 0 or any(suit(c) == self.lead for c in self.hands[p])
        self.hands[p].remove(card)
        self.pile.append((p, card))
        if not self.hands[p]:
            self._just_out.append(p)
        if self.turn == 0:
            self.lead = suit(card)
            self.best, self.best_rank = p, rank(card)
        elif had_suit:
            if rank(card) > self.best_rank:
                self.best, self.best_rank = p, rank(card)
        else:                                 # could not follow suit: round stops
            self._end_round(cut_by=p)
            return
        self.turn += 1
        if self.turn == len(self.order):      # everybody followed suit
            self._end_round(cut_by=None)

    def _end_round(self, cut_by):
        n = self.names
        cards = [c for _, c in self.pile]
        sentences = []
        if cut_by is None:
            sentences.append("Everyone followed suit. The %d cards are thrown away."
                             % len(cards))
        else:
            sentences.append(
                "%s had no %s and played %s. %s played the highest %s and picks up "
                "all %d cards."
                % (n[cut_by], SUIT_NAME[self.lead], card_text(self.pile[-1][1]),
                   n[self.best], SUIT_NAME[self.lead], len(cards)))
            self.hands[self.best].extend(cards)
            self.hands[self.best].sort(key=sort_key)

        # players who ran out of cards get a place (a player who ran out but
        # then picked up the pile is not out)
        for p in self._just_out:
            if not self.hands[p]:
                label = self._free_places.pop(0)
                self.places[p] = label
                self.out_order.append(p)
                sentences.append("%s is out of cards: %s!" % (n[p], label))
        self._just_out = []

        left = [i for i, h in enumerate(self.hands) if h]
        self.leader = self.best
        if len(left) <= 1:
            self.state = "game_over"
            self.donkey = left[0] if left else None
        else:
            self.state = "round_done"
            nxt = self.best
            while not self.hands[nxt]:
                nxt = (nxt + 1) % self.k
            if nxt == self.best:
                sentences.append("%s leads next." % n[nxt])
            else:
                sentences.append("%s is out, so %s leads next." % (n[self.best], n[nxt]))
        self.last_round = {"cut_by": cut_by,
                           "picked_up_by": self.best if cut_by is not None else None,
                           "count": len(cards), "summary": " ".join(sentences)}

    def next_round(self):
        if self.state != "round_done":
            raise ValueError("the round is not finished")
        self._start_round()


# ---------------------------------------------------------------- rooms ----
CODE_ALPHABET = "ABCDEFGHJKMNPQRSTUVWXYZ23456789"   # no I, L, O, 0 or 1
CODE_LENGTH = 5
MAX_ROOMS = 200
ROOM_IDLE_SECONDS = 6 * 3600
AWAY_SECONDS = 20
MAX_BODY = 2048

LOCK = threading.Lock()
ROOMS = {}


class Fail(Exception):
    def __init__(self, message, status=400):
        Exception.__init__(self, message)
        self.message = message
        self.status = status


class Room:
    def __init__(self, code):
        self.code = code
        self.members = []                     # {"name", "token", "seen"}; host is members[0]
        self.game = None
        self.last = None                      # the round that just finished
        self.touched = time.time()

    @property
    def phase(self):
        if self.game is None:
            return "lobby"
        return "over" if self.game.state == "game_over" else "playing"


def clean_name(value):
    name = " ".join(str(value or "").split())[:20]
    if not name:
        raise Fail("Please type your name.")
    return name


def new_member(room, name):
    member = {"name": name, "token": secrets.token_urlsafe(16), "seen": time.time()}
    room.members.append(member)
    return len(room.members) - 1


def get_room(body):
    code = str(body.get("room", "")).strip().upper()
    room = ROOMS.get(code)
    if room is None:
        raise Fail("No game with that code. Check the code and try again.", 404)
    room.touched = time.time()
    return room


def get_member(room, body):
    token = body.get("token")
    if isinstance(token, str):
        for i, m in enumerate(room.members):
            if secrets.compare_digest(m["token"].encode(), token.encode()):
                m["seen"] = time.time()
                return i
    raise Fail("You are not in this game.", 403)


def state_for(room, idx):
    """Everything player idx may see.  Other players' hands are never included."""
    now = time.time()
    g = room.game
    st = {"room": room.code, "you": idx, "host": idx == 0, "phase": room.phase,
          "names": [m["name"] for m in room.members],
          "away": [now - m["seen"] > AWAY_SECONDS for m in room.members]}
    if g is not None:
        mine = g.current_player == idx
        st.update({
            "cards": [len(h) for h in g.hands],
            "places": [g.places.get(i) for i in range(g.k)],
            "table": [{"p": p, "card": c} for p, c in g.pile],
            "lead": g.lead, "best": g.best, "current": g.current_player,
            "round": g.round_number,
            "hand": list(g.hands[idx]),
            "legal": g.legal_cards() if mine else [],
            "must_follow": g.must_follow() if mine else False,
            "last": room.last,
            "donkey": g.donkey, "result": g.result_text(),
            "ranking": [{"p": p, "place": g.places[p]} for p in g.out_order]})
    return st


def purge_old_rooms():
    cutoff = time.time() - ROOM_IDLE_SECONDS
    for code in [c for c, r in ROOMS.items() if r.touched < cutoff]:
        del ROOMS[code]


def api_create(body):
    name = clean_name(body.get("name"))
    purge_old_rooms()
    if len(ROOMS) >= MAX_ROOMS:
        raise Fail("The server is full right now. Try again later.", 503)
    while True:
        code = "".join(secrets.choice(CODE_ALPHABET) for _ in range(CODE_LENGTH))
        if code not in ROOMS:
            break
    room = Room(code)
    ROOMS[code] = room
    idx = new_member(room, name)
    return {"ok": True, "room": code, "token": room.members[idx]["token"],
            "state": state_for(room, idx)}


def api_join(body):
    name = clean_name(body.get("name"))
    room = get_room(body)
    if room.phase != "lobby":
        raise Fail("That game has already started.")
    if len(room.members) >= MAX_PLAYERS:
        raise Fail("This game is full (%d players)." % MAX_PLAYERS)
    if any(m["name"].lower() == name.lower() for m in room.members):
        raise Fail("Someone in this game already uses that name. Pick another.")
    idx = new_member(room, name)
    return {"ok": True, "room": room.code, "token": room.members[idx]["token"],
            "state": state_for(room, idx)}


def api_start(body):
    room = get_room(body)
    idx = get_member(room, body)
    if idx != 0:
        raise Fail("Only the host can start the game.", 403)
    if room.phase != "lobby":
        raise Fail("The game has already started.")
    if len(room.members) < 2:
        raise Fail("Wait for at least one more player.")
    room.game = DonkeyGame(len(room.members), names=[m["name"] for m in room.members])
    room.last = None
    return {"ok": True, "state": state_for(room, idx)}


def api_play(body):
    room = get_room(body)
    idx = get_member(room, body)
    g = room.game
    if g is None or g.state != "playing":
        raise Fail("The game is not running.")
    if g.current_player != idx:
        raise Fail("It is not your turn.")
    card = body.get("card")
    if not isinstance(card, str) or card not in g.legal_cards():
        raise Fail("You can't play that card now.")
    g.play(card)
    if g.state in ("round_done", "game_over"):
        room.last = {"summary": g.last_round["summary"], "round": g.round_number,
                     "pile": [{"p": p, "card": c} for p, c in g.pile],
                     "cut_by": g.last_round["cut_by"], "best": g.best}
        if g.state == "round_done":
            g.next_round()
    return {"ok": True, "state": state_for(room, idx)}


def api_restart(body):
    room = get_room(body)
    idx = get_member(room, body)
    if idx != 0:
        raise Fail("Only the host can start a new game.", 403)
    if room.phase != "over":
        raise Fail("The game is not finished yet.")
    room.game = None
    room.last = None
    return {"ok": True, "state": state_for(room, idx)}


def api_leave(body):
    room = get_room(body)
    idx = get_member(room, body)
    if room.phase == "lobby":                 # in a running game the seat stays
        del room.members[idx]
        if not room.members:
            del ROOMS[room.code]
    return {"ok": True}


ROUTES = {"/api/create": api_create, "/api/join": api_join, "/api/start": api_start,
          "/api/play": api_play, "/api/restart": api_restart, "/api/leave": api_leave}


# ----------------------------------------------------------------- page ----
PAGE = r"""<!doctype html>
<html lang="en">
<head>
<meta charset="utf-8">
<meta name="viewport" content="width=device-width, initial-scale=1">
<title>Donkey card game</title>
<style>
:root{--bg:#1b5e3b;--panel:#154a2f;--text:#f4f1de;--gold:#f2c94c;--red:#c0392b;--ink:#222}
*{box-sizing:border-box}
body{margin:0;background:var(--bg);color:var(--text);font-family:Arial,Helvetica,sans-serif;min-height:100vh}
#app{max-width:940px;margin:0 auto;padding:12px 14px 48px}
h1{color:var(--gold);text-align:center;margin:16px 0 2px;font-size:34px}
.sub{text-align:center;margin:0 0 12px}
.panel{background:var(--panel);border-radius:10px;padding:12px 14px;margin:10px 0}
.panel h2{margin:0 0 8px;font-size:14px;letter-spacing:.04em;text-transform:uppercase;opacity:.85}
.rules{font-size:14px;line-height:1.5;text-align:center}
input{width:100%;padding:12px;font-size:17px;border-radius:8px;border:1px solid #888;margin:6px 0}
input.code{text-transform:uppercase;letter-spacing:.2em;text-align:center}
button{font-size:16px;padding:12px 16px;border-radius:8px;border:0;background:#e8e8e8;color:#111;cursor:pointer}
button.big{width:100%;font-weight:bold;background:var(--gold);margin-top:6px}
button.alt{background:#e8e8e8}
button.link{background:none;color:var(--text);text-decoration:underline;padding:6px;font-size:14px}
button:disabled{opacity:.5;cursor:default}
.or{text-align:center;margin:14px 0 6px;opacity:.8}
.status{text-align:center;color:var(--gold);font-weight:bold;font-size:20px;margin:6px 0;padding:8px;border-radius:8px}
.status.you{background:var(--gold);color:var(--ink)}
.info{text-align:center;font-size:14px;margin-bottom:6px;opacity:.9}
.cards{display:flex;flex-wrap:wrap;gap:6px;justify-content:flex-start}
.card{display:inline-flex;align-items:center;justify-content:center;min-width:54px;height:76px;padding:0 6px;background:#fff;color:var(--ink);border-radius:8px;font:bold 22px Arial,Helvetica,sans-serif;border:2px solid #bbb}
.card.red{color:var(--red)}
.card.small{min-width:44px;height:58px;font-size:18px}
.card.off{background:#d4d4d4;color:#888;border-color:#c4c4c4}
.card.playable{cursor:pointer;border-color:var(--gold);box-shadow:0 0 0 2px var(--gold)}
.card.playable:hover{background:#fff3b0}
.grid{display:grid;grid-template-columns:3fr 1.4fr;gap:10px}
@media(max-width:640px){.grid{grid-template-columns:1fr}.card{min-width:48px;height:68px}}
.cell{display:flex;flex-direction:column;align-items:center;font-size:12px;gap:3px}
.cell .cap{max-width:96px;text-align:center;overflow-wrap:anywhere}
.gold{color:var(--gold)}.bad{color:#ff8a80}.good{color:#8fd694}.me{font-weight:bold;color:var(--gold)}
ul.plain,ol.plain{margin:0;padding-left:20px;line-height:1.8}
ul.plain{list-style:none;padding-left:0}
.hint{color:var(--gold);font-size:14px;margin-bottom:8px}
.summary{font-size:14px;line-height:1.4;margin:0 0 8px}
.linkrow{display:flex;gap:8px}.linkrow input{margin:6px 0}
.code-big{font-size:34px;letter-spacing:.25em;text-align:center;color:var(--gold);font-weight:bold;margin:4px 0}
#toast{position:fixed;left:50%;top:10px;transform:translateX(-50%);background:#a33;color:#fff;padding:10px 16px;border-radius:8px;display:none;z-index:10;max-width:90%;text-align:center}
#banner{position:fixed;left:0;right:0;bottom:0;background:#8a4b00;color:#fff;text-align:center;padding:8px;display:none;z-index:10}
</style>
</head>
<body>
<div id="app"></div>
<div id="toast" role="alert"></div>
<div id="banner">Connection lost. Trying again...</div>
<noscript>This game needs JavaScript.</noscript>
<script>
"use strict";
var SYMBOL = {S:"♠", H:"♥", D:"♦", C:"♣"};
var SUITNAME = {S:"spades", H:"hearts", D:"diamonds", C:"clubs"};
var RANKS = {11:"J", 12:"Q", 13:"K", 14:"A"};
var app = document.getElementById("app");
var session = null, lastJson = "", pollOn = false, pollTimer = null, busy = false, wasMyTurn = false;

function h(tag, attrs) {
  var el = document.createElement(tag);
  var a = attrs || {};
  Object.keys(a).forEach(function (k) {
    var v = a[k];
    if (k === "class") el.className = v;
    else if (k.slice(0, 2) === "on") el.addEventListener(k.slice(2), v);
    else if (v !== false && v != null) el.setAttribute(k, v);
  });
  for (var i = 2; i < arguments.length; i++) {
    var kids = [].concat(arguments[i]);
    kids.forEach(function (kid) {
      if (kid == null || kid === false) return;
      el.append(kid);                       // strings become text, never HTML
    });
  }
  return el;
}
function toast(msg) {
  var t = document.getElementById("toast");
  t.textContent = msg; t.style.display = "block";
  clearTimeout(toast.t); toast.t = setTimeout(function () { t.style.display = "none"; }, 3500);
}
function banner(on) { document.getElementById("banner").style.display = on ? "block" : "none"; }
function store(k, v) { try { if (v == null) localStorage.removeItem(k); else localStorage.setItem(k, v); } catch (e) {} }
function load(k) { try { return localStorage.getItem(k); } catch (e) { return null; } }
function savedSession() { try { return JSON.parse(load("donkey_session")); } catch (e) { return null; } }
function forgetSession() { session = null; lastJson = ""; store("donkey_session", null); }

async function api(path, body) {
  try {
    var res = await fetch(path, {method: "POST", headers: {"Content-Type": "application/json"}, body: JSON.stringify(body)});
    return await res.json();
  } catch (e) {
    return {ok: false, error: "Can't reach the server. Check your connection."};
  }
}

function cardLabel(card) {
  var r = +card.slice(1);
  return SYMBOL[card[0]] + (RANKS[r] || r);
}
function cardEl(card, o) {
  o = o || {};
  var red = card[0] === "H" || card[0] === "D";
  var cls = "card" + (red ? " red" : "") + (o.small ? " small" : "") + (o.off ? " off" : "") + (o.playable ? " playable" : "");
  if (o.playable) return h("button", {class: cls, "aria-label": cardLabel(card), onclick: function () { act("/api/play", {card: card}); }}, cardLabel(card));
  return h("div", {class: cls}, cardLabel(card));
}

/* ---------- polling ---------- */
function startPolling() { stopPolling(); pollOn = true; lastJson = ""; poll(); }
function stopPolling() { pollOn = false; clearTimeout(pollTimer); }
async function poll() {
  if (!pollOn || !session) return;
  try {
    var res = await fetch("/api/state?room=" + encodeURIComponent(session.room) + "&token=" + encodeURIComponent(session.token), {cache: "no-store"});
    var data = await res.json();
    banner(false);
    if (data.ok) show(data.state);
    else if (res.status === 403 || res.status === 404) {
      stopPolling(); forgetSession(); history.replaceState(null, "", "/"); renderHome("");
      toast(data.error || "That game is gone."); return;
    }
  } catch (e) { banner(true); }
  if (pollOn) pollTimer = setTimeout(poll, 1200);
}
function show(st) {
  var j = JSON.stringify(st);
  if (j === lastJson) return;
  lastJson = j;
  var myTurn = st.phase === "playing" && st.current === st.you;
  if (myTurn && !wasMyTurn) { try { navigator.vibrate && navigator.vibrate(150); } catch (e) {} }
  wasMyTurn = myTurn;
  document.title = (myTurn ? "▶ Your turn - " : "") + "Donkey card game";
  if (st.phase === "lobby") renderLobby(st); else renderGame(st);
}
async function act(path, extra) {
  if (busy || !session) return;
  busy = true;
  var r = await api(path, Object.assign({room: session.room, token: session.token}, extra || {}));
  busy = false;
  if (r.ok && r.state) show(r.state);
  else if (!r.ok) toast(r.error || "Something went wrong.");
}
async function enter(path, body) {
  var r = await api(path, body);
  if (!r.ok) { toast(r.error || "Could not join."); return; }
  session = {room: r.room, token: r.token};
  store("donkey_session", JSON.stringify(session));
  history.replaceState(null, "", "/?room=" + r.room);
  startPolling();
}
async function leave() {
  if (!confirm("Leave this game?")) return;
  await api("/api/leave", {room: session.room, token: session.token});
  stopPolling(); forgetSession(); history.replaceState(null, "", "/"); renderHome("");
}

/* ---------- screens ---------- */
function renderHome(prefill) {
  var name = h("input", {id: "name", maxlength: "20", placeholder: "Your name", autocomplete: "off", value: load("donkey_name") || ""});
  var code = h("input", {id: "code", class: "code", maxlength: "8", placeholder: "GAME CODE", autocomplete: "off", autocapitalize: "characters", value: prefill || ""});
  function myName() {
    var n = name.value.trim();
    if (!n) { toast("Type your name first."); name.focus(); return null; }
    store("donkey_name", n); return n;
  }
  app.replaceChildren(
    h("h1", {}, "Donkey ♠♥♦♣"),
    h("p", {class: "sub"}, "also known as Bhabhi - play together, each on your own device"),
    h("div", {class: "panel rules"},
      "The player with the ace of spades starts. Follow the suit that was led. If you cannot, play any card: the highest card of the led suit picks up all the cards. If everyone follows suit the cards are thrown away. Get rid of your cards first. The last player left is the donkey!"),
    h("div", {class: "panel"},
      h("h2", {}, "Your name"), name,
      prefill ? null : h("button", {class: "big", onclick: function () { var n = myName(); if (n) enter("/api/create", {name: n}); }}, "Create a new game"),
      prefill ? null : h("div", {class: "or"}, "or join a friend's game"),
      h("h2", {}, prefill ? "Joining game" : "Game code"), code,
      h("button", {class: "big" + (prefill ? "" : " alt"), onclick: function () {
        var n = myName(); if (!n) return;
        var c = code.value.trim().toUpperCase();
        if (!c) { toast("Type the game code."); code.focus(); return; }
        enter("/api/join", {name: n, room: c});
      }}, "Join game"),
      prefill ? h("button", {class: "link", onclick: function () { history.replaceState(null, "", "/"); renderHome(""); }}, "Start a new game instead") : null));
  document.title = "Donkey card game";
}

function renderLobby(st) {
  var link = location.origin + "/?room=" + st.room;
  var box = h("input", {readonly: "", value: link, onclick: function (e) { e.target.select(); }});
  var copy = h("button", {onclick: async function () {
    try { await navigator.clipboard.writeText(link); } catch (e) { box.select(); try { document.execCommand("copy"); } catch (e2) {} }
    copy.textContent = "Copied!"; setTimeout(function () { copy.textContent = "Copy link"; }, 1500);
  }}, "Copy link");
  app.replaceChildren(
    h("h1", {}, "Donkey ♠♥♦♣"),
    h("div", {class: "panel"},
      h("h2", {}, "Game code"), h("div", {class: "code-big"}, st.room),
      h("div", {class: "info"}, "Friends open this link, or type the code on the start page:"),
      h("div", {class: "linkrow"}, box, copy)),
    h("div", {class: "panel"},
      h("h2", {}, "Players (" + st.names.length + ")"),
      h("ul", {class: "plain"}, st.names.map(function (n, i) {
        return h("li", {class: i === st.you ? "me" : ""}, n + (i === 0 ? " (host)" : "") + (i === st.you ? " (you)" : "") + (st.away[i] ? " - away" : ""));
      }))),
    st.host
      ? h("button", {class: "big", disabled: st.names.length < 2 ? "" : false, onclick: function () { act("/api/start"); }},
          st.names.length < 2 ? "Waiting for more players..." : "Start game")
      : h("div", {class: "status"}, "Waiting for " + st.names[0] + " to start the game..."),
    h("div", {style: "text-align:center"}, h("button", {class: "link", onclick: leave}, "Leave game")));
}

function renderGame(st) {
  var me = st.you, N = st.names, over = st.phase === "over";
  var myTurn = !over && st.current === me;
  var cutBy = (over && st.last) ? st.last.cut_by : null;

  var statusText = over ? "Game over! " + st.result : (myTurn ? "Your turn!" : N[st.current] + "'s turn");
  var infoText = over ? "" : "Round " + st.round + (st.lead ? "   |   Lead suit: " + SYMBOL[st.lead] + " " + SUITNAME[st.lead] : "   |   " + (myTurn ? "You lead" : N[st.current] + " leads"));

  var table = st.table.length ? st.table.map(function (t) {
    var cap = N[t.p], cls = "cap";
    if (over && t.p === cutBy) { cap += " (no " + SUITNAME[st.lead] + ")"; cls += " bad"; }
    else if (t.p === st.best) { cap += " ★"; cls += " gold"; }
    return h("div", {class: "cell"}, h("div", {class: cls}, cap), cardEl(t.card, {small: true}));
  }) : h("div", {class: "info"}, "(no cards yet)");

  var players = N.map(function (n, i) {
    var text, cls = "";
    if (st.places[i]) { text = n + ": " + st.places[i]; cls = "good"; }
    else if (over && i === st.donkey) { text = n + ": DONKEY"; cls = "bad"; }
    else text = n + ": " + st.cards[i] + " card" + (st.cards[i] === 1 ? "" : "s");
    if (i === me) text += " (you)";
    if (st.away[i] && !over) text += " - away";
    var cur = !over && i === st.current;
    return h("li", {class: cur ? "gold" : cls}, (cur ? "▶ " : "   ") + text);
  });

  var hint = "";
  if (myTurn) {
    if (!st.lead) hint = "You lead: play any card.";
    else if (st.must_follow) hint = "You must follow suit (" + SYMBOL[st.lead] + " " + SUITNAME[st.lead] + ").";
    else hint = "You have no " + SUITNAME[st.lead] + ": play any card. The highest " + SUITNAME[st.lead] + " picks up all the cards.";
  } else if (!over) hint = "Waiting for " + N[st.current] + " to play...";

  var legal = st.legal || [];
  var handBox;
  if (!st.hand.length) {
    handBox = h("div", {class: "hint"}, st.places[me] ? "You are out of cards: " + st.places[me] + "!" : (over ? "You have no cards left." : ""));
  } else {
    handBox = [h("div", {class: "hint"}, hint),
      h("div", {class: "cards"}, st.hand.map(function (c) {
        var ok = myTurn && legal.indexOf(c) >= 0;
        return cardEl(c, {playable: ok, off: !ok});
      }))];
  }

  var lastBox = null;
  if (st.last && !over) {
    lastBox = h("div", {class: "panel"}, h("h2", {}, "Last round"),
      h("p", {class: "summary"}, st.last.summary),
      h("div", {class: "cards"}, st.last.pile.map(function (t) {
        return h("div", {class: "cell"}, h("div", {class: "cap" + (t.p === st.last.best ? " gold" : "")}, N[t.p] + (t.p === st.last.best ? " ★" : "")), cardEl(t.card, {small: true}));
      })));
  } else if (over && st.last) {
    lastBox = h("div", {class: "panel"}, h("h2", {}, "Final round"), h("p", {class: "summary"}, st.last.summary));
  }

  var resultBox = null;
  if (over) {
    resultBox = h("div", {class: "panel"}, h("h2", {}, "Result"),
      h("ol", {class: "plain"}, st.ranking.map(function (r) { return h("li", {}, r.place + ": " + N[r.p]); }),
        st.donkey != null ? h("li", {class: "bad"}, "Donkey: " + N[st.donkey]) : null),
      st.host ? h("button", {class: "big", onclick: function () { act("/api/restart"); }}, "Play again with the same players")
              : h("div", {class: "info"}, "Waiting for " + N[0] + " to start another game..."));
  }

  app.replaceChildren(
    h("div", {class: "status" + (myTurn ? " you" : "")}, statusText),
    h("div", {class: "info"}, infoText),
    h("div", {class: "grid"},
      h("div", {class: "panel"}, h("h2", {}, "On the table"), h("div", {class: "cards"}, table)),
      h("div", {class: "panel"}, h("h2", {}, "Players"), h("ul", {class: "plain"}, players))),
    h("div", {class: "panel"}, h("h2", {}, "Your hand (" + N[me] + ")"), handBox),
    resultBox || "", lastBox || "",
    h("div", {style: "text-align:center"}, h("button", {class: "link", onclick: leave}, "Leave game")));
}

/* ---------- start ---------- */
(function () {
  var room = (new URLSearchParams(location.search).get("room") || "").toUpperCase();
  if (!/^[A-Z0-9]{3,8}$/.test(room)) room = "";
  var saved = savedSession();
  if (saved && saved.room && saved.token && (!room || saved.room === room)) { session = saved; startPolling(); }
  else renderHome(room);
})();
</script>
</body>
</html>
"""


# --------------------------------------------------------------- server ----
class Handler(BaseHTTPRequestHandler):
    server_version = "DonkeyServer"
    timeout = 15

    def log_message(self, fmt, *args):         # keep the console quiet
        pass

    def _send(self, status, body, ctype):
        self.send_response(status)
        self.send_header("Content-Type", ctype)
        self.send_header("Content-Length", str(len(body)))
        self.send_header("Cache-Control", "no-store")
        self.send_header("X-Content-Type-Options", "nosniff")
        self.send_header("Referrer-Policy", "no-referrer")
        if ctype.startswith("text/html"):
            self.send_header("Content-Security-Policy",
                             "default-src 'none'; script-src 'unsafe-inline'; "
                             "style-src 'unsafe-inline'; connect-src 'self'; "
                             "base-uri 'none'; form-action 'none'")
        self.end_headers()
        self.wfile.write(body)

    def _json(self, status, obj):
        self._send(status, json.dumps(obj).encode("utf-8"), "application/json")

    def do_GET(self):
        url = urlparse(self.path)
        if url.path == "/":
            self._send(200, PAGE.encode("utf-8"), "text/html; charset=utf-8")
        elif url.path == "/healthz":
            self._send(200, b"ok", "text/plain")
        elif url.path == "/api/state":
            q = {k: v[0] for k, v in parse_qs(url.query).items()}
            try:
                with LOCK:
                    room = get_room(q)
                    idx = get_member(room, q)
                    result = {"ok": True, "state": state_for(room, idx)}
                self._json(200, result)
            except Fail as e:
                self._json(e.status, {"ok": False, "error": e.message})
        else:
            self._send(404, b"Not found", "text/plain")

    def do_POST(self):
        route = ROUTES.get(urlparse(self.path).path)
        if route is None:
            self._send(404, b"Not found", "text/plain")
            return
        try:
            size = int(self.headers.get("Content-Length") or 0)
            if size > MAX_BODY:
                raise Fail("Request too large.", 413)
            body = json.loads(self.rfile.read(size) or b"{}")
            if not isinstance(body, dict):
                raise Fail("Bad request.")
            with LOCK:
                result = route(body)
            self._json(200, result)
        except Fail as e:
            self._json(e.status, {"ok": False, "error": e.message})
        except (ValueError, UnicodeDecodeError):
            self._json(400, {"ok": False, "error": "Bad request."})


class Server(ThreadingHTTPServer):
    daemon_threads = True
    allow_reuse_address = True


def lan_ip():
    s = socket.socket(socket.AF_INET, socket.SOCK_DGRAM)
    try:
        s.connect(("10.255.255.255", 1))      # no packet is sent
        return s.getsockname()[0]
    except OSError:
        return "127.0.0.1"
    finally:
        s.close()


def main():
    port = int(sys.argv[1]) if len(sys.argv) > 1 else int(os.environ.get("PORT", "8000"))
    server = Server(("0.0.0.0", port), Handler)
    print("Donkey game server is running.\n")
    print("  This computer:        http://localhost:%d" % port)
    print("  Same Wi-Fi/network:   http://%s:%d" % (lan_ip(), port))
    print("  Over the internet:    run   cloudflared tunnel --url http://localhost:%d" % port)
    print("                        and share the https link it prints.\n")
    print("Press Ctrl+C to stop.")
    try:
        server.serve_forever()
    except KeyboardInterrupt:
        print("\nStopped.")


if __name__ == "__main__":
    main()
