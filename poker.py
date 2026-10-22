#!/usr/bin/env python3
"""LAN Texas Hold'em. Run this on one machine; friends open http://<your-ip>:8000 in a browser.

    python3 poker.py [--port 8000] [--chips 1000] [--sb 10] [--bb 20] [--turn-time 60]

No dependencies beyond the Python 3.8+ standard library.
"""
import argparse
import json
import random
import secrets
import socket
import threading
import time
from http.server import BaseHTTPRequestHandler, ThreadingHTTPServer
from itertools import combinations
from urllib.parse import parse_qs, urlparse

RANKS = "23456789TJQKA"
SUITS = "shdc"
HAND_NAMES = ["High Card", "Pair", "Two Pair", "Three of a Kind", "Straight",
              "Flush", "Full House", "Four of a Kind", "Straight Flush"]
BETTING = ("preflop", "flop", "turn", "river")
rng = random.SystemRandom()


# ---------------------------------------------------------------- hand evaluation

def eval5(cards):
    vals = sorted((RANKS.index(c[0]) + 2 for c in cards), reverse=True)
    counts = {}
    for v in vals:
        counts[v] = counts.get(v, 0) + 1
    groups = sorted(counts.items(), key=lambda g: (g[1], g[0]), reverse=True)
    flush = len({c[1] for c in cards}) == 1
    uniq = sorted(set(vals), reverse=True)
    straight = 0
    if len(uniq) == 5:
        if uniq[0] - uniq[4] == 4:
            straight = uniq[0]
        elif uniq == [14, 5, 4, 3, 2]:
            straight = 5
    kickers = [g[0] for g in groups]
    if straight and flush:
        return (8, straight)
    if groups[0][1] == 4:
        return (7, *kickers)
    if groups[0][1] == 3 and groups[1][1] == 2:
        return (6, *kickers)
    if flush:
        return (5, *vals)
    if straight:
        return (4, straight)
    if groups[0][1] == 3:
        return (3, *kickers)
    if groups[0][1] == 2 and groups[1][1] == 2:
        return (2, *kickers)
    if groups[0][1] == 2:
        return (1, *kickers)
    return (0, *vals)


def best_hand(cards):
    return max(eval5(c) for c in combinations(cards, 5))


# ---------------------------------------------------------------- game state

class Player:
    def __init__(self, name, chips):
        self.token = secrets.token_hex(12)
        self.name = name
        self.chips = chips
        self.hand = []
        self.bet = 0          # chips put in during the current street
        self.contrib = 0      # chips put in during the whole hand
        self.in_hand = False
        self.folded = True
        self.all_in = False
        self.acted = False
        self.show = False
        self.left = False
        self.last_seen = time.time()


class Game:
    def __init__(self, chips, sb, bb, turn_time):
        self.lock = threading.RLock()
        self.start_chips, self.sb, self.bb, self.turn_time = chips, sb, bb, turn_time
        self.players = []
        self.stage = "waiting"
        self.board, self.deck = [], []
        self.dealer = -1
        self.turn = None
        self.turn_started = 0
        self.current_bet = 0
        self.min_raise = bb
        self.hand_no = 0
        self.hand_over_at = 0
        self.auto_deal = False
        self.log = []
        self.results = []

    def say(self, msg):
        self.log = (self.log + [msg])[-40:]

    # ---- seating

    def join(self, name):
        name = " ".join(name.split())[:16]
        if not name:
            raise ValueError("Enter a name")
        if any(p.name.lower() == name.lower() and not p.left for p in self.players):
            raise ValueError("That name is taken")
        if sum(not p.left for p in self.players) >= 9:
            raise ValueError("Table is full (9 max)")
        p = Player(name, self.start_chips)
        self.players.append(p)
        self.say(f"{name} sat down" + (" (plays next hand)" if self.stage in BETTING else ""))
        return p

    def leave(self, p):
        p.left = True
        self.say(f"{p.name} left the table")
        if self.stage in BETTING and p.in_hand and not p.folded:
            if self.players[self.turn] is p:
                self.act(p, "fold")
            else:
                p.folded = True
                self.check_uncontested()
        if self.stage not in BETTING:
            self.players.remove(p)

    def rebuy(self, p):
        if p.chips > 0 or (p.in_hand and self.stage in BETTING):
            raise ValueError("You can only rebuy when you're out of chips")
        p.chips = self.start_chips
        self.say(f"{p.name} rebought for {self.start_chips}")

    # ---- dealing

    def next_seat(self, i, pred):
        n = len(self.players)
        for k in range(1, n + 1):
            j = (i + k) % n
            if pred(self.players[j]):
                return j
        return None

    def needs_action(self, p):
        return (p.in_hand and not p.folded and not p.all_in
                and (not p.acted or p.bet < self.current_bet))

    def start_hand(self):
        if self.stage in BETTING:
            raise ValueError("A hand is already in progress")
        old = self.players[self.dealer] if 0 <= self.dealer < len(self.players) else None
        self.players = [p for p in self.players if not p.left]
        if sum(p.chips > 0 for p in self.players) < 2:
            raise ValueError("Need at least 2 players with chips")
        self.dealer = self.players.index(old) if old in self.players else -1

        self.hand_no += 1
        self.auto_deal = True
        self.deck = [r + s for r in RANKS for s in SUITS]
        rng.shuffle(self.deck)
        self.board, self.results = [], []
        for p in self.players:
            p.hand, p.bet, p.contrib = [], 0, 0
            p.all_in = p.acted = p.show = False
            p.in_hand = p.chips > 0
            p.folded = not p.in_hand

        live = lambda p: p.in_hand
        self.dealer = self.next_seat(self.dealer, live)
        if sum(p.in_hand for p in self.players) == 2:   # heads-up: dealer posts small blind
            sb_i = self.dealer
        else:
            sb_i = self.next_seat(self.dealer, live)
        bb_i = self.next_seat(sb_i, live)
        self.say(f"--- Hand #{self.hand_no} --- {self.players[self.dealer].name} deals")
        self.post(self.players[sb_i], self.sb, "small blind")
        self.post(self.players[bb_i], self.bb, "big blind")
        self.current_bet, self.min_raise = self.bb, self.bb
        for _ in range(2):
            for p in self.players:
                if p.in_hand:
                    p.hand.append(self.deck.pop())
        self.stage = "preflop"
        self.turn = bb_i
        self.advance()

    def post(self, p, amount, label):
        amt = min(amount, p.chips)
        self.put(p, amt)
        self.say(f"{p.name} posts {label} {amt}")

    def put(self, p, amt):
        p.chips -= amt
        p.bet += amt
        p.contrib += amt
        if p.chips == 0:
            p.all_in = True

    # ---- betting

    def act(self, p, action, amount=0):
        if self.stage not in BETTING or self.turn is None or self.players[self.turn] is not p:
            raise ValueError("It's not your turn")
        to_call = self.current_bet - p.bet
        if action == "allin":
            action, amount = ("raise", p.bet + p.chips) if p.bet + p.chips > self.current_bet else ("call", 0)

        if action == "fold":
            p.folded = True
            self.say(f"{p.name} folds")
        elif action == "check":
            if to_call > 0:
                raise ValueError(f"You need to call {to_call} or fold")
            self.say(f"{p.name} checks")
        elif action == "call":
            if to_call <= 0:
                raise ValueError("Nothing to call — check instead")
            amt = min(to_call, p.chips)
            self.put(p, amt)
            self.say(f"{p.name} calls {amt}" + (" (all in)" if p.all_in else ""))
        elif action == "raise":
            try:
                amount = int(amount)
            except (TypeError, ValueError):
                raise ValueError("Invalid raise amount")
            max_total = p.bet + p.chips
            min_total = self.current_bet + self.min_raise
            if amount >= max_total:
                amount = max_total
            elif amount < min_total:
                raise ValueError(f"Minimum raise is to {min_total}")
            if amount <= self.current_bet:
                raise ValueError("You don't have enough chips to raise — call instead")
            if amount - self.current_bet >= self.min_raise:
                self.min_raise = amount - self.current_bet
            verb = "bets" if self.current_bet == 0 else "raises to"
            self.current_bet = amount
            self.put(p, amount - p.bet)
            self.say(f"{p.name} {verb} {amount}" + (" (all in)" if p.all_in else ""))
        else:
            raise ValueError("Unknown action")
        p.acted = True
        self.advance()

    def alive(self):
        return [p for p in self.players if p.in_hand and not p.folded]

    def check_uncontested(self):
        alive = self.alive()
        if len(alive) == 1:
            winner = alive[0]
            pot = sum(p.contrib for p in self.players)
            winner.chips += pot
            self.say(f"{winner.name} wins {pot}")
            self.results = [f"{winner.name} wins {pot} — everyone else folded"]
            self.end_hand()
            return True
        return False

    def advance(self):
        if self.check_uncontested():
            return
        nxt = self.next_seat(self.turn, self.needs_action)
        if nxt is not None:
            self.turn = nxt
            self.turn_started = time.time()
        else:
            self.next_street()

    def next_street(self):
        for p in self.players:
            p.bet, p.acted = 0, False
        self.current_bet, self.min_raise = 0, self.bb
        if self.stage == "river":
            return self.showdown()
        self.deck.pop()  # burn
        n = 3 if self.stage == "preflop" else 1
        self.board += [self.deck.pop() for _ in range(n)]
        self.stage = {"preflop": "flop", "flop": "turn", "turn": "river"}[self.stage]
        self.say(f"{self.stage.title()}: {' '.join(self.board)}")
        if sum(not p.all_in for p in self.alive()) < 2:
            for p in self.alive():
                p.show = True       # all in: cards go face up and the board runs out
            return self.next_street()
        self.turn = self.next_seat(self.dealer, self.needs_action)
        self.turn_started = time.time()

    def showdown(self):
        alive = self.alive()
        scores = {p.token: best_hand(p.hand + self.board) for p in alive}
        for p in alive:
            p.show = True
            self.say(f"{p.name} shows {' '.join(p.hand)} — {HAND_NAMES[scores[p.token][0]]}")
        won = {}
        prev, carry, last_winners = 0, 0, []
        for level in sorted({p.contrib for p in self.players if p.contrib > 0}):
            pot = carry + sum(min(p.contrib, level) - min(p.contrib, prev) for p in self.players)
            prev = level
            eligible = [p for p in alive if p.contrib >= level]
            if not eligible:
                carry = pot
                continue
            carry = 0
            top = max(scores[p.token] for p in eligible)
            winners = [p for p in eligible if scores[p.token] == top]
            share, rem = divmod(pot, len(winners))
            for i, w in enumerate(winners):
                amt = share + (1 if i < rem else 0)
                w.chips += amt
                won[w.name] = won.get(w.name, 0) + amt
            last_winners = winners
        if carry and last_winners:
            last_winners[0].chips += carry
            won[last_winners[0].name] = won.get(last_winners[0].name, 0) + carry
        by_name = {p.name: p for p in alive}
        self.results = []
        for name, amt in won.items():
            hn = HAND_NAMES[scores[by_name[name].token][0]]
            self.results.append(f"{name} wins {amt} with {hn}")
            self.say(f"{name} wins {amt} with {hn}")
        self.end_hand()

    def end_hand(self):
        self.stage = "hand_over"
        self.turn = None
        self.hand_over_at = time.time()
        for p in [p for p in self.players if p.left]:
            self.players.remove(p)
        self.dealer = min(self.dealer, len(self.players) - 1)
        for p in self.players:
            if p.chips == 0 and p.in_hand:
                self.say(f"{p.name} is out of chips")

    # ---- background clock: turn timer, disconnects, auto-deal

    def tick(self):
        now = time.time()
        if self.stage in BETTING and self.turn is not None:
            p = self.players[self.turn]
            gone = now - p.last_seen > 20
            if gone or now - self.turn_started > self.turn_time:
                self.say(f"{p.name} timed out")
                self.act(p, "check" if self.current_bet == p.bet else "fold")
        elif self.stage == "hand_over" and self.auto_deal and now - self.hand_over_at > 6:
            try:
                self.start_hand()
            except ValueError:
                self.auto_deal = False
                self.stage = "waiting"

    # ---- client view

    def view(self, me):
        players = []
        for i, p in enumerate(self.players):
            visible = p is me or p.show
            players.append({
                "name": p.name, "chips": p.chips, "bet": p.bet,
                "folded": p.folded and p.in_hand, "all_in": p.all_in, "in_hand": p.in_hand,
                "left": p.left, "dealer": i == self.dealer and self.stage != "waiting",
                "turn": i == self.turn, "me": p is me,
                "cards": p.hand if visible else ["??"] * len(p.hand),
                "hand_name": HAND_NAMES[best_hand(p.hand + self.board)[0]]
                if visible and p.hand and len(self.board) >= 3 else "",
            })
        my_turn = self.stage in BETTING and self.turn is not None and self.players[self.turn] is me
        to_call = max(0, self.current_bet - me.bet)
        return {
            "stage": self.stage, "hand_no": self.hand_no, "board": self.board,
            "pot": sum(p.contrib for p in self.players), "players": players,
            "log": self.log[-15:], "results": self.results,
            "sb": self.sb, "bb": self.bb,
            "time_left": max(0, int(self.turn_time - (time.time() - self.turn_started)))
            if self.turn is not None else None,
            "me": {
                "name": me.name, "chips": me.chips, "my_turn": my_turn,
                "to_call": min(to_call, me.chips), "can_check": to_call == 0,
                "min_raise_to": min(self.current_bet + self.min_raise, me.bet + me.chips),
                "max_raise_to": me.bet + me.chips, "current_bet": self.current_bet,
                "can_rebuy": me.chips == 0 and not (me.in_hand and self.stage in BETTING),
            },
        }


# ---------------------------------------------------------------- HTTP

GAME = None


class Handler(BaseHTTPRequestHandler):
    def log_message(self, *args):
        pass

    def send(self, code, body, ctype="application/json"):
        data = body.encode() if isinstance(body, str) else json.dumps(body).encode()
        self.send_response(code)
        self.send_header("Content-Type", ctype)
        self.send_header("Content-Length", str(len(data)))
        self.send_header("Cache-Control", "no-store")
        self.end_headers()
        self.wfile.write(data)

    def player(self, token):
        for p in GAME.players:
            if p.token == token and not p.left:
                p.last_seen = time.time()
                return p
        return None

    def do_GET(self):
        url = urlparse(self.path)
        if url.path == "/":
            return self.send(200, PAGE, "text/html; charset=utf-8")
        if url.path == "/state":
            token = parse_qs(url.query).get("token", [""])[0]
            with GAME.lock:
                p = self.player(token)
                if not p:
                    return self.send(401, {"error": "not seated"})
                return self.send(200, GAME.view(p))
        self.send(404, {"error": "not found"})

    def do_POST(self):
        try:
            length = int(self.headers.get("Content-Length", 0))
            body = json.loads(self.rfile.read(length) or b"{}")
        except (ValueError, json.JSONDecodeError):
            return self.send(400, {"error": "bad request"})
        path = urlparse(self.path).path
        with GAME.lock:
            try:
                if path == "/join":
                    p = GAME.join(str(body.get("name", "")))
                    return self.send(200, {"token": p.token})
                p = self.player(body.get("token", ""))
                if not p:
                    return self.send(401, {"error": "not seated"})
                if path == "/start":
                    GAME.start_hand()
                elif path == "/action":
                    GAME.act(p, body.get("action"), body.get("amount", 0))
                elif path == "/rebuy":
                    GAME.rebuy(p)
                elif path == "/leave":
                    GAME.leave(p)
                    return self.send(200, {"ok": True})
                else:
                    return self.send(404, {"error": "not found"})
                return self.send(200, GAME.view(p))
            except ValueError as e:
                return self.send(400, {"error": str(e)})


def clock():
    while True:
        time.sleep(1)
        with GAME.lock:
            try:
                GAME.tick()
            except Exception as e:  # keep the clock alive no matter what
                print("tick error:", e)


def lan_ip():
    try:
        s = socket.socket(socket.AF_INET, socket.SOCK_DGRAM)
        s.connect(("10.255.255.255", 1))
        ip = s.getsockname()[0]
        s.close()
        return ip
    except OSError:
        return "127.0.0.1"


PAGE = r"""<!doctype html>
<html lang="en"><head><meta charset="utf-8">
<meta name="viewport" content="width=device-width, initial-scale=1">
<title>LAN Poker</title>
<style>
*{box-sizing:border-box}
body{margin:0;font-family:system-ui,-apple-system,Segoe UI,Roboto,sans-serif;background:#0d1b14;color:#eee}
#join{display:flex;flex-direction:column;align-items:center;justify-content:center;height:100vh;gap:12px}
#join h1{font-size:2.4rem;margin:0}
input,button{font:inherit;padding:10px 14px;border-radius:8px;border:none}
input{background:#1f2f27;color:#fff;border:1px solid #3a5245}
button{background:#e8b94a;color:#1a1a1a;font-weight:600;cursor:pointer}
button:disabled{opacity:.35;cursor:default}
button.alt{background:#2f4a3d;color:#eee}
button.red{background:#c0473f;color:#fff}
.err{color:#ff8a80;min-height:1.2em}
#game{display:none;max-width:1100px;margin:0 auto;padding:12px}
#top{display:flex;justify-content:space-between;align-items:center;font-size:.9rem;color:#9bb}
#table{position:relative;height:460px;margin:30px 0 50px}
#felt{position:absolute;inset:60px 90px;background:radial-gradient(#2b7a4b,#155232);border:12px solid #5a3a1e;border-radius:200px;
 display:flex;flex-direction:column;align-items:center;justify-content:center;gap:10px;box-shadow:inset 0 0 40px #0008}
#board{display:flex;gap:6px;min-height:76px}
#pot{font-weight:700;font-size:1.1rem}
#results{color:#ffe082;font-weight:600;text-align:center}
.seat{position:absolute;width:150px;transform:translate(-50%,-50%);background:#1b2a22ee;border:2px solid #36503f;
 border-radius:10px;padding:6px 8px;text-align:center;font-size:.85rem}
.seat.turn{border-color:#e8b94a;box-shadow:0 0 14px #e8b94a88}
.seat.me{background:#24384aee}
.seat.folded{opacity:.45}
.seat .name{font-weight:700}
.seat .cards{display:flex;justify-content:center;gap:3px;margin:4px 0;min-height:52px}
.seat .bet{color:#ffe082}
.tag{display:inline-block;font-size:.7rem;padding:0 5px;border-radius:4px;background:#e8b94a;color:#000;margin-left:4px}
.card{width:50px;height:72px;background:#fff;color:#111;border-radius:6px;display:flex;flex-direction:column;
 align-items:center;justify-content:center;font-weight:700;font-size:1.25rem;line-height:1.1;box-shadow:0 2px 4px #0006}
.seat .card{width:36px;height:52px;font-size:.95rem}
.card.red{color:#c62828}
.card.back{background:repeating-linear-gradient(45deg,#8b1d2c,#8b1d2c 4px,#a8323f 4px,#a8323f 8px);border:2px solid #fff}
#controls{display:flex;flex-wrap:wrap;gap:8px;align-items:center;justify-content:center;background:#16251d;padding:12px;border-radius:10px}
#raiseBox{display:flex;gap:6px;align-items:center}
#raiseAmt{width:90px}
#log{margin-top:10px;background:#111c16;border-radius:10px;padding:8px 12px;font-size:.8rem;color:#9bb;height:150px;overflow:auto}
@media (max-width:700px){#table{height:520px}#felt{inset:90px 20px}.seat{width:110px;font-size:.75rem}.seat .card{width:28px;height:42px;font-size:.8rem}.card{width:40px;height:58px;font-size:1rem}}
</style></head><body>
<div id="join">
  <h1>♠ LAN Poker ♥</h1>
  <input id="name" placeholder="Your name" maxlength="16" autofocus>
  <button onclick="join()">Sit down</button>
  <div class="err" id="joinErr"></div>
</div>
<div id="game">
  <div id="top"><span id="info"></span><span><button class="alt" onclick="leave()">Leave table</button></span></div>
  <div id="table"><div id="felt"><div id="board"></div><div id="pot"></div><div id="results"></div></div></div>
  <div id="controls"></div>
  <div class="err" id="err" style="text-align:center"></div>
  <div id="log"></div>
</div>
<script>
let token = localStorage.getItem('pokerToken');
let S = null, raiseTouched = false, lastTurnKey = '';
const $ = id => document.getElementById(id);
const SUIT = {s:'♠',h:'♥',d:'♦',c:'♣'};

async function api(path, body) {
  const r = await fetch(path, {method:'POST', headers:{'Content-Type':'application/json'},
    body: JSON.stringify(Object.assign({token}, body || {}))});
  const j = await r.json();
  if (!r.ok) throw new Error(j.error || 'error');
  return j;
}
async function join() {
  try {
    const j = await api('/join', {name: $('name').value});
    token = j.token; localStorage.setItem('pokerToken', token); poll();
  } catch (e) { $('joinErr').textContent = e.message; }
}
$('name').addEventListener('keydown', e => { if (e.key === 'Enter') join(); });
async function send(path, body) {
  $('err').textContent = '';
  try { const s = await api(path, body); if (s.stage) render(s); }
  catch (e) { $('err').textContent = e.message; }
}
const act = (action, amount) => { raiseTouched = false; send('/action', {action, amount}); };
async function leave() {
  if (!confirm('Leave the table? Your chips are lost.')) return;
  try { await api('/leave'); } catch (e) {}
  localStorage.removeItem('pokerToken'); token = null; location.reload();
}

function card(c) {
  if (c === '??') return '<div class="card back"></div>';
  const r = c[0] === 'T' ? '10' : c[0], s = c[1];
  return `<div class="card ${'hd'.includes(s) ? 'red' : ''}"><span>${r}</span><span>${SUIT[s]}</span></div>`;
}
const esc = s => s.replace(/[&<>"]/g, ch => ({'&':'&amp;','<':'&lt;','>':'&gt;','"':'&quot;'}[ch]));

function render(s) {
  S = s;
  $('join').style.display = 'none'; $('game').style.display = 'block';
  const me = s.me;
  $('info').textContent = `Hand #${s.hand_no} · Blinds ${s.sb}/${s.bb} · ${s.stage.replace('_',' ')}`;
  $('board').innerHTML = s.board.map(card).join('');
  $('pot').textContent = s.pot ? `Pot: ${s.pot}` : '';
  $('results').innerHTML = s.stage === 'hand_over' ? s.results.map(esc).join('<br>') : '';

  // seats around an ellipse, with "me" at the bottom
  const tbl = $('table');
  tbl.querySelectorAll('.seat').forEach(e => e.remove());
  const n = s.players.length, mi = Math.max(0, s.players.findIndex(p => p.me));
  const W = tbl.clientWidth, H = tbl.clientHeight;
  s.players.forEach((p, i) => {
    const a = Math.PI / 2 + ((i - mi + n) % n) * 2 * Math.PI / n;
    const d = document.createElement('div');
    d.className = 'seat' + (p.turn ? ' turn' : '') + (p.me ? ' me' : '') + (p.folded || p.left ? ' folded' : '');
    d.style.left = (W / 2 + Math.cos(a) * (W / 2 - 80)) + 'px';
    d.style.top = (H / 2 + Math.sin(a) * (H / 2 - 50)) + 'px';
    const status = p.left ? 'left' : p.folded ? 'folded' : p.all_in ? 'ALL IN' : !p.in_hand && s.stage !== 'waiting' ? 'sitting out' : '';
    d.innerHTML = `<div class="name">${esc(p.name)}${p.dealer ? '<span class="tag">D</span>' : ''}</div>
      <div class="cards">${p.cards.map(card).join('')}</div>
      <div>${p.chips} chips ${status ? '· ' + status : ''}</div>
      <div class="bet">${p.bet ? 'Bet ' + p.bet : '&nbsp;'}</div>
      <div style="color:#9cf">${p.hand_name || '&nbsp;'}</div>`;
    tbl.appendChild(d);
  });

  // controls
  const c = $('controls');
  const turnKey = s.hand_no + s.stage + me.current_bet;
  if (me.my_turn) {
    if (turnKey !== lastTurnKey) { raiseTouched = false; lastTurnKey = turnKey; }
    const prev = $('raiseAmt') && raiseTouched ? $('raiseAmt').value : me.min_raise_to;
    const canRaise = me.max_raise_to > me.current_bet;
    c.innerHTML = `<b style="margin-right:6px">Your turn (${s.time_left}s)</b>
      <button class="red" onclick="act('fold')">Fold</button>
      ${me.can_check ? `<button onclick="act('check')">Check</button>`
                     : `<button onclick="act('call')">Call ${me.to_call}</button>`}
      ${canRaise ? `<span id="raiseBox">
        <input id="raiseAmt" type="number" min="${me.min_raise_to}" max="${me.max_raise_to}" step="${s.bb}" value="${prev}"
          oninput="raiseTouched=true">
        <button onclick="act('raise', $('raiseAmt').value)">${me.current_bet ? 'Raise to' : 'Bet'}</button>
        <button class="alt" onclick="setRaise(${Math.floor(s.pot/2)})">½ pot</button>
        <button class="alt" onclick="setRaise(${s.pot})">Pot</button></span>
        <button class="alt" onclick="act('allin')">All in (${me.max_raise_to})</button>` : ''}`;
  } else if (s.stage === 'waiting') {
    c.innerHTML = `<span>${s.players.length} player(s) seated.</span>
      <button onclick="send('/start')" ${s.players.length < 2 ? 'disabled' : ''}>Start game</button>`;
  } else if (s.stage === 'hand_over') {
    c.innerHTML = `<span>Next hand starting shortly…</span>`;
  } else {
    const t = s.players.find(p => p.turn);
    c.innerHTML = `<span>Waiting for ${t ? esc(t.name) : '…'} (${s.time_left}s)</span>`;
  }
  if (me.can_rebuy) c.innerHTML += ` <button onclick="send('/rebuy')">Rebuy</button>`;

  const log = $('log'), atBottom = log.scrollTop + log.clientHeight >= log.scrollHeight - 5;
  log.innerHTML = s.log.map(esc).join('<br>');
  if (atBottom) log.scrollTop = log.scrollHeight;
}
function setRaise(potSize) {
  const v = Math.max(S.me.min_raise_to, Math.min(S.me.max_raise_to, S.me.current_bet + potSize));
  $('raiseAmt').value = v; raiseTouched = true;
}

async function poll() {
  if (!token) return;
  try {
    const r = await fetch('/state?token=' + token);
    if (r.status === 401) { localStorage.removeItem('pokerToken'); token = null;
      $('join').style.display = 'flex'; $('game').style.display = 'none'; return; }
    render(await r.json());
  } catch (e) {}
  setTimeout(poll, 800);
}
poll();
</script></body></html>
"""


def main():
    global GAME
    ap = argparse.ArgumentParser(description="LAN Texas Hold'em server")
    ap.add_argument("--port", type=int, default=8000)
    ap.add_argument("--chips", type=int, default=1000, help="starting stack")
    ap.add_argument("--sb", type=int, default=10, help="small blind")
    ap.add_argument("--bb", type=int, default=20, help="big blind")
    ap.add_argument("--turn-time", type=int, default=60, help="seconds per turn before auto check/fold")
    a = ap.parse_args()
    GAME = Game(a.chips, a.sb, a.bb, a.turn_time)
    threading.Thread(target=clock, daemon=True).start()
    server = ThreadingHTTPServer(("0.0.0.0", a.port), Handler)
    print(f"Poker server running. Tell your friends to open:  http://{lan_ip()}:{a.port}")
    print("(You can play too at http://localhost:%d)  Ctrl+C to stop." % a.port)
    try:
        server.serve_forever()
    except KeyboardInterrupt:
        pass


if __name__ == "__main__":
    main()
