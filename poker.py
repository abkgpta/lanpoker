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
import sys
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


def best_cards(cards):
    return list(max(combinations(cards, 5), key=eval5))


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
        self.action = ""      # latest action, shown as a speech bubble by the client
        self.action_id = 0
        self.last_seen = time.time()


class Game:
    def __init__(self, chips, sb, bb, turn_time, prank=None, reveal_after=10):
        self.lock = threading.RLock()
        # prank mode: one player is dealt the best hand until the reveal, which always happens
        self.prank = {"name": prank.lower(), "after": reveal_after, "rigged": 0} if prank else None
        self.rigged_hand = False
        self.reveal = None
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
        self.winners = []     # [{"name", "amount"}] for the last finished hand
        self.win_cards = []   # the winning five-card hands, for highlighting
        self.action_seq = 0

    def note(self, p, text):
        self.action_seq += 1
        p.action, p.action_id = text, self.action_seq

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
        self.board, self.results, self.winners, self.win_cards = [], [], [], []
        for p in self.players:
            p.action = ""
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
        target = self.prank_target()
        self.rigged_hand = bool(target) and self.rig_deck(target)
        for _ in range(2):
            for p in self.players:
                if p.in_hand:
                    p.hand.append(self.deck.pop())
        self.stage = "preflop"
        self.turn = bb_i
        self.advance()

    def prank_target(self):
        if not self.prank or self.reveal:
            return None
        return next((p for p in self.players if p.in_hand and p.name.lower() == self.prank["name"]), None)

    def rig_deck(self, target):
        """Reshuffle until the target's hole cards plus the board beat everyone else's."""
        dealt = [p for p in self.players if p.in_hand]
        k, ti = len(dealt), dealt.index(target)
        for _ in range(5000):
            seq = self.deck[::-1]   # cards come off the end: hole cards, then burn/flop, burn/turn, burn/river
            holes = [[seq[i], seq[k + i]] for i in range(k)]
            board = [seq[2 * k + 1], seq[2 * k + 2], seq[2 * k + 3], seq[2 * k + 5], seq[2 * k + 7]]
            mine = best_hand(holes[ti] + board)
            if all(best_hand(h + board) < mine for j, h in enumerate(holes) if j != ti):
                return True
            rng.shuffle(self.deck)
        return False

    def do_reveal(self):
        if not self.prank or self.reveal:
            return False
        n = self.prank["rigged"] + (1 if self.rigged_hand and self.stage in BETTING else 0)
        name = next((p.name for p in self.players if p.name.lower() == self.prank["name"]), self.prank["name"])
        self.reveal = {"id": secrets.token_hex(4),
                       "text": f"The deck was rigged! {name} was dealt the best hand for "
                               f"{n} hand{'' if n == 1 else 's'}. Everything from here on is a fair game."}
        self.rigged_hand = False
        self.say(f"🎭 Prank revealed: the deck was rigged for {name}. It's a fair game from now on.")
        print(f"Prank revealed to everyone ({n} rigged hands).")
        return True

    def post(self, p, amount, label):
        amt = min(amount, p.chips)
        self.put(p, amt)
        self.note(p, f"{label.title()} {amt}")
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
            self.note(p, "Fold")
            self.say(f"{p.name} folds")
        elif action == "check":
            if to_call > 0:
                raise ValueError(f"You need to call {to_call} or fold")
            self.note(p, "Check")
            self.say(f"{p.name} checks")
        elif action == "call":
            if to_call <= 0:
                raise ValueError("Nothing to call — check instead")
            amt = min(to_call, p.chips)
            self.put(p, amt)
            self.note(p, "All in" if p.all_in else f"Call {amt}")
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
            self.note(p, "All in" if p.all_in else f"{verb.split()[0].rstrip('s').title()} {amount}")
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
            self.winners = [{"name": winner.name, "amount": pot}]
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
        win_cards = set()
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
                win_cards.update(best_cards(w.hand + self.board))
            last_winners = winners
        if carry and last_winners:
            last_winners[0].chips += carry
            won[last_winners[0].name] = won.get(last_winners[0].name, 0) + carry
        by_name = {p.name: p for p in alive}
        self.winners = [{"name": n, "amount": a} for n, a in won.items()]
        self.win_cards = sorted(win_cards)
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
        if self.rigged_hand:
            self.prank["rigged"] += 1
            self.rigged_hand = False
            if self.prank["rigged"] >= self.prank["after"]:
                self.do_reveal()
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
                "action": p.action, "action_id": p.action_id,
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
            "winners": self.winners, "win_cards": self.win_cards, "turn_time": self.turn_time,
            "reveal": self.reveal,
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


def console():
    """Lets the host type commands into the server's terminal."""
    for line in sys.stdin:
        cmd = line.strip().lower()
        if cmd == "reveal":
            with GAME.lock:
                if not GAME.do_reveal():
                    print("Nothing to reveal (prank mode is off or already revealed).")
        elif cmd:
            print("Commands: reveal")


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
<meta name="viewport" content="width=device-width, initial-scale=1, viewport-fit=cover">
<title>LAN Poker</title>
<style>
@property --p { syntax: '<number>'; inherits: true; initial-value: 1; }
:root { --gold: #e9c46a; --noise: url("data:image/svg+xml,%3Csvg xmlns='http://www.w3.org/2000/svg' width='220' height='220'%3E%3Cfilter id='n'%3E%3CfeTurbulence type='fractalNoise' baseFrequency='.85' numOctaves='3' stitchTiles='stitch'/%3E%3CfeColorMatrix values='0 0 0 0 .5 0 0 0 0 .5 0 0 0 0 .5 0 0 0 .55 0'/%3E%3C/filter%3E%3Crect width='100%25' height='100%25' filter='url(%23n)'/%3E%3C/svg%3E"); }
* { box-sizing: border-box; }
html, body { margin: 0; height: 100%; overflow: hidden; background: #070605; color: #eee;
  font-family: "Segoe UI", system-ui, -apple-system, Roboto, sans-serif; -webkit-font-smoothing: antialiased; }
button { font: inherit; }

/* ---------- room & table ---------- */
#room { position: fixed; inset: 0;
  background: radial-gradient(ellipse 75% 65% at 50% 42%, #2e2720 0%, #17130f 50%, #070605 100%); }
#room::before { content: ""; position: absolute; inset: 0; background: var(--noise); opacity: .35; mix-blend-mode: overlay; }
#stage { position: absolute; left: 0; top: 0; width: 1200px; height: 720px; transform-origin: 0 0; }
#table { position: absolute; left: 100px; top: 90px; width: 1000px; height: 520px; }
.rail { position: absolute; inset: 0; border-radius: 260px;
  background:
    radial-gradient(ellipse 60% 40% at 50% 0%, rgba(255,214,170,.28), transparent 70%),
    repeating-radial-gradient(ellipse at 50% 50%, rgba(0,0,0,0) 0 5px, rgba(0,0,0,.09) 6px 8px, rgba(255,200,150,.04) 9px 10px, rgba(0,0,0,0) 11px 15px),
    linear-gradient(180deg, #82451f, #5a2c10 55%, #3b1c09);
  box-shadow: 0 60px 90px rgba(0,0,0,.85), 0 18px 30px rgba(0,0,0,.6),
    inset 0 2px 1px rgba(255,225,190,.45), inset 0 -8px 14px rgba(0,0,0,.55); }
.leather { position: absolute; inset: 20px; border-radius: 240px;
  background: radial-gradient(ellipse 80% 70% at 50% 25%, #3b2b23, #1a110d 65%, #0c0806);
  box-shadow: inset 0 3px 3px rgba(255,255,255,.16), inset 0 -5px 10px rgba(0,0,0,.85), 0 0 0 1px #000, 0 2px 4px rgba(0,0,0,.6); }
.leather::after { content: ""; position: absolute; inset: 8px; border-radius: 232px; border: 1px dashed rgba(255,235,210,.13); }
.felt { position: absolute; inset: 46px; border-radius: 214px; overflow: hidden;
  background: var(--noise), radial-gradient(ellipse 62% 58% at 50% 42%, #33a062 0%, #1f7a47 42%, #135a32 75%, #0b3b20 100%);
  background-blend-mode: soft-light, normal;
  box-shadow: inset 0 10px 22px rgba(0,0,0,.6), inset 0 0 40px rgba(0,0,0,.55); }
.felt::before { content: ""; position: absolute; inset: 70px 120px; border-radius: 200px; border: 2px solid rgba(255,255,255,.07); }
.felt::after { content: ""; position: absolute; inset: 0;
  background: radial-gradient(ellipse 45% 40% at 50% 40%, rgba(255,246,214,.16), transparent 70%); pointer-events: none; }
.logo { position: absolute; left: 50%; top: 315px; transform: translateX(-50%); font: 700 30px Georgia, serif;
  letter-spacing: .35em; color: rgba(255,255,255,.07); white-space: nowrap; text-shadow: 0 -1px 0 rgba(0,0,0,.25); }

/* ---------- cards ---------- */
.card { position: absolute; --w: 64px; width: var(--w); height: calc(var(--w) * 1.4); perspective: 700px;
  transition: opacity .3s, translate .45s cubic-bezier(.2,.8,.2,1), filter .45s; }
.card .inner { position: absolute; inset: 0; transform-style: preserve-3d; transform: rotateY(180deg);
  transition: transform .65s cubic-bezier(.3,1.35,.5,1); }
.card.up .inner { transform: rotateY(0deg); }
.card.hidden { opacity: 0; }
.noanim, .noanim * { transition: none !important; }
.card .face { position: absolute; inset: 0; border-radius: calc(var(--w) * .085); backface-visibility: hidden;
  -webkit-backface-visibility: hidden; overflow: hidden;
  box-shadow: 0 1px 1px rgba(0,0,0,.35), 0 5px 12px rgba(0,0,0,.45), inset 0 0 0 1px rgba(0,0,0,.14); }
.card .face::after { content: ""; position: absolute; inset: 0;
  background: linear-gradient(125deg, rgba(255,255,255,.4), rgba(255,255,255,0) 38%, rgba(0,0,0,0) 70%, rgba(0,0,0,.06)); }
.front { background: linear-gradient(160deg, #ffffff 0%, #f7f4ec 55%, #e8e2d2 100%); color: #161616;
  font-size: calc(var(--w) * .27); }
.front.red { color: #c3151b; }
.idx { position: absolute; display: flex; flex-direction: column; align-items: center; line-height: .92;
  font-family: Georgia, "Times New Roman", serif; font-weight: 700; }
.idx b { font-size: 1em; letter-spacing: -.06em; } .idx i { font-style: normal; font-size: .82em; }
.tl { left: .2em; top: .22em; } .br { right: .2em; bottom: .22em; transform: rotate(180deg); }
.pip { position: absolute; inset: 0; display: flex; align-items: center; justify-content: center; font-size: 2em; }
.pip.ace { font-size: 2.9em; }
.court { position: absolute; inset: 19% 21%; border-radius: .18em; display: flex; flex-direction: column;
  align-items: center; justify-content: center; font-family: Georgia, serif; font-weight: 700;
  background: linear-gradient(160deg, rgba(233,196,106,.45), rgba(205,70,60,.14) 60%, rgba(60,80,170,.15));
  box-shadow: inset 0 0 0 1px rgba(0,0,0,.28), inset 0 0 0 3px rgba(255,255,255,.6), inset 0 0 0 4px rgba(0,0,0,.12); }
.court span { font-size: 1.75em; line-height: 1; } .court i { font-style: normal; font-size: 1em; }
.back { transform: rotateY(180deg); background: #fbfbf8; }
.back::before { content: ""; position: absolute; inset: calc(var(--w) * .065); border-radius: calc(var(--w) * .05);
  background:
    radial-gradient(circle at 50% 50%, rgba(255,255,255,.35) 0 10%, transparent 11%),
    radial-gradient(circle at 50% 50%, transparent 0 17%, rgba(255,255,255,.22) 18% 19%, transparent 20%),
    repeating-linear-gradient(45deg, rgba(255,255,255,.13) 0 1.5px, transparent 1.5px 6px),
    repeating-linear-gradient(-45deg, rgba(255,255,255,.13) 0 1.5px, transparent 1.5px 6px),
    linear-gradient(160deg, #b3263a, #7d1121);
  box-shadow: inset 0 0 0 1.5px rgba(255,255,255,.45), inset 0 0 0 3px rgba(125,17,33,.9); }
.card.win { translate: 0 -12px; }
.card.win .front { box-shadow: 0 0 0 2px #ffd977, 0 0 22px rgba(255,210,100,.85), 0 8px 16px rgba(0,0,0,.5); }
.card.dim { filter: brightness(.42) saturate(.5); }

#deck { position: absolute; left: 330px; top: 350px; }
#deck .card { --w: 60px; }
#board { position: absolute; left: 0; top: 0; }
.slot { position: absolute; width: 64px; height: 90px; border-radius: 6px; transform: translate(-50%,-50%);
  border: 1.5px solid rgba(255,255,255,.07); background: rgba(0,0,0,.06); }
#board .card { transform: translate(-50%,-50%); }

/* ---------- chips ---------- */
.stack { position: absolute; left: 0; top: 8px; width: 0; height: 0; }
.chip { position: absolute; width: 30px; height: 20px; margin-left: -15px; border-radius: 50%;
  background:
    radial-gradient(ellipse at 50% 50%, var(--c) 0 34%, var(--e) 35% 39%, var(--c) 40% 57%, transparent 58%),
    repeating-conic-gradient(from 8deg, var(--e) 0 14deg, var(--c) 14deg 45deg);
  box-shadow: inset 0 1px 0 rgba(255,255,255,.35), 0 1px 0 rgba(0,0,0,.25), 0 3.5px 0 var(--d), 0 5px 4px rgba(0,0,0,.55); }
.betspot { position: absolute; width: 0; height: 0; transition: left .7s cubic-bezier(.2,.8,.2,1), top .7s cubic-bezier(.2,.8,.2,1); }
.betspot .amt, #pot .amt { position: absolute; left: 50%; transform: translateX(-50%); white-space: nowrap;
  font-weight: 700; font-variant-numeric: tabular-nums; color: #fff; border-radius: 10px;
  background: rgba(0,0,0,.55); box-shadow: inset 0 0 0 1px rgba(255,255,255,.08); }
.betspot .amt { top: 16px; font-size: 13px; padding: 1px 9px; }
.betspot.empty, #pot.empty { opacity: 0; }
#pot { position: absolute; left: 600px; top: 252px; width: 0; height: 0; transition: opacity .35s; }
#pot .amt { top: 18px; font-size: 15px; padding: 3px 14px; color: var(--gold); letter-spacing: .03em; }

#dealerBtn { position: absolute; width: 32px; height: 32px; border-radius: 50%; transform: translate(-50%,-50%);
  background: radial-gradient(circle at 35% 30%, #fff, #e8e8e8 55%, #b9b9b9); color: #1d1d1d; font: 900 15px Georgia, serif;
  display: flex; align-items: center; justify-content: center; opacity: 0;
  box-shadow: 0 3px 0 #8d8d8d, 0 6px 10px rgba(0,0,0,.6), inset 0 0 0 3px rgba(0,0,0,.08);
  transition: left .9s cubic-bezier(.3,1.25,.5,1), top .9s cubic-bezier(.3,1.25,.5,1), opacity .4s; }

/* ---------- seats ---------- */
.seat { position: absolute; width: 190px; height: 132px; transform: translate(-50%,-50%);
  transition: left .7s cubic-bezier(.2,.8,.2,1), top .7s cubic-bezier(.2,.8,.2,1), opacity .5s; }
.seat.me { width: 240px; height: 168px; }
.hole { position: absolute; left: 50%; top: 0; width: 0; height: 0; }
.seat .card { --w: 54px; left: calc(var(--w) / -2); top: 0; }
.seat.me .card { --w: 80px; }
.plate { position: absolute; left: 50%; bottom: 0; transform: translateX(-50%); width: 178px; height: 52px;
  border-radius: 26px; display: flex; align-items: center; z-index: 2;
  background: linear-gradient(180deg, rgba(46,46,52,.97), rgba(16,16,19,.97));
  box-shadow: 0 10px 22px rgba(0,0,0,.65), inset 0 1px 0 rgba(255,255,255,.13), 0 0 0 1px rgba(0,0,0,.85);
  transition: box-shadow .4s, opacity .4s, filter .4s; }
.seat.me .plate { width: 200px; }
.avatar { position: relative; width: 58px; height: 58px; margin-left: -6px; flex: none; }
.av { position: absolute; inset: 6px; border-radius: 50%; display: flex; align-items: center; justify-content: center;
  font-weight: 700; font-size: 17px; color: #fff; text-shadow: 0 1px 2px rgba(0,0,0,.6);
  background: radial-gradient(circle at 35% 28%, hsl(var(--h) 75% 68%), hsl(var(--h) 60% 38%) 62%, hsl(var(--h) 60% 20%));
  box-shadow: inset 0 -3px 6px rgba(0,0,0,.4), 0 2px 5px rgba(0,0,0,.7), 0 0 0 2px rgba(0,0,0,.6); }
.ring { position: absolute; inset: 0; border-radius: 50%; opacity: 0;
  background: conic-gradient(var(--rc, #7ee787) calc(var(--p) * 360deg), rgba(255,255,255,.07) 0);
  -webkit-mask: radial-gradient(circle, transparent 62%, #000 63%); mask: radial-gradient(circle, transparent 62%, #000 63%);
  transition: --p 1s linear, opacity .3s; }
.seat.turn .ring { opacity: 1; }
.pinfo { padding: 0 16px 0 6px; min-width: 0; }
.pname { font-weight: 600; font-size: 15px; white-space: nowrap; overflow: hidden; text-overflow: ellipsis; max-width: 112px; }
.pchips { font-size: 14px; color: var(--gold); font-variant-numeric: tabular-nums; display: flex; align-items: center; gap: 5px; }
.pchips::before { content: ""; width: 11px; height: 11px; border-radius: 50%;
  background: repeating-conic-gradient(#fff 0 30deg, #c0262d 30deg 90deg); box-shadow: 0 0 0 1px rgba(0,0,0,.5); }
.tag { position: absolute; top: -9px; right: 12px; font-size: 10px; font-weight: 800; letter-spacing: .07em;
  padding: 2px 8px; border-radius: 9px; background: #444; color: #fff; opacity: 0; transition: opacity .3s; }
.tag.on { opacity: 1; } .tag.allin { background: linear-gradient(180deg, #e04848, #9c1d1d); }
.seat.turn .plate { animation: pulse 1.5s ease-in-out infinite; }
@keyframes pulse {
  0%, 100% { box-shadow: 0 0 0 2px var(--gold), 0 0 18px rgba(233,196,106,.45), 0 10px 22px rgba(0,0,0,.65); }
  50% { box-shadow: 0 0 0 2px var(--gold), 0 0 34px rgba(233,196,106,.8), 0 10px 22px rgba(0,0,0,.65); } }
.seat.folded .plate, .seat.out .plate { opacity: .5; filter: grayscale(.7); }
.seat.winner .plate { box-shadow: 0 0 0 2px #ffd977, 0 0 46px 8px rgba(255,210,100,.65), 0 10px 22px rgba(0,0,0,.65); }
.hname { position: absolute; left: 50%; top: -26px; transform: translateX(-50%); white-space: nowrap; z-index: 3;
  font-size: 13px; font-weight: 600; color: #cfe8ff; padding: 2px 10px; border-radius: 10px; background: rgba(0,0,0,.6);
  opacity: 0; transition: opacity .4s; }
.hname.on { opacity: 1; }
.bubble { position: absolute; left: 50%; bottom: 58px; z-index: 6; white-space: nowrap; pointer-events: none;
  padding: 6px 15px; border-radius: 16px; font-weight: 800; font-size: 14px; color: #1a1a1a; background: #f4f4f4;
  box-shadow: 0 8px 18px rgba(0,0,0,.55); opacity: 0; transform: translate(-50%, 6px) scale(.6);
  transition: opacity .25s, transform .4s cubic-bezier(.3,1.6,.5,1); }
.seat.upper .bubble { bottom: auto; top: calc(100% + 8px); }
.bubble.show { opacity: 1; transform: translate(-50%, 0) scale(1); }
.bubble.fold { background: #8a8a8a; color: #fff; } .bubble.check { background: #5aa9ff; color: #fff; }
.bubble.call { background: #3fae6a; color: #fff; } .bubble.raise, .bubble.bet { background: var(--gold); }
.bubble.allin { background: #e04848; color: #fff; } .bubble.blind { background: #ddd; }

#fx { position: absolute; inset: 0; pointer-events: none; z-index: 30; }
#fx > * { position: absolute; }
.floater { font: 800 24px Georgia, serif; color: #ffe08a; text-shadow: 0 2px 8px rgba(0,0,0,.8), 0 0 18px rgba(255,200,80,.6); }
#banner { position: absolute; left: 600px; top: 450px; transform: translate(-50%,-50%) scale(.8); opacity: 0; z-index: 25;
  padding: 10px 26px; border-radius: 30px; text-align: center; font: 600 19px Georgia, serif; color: #ffe39a;
  background: rgba(10,10,10,.72); box-shadow: 0 0 0 1px rgba(233,196,106,.5), 0 12px 30px rgba(0,0,0,.6);
  transition: opacity .4s, transform .5s cubic-bezier(.3,1.5,.5,1); pointer-events: none; }
#banner.show { opacity: 1; transform: translate(-50%,-50%) scale(1); }
#feltMsg { position: absolute; left: 600px; top: 350px; transform: translate(-50%,-50%); text-align: center;
  transition: opacity .5s; pointer-events: none; }
#feltMsg h2 { margin: 0; font: 700 30px Georgia, serif; color: rgba(255,255,255,.85); text-shadow: 0 2px 10px rgba(0,0,0,.6); }
#feltMsg p { margin: 6px 0 0; color: rgba(255,255,255,.6); }

/* ---------- HUD, controls, panels ---------- */
#hud { position: fixed; top: 0; left: 0; right: 0; display: flex; justify-content: space-between; align-items: center;
  padding: 10px 14px; z-index: 20; pointer-events: none; }
#hud > * { pointer-events: auto; }
.pill { padding: 7px 14px; border-radius: 18px; background: rgba(0,0,0,.45); font-size: 13px; color: #cbb;
  box-shadow: inset 0 0 0 1px rgba(255,255,255,.08); backdrop-filter: blur(6px); }
.small { border: none; cursor: pointer; color: #ddd; padding: 7px 14px; border-radius: 18px; margin-left: 6px;
  background: rgba(255,255,255,.08); box-shadow: inset 0 0 0 1px rgba(255,255,255,.12); transition: background .2s; }
.small:hover { background: rgba(255,255,255,.16); }
#log { position: fixed; top: 52px; right: 14px; width: 300px; max-height: 45vh; overflow: auto; z-index: 21;
  padding: 12px 14px; border-radius: 14px; font-size: 12.5px; line-height: 1.55; color: #bcc;
  background: rgba(12,12,14,.82); backdrop-filter: blur(10px); box-shadow: 0 12px 30px rgba(0,0,0,.6), inset 0 0 0 1px rgba(255,255,255,.08);
  transform: translateX(120%); transition: transform .45s cubic-bezier(.2,.8,.2,1); }
#log.open { transform: none; }
#controls { position: fixed; left: 0; right: 0; bottom: 0; z-index: 20; min-height: 92px;
  padding: 14px 16px calc(14px + env(safe-area-inset-bottom)); display: flex; justify-content: center; align-items: center;
  background: linear-gradient(180deg, rgba(8,7,6,0), rgba(8,7,6,.88) 35%); }
.panel { display: flex; gap: 10px; align-items: center; justify-content: center; flex-wrap: wrap;
  animation: rise .4s cubic-bezier(.2,.8,.2,1); }
@keyframes rise { from { opacity: 0; transform: translateY(18px); } }
.status { color: #bbb; font-size: 15px; }
.btn { border: none; cursor: pointer; font-weight: 700; font-size: 16px; color: #fff; padding: 14px 22px; border-radius: 14px;
  min-width: 118px; transition: transform .12s, filter .2s, box-shadow .2s;
  box-shadow: inset 0 1px 0 rgba(255,255,255,.3), inset 0 -3px 0 rgba(0,0,0,.25), 0 8px 16px rgba(0,0,0,.5); }
.btn:hover { filter: brightness(1.1); transform: translateY(-2px); }
.btn:active { transform: translateY(1px); box-shadow: inset 0 3px 6px rgba(0,0,0,.4); }
.btn:disabled { opacity: .4; cursor: default; transform: none; }
.btn kbd { font: 600 11px system-ui; opacity: .6; margin-left: 6px; }
.fold { background: linear-gradient(180deg, #dc5a55, #a12924); }
.call { background: linear-gradient(180deg, #45b571, #1f7c45); }
.raise { background: linear-gradient(180deg, #f6d57e, #c8962a); color: #2b1d00; }
.ghost { background: rgba(255,255,255,.09); box-shadow: inset 0 0 0 1px rgba(255,255,255,.15); }
.raisebox { display: flex; flex-direction: column; gap: 7px; padding: 8px 10px; border-radius: 14px;
  background: rgba(255,255,255,.05); box-shadow: inset 0 0 0 1px rgba(255,255,255,.08); }
.presets { display: flex; gap: 5px; }
.presets button { flex: 1; border: none; cursor: pointer; font-size: 12px; font-weight: 600; color: #ddd; padding: 5px 8px;
  border-radius: 8px; background: rgba(255,255,255,.08); transition: background .2s; }
.presets button:hover { background: rgba(255,255,255,.18); }
input[type=range] { -webkit-appearance: none; appearance: none; width: 240px; height: 6px; border-radius: 3px; outline: none;
  background: linear-gradient(90deg, var(--gold) var(--fill, 0%), rgba(255,255,255,.15) var(--fill, 0%)); }
input[type=range]::-webkit-slider-thumb { -webkit-appearance: none; width: 22px; height: 22px; border-radius: 50%; cursor: pointer;
  background: radial-gradient(circle at 35% 30%, #fff, #e9c46a 60%, #a8781f); box-shadow: 0 2px 6px rgba(0,0,0,.6); }
input[type=range]::-moz-range-thumb { width: 22px; height: 22px; border: none; border-radius: 50%; cursor: pointer;
  background: radial-gradient(circle at 35% 30%, #fff, #e9c46a 60%, #a8781f); box-shadow: 0 2px 6px rgba(0,0,0,.6); }
.turnbar { position: absolute; left: 0; right: 0; bottom: 0; height: 4px; overflow: hidden; }
.turnbar div { height: 100%; background: linear-gradient(90deg, #e9c46a, #f08a4b); transition: width 1s linear; }
#toast { position: fixed; top: 60px; left: 50%; transform: translate(-50%, -20px); opacity: 0; z-index: 60;
  padding: 10px 18px; border-radius: 12px; background: rgba(160,30,30,.92); color: #fff; font-weight: 600;
  box-shadow: 0 10px 24px rgba(0,0,0,.5); transition: opacity .3s, transform .4s cubic-bezier(.3,1.5,.5,1); pointer-events: none; }
#toast.show { opacity: 1; transform: translate(-50%, 0); }

/* ---------- join screen ---------- */
#join { position: fixed; inset: 0; z-index: 50; display: flex; align-items: center; justify-content: center;
  background: rgba(6,5,4,.55); backdrop-filter: blur(7px); transition: opacity .6s; }
#join.gone { opacity: 0; pointer-events: none; }
.jbox { text-align: center; padding: 20px; }
.fan { position: relative; height: 150px; width: 260px; margin: 0 auto 6px; }
.fan .card { --w: 80px; left: 90px; top: 10px; transform-origin: 50% 120%; }
.jbox h1 { margin: 0; font: 700 54px Georgia, serif; letter-spacing: .04em;
  background: linear-gradient(180deg, #fff6d0, #e9c46a 52%, #9c6c18); -webkit-background-clip: text; background-clip: text; color: transparent;
  filter: drop-shadow(0 4px 10px rgba(0,0,0,.7)); }
.jbox p { margin: 2px 0 22px; color: #a99; letter-spacing: .3em; text-transform: uppercase; font-size: 12px; }
.jbox input { display: block; margin: 0 auto 12px; width: 260px; padding: 14px 16px; border-radius: 12px; border: none; outline: none;
  font: inherit; font-size: 17px; text-align: center; color: #fff; background: rgba(255,255,255,.08);
  box-shadow: inset 0 0 0 1px rgba(255,255,255,.18), inset 0 2px 6px rgba(0,0,0,.4); transition: box-shadow .2s; }
.jbox input:focus { box-shadow: inset 0 0 0 1.5px var(--gold), 0 0 18px rgba(233,196,106,.25); }
.jbox .btn { width: 260px; }
.err { color: #ff8f86; min-height: 1.4em; margin-top: 10px; font-size: 14px; }
#reveal { position: fixed; inset: 0; z-index: 55; display: flex; align-items: center; justify-content: center;
  background: rgba(6,5,4,.6); backdrop-filter: blur(5px); opacity: 0; pointer-events: none; transition: opacity .5s; }
#reveal.show { opacity: 1; pointer-events: auto; }
.rbox { text-align: center; max-width: 440px; padding: 30px 30px 26px; border-radius: 22px; background: rgba(20,18,16,.92);
  box-shadow: 0 0 0 1px rgba(233,196,106,.45), 0 30px 70px rgba(0,0,0,.7); transform: scale(.7) rotate(-4deg);
  transition: transform .7s cubic-bezier(.3,1.6,.5,1); }
#reveal.show .rbox { transform: none; }
.rbox .mask { font-size: 64px; animation: wobble 1.2s ease-in-out infinite; display: inline-block; }
@keyframes wobble { 0%, 100% { transform: rotate(-10deg); } 50% { transform: rotate(10deg) scale(1.08); } }
.rbox h2 { margin: 6px 0 8px; font: 700 40px Georgia, serif; color: var(--gold); }
.rbox p { margin: 0 0 20px; color: #ddd; line-height: 1.5; font-size: 16px; }
@media (prefers-reduced-motion: reduce) { .seat.turn .plate { animation: none; } }
</style></head><body>
<div id="room">
  <div id="stage">
    <div id="table"><div class="rail"></div><div class="leather"></div><div class="felt"><div class="logo">♠ LAN POKER ♥</div></div></div>
    <div id="feltMsg"></div>
    <div id="deck"></div>
    <div id="board"></div>
    <div id="pot" class="empty"><div class="stack"></div><div class="amt">Pot 0</div></div>
    <div id="dealerBtn">D</div>
    <div id="seats"></div>
    <div id="banner"></div>
    <div id="fx"></div>
  </div>
</div>
<div id="hud"><span class="pill" id="info">LAN Poker</span>
  <span><button class="small" id="musicBtn" onclick="toggleMusic()">🎵 Music</button><button class="small" id="muteBtn" onclick="toggleMute()">🔊 Sound</button><button class="small" onclick="toggleLog()">History</button><button class="small" onclick="leave()">Leave</button></span></div>
<div id="log"></div>
<div id="controls"></div>
<div id="toast"></div>
<div id="reveal"><div class="rbox"><div class="mask">🎭</div><h2>Gotcha!</h2><p id="revealText"></p>
  <button class="btn raise" onclick="$('reveal').classList.remove('show')">😂 Fair enough</button></div></div>
<div id="join"><div class="jbox">
  <div class="fan" id="fan"></div>
  <h1>LAN Poker</h1><p>Texas Hold'em</p>
  <input id="name" placeholder="Your name" maxlength="16" autocomplete="off">
  <button class="btn raise" onclick="join()">Take a seat</button>
  <div class="err" id="joinErr"></div>
</div></div>
<script>
const SPEED = matchMedia('(prefers-reduced-motion: reduce)').matches ? 0.01 : 1;
const W = 1200, H = 720, CX = 600, CY = 350, RX = 505, RY = 285, BX = 330, BY = 168;
const SUIT = { s: '♠', h: '♥', d: '♦', c: '♣' };
const DENOMS = [[1000, '#e3ab12', '#5b3d00', '#8a6200'], [500, '#7d2fc2', '#f3e9ff', '#4a1878'],
  [100, '#1e1e1e', '#e8e8e8', '#000'], [25, '#1f8b3c', '#f4fff4', '#0e5222'],
  [5, '#c4262e', '#fff3f3', '#7a1016'], [1, '#efefef', '#2160c4', '#9a9a9a']];
const $ = id => document.getElementById(id);
const stage = $('stage'), fx = $('fx');
const wait = ms => new Promise(r => setTimeout(r, ms * SPEED));
const fmt = n => Number(n).toLocaleString();
const esc = s => String(s).replace(/[&<>"]/g, c => ({ '&': '&amp;', '<': '&lt;', '>': '&gt;', '"': '&quot;' }[c]));
let token = null;
try { token = localStorage.getItem('pokerToken'); } catch (e) {}
let scale = 1, latest = null, shown = null, busy = false, seatKey = '', potAmt = 0;

// ---------------------------------------------------------------- sound (synthesized, no audio files)
const Sound = (() => {
  let ctx = null, master = null, noiseBuf = null, muted = false;
  try { muted = localStorage.getItem('pokerMuted') === '1'; } catch (e) {}
  function init() {
    if (ctx) { if (ctx.state === 'suspended') ctx.resume(); startMusic(); return; }
    const AC = window.AudioContext || window.webkitAudioContext;
    if (!AC) return;
    ctx = new AC();
    master = ctx.createGain(); master.gain.value = .6;
    const comp = ctx.createDynamicsCompressor();
    master.connect(comp); comp.connect(ctx.destination);
    noiseBuf = ctx.createBuffer(1, ctx.sampleRate, ctx.sampleRate);
    const d = noiseBuf.getChannelData(0);
    for (let i = 0; i < d.length; i++) d[i] = Math.random() * 2 - 1;
    startMusic();
  }
  ['pointerdown', 'keydown'].forEach(ev => addEventListener(ev, init, { passive: true }));
  function env(t, dur, gain, attack, dest) {
    const g = ctx.createGain();
    g.gain.setValueAtTime(0, t);
    g.gain.linearRampToValueAtTime(gain, t + attack);
    g.gain.exponentialRampToValueAtTime(.0001, t + dur);
    g.connect(dest || master);
    return g;
  }
  function noise(t, dur, { type = 'bandpass', freq = 3000, sweep = 0, q = 1, gain = .4, attack = .002, dest } = {}) {
    const src = ctx.createBufferSource(), f = ctx.createBiquadFilter();
    src.buffer = noiseBuf; f.type = type; f.Q.value = q;
    f.frequency.setValueAtTime(freq, t);
    if (sweep) f.frequency.exponentialRampToValueAtTime(sweep, t + dur);
    src.connect(f); f.connect(env(t, dur, gain, attack, dest));
    src.start(t, Math.random() * .5); src.stop(t + dur + .05);
  }
  function tone(t, freq, dur, { type = 'sine', gain = .2, attack = .003, to = 0 } = {}) {
    const o = ctx.createOscillator();
    o.type = type; o.frequency.setValueAtTime(freq, t);
    if (to) o.frequency.exponentialRampToValueAtTime(to, t + dur);
    o.connect(env(t, dur, gain, attack));
    o.start(t); o.stop(t + dur + .05);
  }
  function clink(t, v = 1) {   // ceramic chip on chip: a few inharmonic partials and a click
    const f = 2400 + Math.random() * 1600;
    tone(t, f, .1, { gain: .1 * v }); tone(t, f * 1.47, .07, { gain: .06 * v }); tone(t, f * 2.31, .05, { gain: .035 * v });
    noise(t, .02, { type: 'highpass', freq: 5000, gain: .22 * v });
  }
  const S = {
    deal(t) { noise(t, .13, { freq: 2600, sweep: 900, q: .7, gain: .3 }); noise(t + .1, .05, { freq: 1100, gain: .22 }); },
    flip(t) { noise(t, .045, { type: 'highpass', freq: 2600, gain: .3 }); noise(t + .025, .06, { freq: 750, q: 1.2, gain: .22 }); },
    shuffle(t) { for (let i = 0; i < 16; i++) noise(t + i * .028 + Math.random() * .01, .03, { freq: 2500 + Math.random() * 2000, gain: .13 }); },
    chips(t, n = 3) {
      for (let i = 0; i < n; i++) clink(t + i * (.03 + Math.random() * .03), 1 - i * .07);
      noise(t, .06, { type: 'lowpass', freq: 700, gain: .2 });
    },
    sweep(t) { noise(t, .38, { freq: 1700, sweep: 600, q: .6, gain: .2 }); for (let i = 0; i < 8; i++) clink(t + .06 + i * .04 + Math.random() * .02, .55); },
    knock(t) { for (const d of [0, .14]) { tone(t + d, 150, .12, { gain: .45, to: 70 }); noise(t + d, .04, { type: 'lowpass', freq: 900, gain: .35 }); } },
    fold(t) { noise(t, .3, { freq: 1400, sweep: 380, q: .5, gain: .2 }); },
    turn(t) { tone(t, 880, .4, { type: 'triangle', gain: .1 }); tone(t + .13, 1318.5, .6, { type: 'triangle', gain: .1 }); },
    tick(t) { tone(t, 1900, .035, { type: 'square', gain: .035 }); },
    allin(t) { tone(t, 95, .7, { gain: .4, to: 42 }); noise(t, .45, { type: 'lowpass', freq: 320, gain: .3 }); S.chips(t + .05, 7); },
    win(t, mine) {
      for (let i = 0; i < 12; i++) clink(t + i * .045 + Math.random() * .02, .75);
      if (mine) [523.25, 659.25, 783.99, 1046.5].forEach((f, i) => {
        tone(t + .1 + i * .11, f, .7, { type: 'triangle', gain: .09 }); tone(t + .1 + i * .11, f * 2, .4, { gain: .03 });
      });
    },
    click(t) { noise(t, .018, { type: 'highpass', freq: 3200, gain: .1 }); },
    gotcha(t) {   // sad trombone: wah, wah, wah, waaaah
      [[392, .32], [370, .32], [349, .32], [330, 1.3]].forEach(([f, d], i) => {
        const st = t + i * .36, o = ctx.createOscillator(), lp = ctx.createBiquadFilter();
        o.type = 'sawtooth'; o.frequency.setValueAtTime(f, st); lp.type = 'lowpass'; lp.Q.value = 4;
        lp.frequency.setValueAtTime(500, st); lp.frequency.linearRampToValueAtTime(1600, st + .12);
        lp.frequency.linearRampToValueAtTime(700, st + d);
        if (i === 3) {
          const lfo = ctx.createOscillator(), lg = ctx.createGain();
          lfo.frequency.value = 5.5; lg.gain.value = 9; lfo.connect(lg); lg.connect(o.frequency);
          lfo.start(st); lfo.stop(st + d + .1);
        }
        o.connect(lp); lp.connect(env(st, d, .16, .04)); o.start(st); o.stop(st + d + .1);
      });
    },
  };

  // ---- background music: an endless, quiet lounge-jazz trio generated on the fly
  let musicOn = true, mbus = null, timer = null, nextT = 0, beat = 0;
  try { musicOn = localStorage.getItem('pokerMusic') !== '0'; } catch (e) {}
  const mtof = m => 440 * Math.pow(2, (m - 69) / 12);
  const SPB = 60 / 76;   // seconds per beat
  const SONG = [         // [bass root, piano voicing]: Dm9 G13 Cmaj9 Am9 Dm9 G7b9 Cmaj9 A7b9
    [38, [53, 57, 60, 64]], [43, [53, 59, 64, 69]], [36, [52, 55, 59, 62]], [45, [55, 59, 60, 64]],
    [38, [53, 57, 60, 64]], [43, [53, 56, 59, 62]], [36, [52, 55, 59, 62]], [45, [55, 61, 64, 70]]];
  function voice(t, freq, dur, gain, { type = 'sine', cutoff = 2400, attack = .012 } = {}) {
    const o = ctx.createOscillator(), f = ctx.createBiquadFilter(), g = ctx.createGain();
    o.type = type; o.frequency.value = freq; f.type = 'lowpass'; f.frequency.value = cutoff;
    g.gain.setValueAtTime(0, t);
    g.gain.linearRampToValueAtTime(gain, t + attack);
    g.gain.exponentialRampToValueAtTime(gain * .35, t + attack + .25);
    g.gain.exponentialRampToValueAtTime(.0001, t + dur);
    o.connect(f); f.connect(g); g.connect(mbus); o.start(t); o.stop(t + dur + .05);
  }
  function keys(t, notes, dur, gain) {   // soft electric piano: sine plus a quiet bell-like overtone
    for (const n of notes) { voice(t, mtof(n), dur, gain); voice(t, mtof(n) * 2.003, dur * .5, gain * .22, { type: 'triangle' }); }
  }
  function scheduleBeat(t, i) {
    const bar = Math.floor(i / 4) % SONG.length, b = i % 4, [root, chord] = SONG[bar];
    const next = SONG[(bar + 1) % SONG.length][0], swing = SPB * 2 / 3;
    const walk = [root, root + 7, root + 12, next + (bar % 2 ? -1 : 1)];   // walking bass with a chromatic approach
    voice(t, mtof(walk[b]), SPB * .95, .17, { type: 'triangle', cutoff: 650, attack: .006 });
    if (b === 0) keys(t + .01, chord, SPB * 1.5, .026);
    if (b === 1 && Math.random() < .7) keys(t + swing, chord, SPB * 1.2, .02);
    if (b === 3 && Math.random() < .3) keys(t + swing, chord, SPB * .8, .016);
    noise(t, .2, { type: 'highpass', freq: 7000, gain: .02, dest: mbus });                     // ride cymbal
    if (b % 2) {
      noise(t + swing, .12, { type: 'highpass', freq: 7500, gain: .014, dest: mbus });
      noise(t, .28, { freq: 2400, q: .5, gain: .018, dest: mbus });                              // brushed snare
    }
    for (const off of [0, swing]) if (Math.random() < .18)                                        // a few vibraphone notes
      voice(t + off, mtof(chord[Math.floor(Math.random() * chord.length)] + 12), SPB * 1.8, .028, { cutoff: 4000, attack: .004 });
  }
  function musicTick() { while (nextT < ctx.currentTime + .4) { scheduleBeat(nextT, beat++); nextT += SPB; } }
  function startMusic() {
    if (!ctx || timer || !musicOn || document.hidden) return;
    if (!mbus) { mbus = ctx.createGain(); mbus.connect(master); }
    const now = ctx.currentTime;
    mbus.gain.cancelScheduledValues(now); mbus.gain.setValueAtTime(0, now); mbus.gain.linearRampToValueAtTime(.85, now + 2.5);
    nextT = now + .15; timer = setInterval(musicTick, 100); musicTick();
  }
  function stopMusic() {
    if (!timer) return;
    clearInterval(timer); timer = null;
    mbus.gain.cancelScheduledValues(ctx.currentTime); mbus.gain.setTargetAtTime(0, ctx.currentTime, .25);
  }
  document.addEventListener('visibilitychange', () => document.hidden ? stopMusic() : startMusic());
  return {
    play(name, delayMs = 0, ...args) {
      if (muted || !ctx || ctx.state !== 'running' || SPEED < 1) return;
      S[name](ctx.currentTime + .01 + delayMs / 1000, ...args);
    },
    get muted() { return muted; },
    get musicOn() { return musicOn; },
    toggleMusic() {
      musicOn = !musicOn;
      try { localStorage.setItem('pokerMusic', musicOn ? '1' : '0'); } catch (e) {}
      init(); musicOn ? startMusic() : stopMusic();
      return musicOn;
    },
    toggle() { muted = !muted; try { localStorage.setItem('pokerMuted', muted ? '1' : '0'); } catch (e) {} init(); return muted; },
  };
})();
const sfx = (...a) => Sound.play(...a);
function toggleMusic() { $('musicBtn').textContent = Sound.toggleMusic() ? '🎵 Music' : '🎵 Music off'; }
function toggleMute() { $('muteBtn').textContent = Sound.toggle() ? '🔇 Sound' : '🔊 Sound'; }
addEventListener('pointerdown', e => { if (e.target.closest('.btn, .presets button, .small')) sfx('click'); });
const seats = {};

// ---------------------------------------------------------------- layout
function fit() {
  const ch = $('controls').offsetHeight || 92, top = 44, avail = innerHeight - ch - top + 30;
  scale = Math.min(innerWidth / W, avail / H);
  stage.style.transform = `scale(${scale})`;
  stage.style.left = (innerWidth - W * scale) / 2 + 'px';
  stage.style.top = top + Math.max(0, (avail - H * scale) / 2) - 10 + 'px';
}
addEventListener('resize', fit);

function center(el) {
  const r = el.getBoundingClientRect(), s = stage.getBoundingClientRect();
  return { x: (r.left + r.width / 2 - s.left) / scale, y: (r.top + r.height / 2 - s.top) / scale };
}

// ---------------------------------------------------------------- cards
function makeCard(w) {
  const c = document.createElement('div');
  c.className = 'card';
  if (w) c.style.setProperty('--w', w + 'px');
  c.innerHTML = '<div class="inner"><div class="face front"></div><div class="face back"></div></div>';
  return c;
}
function faceHTML(code) {
  const r = code[0] === 'T' ? '10' : code[0], s = SUIT[code[1]];
  const idx = `<b>${r}</b><i>${s}</i>`;
  const mid = 'JQK'.includes(r) ? `<div class="court"><span>${r}</span><i>${s}</i></div>`
    : `<div class="pip ${r === 'A' ? 'ace' : ''}">${s}</div>`;
  return `<div class="idx tl">${idx}</div>${mid}<div class="idx br">${idx}</div>`;
}
function instant(el, fn) { el.classList.add('noanim'); fn(); el.offsetWidth; el.classList.remove('noanim'); }
function setCard(c, code, anim = true) {
  if (!code) { if (!c.classList.contains('hidden')) c.classList.add('hidden'); return; }
  const apply = () => {
    c.classList.remove('hidden');
    if (c.dataset.code === code) return;
    c.dataset.code = code;
    if (code === '??') c.classList.remove('up');
    else {
      const f = c.querySelector('.front');
      f.innerHTML = faceHTML(code);
      f.classList.toggle('red', 'hd'.includes(code[1]));
      c.classList.add('up');
      if (anim) sfx('flip');
    }
  };
  anim ? apply() : instant(c, apply);
}
function resetCard(c) { instant(c, () => { c.classList.add('hidden'); c.classList.remove('up', 'win', 'dim'); c.dataset.code = ''; }); }

// ---------------------------------------------------------------- chips
function stackEl(amount, maxCols = 4) {
  const el = document.createElement('div');
  el.className = 'stack';
  let rest = amount; const cols = [];
  for (const [v, c, e, d] of DENOMS) {
    let k = Math.floor(rest / v); rest -= k * v;
    while (k > 0) { const n = Math.min(k, 10); cols.push({ n, c, e, d }); k -= n; }
  }
  const use = cols.slice(0, maxCols);
  use.forEach((col, ci) => {
    for (let j = 0; j < col.n; j++) {
      const chip = document.createElement('i');
      chip.className = 'chip';
      chip.style.cssText = `--c:${col.c};--e:${col.e};--d:${col.d};left:${ci * 25 - (use.length - 1) * 12.5}px;bottom:${j * 3.6 + (ci % 2) * 2}px`;
      el.appendChild(chip);
    }
  });
  return el;
}
function wrapStack(amount, cols) { const w = document.createElement('div'); w.style.width = w.style.height = '0'; w.appendChild(stackEl(amount, cols)); return w; }

function setBet(st, amt) {
  if (st.betAmt === amt) return;
  st.betAmt = amt;
  st.bet.querySelector('.stack').replaceWith(stackEl(amt, 3));
  st.bet.querySelector('.amt').textContent = fmt(amt);
  st.bet.classList.toggle('empty', !amt);
}
function setPot(amt) {
  const pot = $('pot');
  if (potAmt !== amt) pot.querySelector('.stack').replaceWith(stackEl(amt, 6));
  tween(pot.querySelector('.amt'), amt, 'Pot ');
  potAmt = amt;
  pot.classList.toggle('empty', !amt);
}
function tween(el, to, prefix = '', dur = 700) {
  const from = el.dataset.v === undefined ? to : +el.dataset.v;
  el.dataset.v = to;
  cancelAnimationFrame(el._raf);
  if (from === to || SPEED < 1) { el.textContent = prefix + fmt(to); return; }
  const t0 = performance.now();
  const step = t => {
    const k = Math.min(1, (t - t0) / dur), e = 1 - Math.pow(1 - k, 3);
    el.textContent = prefix + fmt(Math.round(from + (to - from) * e));
    if (k < 1) el._raf = requestAnimationFrame(step);
  };
  el._raf = requestAnimationFrame(step);
}

// ---------------------------------------------------------------- motion
function fly(node, a, b, o = {}) {
  node.style.left = a.x + 'px'; node.style.top = a.y + 'px';
  fx.appendChild(node);
  const dx = b.x - a.x, dy = b.y - a.y, arc = o.arc || 0;
  const tf = (x, y, r, s) => `translate(-50%,-50%) translate(${x}px,${y}px) rotate(${r}deg) scale(${s})`;
  const r0 = o.r0 || 0, r1 = o.r1 || 0, s0 = o.s0 || 1, s1 = o.s1 || 1;
  const frames = [
    { transform: tf(0, 0, r0, s0), opacity: o.o0 ?? 1 },
    { transform: tf(dx / 2, dy / 2 - arc, (r0 + r1) / 2, Math.max(s0, s1) * (arc ? 1.08 : 1)), opacity: o.o0 ?? 1, offset: .5 },
    { transform: tf(dx, dy, r1, s1), opacity: o.o1 ?? 1 }];
  const anim = node.animate(frames, { duration: (o.dur || 500) * SPEED, delay: (o.delay || 0) * SPEED,
    easing: o.ease || 'cubic-bezier(.25,.75,.3,1)', fill: 'both' });
  return anim.finished.then(() => node.remove(), () => node.remove());
}
function dealTo(slot, delay, from) {
  resetCard(slot);
  instant(slot, () => { slot.dataset.code = '??'; });
  const w = parseFloat(getComputedStyle(slot).getPropertyValue('--w')) || 64;
  sfx('deal', delay * SPEED);
  return fly(makeCard(w), from || center($('deck')), center(slot),
    { dur: 430, delay, r0: -12, r1: parseFloat(slot.dataset.rot || 0), arc: 26 })
    .then(() => instant(slot, () => slot.classList.remove('hidden')));
}
function muck(st) {
  if (st.cards.some(c => !c.classList.contains('hidden'))) sfx('fold');
  st.cards.forEach((c, k) => {
    if (c.classList.contains('hidden')) return;
    const w = parseFloat(getComputedStyle(c).getPropertyValue('--w'));
    const from = center(c);
    resetCard(c);
    fly(makeCard(w), from, { x: 330 + (Math.random() * 40 - 20), y: 350 + (Math.random() * 30 - 15) },
      { dur: 520, delay: k * 60, r0: parseFloat(c.dataset.rot), r1: Math.random() * 160 - 80, s1: .85, o1: 0, arc: 20 });
  });
}
async function betChips(name, to, delay = 0) {
  const st = seats[name];
  if (!st || to <= st.betAmt) return;
  const amt = to - st.betAmt;
  await fly(wrapStack(amt, 3), center(st.plate), center(st.bet), { dur: 480, delay, arc: 36, s0: .8 });
  sfx('chips', 0, Math.min(8, 2 + Math.round(Math.log10(amt + 1) * 1.6)));
  setBet(st, to);
}
async function gather() {
  const list = Object.values(seats).filter(st => st.betAmt > 0);
  if (!list.length) return;
  let total = potAmt;
  sfx('sweep', 300 * SPEED);
  await Promise.all(list.map((st, k) => {
    const amt = st.betAmt, from = center(st.bet);
    total += amt; setBet(st, 0);
    return fly(wrapStack(amt, 3), from, center($('pot')), { dur: 520, delay: k * 70, arc: 18 });
  }));
  setPot(total);
}
function bubble(st, text) {
  const b = st.bubble, kind = text.split(' ')[0].toLowerCase();
  b.className = 'bubble ' + (kind === 'all' ? 'allin' : kind === 'small' || kind === 'big' ? 'blind' : kind);
  b.textContent = text;
  if (kind === 'check') sfx('knock');
  else if (kind === 'all') sfx('allin');
  b.offsetWidth;
  b.classList.add('show');
  clearTimeout(b._t);
  b._t = setTimeout(() => b.classList.remove('show'), 2200);
}
function floater(st, text) {
  const f = document.createElement('div');
  f.className = 'floater'; f.textContent = text;
  const p = center(st.plate);
  fly(f, { x: p.x, y: p.y - 20 }, { x: p.x, y: p.y - 110 }, { dur: 1600, s0: .6, s1: 1.15, o1: 0, ease: 'cubic-bezier(.2,.9,.3,1)' });
}

// ---------------------------------------------------------------- seats
function hue(name) { let h = 0; for (const ch of name) h = (h * 31 + ch.charCodeAt(0)) % 360; return h; }
function makeSeat(p) {
  const el = document.createElement('div');
  el.className = 'seat';
  el.innerHTML = `<div class="hole"></div><div class="hname"></div>
    <div class="plate"><div class="avatar"><div class="ring"></div><div class="av" style="--h:${hue(p.name)}">${esc(p.name.slice(0, 2).toUpperCase())}</div></div>
    <div class="pinfo"><div class="pname">${esc(p.name)}</div><div class="pchips">0</div></div><div class="tag"></div></div>
    <div class="bubble"></div>`;
  const cards = [makeCard(), makeCard()];
  cards.forEach((c, k) => { c.classList.add('hidden'); el.querySelector('.hole').appendChild(c); });
  const bet = document.createElement('div');
  bet.className = 'betspot empty';
  bet.innerHTML = '<div class="stack"></div><div class="amt"></div>';
  $('seats').append(bet, el);
  el.style.opacity = 0;
  requestAnimationFrame(() => requestAnimationFrame(() => el.style.opacity = 1));
  return { el, cards, bet, betAmt: 0, plate: el.querySelector('.plate'), chips: el.querySelector('.pchips'),
    tag: el.querySelector('.tag'), hname: el.querySelector('.hname'), ring: el.querySelector('.ring'),
    bubble: el.querySelector('.bubble') };
}
function layoutSeats(s) {
  const n = s.players.length, mi = Math.max(0, s.players.findIndex(p => p.me));
  const names = new Set(s.players.map(p => p.name));
  for (const name of Object.keys(seats)) {
    if (names.has(name)) continue;
    const st = seats[name]; delete seats[name];
    st.el.style.opacity = 0; st.bet.style.opacity = 0;
    setTimeout(() => { st.el.remove(); st.bet.remove(); }, 600);
  }
  s.players.forEach((p, i) => {
    const st = seats[p.name] || (seats[p.name] = makeSeat(p));
    const a = Math.PI / 2 + ((i - mi + n) % n) * 2 * Math.PI / n;
    st.angle = a;
    st.el.classList.toggle('me', p.me);
    st.el.classList.toggle('upper', Math.sin(a) < -0.25);
    st.el.style.left = CX + Math.cos(a) * RX + 'px';
    st.el.style.top = CY + Math.sin(a) * RY + 'px';
    st.bet.style.left = CX + Math.cos(a) * (BX + 40 * Math.abs(Math.cos(a))) + 'px';
    st.bet.style.top = CY + Math.sin(a) * BY + 'px';
    const spread = p.me ? 26 : 17, tilt = p.me ? 5 : 7;
    st.cards.forEach((c, k) => {
      const dir = k ? 1 : -1;
      c.style.marginLeft = dir * spread + 'px';
      c.style.rotate = dir * tilt + 'deg';
      c.dataset.rot = dir * tilt;
    });
  });
}
function positionDealer(s) {
  const d = s.players.find(p => p.dealer), btn = $('dealerBtn');
  if (!d || !seats[d.name]) { btn.style.opacity = 0; return; }
  const a = seats[d.name].angle, r = .66;
  btn.style.left = CX + Math.cos(a) * RX * r + Math.sin(a) * 88 + 'px';
  btn.style.top = CY + Math.sin(a) * RY * r - Math.cos(a) * 40 + 'px';
  btn.style.opacity = 1;
}
function updateTurn(s) {
  for (const p of s.players) {
    const st = seats[p.name]; if (!st) continue;
    st.el.classList.toggle('turn', p.turn);
    if (p.turn && s.time_left != null) {
      const f = Math.max(0, Math.min(1, s.time_left / s.turn_time));
      st.ring.style.setProperty('--p', f);
      st.ring.style.setProperty('--rc', f > .5 ? '#7ee787' : f > .2 ? '#f2cc60' : '#ff6b6b');
    } else st.ring.style.setProperty('--p', 1);
  }
}

// ---------------------------------------------------------------- board
const boardCards = [];
(function buildTable() {
  for (let i = 0; i < 5; i++) {
    const x = CX + (i - 2) * 76;
    const slot = document.createElement('div');
    slot.className = 'slot'; slot.style.left = x + 'px'; slot.style.top = CY + 'px';
    const c = makeCard(64); c.classList.add('hidden');
    c.style.left = x + 'px'; c.style.top = CY + 'px'; c.dataset.rot = 0;
    $('board').append(slot, c); boardCards.push(c);
  }
  for (let i = 0; i < 4; i++) {
    const c = makeCard(60); c.style.left = -30 - i * .7 + 'px'; c.style.top = -42 - i * 1.4 + 'px';
    c.style.rotate = (i - 2) * 1.5 + 'deg'; $('deck').appendChild(c);
  }
  ['As', 'Kh', 'Qd', 'Jc'].forEach((code, i) => {
    const c = makeCard(80); $('fan').appendChild(c); setCard(c, code, false);
    c.animate([{ transform: 'rotate(0deg) translateY(30px)', opacity: 0 }, { transform: `rotate(${(i - 1.5) * 14}deg)`, opacity: 1 }],
      { duration: 900 * SPEED, delay: (200 + i * 110) * SPEED, easing: 'cubic-bezier(.2,1.3,.4,1)', fill: 'both' });
  });
})();

async function dealBoard(from, board) {
  let k = from;
  while (k < board.length) {
    const group = k === 0 ? [0, 1, 2] : [k];
    await Promise.all(group.map((i, j) => dealTo(boardCards[i], j * 110)));
    for (const [j, i] of group.entries()) { await wait(j ? 110 : 60); setCard(boardCards[i], board[i]); }
    k = group[group.length - 1] + 1;
    await wait(k < board.length ? 900 : 450);
  }
}
async function reveals(s) {
  let any = false;
  for (const p of s.players) {
    const st = seats[p.name]; if (!st || p.folded) continue;
    p.cards.forEach((code, k) => {
      const c = st.cards[k];
      if (code !== '??' && c.dataset.code === '??' && !c.classList.contains('hidden')) {
        setTimeout(() => setCard(c, code), (k * 120) * SPEED); any = true;
      }
    });
  }
  if (any) await wait(700);
}
function showdownMarks(s) {
  const win = new Set(s.win_cards || []);
  const all = [...boardCards, ...Object.values(seats).flatMap(st => st.cards)];
  for (const c of all) {
    const on = win.size && !c.classList.contains('hidden') && c.dataset.code && c.dataset.code !== '??';
    c.classList.toggle('win', !!(on && win.has(c.dataset.code)));
    c.classList.toggle('dim', !!(on && !win.has(c.dataset.code)));
  }
  const names = new Set((s.winners || []).map(w => w.name));
  for (const [name, st] of Object.entries(seats)) st.el.classList.toggle('winner', names.has(name));
  const b = $('banner');
  b.innerHTML = s.results.map(esc).join('<br>');
  b.classList.toggle('show', s.results.length > 0);
}
function clearShowdown() {
  [...boardCards, ...Object.values(seats).flatMap(st => st.cards)].forEach(c => c.classList.remove('win', 'dim'));
  Object.values(seats).forEach(st => st.el.classList.remove('winner'));
  $('banner').classList.remove('show');
}
async function payout(s) {
  await wait(250);
  showdownMarks(s);
  const ws = s.winners || [], from = center($('pot'));
  setPot(0);
  await Promise.all(ws.map((w, k) => {
    const st = seats[w.name]; if (!st) return;
    return fly(wrapStack(w.amount, 5), from, center(st.plate), { dur: 800, delay: 250 + k * 160, arc: 50 })
      .then(() => { sfx('win', 0, w.name === s.me.name); floater(st, '+' + fmt(w.amount)); });
  }));
}

// ---------------------------------------------------------------- state diffing
function syncStatic(s) {
  const over = s.stage === 'hand_over';
  for (const p of s.players) {
    const st = seats[p.name]; if (!st) continue;
    const live = p.in_hand && !p.folded && !p.left;
    st.cards.forEach((c, k) => setCard(c, live ? p.cards[k] : null, false));
    tween(st.chips, p.chips);
    st.el.classList.toggle('folded', !!p.folded);
    st.el.classList.toggle('out', p.left || (!p.in_hand && s.stage !== 'waiting'));
    const tag = p.left ? 'LEFT' : p.all_in && !p.folded ? 'ALL IN' : !p.in_hand && s.stage !== 'waiting' ? (p.chips ? 'NEXT HAND' : 'BUSTED') : '';
    st.tag.textContent = tag;
    st.tag.className = 'tag' + (tag ? ' on' : '') + (tag === 'ALL IN' ? ' allin' : '');
    st.hname.textContent = p.hand_name;
    st.hname.classList.toggle('on', !!(p.me && p.hand_name && live));
    setBet(st, over ? 0 : p.bet);
  }
  boardCards.forEach((c, i) => setCard(c, s.board[i], false));
  setPot(over ? 0 : s.pot - s.players.reduce((a, p) => a + p.bet, 0));
  positionDealer(s);
  if (over) showdownMarks(s); else clearShowdown();
  updateTurn(s);
}

async function newHand(p, s) {
  clearShowdown();
  const visible = [...boardCards, ...Object.values(seats).flatMap(st => st.cards)].filter(c => !c.classList.contains('hidden'));
  visible.forEach(c => c.classList.add('hidden'));
  Object.values(seats).forEach(st => setBet(st, 0));
  setPot(0);
  await wait(visible.length ? 380 : 0);
  visible.forEach(resetCard);
  positionDealer(s);
  sfx('shuffle');
  await wait(450);
  const di = Math.max(0, s.players.findIndex(x => x.dealer));
  const order = [...s.players.slice(di + 1), ...s.players.slice(0, di + 1)].filter(x => x.in_hand);
  const lands = [];
  let i = 0;
  for (const r of [0, 1]) for (const x of order) if (seats[x.name]) lands.push(dealTo(seats[x.name].cards[r], i++ * 130));
  await Promise.all(lands);
  const me = s.players.find(x => x.me);
  if (me && me.in_hand) { me.cards.forEach((code, k) => setTimeout(() => setCard(seats[me.name].cards[k], code), k * 140 * SPEED)); await wait(450); }
  const pm = {}; (p ? p.players : []).forEach(x => pm[x.name] = x);
  showBubbles(pm, s);
  await Promise.all(s.players.filter(x => x.bet > 0).map((x, k) => betChips(x.name, x.bet, k * 140)));
}
function showBubbles(pm, s) {
  for (const x of s.players) {
    const px = pm[x.name];
    if (x.action && (!px || px.action_id !== x.action_id) && seats[x.name]) bubble(seats[x.name], x.action);
  }
}
async function progress(p, s) {
  const pm = {}; p.players.forEach(x => pm[x.name] = x);
  showBubbles(pm, s);
  for (const x of s.players) {
    const px = pm[x.name];
    if (px && !px.folded && x.folded && seats[x.name]) muck(seats[x.name]);
  }
  const over = s.stage === 'hand_over';
  const street = s.board.length !== p.board.length || (over && p.stage !== 'hand_over');
  if (!street) {
    await Promise.all(s.players.map((x, k) => betChips(x.name, x.bet, k * 60)));
    await reveals(s);
    return;
  }
  // chips that closed out the previous street, then sweep everything into the pot
  await Promise.all(s.players.map((x, k) => {
    const px = pm[x.name], st = seats[x.name];
    if (!px || !st) return;
    const extra = (px.chips - x.chips) - (over ? 0 : x.bet);
    return extra > 0 ? betChips(x.name, st.betAmt + extra, k * 60) : null;
  }));
  await wait(150);
  await gather();
  await reveals(s);
  await dealBoard(p.board.length, s.board);
  if (over) await payout(s);
  else await Promise.all(s.players.map((x, k) => betChips(x.name, x.bet, k * 100)));
}

async function apply(p, s) {
  const key = s.players.map(x => x.name).join('|');
  if (key !== seatKey) { layoutSeats(s); seatKey = key; }
  if (!p) return;
  if (s.hand_no !== p.hand_no) await newHand(p, s);
  else await progress(p, s);
}
async function pump() {
  if (busy) return;
  busy = true;
  while (latest && latest !== shown) {
    const s = latest;
    try { await apply(shown, s); } catch (e) { console.error(e); }
    syncStatic(s);
    shown = s;
  }
  busy = false;
}
let revealSeen = null;
try { revealSeen = localStorage.getItem('pokerReveal'); } catch (e) {}
function receive(s) {
  latest = s;
  if (s.reveal && s.reveal.id !== revealSeen) {
    revealSeen = s.reveal.id;
    try { localStorage.setItem('pokerReveal', revealSeen); } catch (e) {}
    setTimeout(() => { $('revealText').textContent = s.reveal.text; $('reveal').classList.add('show'); sfx('gotcha'); },
      (s.stage === 'hand_over' ? 4000 : 300) * SPEED);
  }
  $('join').classList.add('gone');
  $('info').textContent = s.hand_no ? `Hand #${s.hand_no} · Blinds ${s.sb}/${s.bb}` : `Blinds ${s.sb}/${s.bb}`;
  $('log').innerHTML = s.log.map(esc).join('<br>');
  renderControls(s);
  const msg = $('feltMsg');
  msg.style.opacity = s.stage === 'waiting' ? 1 : 0;
  if (s.stage === 'waiting') msg.innerHTML = `<h2>Waiting for players</h2><p>${s.players.length} seated · anyone can start once 2 are in</p>`;
  if (shown) updateTurn(s);
  pump();
}

// ---------------------------------------------------------------- controls
let ctrlKey = '', wasMyTurn = false, lastTick = null;
function renderControls(s) {
  const me = s.me, c = $('controls');
  if (me.my_turn && !wasMyTurn) sfx('turn', 200);
  if (me.my_turn && s.time_left != null && s.time_left <= 10 && s.time_left !== lastTick) sfx('tick');
  wasMyTurn = me.my_turn; lastTick = me.my_turn ? s.time_left : null;
  const key = [s.stage, me.my_turn, me.to_call, me.can_check, me.min_raise_to, me.max_raise_to, me.can_rebuy, s.players.length, s.hand_no,
    s.stage === 'waiting' || me.my_turn ? '' : (s.players.find(p => p.turn) || {}).name].join('|');
  if (key !== ctrlKey) {
    ctrlKey = key;
    let html = '';
    if (me.my_turn) {
      const canRaise = me.max_raise_to > me.current_bet;
      const onlyAllIn = me.min_raise_to >= me.max_raise_to;
      html = `<button class="btn fold" onclick="act('fold')">Fold<kbd>F</kbd></button>
        <button class="btn call" onclick="act('${me.can_check ? 'check' : 'call'}')">${me.can_check ? 'Check' : 'Call ' + fmt(me.to_call)}<kbd>C</kbd></button>`;
      if (canRaise && !onlyAllIn) html += `<div class="raisebox">
          <div class="presets"><button onclick="preset('min')">Min</button><button onclick="preset(.5)">½ Pot</button>
          <button onclick="preset(.75)">¾ Pot</button><button onclick="preset(1)">Pot</button><button onclick="preset('max')">All in</button></div>
          <input type="range" id="raiseAmt" min="${me.min_raise_to}" max="${me.max_raise_to}" step="1" value="${me.min_raise_to}" oninput="slid()">
        </div>
        <button class="btn raise" id="raiseBtn" onclick="act('raise', $('raiseAmt').value)"></button>`;
      else if (canRaise) html += `<button class="btn raise" onclick="act('allin')">All in ${fmt(me.max_raise_to)}</button>`;
    } else if (s.stage === 'waiting') {
      html = `<button class="btn raise" onclick="send('/start')" ${s.players.length < 2 ? 'disabled' : ''}>Deal the cards</button>`;
    } else if (s.stage === 'hand_over') {
      html = `<span class="status">Next hand starting…</span>`;
    } else {
      const t = s.players.find(p => p.turn);
      html = `<span class="status">${t ? 'Waiting for ' + esc(t.name) + '…' : ''}</span>`;
    }
    if (me.can_rebuy) html += `<button class="btn ghost" onclick="send('/rebuy')">Rebuy</button>`;
    c.innerHTML = `<div class="turnbar"><div></div></div><div class="panel">${html}</div>`;
    if ($('raiseAmt')) slid();
    fit();
  }
  const bar = c.querySelector('.turnbar div');
  if (bar) bar.style.width = me.my_turn && s.time_left != null ? (100 * s.time_left / s.turn_time) + '%' : '0%';
}
function slid() {
  const r = $('raiseAmt'), v = +r.value, me = latest.me;
  r.style.setProperty('--fill', (100 * (v - r.min) / Math.max(1, r.max - r.min)) + '%');
  $('raiseBtn').textContent = v >= me.max_raise_to ? `All in ${fmt(v)}` : `${me.current_bet ? 'Raise to' : 'Bet'} ${fmt(v)}`;
}
function preset(k) {
  const me = latest.me, r = $('raiseAmt');
  let v = k === 'min' ? me.min_raise_to : k === 'max' ? me.max_raise_to : me.current_bet + Math.round((latest.pot + me.to_call) * k);
  r.value = Math.max(me.min_raise_to, Math.min(me.max_raise_to, v));
  slid();
}
addEventListener('keydown', e => {
  if (!latest || !latest.me.my_turn || e.target.tagName === 'INPUT' && e.target.type !== 'range') return;
  const k = e.key.toLowerCase();
  if (k === 'f') act('fold');
  else if (k === 'c') act(latest.me.can_check ? 'check' : 'call');
  else if (k === 'r' && $('raiseAmt')) act('raise', $('raiseAmt').value);
});

// ---------------------------------------------------------------- network
async function api(path, body) {
  const r = await fetch(path, { method: 'POST', headers: { 'Content-Type': 'application/json' },
    body: JSON.stringify(Object.assign({ token }, body || {})) });
  const j = await r.json();
  if (!r.ok) throw new Error(j.error || 'error');
  return j;
}
function toast(msg) {
  const t = $('toast'); t.textContent = msg; t.classList.add('show');
  clearTimeout(t._t); t._t = setTimeout(() => t.classList.remove('show'), 2600);
}
async function send(path, body) {
  try { const s = await api(path, body); if (s.stage) receive(s); } catch (e) { toast(e.message); }
}
const act = (action, amount) => send('/action', { action, amount });
async function join() {
  try {
    const j = await api('/join', { name: $('name').value });
    token = j.token;
    try { localStorage.setItem('pokerToken', token); } catch (e) {}
    poll();
  } catch (e) { $('joinErr').textContent = e.message; }
}
$('name').addEventListener('keydown', e => { if (e.key === 'Enter') join(); });
async function leave() {
  if (!confirm('Leave the table? Your chips are lost.')) return;
  try { await api('/leave'); } catch (e) {}
  try { localStorage.removeItem('pokerToken'); } catch (e) {}
  location.reload();
}
function toggleLog() { const l = $('log'); l.classList.toggle('open'); l.scrollTop = l.scrollHeight; }
let polling = false;
async function poll() {
  if (polling || !token) return;
  polling = true;
  while (token) {
    try {
      const r = await fetch('/state?token=' + token);
      if (r.status === 401) {
        token = null; try { localStorage.removeItem('pokerToken'); } catch (e) {}
        $('join').classList.remove('gone'); break;
      }
      receive(await r.json());
    } catch (e) {}
    await new Promise(r => setTimeout(r, 700));
  }
  polling = false;
}
fit();
if (Sound.muted) $('muteBtn').textContent = '🔇 Sound';
if (!Sound.musicOn) $('musicBtn').textContent = '🎵 Music off';
if (token) poll(); else $('name').focus();
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
    ap.add_argument("--prank", metavar="NAME", help="deal NAME the best hand every round until the reveal")
    ap.add_argument("--reveal-after", type=int, default=10, metavar="N",
                    help="with --prank: reveal the rig to everyone after N rigged hands (1-50, default 10)")
    a = ap.parse_args()
    if not 1 <= a.reveal_after <= 50:
        ap.error("--reveal-after must be between 1 and 50")
    GAME = Game(a.chips, a.sb, a.bb, a.turn_time, a.prank, a.reveal_after)
    threading.Thread(target=clock, daemon=True).start()
    threading.Thread(target=console, daemon=True).start()
    try:
        server = ThreadingHTTPServer(("0.0.0.0", a.port), Handler)
    except OSError as e:
        if e.errno in (48, 98, 10048):  # address already in use (macOS, Linux, Windows)
            raise SystemExit(f"Port {a.port} is already in use — probably a poker server that's still running.\n"
                             f"Stop it with Ctrl+C in its terminal, or run:  lsof -ti :{a.port} | xargs kill\n"
                             f"Or pick another port:  python3 poker.py --port {a.port + 1}")
        raise
    print(f"Poker server running. Tell your friends to open:  http://{lan_ip()}:{a.port}")
    print("(You can play too at http://localhost:%d)  Ctrl+C to stop." % a.port)
    if a.prank:
        print(f"🎭 Prank mode: '{a.prank}' gets the best hand every round. Everyone sees the reveal after "
              f"{a.reveal_after} rigged hands, or type 'reveal' here and press Enter to reveal it now.")
    try:
        server.serve_forever()
    except KeyboardInterrupt:
        pass


if __name__ == "__main__":
    main()
