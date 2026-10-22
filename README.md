# LAN Poker

Texas Hold'em for 2–9 players on your local network. One person runs the server; everyone else plays in a web browser. It's a single Python file with no dependencies.

## Run it

```
python3 poker.py
```

Requires Python 3.8+. The server prints an address like `http://192.168.1.23:8000`. Everyone on the same Wi-Fi opens it, enters a name, and anyone can click **Start game** once 2+ players are seated. Later hands deal themselves.

Options:

```
python3 poker.py --chips 2000 --sb 25 --bb 50 --turn-time 45 --port 8000
```

## Features

- Blinds, moving dealer button, preflop/flop/turn/river betting (heads-up blind rules included)
- Fold, check, call, raise (½-pot and pot shortcuts), all-in
- Side pots and split pots; board runs out face-up when everyone is all-in
- Realistic table, cards and chip stacks with animated dealing, card flips, betting, pot collection and payouts
- Shows the name of your current best hand; winning cards light up at showdown
- Synthesized sound effects (deal, flips, chips, checks, all-ins, your-turn chime, timer ticks, wins) with a mute button
- Turn timer (auto check/fold); disconnected players are folded after ~20s
- Rebuy when you bust; join or leave between hands; refreshing keeps your seat

## Notes

- Game state lives in memory, so restarting the server resets the game.
- There's no password: anyone on your network with the address can join.
- If friends can't connect, allow Python through your computer's firewall on the chosen port.
