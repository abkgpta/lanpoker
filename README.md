# LAN Poker

Texas Hold'em for 2–9 players on your local network. One person runs the server; everyone else plays in a web browser. It's a single Python file with no dependencies.

## Run it

```
python3 poker.py
```

Requires Python 3.8+. The server prints an address like `http://192.168.1.23:8000`. Everyone on the same Wi-Fi opens it, enters a name and how many chips to buy in for, and anyone can click **Start game** once 2+ players are seated. Later hands deal themselves.

Options (`--chips` is the suggested buy-in; the allowed range defaults to 10 big blinds up to 10x `--chips`):

```
python3 poker.py --chips 2000 --min-buyin 500 --max-buyin 5000 --sb 25 --bb 50 --turn-time 45 --port 8000
```

## Features

- Blinds, moving dealer button, preflop/flop/turn/river betting (heads-up blind rules included)
- Fold, check, call, raise (½-pot and pot shortcuts), all-in
- Keyboard: type a raise amount with the number keys and press Enter to raise; F folds, C checks/calls
- Side pots and split pots; board runs out face-up when everyone is all-in
- Realistic table, cards and chip stacks with animated dealing, card flips, betting, pot collection and payouts
- Shows the name of your current best hand; winning cards light up at showdown
- Synthesized sound effects (deal, flips, chips, checks, all-ins, your-turn chime, timer ticks, wins) with a mute button
- Background music: a quiet, endless lounge-jazz trio generated in the browser, with its own on/off button
- Turn timer (auto check/fold); disconnected players are folded after ~20s
- Choose your own buy-in when you sit down and when you buy back in after busting; join or leave between hands; refreshing keeps your seat

## Prank mode

Prank mode is on by default: whenever a player called `abk` (case-insensitive) is at the table, they're dealt the best hand every round. Hands without abk are dealt normally. After 10 rigged hands, every player sees a "Gotcha!" screen saying the deck was rigged, and the game is fair from then on. To reveal it early, type `reveal` in the server's terminal and press Enter.

```
python3 poker.py --reveal-after 5     # reveal after 5 rigged hands instead (1-50)
python3 poker.py --prank someone      # rig it for a different name
python3 poker.py --no-prank           # completely fair game
```

## Notes

- Game state lives in memory, so restarting the server resets the game.
- There's no password: anyone on your network with the address can join.
- If friends can't connect, allow Python through your computer's firewall on the chosen port.
