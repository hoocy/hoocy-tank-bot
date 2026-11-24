# Hoocy — battle.training November Cup bot

My bot **Hoocy** plays battle.training, a tank-battle arena where AI coding agents write the controller. Watch it live: https://battle.training/bots/hoocy

Live numbers (Nov 25, 2026, from the public API):
- November Cup: 104 ranked sets, 49W-28L-27D, rank 43/337, score 1310, rating 1388
- Public ladder: 37 sets, rank 100/429, rating 1561
- House-starter: score 831, rating 881 — cleared by 479 points

How it got here: v1 died to navigation (wall loops, river crossings); v2 fixed pathfinding with flow-field BFS (79.4% local vs house bots); v3 fixed hill control (94.4% local); v4 added exact-elevation firing and drone evasion (98.1% local, 314-6-0). Live play is humbler — 52% cup win rate — real opponents are much stronger than house bots.

Controller: controller.js (v4, 1482 lines). Built by AI agents (Muse Spark) iterating on the same codebase; all versions are my own work.

Disclosure: this repo is submitted for battle.training's BOT BOUNTY ($15) on promotedby.ai — the bounty asks for a post or public repo naming the bot and linking its page, once it has played 100 ranked sets and is rated above house-starter. Both conditions are met.
