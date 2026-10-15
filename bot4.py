import asyncio
from concurrent.futures import ProcessPoolExecutor
import inspect
import json
import math
import os
import random
import time
import uuid
from collections import defaultdict, Counter

import aiohttp
from aiohttp import web
import requests
import websockets
from treys import Card, Evaluator, Deck

# =====================================================================
# 1. CONFIGURATION & ENVIRONMENT
# =====================================================================
API_KEY = os.getenv("OPEN_POKER_API_KEY", "sO03ApKecoElfE0-GfeMQC7GI4XJ-0qjX_2vGtXXbjQ")
WS_URL = os.getenv("OPEN_POKER_WS_URL", "wss://openpoker.ai/ws")
REST_BASE_URL = os.getenv("OPEN_POKER_REST_URL", "https://openpoker.ai")
PORT = int(os.getenv("PORT", 10000))
RENDER_EXTERNAL_URL = os.getenv("RENDER_EXTERNAL_URL", "")

# 2-CPU Adaptive Timing Config (Target ~5.0s on close decisions, faster on trivial ones)
CPU_WORKERS = int(os.getenv("CPU_WORKERS", "2"))
TARGET_ACTION_TIME = float(os.getenv("TARGET_ACTION_TIME", "4.75"))
MIN_ADAPTIVE_TIME = float(os.getenv("MIN_ADAPTIVE_TIME", "0.60"))
MC_MAX_ITERS = int(os.getenv("MC_MAX_ITERS", "700000"))

# Stack Management & Ratholing (Leave at 5,000, Rejoin with 1,500)
BUY_IN_AMOUNT = int(os.getenv("BUY_IN_AMOUNT", "1500"))
PROFIT_LOCK_STACK = int(os.getenv("PROFIT_LOCK_STACK", "5000"))

FULL_DECK_INTS = Deck.GetFullDeck()
RANK_CHARS = "23456789TJQKA"

# =====================================================================
# 2. 169-HAND PREFLOP LOOKUP TABLE & RANGE CHARTS
# =====================================================================
PREFLOP_169_LOOKUP = {
    "AA": 100, "KK": 98, "QQ": 95, "JJ": 91, "TT": 87, "99": 82, "88": 78,
    "77": 74, "66": 70, "55": 67, "44": 64, "33": 62, "22": 60,
    "AKs": 96, "AQs": 92, "AJs": 88, "ATs": 85, "A9s": 76, "A8s": 74, "A7s": 72,
    "A6s": 70, "A5s": 75, "A4s": 73, "A3s": 71, "A2s": 69,
    "KQs": 89, "KJs": 85, "KTs": 81, "K9s": 73, "K8s": 66, "K7s": 64, "K6s": 62, "K5s": 60,
    "QJs": 83, "QTs": 79, "Q9s": 71, "Q8s": 63,
    "JTs": 82, "J9s": 72, "J8s": 64,
    "T9s": 76, "T8s": 68, "98s": 73, "97s": 64, "87s": 71, "86s": 62,
    "76s": 69, "75s": 60, "65s": 67, "54s": 65,
    "AKo": 93, "AQo": 86, "AJo": 81, "ATo": 75, "A9o": 64, "A8o": 61, "A7o": 58, "A5o": 57,
    "KQo": 82, "KJo": 76, "KTo": 71, "K9o": 60,
    "QJo": 74, "QTo": 68, "JTo": 70, "T9o": 61, "98o": 58,
}

THREE_BET_BLUFFS = {"A5s", "A4s", "A3s", "K9s", "Q9s", "J9s", "T9s", "98s", "87s"}
FOUR_BET_VALUE = {"AA", "KK", "QQ", "AKs", "AKo"}


def cards_to_hand_str(c1: int, c2: int) -> str:
    r1, r2 = Card.get_rank_int(c1), Card.get_rank_int(c2)
    s1, s2 = Card.get_suit_int(c1), Card.get_suit_int(c2)
    if r1 == r2:
        return f"{RANK_CHARS[r1]}{RANK_CHARS[r2]}"
    high, low = (r1, r2) if r1 > r2 else (r2, r1)
    suffix = "s" if s1 == s2 else "o"
    return f"{RANK_CHARS[high]}{RANK_CHARS[low]}{suffix}"


def get_preflop_score(hand_str: str) -> int:
    if hand_str in PREFLOP_169_LOOKUP:
        return PREFLOP_169_LOOKUP[hand_str]
    r1 = RANK_CHARS.index(hand_str[0])
    r2 = RANK_CHARS.index(hand_str[1])
    suited = hand_str.endswith("s")
    gap = r1 - r2
    base = r1 * 3.2 + r2 * 1.4 + (8 if suited else 0) - min(12, max(0, gap - 1) * 3)
    return int(max(10, min(65, base)))


def hand_preflop_tier(hand_str: str) -> int:
    score = get_preflop_score(hand_str)
    if score >= 87:
        return 1
    if score >= 78:
        return 2
    if score >= 67:
        return 3
    if score >= 58:
        return 4
    return 5


def _build_range_tiers():
    all_169 = set()
    for i in range(13):
        all_169.add(f"{RANK_CHARS[i]}{RANK_CHARS[i]}")
        for j in range(i):
            all_169.add(f"{RANK_CHARS[i]}{RANK_CHARS[j]}s")
            all_169.add(f"{RANK_CHARS[i]}{RANK_CHARS[j]}o")
    return {
        t: frozenset(h for h in all_169 if get_preflop_score(h) >= min_sc)
        for t, min_sc in [(1, 87), (2, 78), (3, 67), (4, 58)]
    }


RANGE_TIER = _build_range_tiers()
RANGE_VS_3BET = frozenset(h for h in RANGE_TIER[3] if get_preflop_score(h) >= 81)


# =====================================================================
# 3. BOARD TEXTURE, DRAW DETECTOR & COUNTERFEIT GUARD
# =====================================================================
def analyze_board_and_draws(hole_cards, community_cards, evaluator: Evaluator):
    info = {
        "paired": False,
        "double_paired": False,
        "flushy": False,
        "four_flush": False,
        "connected": False,
        "four_straight": False,
        "dry": True,
        "wet": False,
        "high": False,
        "hero_flush_draw": False,
        "hero_nut_flush_draw": False,
        "hero_oesd": False,
        "hero_gutshot": False,
        "draw_outs": 0,
        "playing_board": False,
        "vulnerable_one_pair": False,
        "rank_class": 9,
    }
    if len(community_cards) < 3 or len(hole_cards) < 2:
        return info

    board_ranks = [Card.get_rank_int(c) for c in community_cards]
    board_suits = [Card.get_suit_int(c) for c in community_cards]
    hole_ranks = [Card.get_rank_int(c) for c in hole_cards]
    hole_suits = [Card.get_suit_int(c) for c in hole_cards]

    rank_counts = Counter(board_ranks)
    info["paired"] = any(v >= 2 for v in rank_counts.values())
    info["double_paired"] = sum(1 for v in rank_counts.values() if v >= 2) >= 2 or any(
        v >= 3 for v in rank_counts.values()
    )

    suit_counts = Counter(board_suits)
    _, max_board_suit = suit_counts.most_common(1)[0]
    info["flushy"] = max_board_suit >= 3
    info["four_flush"] = max_board_suit >= 4
    two_tone = max_board_suit == 2

    unique_b_ranks = sorted(set(board_ranks))
    if 12 in unique_b_ranks:
        unique_b_ranks = [-1] + unique_b_ranks
    max_in_span5 = 1
    for i in range(len(unique_b_ranks)):
        cnt = sum(1 for r in unique_b_ranks if 0 <= r - unique_b_ranks[i] <= 4)
        if cnt > max_in_span5:
            max_in_span5 = cnt

    info["connected"] = max_in_span5 >= 3
    info["four_straight"] = max_in_span5 >= 4
    info["high"] = max(board_ranks) >= 10
    info["wet"] = (
        info["flushy"]
        or info["connected"]
        or (two_tone and max_in_span5 >= 2 and not info["paired"])
    )
    info["dry"] = not info["wet"]

    score = evaluator.evaluate(community_cards, hole_cards)
    rc = evaluator.get_rank_class(score)
    info["rank_class"] = rc

    if len(community_cards) == 5:
        board_only_score = evaluator.evaluate(community_cards, [])
        if score == board_only_score:
            info["playing_board"] = True

    hero_matches_board = sum(1 for r in hole_ranks if r in board_ranks)
    is_pocket_pair = hole_ranks[0] == hole_ranks[1]
    if rc == 8:
        info["vulnerable_one_pair"] = True
    elif rc == 7 and info["paired"] and not is_pocket_pair and hero_matches_board == 1:
        info["vulnerable_one_pair"] = True
    elif rc == 7 and info["double_paired"] and not is_pocket_pair and hero_matches_board == 0:
        info["vulnerable_one_pair"] = True

    if len(community_cards) < 5:
        all_suits = Counter(board_suits + hole_suits)
        suit_id, suit_total = all_suits.most_common(1)[0]
        if suit_total == 4 and (suit_id in hole_suits):
            info["hero_flush_draw"] = True
            for c in hole_cards:
                if Card.get_suit_int(c) == suit_id and Card.get_rank_int(c) >= 11:
                    info["hero_nut_flush_draw"] = True

        all_ranks = set(board_ranks + hole_ranks)
        straight_completing_ranks = 0
        for test_r in range(13):
            if test_r in all_ranks:
                continue
            cand = all_ranks | {test_r}
            if 12 in cand:
                cand = cand | {-1}
            hole_set = set(hole_ranks) | ({-1} if 12 in hole_ranks else set())
            for low in range(-1, 9):
                window = {low, low + 1, low + 2, low + 3, low + 4}
                if window.issubset(cand) and (window & hole_set):
                    straight_completing_ranks += 1
                    break

        if straight_completing_ranks >= 2:
            info["hero_oesd"] = True
        elif straight_completing_ranks == 1:
            info["hero_gutshot"] = True

        outs = 0
        if info["hero_flush_draw"]:
            outs += 9
        if info["hero_oesd"]:
            outs += 6 if info["hero_flush_draw"] else 8
        elif info["hero_gutshot"]:
            outs += 3 if info["hero_flush_draw"] else 4
        info["draw_outs"] = outs

    return info


# =====================================================================
# 4. TRUE ADAPTIVE MONTE CARLO & UCB1 ACTION EV WORKER (2-CPU)
# =====================================================================
_WORKER_EVALUATOR = None


def _init_worker():
    global _WORKER_EVALUATOR
    _WORKER_EVALUATOR = Evaluator()


def _adaptive_mc_worker(args):
    """
    True Adaptive Monte Carlo Worker:
    1. Exact Enumeration on Heads-Up River (and Heads-Up Turn if <= 14,000 states).
    2. Importance-Weighted Rollouts with Dynamic Confidence-Bound (Wald/Hoeffding) Stopping:
       - Checks 99% confidence interval [p - 2.58*SE, p + 2.58*SE] against decision thresholds.
       - Stops early once min_time is met AND confidence interval is completely clear of thresholds.
       - Uses full time_budget when the decision is marginal/close.
    """
    (
        hole_cards,
        community_cards,
        num_opponents,
        allowed_hands,
        postflop_aggression,
        decision_thresholds,
        min_time,
        max_time,
        max_iters,
        seed,
    ) = args

    rng = random.Random(seed)
    evaluator = _WORKER_EVALUATOR or Evaluator()
    t_start = time.perf_counter()

    dead_cards = set(hole_cards) | set(community_cards)
    available = [c for c in FULL_DECK_INTS if c not in dead_cards]
    cards_to_come = 5 - len(community_cards)
    street = len(community_cards)

    # Pre-compute weighted candidate opponent hands (Importance Sampling Table)
    valid_opp_combos = []
    n_avail = len(available)
    for i in range(n_avail):
        c1 = available[i]
        for j in range(i + 1, n_avail):
            c2 = available[j]
            if allowed_hands is None or cards_to_hand_str(c1, c2) in allowed_hands:
                w = 1.0
                if street >= 3 and postflop_aggression >= 1:
                    opp_sc = evaluator.evaluate(community_cards, [c1, c2])
                    opp_rc = evaluator.get_rank_class(opp_sc)
                    if postflop_aggression >= 2:
                        w = 1.0 if opp_rc <= 7 else (0.45 if opp_rc == 8 else 0.15)
                    else:
                        w = 1.0 if opp_rc <= 8 else 0.30
                valid_opp_combos.append((c1, c2, w))

    if not valid_opp_combos:
        for i in range(n_avail):
            for j in range(i + 1, n_avail):
                valid_opp_combos.append((available[i], available[j], 1.0))

    # --- PATH A: EXACT ENUMERATION (River Heads-Up OR Turn Heads-Up) ---
    if num_opponents == 1 and street == 5:
        my_score = evaluator.evaluate(community_cards, hole_cards)
        w_wins = 0.0
        w_total = 0.0
        for c1, c2, w in valid_opp_combos:
            opp_score = evaluator.evaluate(community_cards, [c1, c2])
            w_total += w
            if my_score < opp_score:
                w_wins += w
            elif my_score == opp_score:
                w_wins += 0.5 * w
        return w_wins, w_total, len(valid_opp_combos), True

    if num_opponents == 1 and street == 4 and len(valid_opp_combos) * len(available) <= 22000:
        w_wins = 0.0
        w_total = 0.0
        evals = 0
        for river_card in available:
            sim_board = community_cards + [river_card]
            my_score = evaluator.evaluate(sim_board, hole_cards)
            for c1, c2, w in valid_opp_combos:
                if c1 == river_card or c2 == river_card:
                    continue
                opp_score = evaluator.evaluate(sim_board, [c1, c2])
                w_total += w
                if my_score < opp_score:
                    w_wins += w
                elif my_score == opp_score:
                    w_wins += 0.5 * w
                evals += 1
        return w_wins, w_total, evals, True

    # --- PATH B: ADAPTIVE MONTE CARLO WITH CONFIDENCE-INTERVAL STOPPING ---
    w_wins = 0.0
    w_total = 0.0
    iterations = 0
    n_combos = len(valid_opp_combos)
    early_stopped = False

    while iterations < max_iters:
        now = time.perf_counter()
        elapsed = now - t_start
        if elapsed >= max_time:
            break

        # Adaptive Stopping Check every 512 rollouts once minimum time has passed
        if iterations >= 1500 and elapsed >= min_time and w_total > 0:
            p_hat = w_wins / w_total
            # 99% Wald/Hoeffding confidence radius (z = 2.576)
            se = math.sqrt(max(0.0001, p_hat * (1.0 - p_hat)) / iterations)
            ci_radius = 2.576 * se + (0.008 / math.sqrt(CPU_WORKERS))
            # Check if ALL critical decision boundaries lie outside [p_hat - ci_radius, p_hat + ci_radius]
            is_ambiguous = any(abs(p_hat - th) <= ci_radius for th in decision_thresholds)
            if not is_ambiguous and ci_radius < 0.018:
                early_stopped = True
                break

        batch = min(256, max_iters - iterations)
        for _ in range(batch):
            opp_hands = []
            used = set()
            sample_w = 1.0
            skip = False
            for opp_idx in range(num_opponents):
                found = None
                for _try in range(8):
                    c1, c2, w = valid_opp_combos[rng.randrange(n_combos)]
                    if c1 not in used and c2 not in used:
                        found = [c1, c2]
                        used.add(c1)
                        used.add(c2)
                        if opp_idx == 0:
                            sample_w = w
                        break
                if not found:
                    skip = True
                    break
                opp_hands.append(found)
            if skip:
                continue

            if cards_to_come > 0:
                rem_deck = [c for c in available if c not in used]
                if len(rem_deck) < cards_to_come:
                    continue
                extra = rng.sample(rem_deck, cards_to_come)
                sim_board = community_cards + extra
            else:
                sim_board = community_cards

            my_score = evaluator.evaluate(sim_board, hole_cards)
            best_opp_score = 7463
            for oh in opp_hands:
                sc = evaluator.evaluate(sim_board, oh)
                if sc < best_opp_score:
                    best_opp_score = sc

            w_total += sample_w
            if my_score < best_opp_score:
                w_wins += sample_w
            elif my_score == best_opp_score:
                w_wins += 0.5 * sample_w
            iterations += 1

    return w_wins, w_total, iterations, early_stopped


# =====================================================================
# 5. LIVE OPPONENT TRACKER (HUD)
# =====================================================================
class OpponentTracker:
    def __init__(self):
        self.stats = defaultdict(
            lambda: {
                "hands": 0,
                "vpip": 0,
                "pfr": 0,
                "postflop_aggressive": 0,
                "postflop_passive": 0,
                "folds_to_bet": 0,
                "faced_bet": 0,
            }
        )
        self.hand_vpip_flagged = set()
        self.hand_pfr_flagged = set()

    def start_new_hand(self, players):
        self.hand_vpip_flagged.clear()
        self.hand_pfr_flagged.clear()
        for p in players:
            pid = p.get("id") or p.get("player_id") or p.get("name") or str(p.get("seat"))
            if pid:
                self.stats[pid]["hands"] += 1

    def record_action(self, pid: str, action: str, is_preflop: bool, facing_bet: bool = False):
        if not pid:
            return
        s = self.stats[pid]
        if is_preflop:
            if action in ("call", "raise", "bet", "all_in") and pid not in self.hand_vpip_flagged:
                s["vpip"] += 1
                self.hand_vpip_flagged.add(pid)
            if action in ("raise", "bet", "all_in") and pid not in self.hand_pfr_flagged:
                s["pfr"] += 1
                self.hand_pfr_flagged.add(pid)
        else:
            if facing_bet:
                s["faced_bet"] += 1
                if action == "fold":
                    s["folds_to_bet"] += 1
            if action in ("raise", "bet", "all_in"):
                s["postflop_aggressive"] += 1
            elif action in ("call", "check"):
                s["postflop_passive"] += 1

    def get_vpip(self, pid: str) -> float:
        s = self.stats.get(pid)
        if not s or s["hands"] < 6:
            return 0.30
        return max(0.10, min(0.85, s["vpip"] / s["hands"]))

    def get_aggression_factor(self, pid: str) -> float:
        s = self.stats.get(pid)
        if not s or (s["postflop_aggressive"] + s["postflop_passive"]) < 4:
            return 1.1
        return (s["postflop_aggressive"] + 1.0) / (s["postflop_passive"] + 1.0)

    def get_fold_to_bet(self, pid: str) -> float:
        s = self.stats.get(pid)
        if not s or s["faced_bet"] < 4:
            return 0.42
        return max(0.15, min(0.80, s["folds_to_bet"] / s["faced_bet"]))


# =====================================================================
# 6. ADAPTIVE POKER ENGINE V4.1 (ADAPTIVE MC + EV BANDIT + LOSS SHIELD)
# =====================================================================
def empty_line_plan(hand_id=None):
    return {
        "hand_id": hand_id,
        "line": "none",
        "streets_bet": 0,
        "flop_checked": False,
        "chips_invested": 0,
    }


class PokerEngineV4Adaptive:
    def __init__(self, tracker: OpponentTracker, pool: ProcessPoolExecutor):
        self.evaluator = Evaluator()
        self.tracker = tracker
        self.pool = pool

    def compute_adaptive_budget(self, street: int, pot: int, to_call: int, big_blind: int):
        """
        Allocates time budget based on street complexity and pot stakes.
        Close/high-stakes postflop spots get the full ~4.75s budget;
        trivial preflop spots can early-stop once confidence bounds converge.
        """
        pot_bb = (pot + to_call) / max(1, big_blind)
        if street == 0 and to_call <= big_blind:
            return MIN_ADAPTIVE_TIME, 2.2  # Unopened preflop: fast convergence
        if street == 0:
            return 1.2, TARGET_ACTION_TIME
        if pot_bb >= 12 or to_call >= big_blind * 4:
            return 3.2, TARGET_ACTION_TIME  # Big pot / facing bet: force deep 4.75s search
        return 2.0, TARGET_ACTION_TIME

    async def estimate_equity_adaptive(
        self,
        hole_cards,
        community_cards,
        num_opponents: int,
        allowed_hands,
        postflop_aggression: int,
        decision_thresholds: list,
        min_time: float,
        max_time: float,
    ):
        if len(hole_cards) < 2:
            return 0.0, 0, False

        num_opponents = max(1, min(5, num_opponents))
        per_worker_iters = max(1000, MC_MAX_ITERS // CPU_WORKERS)
        loop = asyncio.get_running_loop()

        tasks = []
        base_seed = random.randrange(1_000_000_000)
        for w_idx in range(CPU_WORKERS):
            args = (
                hole_cards,
                community_cards,
                num_opponents,
                allowed_hands,
                postflop_aggression,
                decision_thresholds,
                min_time,
                max_time,
                per_worker_iters,
                base_seed + w_idx * 9973,
            )
            tasks.append(loop.run_in_executor(self.pool, _adaptive_mc_worker, args))

        results = await asyncio.gather(*tasks)
        total_wins = sum(r[0] for r in results)
        total_weight = sum(r[1] for r in results)
        total_iters = sum(r[2] for r in results)
        early_stopped = all(r[3] for r in results)

        equity = (total_wins / total_weight) if total_weight > 0 else 0.5
        return equity, total_iters, early_stopped

    def select_best_bet_size_ev(
        self,
        pot: int,
        to_call: int,
        min_raise: int,
        max_raise: int,
        adj_equity: float,
        opp_fold_freq: float,
        active_opponents: int,
        wet_board: bool,
    ):
        """
        Adaptive Action EV Calculator:
        Evaluates candidate bet/raise sizes (35%, 55%, 80%, 110% pot) by modeling:
        - Fold Equity (p_fold * pot)
        - Called Equity (1 - p_fold) * (eq_when_called * new_pot - bet_cost)
        Returns (best_size, best_ev).
        """
        candidates = []
        for frac in (0.35, 0.55, 0.80, 1.15):
            raw_size = int(to_call + (pot + to_call) * frac)
            clamped = max(min_raise, min(raw_size, max_raise))
            if clamped not in candidates:
                candidates.append(clamped)

        best_size = candidates[0]
        best_ev = -1e9

        for size in candidates:
            risk = size
            size_ratio = (size - to_call) / max(1, pot + to_call)
            # Multi-opponent fold probability decays exponentially with active opponents
            single_fold_p = min(0.75, opp_fold_freq * (0.75 + 0.45 * min(1.5, size_ratio)))
            if wet_board:
                single_fold_p *= 0.85
            p_all_fold = single_fold_p ** max(1, active_opponents)

            # When an opponent calls a larger bet, their range narrows -> our equity drops slightly
            eq_when_called = max(0.05, adj_equity - 0.06 * min(1.2, size_ratio))
            called_pot = pot + size + (size - to_call)
            ev_fold = p_all_fold * pot
            ev_called = (1.0 - p_all_fold) * (eq_when_called * called_pot - risk)
            total_ev = ev_fold + ev_called

            if total_ev > best_ev:
                best_ev = total_ev
                best_size = size

        return best_size, best_ev

    def format_valid_action(self, desired_action: str, desired_amount: int, valid_actions_list):
        actions_map = {a["action"]: a for a in valid_actions_list}
        to_call = actions_map.get("call", {}).get("amount", 0)

        if desired_action == "raise":
            if "raise" in actions_map:
                r_info = actions_map["raise"]
                r_min = r_info.get("min", r_info.get("amount", max(20, to_call * 2)))
                r_max = r_info.get("max", r_min)
                clamped = max(r_min, min(int(desired_amount), r_max))
                return "raise", clamped
            elif "bet" in actions_map:
                b_info = actions_map["bet"]
                b_min = b_info.get("min", b_info.get("amount", 20))
                b_max = b_info.get("max", b_min)
                clamped = max(b_min, min(int(desired_amount), b_max))
                return "bet", clamped
            elif "call" in actions_map:
                return "call", to_call
            elif "check" in actions_map:
                return "check", 0

        if desired_action == "call":
            if "call" in actions_map:
                return "call", to_call
            if "check" in actions_map:
                return "check", 0

        if desired_action == "check":
            if "check" in actions_map:
                return "check", 0
            if to_call == 0 and "call" in actions_map:
                return "call", 0
            return ("fold", 0) if "fold" in actions_map else ("check", 0)

        if to_call == 0 and "check" in actions_map:
            return "check", 0
        if "fold" in actions_map:
            return "fold", 0
        first = valid_actions_list[0]
        return first["action"], first.get("amount", first.get("min", 0)) or 0

    async def decide(self, state: dict):
        hole_cards = state["hole_cards"]
        community_cards = state["community_cards"]
        pot = state["pot"]
        valid_actions = state["valid_actions"]
        position = state["position"]
        big_blind = state.get("big_blind", 20)
        active_opponents = state.get("active_opponents", 1)
        opp_max_tier = state.get("opp_max_tier", 3)
        opp_af = state.get("opp_af", 1.1)
        opp_fold_freq = state.get("opp_fold_freq", 0.42)
        profit_lock_active = state.get("profit_lock_active", False)
        plan = state.get("line_plan") or empty_line_plan()
        state["line_plan"] = plan

        actions_map = {a["action"]: a for a in valid_actions}
        to_call = actions_map.get("call", {}).get("amount", 0)
        raise_info = actions_map.get("raise") or actions_map.get("bet") or {}
        min_raise = raise_info.get("min", big_blind * 2)
        max_raise = raise_info.get("max", state.get("stack", BUY_IN_AMOUNT))
        effective_stack = max(state.get("stack", BUY_IN_AMOUNT), max_raise, to_call)

        if len(hole_cards) < 2:
            return self.format_valid_action("check", 0, valid_actions), 0.0, 0, False

        hand_str = cards_to_hand_str(hole_cards[0], hole_cards[1])
        pf_score = get_preflop_score(hand_str)
        tier = hand_preflop_tier(hand_str)
        in_position = position in ("BTN", "CO")
        pot_odds = to_call / (pot + to_call) if (pot + to_call) > 0 else 0.0
        street = len(community_cards)
        board_info = analyze_board_and_draws(hole_cards, community_cards, self.evaluator)

        postflop_agg = 0
        if street >= 3 and to_call > 0:
            postflop_agg = 2 if (to_call >= pot * 0.55 or to_call >= big_blind * 8) else 1

        if street == 0 and to_call > big_blind * 4.5:
            allowed_hands = RANGE_VS_3BET
        elif street >= 3 and postflop_agg >= 2:
            allowed_hands = RANGE_TIER[max(1, min(2, opp_max_tier))]
        else:
            allowed_hands = RANGE_TIER.get(max(1, min(4, opp_max_tier)), RANGE_TIER[3])

        # Compute critical decision thresholds so Adaptive MC knows when to early-stop vs deep-search
        req_call_threshold = min(0.90, pot_odds + (0.03 if in_position else 0.06))
        value_bet_threshold = 0.58 if in_position else 0.63
        jam_threshold = 0.76
        decision_thresholds = [req_call_threshold, value_bet_threshold, jam_threshold]

        min_t, max_t = self.compute_adaptive_budget(street, pot, to_call, big_blind)

        # 1. RUN 2-CPU ADAPTIVE MONTE CARLO / EXACT ENUMERATION
        equity, rollouts, early_stopped = await self.estimate_equity_adaptive(
            hole_cards=hole_cards,
            community_cards=community_cards,
            num_opponents=active_opponents,
            allowed_hands=allowed_hands,
            postflop_aggression=postflop_agg,
            decision_thresholds=decision_thresholds,
            min_time=min_t,
            max_time=max_t,
        )

        draw_bonus = 0.0
        if street == 3 and board_info["draw_outs"] >= 8:
            draw_bonus = 0.03 if board_info["hero_nut_flush_draw"] else 0.015
        adj_equity = min(0.99, max(0.0, equity + draw_bonus))

        if board_info["playing_board"] and to_call > 0:
            adj_equity = min(adj_equity, 0.15)

        def finish(desired_action, desired_amount=0):
            a, amt = self.format_valid_action(desired_action, desired_amount, valid_actions)
            if a in ("call", "raise", "bet", "all_in"):
                plan["chips_invested"] = plan.get("chips_invested", 0) + (
                    amt if a != "call" else to_call
                )
            if street >= 3:
                if a in ("raise", "bet", "all_in"):
                    plan["streets_bet"] = plan.get("streets_bet", 0) + 1
                    plan["line"] = "value" if adj_equity >= 0.64 else "draw"
                elif a == "check" and street == 3:
                    plan["flop_checked"] = True
            state["line_plan"] = plan
            return (a, amt), adj_equity, rollouts, early_stopped

        # PROFIT-LOCK GUARD (When stack >= 5,000 mid-hand, protect the 5k stack!)
        if profit_lock_active and to_call > 0:
            if street == 0 and hand_str not in ("AA", "KK"):
                return finish("fold", 0)
            if street >= 3 and (board_info["rank_class"] > 5 or adj_equity < 0.82):
                return finish("fold", 0)

        # 2. PRE-FLOP STRATEGY
        if street == 0:
            stack_bb = effective_stack / big_blind if big_blind > 0 else 75
            is_unopened = to_call <= big_blind

            if stack_bb <= 12:
                if pf_score >= 78 or (pf_score >= 70 and position in ("BTN", "SB", "CO")):
                    return finish("raise", max_raise)
                return finish("check" if to_call == 0 else "fold", 0)

            if is_unopened:
                open_size = int(big_blind * 2.5) if position != "SB" else int(big_blind * 3.0)
                if position == "UTG" and pf_score >= 78:
                    return finish("raise", open_size)
                if position == "MP" and pf_score >= 74:
                    return finish("raise", open_size)
                if position == "CO" and pf_score >= 66:
                    return finish("raise", open_size)
                if position in ("BTN", "SB") and pf_score >= 58:
                    return finish("raise", open_size)
                if position == "BB":
                    if pf_score >= 82:
                        return finish("raise", int(big_blind * 3.0))
                    return finish("check" if to_call == 0 else "call", to_call)
                if position == "SB" and to_call <= big_blind // 2 and pf_score >= 54:
                    return finish("call", to_call)
                return finish("check" if to_call == 0 else "fold", 0)

            if to_call > big_blind * 9:
                if hand_str in ("AA", "KK"):
                    return finish("raise", max_raise)
                if hand_str in ("QQ", "AKs") and to_call <= effective_stack * 0.45:
                    return finish("call", to_call)
                return finish("fold", 0)

            if to_call > big_blind * 4.5:
                if hand_str in FOUR_BET_VALUE:
                    return finish("raise", int(to_call * 2.3))
                if pf_score >= 85 and (in_position or to_call <= effective_stack * 0.18):
                    return finish("call", to_call)
                return finish("fold", 0)

            three_bet_size = int(to_call * (3.0 if in_position else 3.5))
            if tier == 1:
                return finish("raise", three_bet_size)
            if pf_score >= 85 and in_position and active_opponents <= 2:
                return finish("raise", three_bet_size)
            if (
                hand_str in THREE_BET_BLUFFS
                and position in ("BTN", "CO")
                and active_opponents == 1
                and random.random() < 0.15
            ):
                return finish("raise", three_bet_size)

            min_call_score = 64 if position == "BB" else (70 if in_position else 77)
            if pf_score >= min_call_score and adj_equity >= (pot_odds + 0.03):
                return finish("call", to_call)
            if hand_str[0] == hand_str[1] and effective_stack >= to_call * 12:
                return finish("call", to_call)

            return finish("fold", 0)

        # 3. POST-FLOP STRATEGY (With Adaptive Action EV Sizing + One-Pair Shield)
        spr = effective_stack / max(1, pot)
        rc = board_info["rank_class"]
        is_monster = rc <= 5 and not board_info["playing_board"]
        is_trips_or_two_pair = (
            rc in (6, 7)
            and not board_info["vulnerable_one_pair"]
            and not board_info["playing_board"]
        )
        danger_board = (board_info["four_flush"] and rc > 4) or (
            board_info["four_straight"] and rc > 5
        )

        # --- CASE A: Checked to Hero (to_call == 0) ---
        if to_call == 0:
            if danger_board and not is_monster:
                return finish("check", 0)

            if is_monster or (is_trips_or_two_pair and adj_equity >= 0.68):
                best_sz, _ = self.select_best_bet_size_ev(
                    pot, 0, min_raise, max_raise, adj_equity, opp_fold_freq, active_opponents, board_info["wet"]
                )
                return finish("raise", best_sz)

            if adj_equity >= value_bet_threshold:
                if street == 5 and board_info["vulnerable_one_pair"] and board_info["wet"]:
                    return finish("check", 0)
                best_sz, best_ev = self.select_best_bet_size_ev(
                    pot, 0, min_raise, max_raise, adj_equity, opp_fold_freq, active_opponents, board_info["wet"]
                )
                if best_ev > adj_equity * pot:
                    return finish("raise", best_sz)
                return finish("raise", int(max(min_raise, pot * 0.42)))

            if (
                street < 5
                and active_opponents == 1
                and board_info["draw_outs"] >= 8
                and (in_position or plan.get("streets_bet", 0) == 0)
            ):
                return finish("raise", int(max(min_raise, pot * 0.45)))

            if (
                street == 3
                and active_opponents == 1
                and in_position
                and board_info["dry"]
                and adj_equity >= 0.36
                and opp_fold_freq >= 0.38
            ):
                return finish("raise", int(max(min_raise, pot * 0.33)))

            return finish("check", 0)

        # --- CASE B: Facing a Bet or Raise (to_call > 0) ---
        if board_info["playing_board"]:
            return finish("fold", 0)
        if danger_board and not is_monster and to_call > pot * 0.25:
            return finish("fold", 0)

        # LOSS PREVENTION: One-Pair Stack-Off Shield
        if board_info["vulnerable_one_pair"] or rc >= 8:
            max_one_pair_call = BUY_IN_AMOUNT * (0.35 if opp_af > 2.2 else 0.22)
            if street >= 4 and to_call > max_one_pair_call and adj_equity < 0.76:
                return finish("fold", 0)
            if street == 5 and to_call > pot * 0.65 and adj_equity < 0.68 and opp_af < 1.8:
                return finish("fold", 0)

        street_margin = 0.03 if street == 3 else (0.05 if street == 4 else 0.07)
        if board_info["wet"]:
            street_margin += 0.02
        pos_margin = 0.0 if in_position else 0.03
        nit_margin = 0.04 if (opp_af < 0.9 and to_call > pot * 0.5) else 0.0
        required_equity = pot_odds + street_margin + pos_margin + nit_margin

        if (is_monster and adj_equity >= 0.76) or (is_trips_or_two_pair and adj_equity >= 0.80):
            raise_target = max_raise if spr <= 2.2 else int(pot + to_call * 2.4)
            return finish("raise", raise_target)

        if adj_equity >= required_equity:
            return finish("call", to_call)

        if street < 5 and board_info["draw_outs"] >= 8:
            implied_discount = 0.06 if (in_position and spr >= 3.5) else 0.03
            if adj_equity >= (pot_odds - implied_discount) and to_call <= pot * 0.65:
                return finish("call", to_call)

        return finish("fold", 0)


# =====================================================================
# 7. WEBSOCKET CLIENT WITH 5K RATHOLING & RESYNC
# =====================================================================
class OpenPokerClientV4:
    def __init__(self, api_key: str, ws_url: str, pool: ProcessPoolExecutor):
        self.api_key = api_key
        self.ws_url = ws_url
        self.tracker = OpponentTracker()
        self.engine = PokerEngineV4Adaptive(self.tracker, pool)

        self.bot_name = None
        self.my_player_id = None
        self.my_seat = None
        self.my_stack = BUY_IN_AMOUNT
        self.pending_rathole = False

        self.hole_cards = []
        self.community_cards = []
        self.dealer_seat = 0
        self.table_id = None
        self.last_table_seq = 0
        self.players = []
        self.folded_seats = set()
        self.last_aggressor_id = None
        self.current_street_bet = False
        self.line_plan = empty_line_plan()

        self.hands_played = 0
        self.hands_won = 0
        self.ratholes_completed = 0
        self.last_action_summary = "Waiting for first hand..."
        self.connected = False
        self.boot_time = time.time()

    def check_active_game(self):
        headers = {"Authorization": f"Bearer {self.api_key}"}
        try:
            resp = requests.get(f"{REST_BASE_URL}/api/me/active-game", headers=headers, timeout=5)
            if resp.status_code == 200:
                return resp.json()
        except Exception as e:
            print(f"[REST] Active-game check skipped: {e}")
        return None

    def update_hero_info_from_players(self, players):
        if not players:
            return
        self.players = players
        for p in players:
            pid = p.get("id") or p.get("player_id")
            pname = p.get("name")
            pseat = p.get("seat")
            if (
                (self.my_seat is not None and pseat == self.my_seat)
                or (self.my_player_id and pid == self.my_player_id)
                or (self.bot_name and pname == self.bot_name)
            ):
                if pseat is not None:
                    self.my_seat = pseat
                if pid:
                    self.my_player_id = pid
                stack_val = p.get("stack", p.get("chips"))
                if stack_val is not None:
                    self.my_stack = int(stack_val)
                    if self.my_stack >= PROFIT_LOCK_STACK:
                        self.pending_rathole = True
                break

    async def execute_rathole_leave_and_rejoin(self, ws):
        print(
            f"[Profit-Lock] Stack reached {self.my_stack} (>= {PROFIT_LOCK_STACK})! "
            f"Leaving table to lock profit and rejoining with {BUY_IN_AMOUNT}..."
        )
        self.pending_rathole = False
        self.ratholes_completed += 1
        await ws.send(json.dumps({"type": "leave_table"}))
        await asyncio.sleep(1.5)
        self.my_stack = BUY_IN_AMOUNT
        self.table_id = None
        await ws.send(json.dumps({"type": "join_lobby", "buy_in": BUY_IN_AMOUNT}))

    def get_my_position(self, my_seat, players) -> str:
        if not players or my_seat is None:
            return "MP"
        active_seats = sorted(
            [p["seat"] for p in players if "seat" in p and p.get("stack", p.get("chips", 1)) > 0]
        )
        if my_seat not in active_seats:
            active_seats = sorted([p["seat"] for p in players if "seat" in p])
        if my_seat not in active_seats or not active_seats:
            return "MP"

        dealer_idx = 0
        for i, s in enumerate(active_seats):
            if s <= (self.dealer_seat or 0):
                dealer_idx = i
        rotated = active_seats[dealer_idx:] + active_seats[:dealer_idx]
        rel = rotated.index(my_seat)
        n = len(active_seats)
        if n == 2:
            return "BTN" if rel == 0 else "BB"
        if rel == 0:
            return "BTN"
        if rel == 1:
            return "SB"
        if rel == 2:
            return "BB"
        if rel == n - 1:
            return "CO"
        if rel == 3 and n >= 5:
            return "UTG"
        return "MP"

    async def handle_your_turn(self, ws, msg: dict):
        turn_token = msg.get("turn_token")
        if not turn_token:
            return

        hand_id = msg.get("hand_id")
        pot = msg.get("pot", 0)
        valid_actions = msg.get("valid_actions", [])
        if not valid_actions:
            return

        if "seat" in msg and msg["seat"] is not None:
            self.my_seat = msg["seat"]
        if "players" in msg and msg["players"]:
            self.update_hero_info_from_players(msg["players"])
        if "community_cards" in msg and msg["community_cards"] is not None:
            self.community_cards = [Card.new(c) for c in msg["community_cards"]]
        if "hole_cards" in msg and msg["hole_cards"]:
            self.hole_cards = [Card.new(c) for c in msg["hole_cards"]]
        if "dealer_seat" in msg or "button_seat" in msg:
            self.dealer_seat = msg.get("dealer_seat", msg.get("button_seat", self.dealer_seat))

        for va in valid_actions:
            if va.get("action") in ("raise", "bet") and va.get("max"):
                self.my_stack = max(self.my_stack, int(va["max"]))
                if self.my_stack >= PROFIT_LOCK_STACK:
                    self.pending_rathole = True

        position = self.get_my_position(self.my_seat, self.players)

        if self.line_plan.get("hand_id") != hand_id:
            self.line_plan = empty_line_plan(hand_id)

        total_players = len(self.players) if self.players else 6
        active_opponents = max(1, total_players - len(self.folded_seats) - 1)

        opp_vpip = self.tracker.get_vpip(self.last_aggressor_id) if self.last_aggressor_id else 0.30
        opp_af = (
            self.tracker.get_aggression_factor(self.last_aggressor_id)
            if self.last_aggressor_id
            else 1.1
        )
        opp_fold_freq = (
            self.tracker.get_fold_to_bet(self.last_aggressor_id)
            if self.last_aggressor_id
            else 0.42
        )
        if opp_vpip < 0.19:
            opp_max_tier = 2
        elif opp_vpip < 0.33:
            opp_max_tier = 3
        else:
            opp_max_tier = 4

        state = {
            "hole_cards": self.hole_cards,
            "community_cards": self.community_cards,
            "pot": pot,
            "valid_actions": valid_actions,
            "position": position,
            "big_blind": msg.get("big_blind", 20),
            "stack": self.my_stack,
            "active_opponents": active_opponents,
            "opp_max_tier": opp_max_tier,
            "opp_af": opp_af,
            "opp_fold_freq": opp_fold_freq,
            "profit_lock_active": self.pending_rathole,
            "line_plan": self.line_plan,
        }

        t0 = time.perf_counter()
        (action, amount), equity, rollouts, early_stopped = await self.engine.decide(state)
        self.line_plan = state.get("line_plan", self.line_plan)
        elapsed = time.perf_counter() - t0

        payload = {
            "type": "action",
            "hand_id": hand_id,
            "client_action_id": str(uuid.uuid4()),
            "turn_token": turn_token,
            "action": action,
        }
        if action in ("raise", "bet", "call") and amount and amount > 0:
            payload["amount"] = int(amount)

        await ws.send(json.dumps(payload))

        hc_str = " ".join([Card.int_to_str(c) for c in self.hole_cards]) if self.hole_cards else "??"
        bd_str = (
            " ".join([Card.int_to_str(c) for c in self.community_cards])
            if self.community_cards
            else "Preflop"
        )
        mode_tag = "CONV-EARLY" if early_stopped else "FULL-DEEP"
        win_rate_pct = (self.hands_won / self.hands_played * 100) if self.hands_played else 0.0
        self.last_action_summary = (
            f"[{position} | Stack: {self.my_stack} | WR: {win_rate_pct:.1f}%] "
            f"Cards: {hc_str} | Board: {bd_str} | "
            f"Eq: {equity*100:.1f}% ({rollouts:,} sims [{mode_tag}] in {elapsed:.2f}s) "
            f"-> {action.upper()} {amount}"
        )
        print(self.last_action_summary)

    async def run_forever(self):
        headers = {"Authorization": f"Bearer {self.api_key}"}
        header_kwarg = (
            "additional_headers"
            if "additional_headers" in inspect.signature(websockets.connect).parameters
            else "extra_headers"
        )
        backoff = 2

        while True:
            try:
                active = await asyncio.to_thread(self.check_active_game)
                print(f"[Client] Connecting to {self.ws_url}...")

                async with websockets.connect(
                    self.ws_url,
                    ping_interval=20,
                    ping_timeout=20,
                    **{header_kwarg: headers},
                ) as ws:
                    self.connected = True
                    backoff = 2
                    print("[WebSocket] Connected to OpenPoker.")

                    await ws.send(json.dumps({"type": "set_auto_rebuy", "enabled": True}))

                    if active and active.get("playing") and active.get("table_id"):
                        self.table_id = active["table_id"]
                        print(f"[Resync] Resuming active table {self.table_id}...")
                        await ws.send(
                            json.dumps(
                                {
                                    "type": "resync_request",
                                    "table_id": self.table_id,
                                    "last_table_seq": self.last_table_seq,
                                }
                            )
                        )
                    else:
                        await ws.send(json.dumps({"type": "join_lobby", "buy_in": BUY_IN_AMOUNT}))

                    async for raw_message in ws:
                        msg = json.loads(raw_message)
                        msg_type = msg.get("type")

                        if "table_seq" in msg:
                            self.last_table_seq = max(self.last_table_seq, msg["table_seq"])
                        if "table_id" in msg:
                            self.table_id = msg["table_id"]

                        if msg_type == "connected":
                            self.bot_name = msg.get("name")
                            self.my_player_id = msg.get("player_id") or msg.get("id")
                            print(f"[Server] Authenticated as: {self.bot_name or 'Bot'}")

                        elif msg_type == "error":
                            code = msg.get("code")
                            print(f"[Server Error] {code}: {msg.get('message')}")
                            if code == "already_seated":
                                if self.pending_rathole:
                                    await self.execute_rathole_leave_and_rejoin(ws)
                                elif msg.get("table_id"):
                                    self.table_id = msg["table_id"]
                                    await ws.send(
                                        json.dumps(
                                            {
                                                "type": "resync_request",
                                                "table_id": self.table_id,
                                                "last_table_seq": 0,
                                            }
                                        )
                                    )
                            elif code == "insufficient_season_chips":
                                print("[Bankroll] Low season chips. Triggering rebuy...")
                                await ws.send(json.dumps({"type": "rebuy", "amount": 0}))
                                await asyncio.sleep(2)
                                await ws.send(json.dumps({"type": "join_lobby", "buy_in": 1000}))

                        elif msg_type in ("hand_start", "new_hand"):
                            self.hands_played += 1
                            self.hole_cards = []
                            self.community_cards = []
                            self.folded_seats.clear()
                            self.last_aggressor_id = None
                            self.current_street_bet = False
                            self.line_plan = empty_line_plan(msg.get("hand_id"))
                            if "seat" in msg or "your_seat" in msg:
                                self.my_seat = msg.get("seat", msg.get("your_seat", self.my_seat))
                            self.dealer_seat = msg.get(
                                "dealer_seat", msg.get("button_seat", msg.get("dealer", 0))
                            )
                            if "players" in msg:
                                self.update_hero_info_from_players(msg["players"])
                            self.tracker.start_new_hand(self.players)

                        elif msg_type == "hole_cards":
                            self.hole_cards = [Card.new(c) for c in msg.get("cards", [])]

                        elif msg_type == "community_cards":
                            self.community_cards = [Card.new(c) for c in msg.get("cards", [])]
                            self.current_street_bet = False

                        elif msg_type == "player_action":
                            seat = msg.get("seat")
                            act = msg.get("action")
                            pid = msg.get("player_id") or msg.get("name") or str(seat)
                            is_pf = len(self.community_cards) == 0
                            if act == "fold" and seat is not None:
                                self.folded_seats.add(seat)
                            self.tracker.record_action(
                                pid=pid,
                                action=act,
                                is_preflop=is_pf,
                                facing_bet=self.current_street_bet,
                            )
                            if act in ("raise", "bet", "all_in"):
                                self.last_aggressor_id = pid
                                self.current_street_bet = True

                        elif msg_type in ("hand_result", "hand_end", "hand_complete"):
                            winners = msg.get("winners", [])
                            for w in winners:
                                w_seat = w.get("seat")
                                w_name = w.get("name") or w.get("player_id")
                                if (self.my_seat is not None and w_seat == self.my_seat) or (
                                    self.bot_name and w_name == self.bot_name
                                ):
                                    self.hands_won += 1
                                    if "new_stack" in w or "stack" in w:
                                        self.my_stack = int(w.get("new_stack", w.get("stack")))
                                    elif "amount" in w:
                                        self.my_stack += int(w["amount"])

                            if "players" in msg:
                                self.update_hero_info_from_players(msg["players"])

                            if self.my_stack >= PROFIT_LOCK_STACK or self.pending_rathole:
                                await self.execute_rathole_leave_and_rejoin(ws)

                        elif msg_type == "resync_response":
                            snap = msg.get("snapshot", {})
                            if snap.get("community_cards"):
                                self.community_cards = [
                                    Card.new(c) for c in snap["community_cards"]
                                ]
                            if snap.get("players"):
                                self.update_hero_info_from_players(snap["players"])
                            hero = snap.get("hero", {})
                            if hero.get("seat") is not None:
                                self.my_seat = hero["seat"]
                            if hero.get("stack") is not None:
                                self.my_stack = int(hero["stack"])
                                if self.my_stack >= PROFIT_LOCK_STACK:
                                    self.pending_rathole = True
                            if hero.get("hole_cards"):
                                self.hole_cards = [Card.new(c) for c in hero["hole_cards"]]
                            if hero.get("turn_token") and hero.get("valid_actions"):
                                turn_msg = {
                                    "turn_token": hero["turn_token"],
                                    "valid_actions": hero["valid_actions"],
                                    "hand_id": snap.get("hand_id"),
                                    "pot": snap.get("pot", 0),
                                    "seat": hero.get("seat"),
                                    "players": snap.get("players", []),
                                }
                                await self.handle_your_turn(ws, turn_msg)

                        elif msg_type == "your_turn":
                            await self.handle_your_turn(ws, msg)

                        elif msg_type == "action_rejected":
                            print(
                                f"[Warning] Action rejected: {msg.get('reason')} "
                                f"({msg.get('attempted_action')})"
                            )

                        elif msg_type == "auto_rebuy_scheduled":
                            wait_sec = msg.get("cooldown_seconds", 300)
                            print(f"[Rebuy] Cooldown active. Waiting {wait_sec}s...")
                            await asyncio.sleep(wait_sec + 2)
                            self.my_stack = BUY_IN_AMOUNT
                            await ws.send(
                                json.dumps({"type": "join_lobby", "buy_in": BUY_IN_AMOUNT})
                            )

                        elif msg_type == "rebuy_success":
                            print(f"[Rebuy] Chips credited! Joining with {BUY_IN_AMOUNT}...")
                            self.my_stack = BUY_IN_AMOUNT
                            await ws.send(
                                json.dumps({"type": "join_lobby", "buy_in": BUY_IN_AMOUNT})
                            )

                        elif msg_type == "busted":
                            print(f"[Table] Busted! Rejoining in 3s with {BUY_IN_AMOUNT}...")
                            self.pending_rathole = False
                            self.my_stack = BUY_IN_AMOUNT
                            await asyncio.sleep(3)
                            await ws.send(
                                json.dumps({"type": "join_lobby", "buy_in": BUY_IN_AMOUNT})
                            )

            except Exception as e:
                self.connected = False
                jitter = random.uniform(0.5, 2.0)
                wait_time = min(60, backoff + jitter)
                print(f"[Disconnected] {e}. Reconnecting in {wait_time:.1f}s...")
                await asyncio.sleep(wait_time)
                backoff = min(60, backoff * 2)


# =====================================================================
# 8. RENDER KEEP-ALIVE WEB SERVER & MAIN ENTRYPOINT
# =====================================================================
async def start_render_server(bot: OpenPokerClientV4):
    app = web.Application()

    async def health_handler(request):
        uptime_min = int((time.time() - bot.boot_time) / 60)
        win_rate = (bot.hands_won / bot.hands_played * 100) if bot.hands_played else 0.0
        status = {
            "version": "v4.1-adaptive-2cpu",
            "status": "online" if bot.connected else "reconnecting",
            "uptime_minutes": uptime_min,
            "current_stack": bot.my_stack,
            "profit_lock_target": PROFIT_LOCK_STACK,
            "ratholes_completed": bot.ratholes_completed,
            "hands_played": bot.hands_played,
            "hands_won": bot.hands_won,
            "win_rate_pct": round(win_rate, 2),
            "last_decision": bot.last_action_summary,
            "tracked_opponents": len(bot.tracker.stats),
        }
        return web.json_response(status)

    app.router.add_get("/", health_handler)
    app.router.add_get("/health", health_handler)

    runner = web.AppRunner(app)
    await runner.setup()
    site = web.TCPSite(runner, "0.0.0.0", PORT)
    await site.start()
    print(f"[Server] Health dashboard listening on http://0.0.0.0:{PORT}")


async def self_ping_loop():
    await asyncio.sleep(15)
    target_url = (
        f"{RENDER_EXTERNAL_URL.rstrip('/')}/health"
        if RENDER_EXTERNAL_URL
        else f"http://127.0.0.1:{PORT}/health"
    )
    async with aiohttp.ClientSession() as session:
        while True:
            try:
                async with session.get(target_url, timeout=10) as resp:
                    print(f"[Keep-Alive] Pinged {target_url} -> HTTP {resp.status}")
            except Exception as e:
                print(f"[Keep-Alive] Ping warning: {e}")
            await asyncio.sleep(600)


async def main():
    pool = ProcessPoolExecutor(max_workers=CPU_WORKERS, initializer=_init_worker)
    bot = OpenPokerClientV4(api_key=API_KEY, ws_url=WS_URL, pool=pool)
    await start_render_server(bot)
    try:
        await asyncio.gather(
            bot.run_forever(),
            self_ping_loop(),
        )
    finally:
        pool.shutdown(wait=False, cancel_futures=True)


if __name__ == "__main__":
    try:
        asyncio.run(main())
    except KeyboardInterrupt:
        print("\n[Shutdown] Bot v4.1 stopped.")
