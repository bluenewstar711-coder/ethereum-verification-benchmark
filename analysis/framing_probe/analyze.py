#!/usr/bin/env python3
"""Summarise framing-probe runs into summary.json and REPORT.md."""
from __future__ import annotations

import json
import statistics as st
from collections import Counter, defaultdict
from pathlib import Path

DIR = Path(__file__).resolve().parent
RUNS = sorted((DIR / "runs").glob("*.json"))


def med(xs):
    xs = [x for x in xs if x is not None]
    return round(st.median(xs), 3) if xs else None


def run_stats(r: dict) -> dict:
    task_reqs = [q for q in r["requests"] if q["phase"] == "task"]
    # Output speed: completion tokens per second of request latency.
    tps = [q["usage"]["completion_tokens"] / q["latency_s"] for q in task_reqs
           if q.get("usage") and q["latency_s"] > 0 and q["usage"].get("completion_tokens", 0) >= 50]
    # Prompt-cache continuity: from the second request on, the cached prefix should cover
    # (most of) the previous prompt. A different backend model cannot read this cache.
    breaks, eligible = 0, 0
    reqs = r["requests"]
    for prev, cur in zip(reqs, reqs[1:]):
        pu, cu = prev.get("usage") or {}, cur.get("usage") or {}
        if not pu or not cu:
            continue
        eligible += 1
        cached = (cu.get("prompt_tokens_details") or {}).get("cached_tokens") or 0
        if cached < 0.5 * pu.get("prompt_tokens", 0):
            breaks += 1
    # Tokenizer proxy: characters of appended non-assistant messages per appended prompt token.
    msgs = r["messages"]
    asst_idx = [i for i, m in enumerate(msgs) if m["role"] == "assistant"]
    cpt = []
    for k in range(len(asst_idx) - 1):
        if k + 1 >= len(task_reqs):
            break
        a, b = asst_idx[k], asst_idx[k + 1]
        added_chars = sum(len(m.get("content") or "") for m in msgs[a + 1 : b] if m["role"] != "assistant")
        u0, u1 = task_reqs[k].get("usage") or {}, task_reqs[k + 1].get("usage") or {}
        added_tokens = u1.get("prompt_tokens", 0) - u0.get("prompt_tokens", 0) - u0.get("completion_tokens", 0)
        if added_chars >= 400 and added_tokens > 0:
            cpt.append(added_chars / added_tokens)
    calib = r.get("calibration") or {}
    return {
        "tok_per_s": med(tps), "cache_breaks": breaks, "cache_eligible": eligible,
        "chars_per_token": med(cpt), "calib_score": calib.get("score"),
        "self_reported": (calib.get("parsed") or {}).get("model"),
        "returned_models": sorted({q.get("returned_model") or "?" for q in r["requests"]}),
        "completion_tokens": sum((q.get("usage") or {}).get("completion_tokens", 0) for q in task_reqs),
        "refusal_finish": sum(1 for q in r["requests"] if q.get("finish_reason") in ("refusal", "content_filter") or q.get("refusal")),
    }


def main() -> None:
    rows = [json.loads(p.read_text()) for p in RUNS]
    groups: dict[tuple[str, str], list] = defaultdict(list)
    per_run = []
    for r in rows:
        s = run_stats(r)
        per_run.append({k: r[k] for k in ("model", "arm", "task_ref", "status", "outcome_target", "expected_target", "correct", "n_checks", "n_turns", "wall_s")} | s)
        groups[(r["model"], r["arm"])].append((r, s))
    summary = []
    for (model, arm), items in sorted(groups.items()):
        rs = [r for r, _ in items]
        ss = [s for _, s in items]
        summary.append({
            "model": model, "arm": arm, "runs": len(rs),
            "correct": sum(r["correct"] for r in rs),
            "statuses": dict(Counter(r["status"].split(":")[0] for r in rs)),
            "wrong_direction_claims": sum(1 for r in rs if r["outcome_target"] and not r["correct"]),
            "refusal_finishes": sum(s["refusal_finish"] for s in ss),
            "median_checks": med([r["n_checks"] for r in rs]),
            "median_turns": med([r["n_turns"] for r in rs]),
            "completion_tokens": sum(s["completion_tokens"] for s in ss),
            "median_tok_per_s": med([s["tok_per_s"] for s in ss]),
            "median_chars_per_token": med([s["chars_per_token"] for s in ss]),
            "cache_breaks": f"{sum(s['cache_breaks'] for s in ss)}/{sum(s['cache_eligible'] for s in ss)}",
            "calibration_mean": med([s["calib_score"] for s in ss]) if ss else None,
            "calibration_scores": [s["calib_score"] for s in ss],
            "returned_models": sorted({m for s in ss for m in s["returned_models"]}),
            "self_reported_models": dict(Counter(str(s["self_reported"]) for s in ss)),
        })
    (DIR / "summary.json").write_text(json.dumps({"groups": summary, "runs": per_run}, indent=1) + "\n")
    lines = ["| Model | Arm | Correct | Statuses | Refusals | Median checks | Completion tok | tok/s | chars/token | Cache breaks | Quiz | Returned model | Self-reported |",
             "|---|---|---:|---|---:|---:|---:|---:|---:|---:|---|---|---|"]
    for g in summary:
        lines.append(
            f"| {g['model']} | {g['arm']} | {g['correct']}/{g['runs']} | {g['statuses']} | {g['refusal_finishes']} | "
            f"{g['median_checks']} | {g['completion_tokens']} | {g['median_tok_per_s']} | {g['median_chars_per_token']} | "
            f"{g['cache_breaks']} | {g['calibration_scores']} | {', '.join(g['returned_models'])} | {g['self_reported_models']} |")
    (DIR / "summary_table.md").write_text("\n".join(lines) + "\n")
    print("\n".join(lines))


if __name__ == "__main__":
    main()
