#!/usr/bin/env python3
"""Replay archived proof attempts through two Lean check backends and compare them.

No model is called. Each archived attempt (results/runs/*/attempts/*-check_proof.lean)
is copied into a workspace for its task and checked twice:

  backend A (reference): the in-task command the harness runs today,
                         ``lake env lean <editable>``
  backend B (candidate): selected with --candidate; ``lake`` (the same command
                         again) measures the reference's own nondeterminism

Two results are equivalent when the exit code and the full output bytes match.
Timeouts (exit 124) on either side are reported separately: they depend on load,
not on the backend.
"""
from __future__ import annotations

import argparse
import hashlib
import json
import os
import random
import shutil
import subprocess
import sys
import time
from concurrent.futures import ThreadPoolExecutor
from pathlib import Path

DEFAULT_BENCH = Path("/var/lib/sandboxed-node/4f2d1609-558c-4b71-805a-af5dae112f5d/ethereum-verification-benchmark")
FAST_RUNNER_DIR = Path("/var/lib/sandboxed-node/4f2d1609-558c-4b71-805a-af5dae112f5d/.gemini/antigravity-cli/brain/a2664f62-92f7-48f4-a506-ae80c95dca3a/scratch")


def run(cmd: list[str], cwd: Path, timeout: int) -> tuple[int, str, float]:
    t0 = time.time()
    proc = subprocess.Popen(cmd, cwd=cwd, stdout=subprocess.PIPE, stderr=subprocess.PIPE, start_new_session=True)
    try:
        out, err = proc.communicate(timeout=timeout)
        code = proc.returncode
    except subprocess.TimeoutExpired:
        os.killpg(proc.pid, 9)
        out, err = proc.communicate()
        code = 124
    return code, (out + err).decode("utf-8", "replace"), time.time() - t0


def sample_attempts(bench: Path, n: int, seed: int, since: str) -> list[tuple[Path, str]]:
    rows = []
    for run_dir in sorted((bench / "results" / "runs").iterdir()):
        if run_dir.name[:8] < since or not (run_dir / "run.json").is_file():
            continue
        attempts = sorted((run_dir / "attempts").glob("*-check_proof.lean")) if (run_dir / "attempts").is_dir() else []
        if not attempts:
            continue
        task_ref = json.loads((run_dir / "run.json").read_text()).get("task_ref")
        if task_ref:
            rows += [(a, task_ref) for a in attempts]
    random.Random(seed).shuffle(rows)
    return rows[:n]


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--bench-root", type=Path, default=DEFAULT_BENCH)
    ap.add_argument("--candidate", default="lake", choices=["lake"])
    ap.add_argument("--n", type=int, default=40)
    ap.add_argument("--seed", type=int, default=7)
    ap.add_argument("--since", default="20261009", help="only runs whose id starts at or after this date")
    ap.add_argument("--timeout", type=int, default=240)
    ap.add_argument("--jobs", type=int, default=2)
    ap.add_argument("--out", type=Path, required=True)
    args = ap.parse_args()

    os.environ.setdefault("FAST_SKIP_DEP_WARM", "1")
    sys.path.insert(0, str(args.bench_root))
    sys.path.insert(0, str(FAST_RUNNER_DIR))
    import run_task_fast  # noqa: F401  (patches workspace setup to reuse the prebuilt .lake)
    from harness.manifests import filter_group_to_task, group_id_from_task_ref, load_group
    from harness.workspace_builder import build_group_workspace

    args.out.mkdir(parents=True, exist_ok=True)
    ws_root = args.out / "workspaces"
    attempts = sample_attempts(args.bench_root, args.n, args.seed, args.since)
    workspaces: dict[str, tuple[Path, str]] = {}

    def workspace_for(task_ref: str) -> tuple[Path, str]:
        if task_ref not in workspaces:
            group = filter_group_to_task(load_group(group_id_from_task_ref(task_ref), "all"), task_ref)
            ws = ws_root / task_ref.replace("/", "__")
            if not ws.is_dir():
                build_group_workspace(group, workspace_dir=ws, run_id="replay")
            workspaces[task_ref] = (ws, group.tasks[0].editable_files[0])
        return workspaces[task_ref]

    # Build workspaces serially: build_group_workspace is not meant to race on one path.
    for _, task_ref in attempts:
        workspace_for(task_ref)

    def one(item: tuple[int, tuple[Path, str]]) -> dict:
        idx, (attempt, task_ref) = item
        base, rel = workspace_for(task_ref)
        ws = args.out / "scratch" / f"{idx:05d}"
        if ws.exists():
            shutil.rmtree(ws)
        shutil.copytree(base, ws, symlinks=True)
        shutil.copy2(attempt, ws / rel)
        a_code, a_out, a_t = run(["lake", "env", "lean", rel], ws, args.timeout)
        b_code, b_out, b_t = run(["lake", "env", "lean", rel], ws, args.timeout)
        shutil.rmtree(ws, ignore_errors=True)
        row = {
            "attempt": str(attempt.relative_to(args.bench_root)), "task_ref": task_ref,
            "a_code": a_code, "b_code": b_code, "a_seconds": round(a_t, 1), "b_seconds": round(b_t, 1),
            "a_sha": hashlib.sha256(a_out.encode()).hexdigest(), "b_sha": hashlib.sha256(b_out.encode()).hexdigest(),
            "timeout": 124 in (a_code, b_code),
        }
        row["identical"] = row["a_code"] == row["b_code"] and row["a_sha"] == row["b_sha"]
        if not row["identical"] and not row["timeout"]:
            (args.out / "diffs").mkdir(exist_ok=True)
            (args.out / "diffs" / f"{idx:05d}.a.txt").write_text(a_out)
            (args.out / "diffs" / f"{idx:05d}.b.txt").write_text(b_out)
        with (args.out / "rows.jsonl").open("a") as fh:
            fh.write(json.dumps(row) + "\n")
        print(f"[{idx}] {task_ref} a={a_code}/{a_t:.0f}s b={b_code}/{b_t:.0f}s identical={row['identical']}", flush=True)
        return row

    with ThreadPoolExecutor(args.jobs) as ex:
        rows = list(ex.map(one, enumerate(attempts)))
    compared = [r for r in rows if not r["timeout"]]
    summary = {
        "candidate": args.candidate, "attempts": len(rows), "timeouts": len(rows) - len(compared),
        "identical": sum(r["identical"] for r in compared), "compared": len(compared),
        "verdict_agree": sum((r["a_code"] == 0) == (r["b_code"] == 0) for r in compared),
    }
    (args.out / "summary.json").write_text(json.dumps(summary, indent=2) + "\n")
    print(json.dumps(summary))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
