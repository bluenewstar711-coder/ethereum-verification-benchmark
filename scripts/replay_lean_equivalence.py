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
import statistics
import subprocess
import sys
import tempfile
import threading
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


FALLBACK = -1


class WarmWorker:
    """`lake env warm-lean` in one workspace; restarted after a timeout or crash."""

    def __init__(self, workspace: Path, binary: Path, timeout: int):
        self.workspace, self.binary, self.timeout = workspace, binary, timeout
        self.proc: subprocess.Popen | None = None

    def _start(self) -> None:
        self.proc = subprocess.Popen(["lake", "env", str(self.binary)], cwd=self.workspace, stdin=subprocess.PIPE,
                                     stdout=subprocess.PIPE, stderr=subprocess.DEVNULL, text=True, start_new_session=True)

    def close(self) -> None:
        if self.proc and self.proc.poll() is None:
            os.killpg(self.proc.pid, 9)
        self.proc = None

    def check(self, rel: str) -> tuple[int, str, float]:
        if self.proc is None or self.proc.poll() is not None:
            self._start()
        with tempfile.NamedTemporaryFile(prefix="warm-out-", delete=False) as fh:
            out_path = fh.name
        t0 = time.time()
        reply: list[str] = []
        reader = threading.Thread(target=lambda: reply.append(self.proc.stdout.readline()))
        self.proc.stdin.write(f"{out_path}\t{rel}\n")
        self.proc.stdin.flush()
        reader.start()
        reader.join(self.timeout)
        elapsed = time.time() - t0
        out = Path(out_path).read_text("utf-8", "replace") if Path(out_path).exists() else ""
        os.unlink(out_path)
        if reader.is_alive() or not reply or not reply[0]:
            timed_out = reader.is_alive()
            exit_code = self.proc.wait() if not timed_out else None
            self.close()
            if timed_out:
                return 124, out + "\ntimeout", elapsed
            # Lean's message reporter calls `IO.Process.exit 1` once `maxErrors` is hit; the
            # `lean` binary stops at exactly the same point, so this output is the result.
            if exit_code == 1 and "from option `maxErrors`) reached, exiting" in out:
                return 1, out, elapsed
            return FALLBACK, out, elapsed
        status = reply[0].split()
        if status[0] != "ok":
            return FALLBACK, out, elapsed
        return int(status[1]), out, elapsed


def sample_runs(bench: Path, n_runs: int, seed: int, since: str) -> list[tuple[Path, str]]:
    """Whole agent loops: every attempt of a run in order, then its final submission."""
    runs = []
    for run_dir in sorted((bench / "results" / "runs").iterdir()):
        if run_dir.name[:8] < since or not (run_dir / "run.json").is_file() or not (run_dir / "attempts").is_dir():
            continue
        attempts = sorted((run_dir / "attempts").glob("*-check_proof.lean"),
                          key=lambda p: int(p.name.rsplit("-fair-", 1)[1].split("-")[0]))
        if len(attempts) >= 2:
            runs.append((run_dir, attempts))
    random.Random(seed).shuffle(runs)
    picked = []
    for run_dir, attempts in runs[:n_runs]:
        task_ref = json.loads((run_dir / "run.json").read_text())["task_ref"]
        picked += [(a, task_ref) for a in attempts]
        final = sorted((run_dir / "submitted").rglob("*.lean"))[:1] if (run_dir / "submitted").is_dir() else []
        picked += [(f, task_ref) for f in final]
    return picked


def sample_attempts(bench: Path, n: int, seed: int, since: str) -> list[tuple[Path, str]]:
    """Half intermediate attempts (mostly failing), half final submissions of solved runs."""
    attempts, solved = [], []
    for run_dir in sorted((bench / "results" / "runs").iterdir()):
        if run_dir.name[:8] < since or not (run_dir / "run.json").is_file():
            continue
        run = json.loads((run_dir / "run.json").read_text())
        task_ref = run.get("task_ref")
        if not task_ref:
            continue
        if (run_dir / "attempts").is_dir():
            attempts += [(a, task_ref) for a in sorted((run_dir / "attempts").glob("*-check_proof.lean"))]
        targets = (run.get("classification") or {}).get("targets") or []
        if targets and targets[0].get("final_class") == "SOLVED" and (run_dir / "submitted").is_dir():
            solved += [(f, task_ref) for f in sorted((run_dir / "submitted").rglob("*.lean"))[:1]]
    rng = random.Random(seed)
    rng.shuffle(attempts)
    rng.shuffle(solved)
    picked = solved[: n // 2] + attempts[: n - min(n // 2, len(solved))]
    rng.shuffle(picked)
    return picked


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--bench-root", type=Path, default=DEFAULT_BENCH)
    ap.add_argument("--candidate", default="lake", choices=["lake", "warm"])
    ap.add_argument("--warm-bin", type=Path, default=Path(__file__).resolve().parent.parent / "tools/warm_lean/.lake/build/bin/warm-lean")
    ap.add_argument("--n", type=int, default=40)
    ap.add_argument("--runs", type=int, default=0, help="replay N whole runs in order instead of --n random attempts")
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
    attempts = (sample_runs(args.bench_root, args.runs, args.seed, args.since) if args.runs
                else sample_attempts(args.bench_root, args.n, args.seed, args.since))
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

    by_task: dict[str, list[tuple[int, Path]]] = {}
    for idx, (attempt, task_ref) in enumerate(attempts):
        by_task.setdefault(task_ref, []).append((idx, attempt))

    def task_lane(task_ref: str) -> list[dict]:
        # One workspace and (for `warm`) one long-lived worker per task, fed the task's
        # attempts one after another in the same file: this is the agent loop, so any
        # state leaking between requests shows up as a diff.
        base, rel = workspace_for(task_ref)
        ws = args.out / "scratch" / task_ref.replace("/", "__")
        if ws.exists():
            shutil.rmtree(ws)
        shutil.copytree(base, ws, symlinks=True)
        worker = WarmWorker(ws, args.warm_bin, args.timeout) if args.candidate == "warm" else None
        rows = []
        try:
            for idx, attempt in by_task[task_ref]:
                shutil.copy2(attempt, ws / rel)
                a_code, a_out, a_t = run(["lake", "env", "lean", rel], ws, args.timeout)
                if worker:
                    b_code, b_out, b_t = worker.check(rel)
                else:
                    b_code, b_out, b_t = run(["lake", "env", "lean", rel], ws, args.timeout)
                row = {
                    "attempt": str(attempt.relative_to(args.bench_root)), "task_ref": task_ref,
                    "a_code": a_code, "b_code": b_code, "a_seconds": round(a_t, 1), "b_seconds": round(b_t, 1),
                    "a_sha": hashlib.sha256(a_out.encode()).hexdigest(), "b_sha": hashlib.sha256(b_out.encode()).hexdigest(),
                    "timeout": 124 in (a_code, b_code),
                    # A full disk or other host failure is not a property of the backend.
                    "infra": any("no space left" in o.lower() for o in (a_out, b_out)),
                    "fallback": b_code == FALLBACK,
                }
                row["identical"] = row["a_code"] == row["b_code"] and row["a_sha"] == row["b_sha"]
                if not row["identical"] and not row["timeout"] and not row["infra"]:
                    (args.out / "diffs").mkdir(exist_ok=True)
                    (args.out / "diffs" / f"{idx:05d}.a.txt").write_text(a_out)
                    (args.out / "diffs" / f"{idx:05d}.b.txt").write_text(b_out)
                with lock, (args.out / "rows.jsonl").open("a") as fh:
                    fh.write(json.dumps(row) + "\n")
                print(f"[{idx}] {task_ref} a={a_code}/{a_t:.0f}s b={b_code}/{b_t:.1f}s identical={row['identical']}", flush=True)
                rows.append(row)
        finally:
            if worker:
                worker.close()
            shutil.rmtree(ws, ignore_errors=True)
        return rows

    lock = threading.Lock()
    with ThreadPoolExecutor(args.jobs) as ex:
        rows = [r for lane in ex.map(task_lane, list(by_task)) for r in lane]
    compared = [r for r in rows if not r["timeout"] and not r["infra"]]
    summary = {
        "candidate": args.candidate, "attempts": len(rows),
        "timeouts": sum(r["timeout"] for r in rows), "infra": sum(r["infra"] and not r["timeout"] for r in rows),
        "reference_passed": sum(r["a_code"] == 0 for r in compared),
        "identical": sum(r["identical"] for r in compared), "compared": len(compared),
        "verdict_agree": sum((r["a_code"] == 0) == (r["b_code"] == 0) for r in compared),
        "fallbacks": sum(r["fallback"] for r in rows),
        "median_a_seconds": statistics.median([r["a_seconds"] for r in compared]) if compared else None,
        "median_b_seconds": statistics.median([r["b_seconds"] for r in compared]) if compared else None,
    }
    (args.out / "summary.json").write_text(json.dumps(summary, indent=2) + "\n")
    print(json.dumps(summary))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
