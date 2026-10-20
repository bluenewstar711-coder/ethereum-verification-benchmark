#!/usr/bin/env python3
"""Fit effort-scaling curves for the v0.3 STRAT-50 budget cascade and test whether
all models share one curve shape that differs only by scale.

Data: output/budget_scaling_v03_strat50/<model>/cascade_results.json, one row per
(profile, task) run. For each model and task we accumulate the tokens spent on that
task over the cascade profiles. A task solved at profile k is interval-censored
between the cumulative spend before k and after k; a never-solved task is
right-censored at its total spend.

Per-task model: P(solved with cumulative effort <= e) = A * Phi((ln e - mu) / sigma)
  A      ceiling (fraction of tasks reachable at all)
  mu     scale: log-tokens at which half of the reachable tasks are solved
  sigma  shape: spread of task difficulty in log-tokens (curve steepness)

Nested hypotheses compared by likelihood-ratio test and AIC:
  H1 free:          A_m, mu_m, sigma_m per model
  H2 shared shape:  sigma shared; A_m, mu_m per model
  H3 pure scaling:  sigma and A shared; mu_m per model
"""
from __future__ import annotations

import argparse
import csv
import json
import math
from pathlib import Path

import numpy as np
from scipy import optimize, stats

ROOT = Path(__file__).resolve().parents[2]
DEFAULT_INPUT = ROOT / "output" / "budget_scaling_v03_strat50"
OUT = Path(__file__).resolve().parent
PROFILE_ORDER = [
    "p01_ultra_tiny", "p02_tiny", "p03_ultra_cheap", "p04_cheap", "p05_quick_minus",
    "p06_quick", "p07_medium", "p08_normal", "p09_high", "p10_ultra_high",
]
EPS = 1e-12


def load_model(path: Path) -> dict:
    rows = json.loads((path / "cascade_results.json").read_text())
    rows = [r for r in rows if r.get("profile") in PROFILE_ORDER and not r.get("skipped_already_solved")]
    rows.sort(key=lambda r: PROFILE_ORDER.index(r["profile"]))
    profiles_run = sorted({r["profile"] for r in rows}, key=PROFILE_ORDER.index)
    tasks: dict[str, dict] = {}
    for r in rows:
        t = tasks.setdefault(r["task_ref"], {"spent": 0, "solved_interval": None, "infra": 0})
        if t["solved_interval"]:
            continue
        before = t["spent"]
        t["spent"] += int(r.get("total_tokens") or 0)
        if r.get("final_class") == "INFRA_INVALID":
            t["infra"] += 1
        if r.get("passed"):
            t["solved_interval"] = (before, t["spent"])
    # Panel-level cascade points (the v0.1 figure): cumulative tokens vs solve rate.
    points, cum, solved = [], 0, 0
    for p in profiles_run:
        prow = [r for r in rows if r["profile"] == p]
        cum += sum(int(r.get("total_tokens") or 0) for r in prow)
        solved += sum(1 for r in prow if r.get("passed"))
        points.append({"profile": p, "cumulative_total_tokens": cum, "cumulative_solved": solved})
    return {"tasks": tasks, "points": points, "profiles": profiles_run}


def task_arrays(tasks: dict) -> tuple[np.ndarray, np.ndarray, np.ndarray]:
    lo, hi, solved = [], [], []
    for t in tasks.values():
        if t["solved_interval"]:
            a, b = t["solved_interval"]
            lo.append(max(a, 1)); hi.append(max(b, 1)); solved.append(1)
        else:
            lo.append(max(t["spent"], 1)); hi.append(np.inf); solved.append(0)
    return np.log(lo), np.log(np.where(np.isinf(hi), 1.0, hi)), np.array(solved, bool)


def cdf(x, A, mu, sigma):
    return A * stats.norm.cdf((x - mu) / sigma)


def nll_model(A, mu, sigma, lo, hi, solved) -> float:
    g_lo = cdf(lo, A, mu, sigma)
    g_hi = cdf(hi, A, mu, sigma)
    # Tasks solved with zero prior spend have lo = ln 1 = 0, where G is ~0.
    p_solved = np.clip(g_hi - g_lo, EPS, 1)
    p_unsolved = np.clip(1 - g_lo, EPS, 1)
    return -float(np.sum(np.where(solved, np.log(p_solved), np.log(p_unsolved))))


def unpack(theta, hyp, n):
    """theta layout per hypothesis; A via logistic, sigma via exp."""
    sig = lambda v: 1 / (1 + math.exp(-v))
    if hyp == "H1":
        return [(sig(theta[3 * i]), theta[3 * i + 1], math.exp(theta[3 * i + 2])) for i in range(n)]
    if hyp == "H2":
        s = math.exp(theta[0])
        return [(sig(theta[1 + 2 * i]), theta[2 + 2 * i], s) for i in range(n)]
    s, a = math.exp(theta[0]), sig(theta[1])
    return [(a, theta[2 + i], s) for i in range(n)]


def fit(models: dict, hyp: str):
    names = list(models)
    data = [task_arrays(models[m]["tasks"]) for m in names]
    n = len(names)
    mu0 = [float(np.median(np.concatenate([d[0], d[1][d[2]]]))) for d in data]
    if hyp == "H1":
        x0 = sum(([0.5, mu0[i], 0.5] for i in range(n)), [])
    elif hyp == "H2":
        x0 = [0.5] + sum(([0.5, mu0[i]] for i in range(n)), [])
    else:
        x0 = [0.5, 0.5] + mu0
    f = lambda th: sum(nll_model(*p, *d) for p, d in zip(unpack(th, hyp, n), data))
    best = None
    for jitter in (0.0, 0.7, -0.7, 1.5):
        start = np.array(x0) + jitter * (np.arange(len(x0)) % 2 == 0)
        res = optimize.minimize(f, start, method="Nelder-Mead", options={"maxiter": 40000, "maxfev": 40000, "xatol": 1e-6, "fatol": 1e-8})
        if best is None or res.fun < best.fun:
            best = res
    params = unpack(best.x, hyp, n)
    return {"hypothesis": hyp, "nll": best.fun, "k": len(x0), "aic": 2 * len(x0) + 2 * best.fun,
            "params": {m: {"A": p[0], "mu": p[1], "sigma": p[2], "median_tokens_reachable": math.exp(p[1])} for m, p in zip(names, params)}}


def plot(models: dict, fits: dict, out: Path) -> None:
    import matplotlib
    matplotlib.use("Agg")
    import matplotlib.pyplot as plt
    names = list(models)
    colors = plt.rcParams["axes.prop_cycle"].by_key()["color"]
    fig, axes = plt.subplots(1, 3, figsize=(18, 5.5))
    ax = axes[0]
    for i, m in enumerate(names):
        pts = models[m]["points"]
        n = len(models[m]["tasks"])
        ax.plot([p["cumulative_total_tokens"] for p in pts], [100 * p["cumulative_solved"] / n for p in pts], "o-", color=colors[i % 10], label=m)
    ax.set_xscale("log"); ax.set_xlabel("cumulative panel tokens (cascade)"); ax.set_ylabel("solve rate (%)")
    ax.set_title("Cascade solve rate vs cumulative tokens"); ax.grid(alpha=0.3); ax.legend(fontsize=8)
    ax = axes[1]
    xs = np.linspace(math.log(2e3), math.log(5e6), 300)
    for i, m in enumerate(names):
        tasks = models[m]["tasks"]
        ev = sorted(math.log(max(t["solved_interval"][1], 1)) for t in tasks.values() if t["solved_interval"])
        n = len(tasks)
        ax.step([math.exp(v) for v in ev], [100 * (k + 1) / n for k in range(len(ev))], where="post", color=colors[i % 10], alpha=0.6)
        p = fits["H2"]["params"][m]
        ax.plot(np.exp(xs), 100 * cdf(xs, p["A"], p["mu"], p["sigma"]), "--", color=colors[i % 10], label=f"{m} (H2 fit)")
    ax.set_xscale("log"); ax.set_xlabel("tokens spent on the task (cumulative over profiles)"); ax.set_ylabel("tasks solved (%)")
    ax.set_title("Per-task effort: empirical vs shared-shape fit (H2)"); ax.grid(alpha=0.3); ax.legend(fontsize=7)
    ax = axes[2]
    z = np.linspace(-4, 4, 200)
    ax.plot(z, stats.norm.cdf(z), "k-", lw=2, label="shared shape Φ")
    for i, m in enumerate(names):
        tasks = models[m]["tasks"]
        p = fits["H2"]["params"][m]
        ev = sorted((math.log(max(t["solved_interval"][1], 1)) - p["mu"]) / p["sigma"] for t in tasks.values() if t["solved_interval"])
        n = len(tasks)
        ax.step(ev, [(k + 1) / n / p["A"] for k in range(len(ev))], where="post", color=colors[i % 10], alpha=0.7, label=m)
    ax.set_xlabel("(ln tokens − μ_model) / σ"); ax.set_ylabel("solved / ceiling A")
    ax.set_title("Collapse onto one curve (rescaled by each model's μ, A)"); ax.grid(alpha=0.3); ax.legend(fontsize=7)
    fig.tight_layout()
    fig.savefig(out / "effort_scaling.png", dpi=130)
    fig.savefig(out / "effort_scaling.svg")


def main() -> None:
    ap = argparse.ArgumentParser()
    ap.add_argument("--input", type=Path, default=DEFAULT_INPUT)
    args = ap.parse_args()
    models = {}
    for d in sorted(args.input.iterdir()):
        if (d / "cascade_results.json").is_file():
            models[d.name.replace("__", "/")] = load_model(d)
    fits = {h: fit(models, h) for h in ("H1", "H2", "H3")}
    tests = {}
    for small, big in (("H2", "H1"), ("H3", "H2"), ("H3", "H1")):
        lr = 2 * (fits[small]["nll"] - fits[big]["nll"])
        df = fits[big]["k"] - fits[small]["k"]
        tests[f"{small}_vs_{big}"] = {"lr_stat": lr, "df": df, "p_value": float(stats.chi2.sf(max(lr, 0), df))}
    summary = {
        "models": {m: {"tasks": len(v["tasks"]), "solved": sum(1 for t in v["tasks"].values() if t["solved_interval"]),
                       "profiles_run": v["profiles"], "infra_invalid_runs": sum(t["infra"] for t in v["tasks"].values()),
                       "cascade_points": v["points"]} for m, v in models.items()},
        "fits": fits, "likelihood_ratio_tests": tests,
        "preferred_by_aic": min(fits, key=lambda h: fits[h]["aic"]),
    }
    (OUT / "fit_summary.json").write_text(json.dumps(summary, indent=2) + "\n")
    with (OUT / "cascade_points.csv").open("w", newline="") as fh:
        w = csv.writer(fh)
        w.writerow(["model", "profile", "cumulative_total_tokens", "cumulative_solved", "solve_rate"])
        for m, v in models.items():
            for p in v["points"]:
                w.writerow([m, p["profile"], p["cumulative_total_tokens"], p["cumulative_solved"], round(p["cumulative_solved"] / len(v["tasks"]), 4)])
    plot(models, fits, OUT)
    for h, f in fits.items():
        print(h, f"nll={f['nll']:.2f} k={f['k']} aic={f['aic']:.2f}")
        for m, p in f["params"].items():
            print(f"   {m:32} A={p['A']:.3f} median_tokens={p['median_tokens_reachable']:.0f} sigma={p['sigma']:.3f}")
    print(json.dumps(tests, indent=1)); print("preferred by AIC:", summary["preferred_by_aic"])


if __name__ == "__main__":
    main()
