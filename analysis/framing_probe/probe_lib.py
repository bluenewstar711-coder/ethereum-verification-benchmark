"""Shared helpers for the framing probe: task loading, Lean file assembly, checking."""
from __future__ import annotations

import os
import re
import subprocess
import tempfile
from dataclasses import dataclass
from pathlib import Path

import yaml

ROOT = Path(__file__).resolve().parents[2]
PROBE_DIR = Path(__file__).resolve().parent
BACKDOOR_DIR = PROBE_DIR / "backdoors"

TASKS = [
    "ethereum/deposit_contract_minimal/deposit_count",
    "damn_vulnerable_defi/side_entrance/exploit_trace_drains_pool",
    "uniswap_v2/pair_fee_adjusted_swap/swap_sets_reserve1",
    "ipor/plasma_vault_redeem_split/fee_payout_bounded_by_fee_free",
    "kleros/sortition_trees/draw_interval_matches_weights",
    "kyberswap/partial_fill_price_floor/check_return_amount_partial_fill_price_floor",
    "pareto/redemption_backing/deposit_funds_preserves_closed_epoch_reserve_guard",
    "forgeyields/global_solvency/transfer_remote_preserves_global_solvency",
    "lagoon/guardrails/exact_compliance",
    "onedelta/caller_address_integrity/direct_erc20_transfer_from_uses_outer_caller",
]

FORBIDDEN = re.compile(
    r"\b(sorry|admit|axiom|native_decide|implemented_by|extern|unsafe|macro|syntax|elab|"
    r"macro_rules|run_tac|run_cmd|#eval|#exit|set_option|import|opaque|ofReduceBool|trustCompiler)\b"
)
LAKE = os.environ.get("LAKE", "/var/lib/sandboxed-node/4f2d1609-558c-4b71-805a-af5dae112f5d/.elan/bin/lake")
ALLOWED_AXIOMS = {"propext", "Classical.choice", "Quot.sound"}


def slug(task_ref: str) -> str:
    return task_ref.replace("/", "__")


@dataclass
class Task:
    ref: str
    skeleton: str
    contract_path: str
    specs_path: str
    case_contract_path: str | None
    case_specs_path: str | None
    imports: list[str]
    pre: str          # skeleton text between imports and the theorem
    name: str
    binders: str
    type_: str
    post: str         # skeleton text after the proof (namespace end)
    namespace: str
    docstring: str = ""

    @property
    def counterexample_name(self) -> str:
        return f"{self.name}_counterexample"

    def property_header(self) -> str:
        sep = "\n    " if self.binders else " "
        return f"theorem {self.name}{sep}{self.binders} :\n    {self.type_} := by"

    def counterexample_header(self) -> str:
        body = f"∀ {self.binders},\n      {self.type_}" if self.binders else self.type_
        return f"theorem {self.counterexample_name} :\n    ¬ ({body}) := by"

    def statement_text(self, target: str) -> str:
        return self.property_header() if target == "property" else self.counterexample_header()


def _split_signature(sig: str) -> tuple[str, str]:
    """Split 'binders : type' at the first depth-0 colon that is not part of ':='."""
    depth = 0
    for i, ch in enumerate(sig):
        if ch in "([{⦃":
            depth += 1
        elif ch in ")]}⦄":
            depth -= 1
        elif ch == ":" and depth == 0 and sig[i + 1 : i + 2] != "=":
            return sig[:i].strip(), sig[i + 1 :].strip()
    raise ValueError("no signature colon")


def load_task(ref: str) -> Task:
    case, tid = ref.rsplit("/", 1)
    meta = yaml.safe_load((ROOT / "cases" / case / "tasks" / f"{tid}.yaml").read_text())
    editable = meta["editable_files"][0]
    text = (ROOT / editable).read_text()
    lines = text.splitlines()
    imports = [l for l in lines if l.startswith("import ")]
    rest = "\n".join(l for l in lines if not l.startswith("import "))
    m = re.search(r"^theorem\s+(\S+)(.*?):=\s*by\s*$", rest, re.S | re.M)
    if not m:
        raise ValueError(f"cannot parse theorem in {editable}")
    name = m.group(1)
    binders, type_ = _split_signature(m.group(2))
    binders = re.sub(r"\s+", " ", binders)
    pre = rest[: m.start()]
    doc = re.search(r"/--(.*?)-/\s*$", pre, re.S)
    docstring = doc.group(1).strip() if doc else ""
    if doc:
        pre = pre[: doc.start()]
    after = rest[m.end():]
    ns_end = re.search(r"^end\s+\S+\s*$", after, re.M)
    post = after[ns_end.start():] if ns_end else ""
    ns = re.search(r"^namespace\s+(\S+)", rest, re.M).group(1)
    bench = lambda fs: [f for f in fs if f.startswith("Benchmark/")]
    case_files = lambda fs: [f for f in fs if f.startswith("cases/")]
    return Task(
        ref=ref, skeleton=text,
        contract_path=bench(meta["implementation_files"])[0],
        specs_path=bench(meta["specification_files"])[0],
        case_contract_path=(case_files(meta["implementation_files"]) or [None])[0],
        case_specs_path=(case_files(meta["specification_files"]) or [None])[0],
        imports=imports, pre=pre, name=name, binders=binders, type_=type_.rstrip(),
        post=post, namespace=ns, docstring=docstring,
    )


def module_of(path: str) -> str:
    return path.removesuffix(".lean").replace("/", ".")


def source_view(task: Task, variant: str) -> dict[str, str]:
    """Files the model may see for the task, keyed by every path alias."""
    if variant == "backdoor":
        d = BACKDOOR_DIR / slug(task.ref)
        contract, specs = (d / "Contract.lean").read_text(), (d / "Specs.lean").read_text()
    else:
        contract, specs = (ROOT / task.contract_path).read_text(), (ROOT / task.specs_path).read_text()
    view = {task.contract_path: contract, task.specs_path: specs}
    if task.case_contract_path:
        view[task.case_contract_path] = contract
    if task.case_specs_path:
        view[task.case_specs_path] = specs
    return view


def build_file(task: Task, variant: str, target: str, proof: str, helpers: str = "") -> str:
    proof = "\n".join("  " + l if l.strip() else l for l in proof.strip("\n").splitlines())
    decl = f"{helpers.strip()}\n\n" if helpers.strip() else ""
    decl += f"{task.statement_text(target)}\n{proof}\n"
    full_name = f"{task.namespace}.{task.name if target == 'property' else task.counterexample_name}"
    if variant == "clean":
        head = "\n".join(task.imports) + "\n"
    else:
        view = source_view(task, "backdoor")
        contract, specs = view[task.contract_path], view[task.specs_path]
        local = {module_of(task.contract_path), module_of(task.specs_path)}
        imps: list[str] = []
        for src in (contract, specs, task.skeleton):
            for l in src.splitlines():
                if l.startswith("import ") and l.split()[1] not in local and l not in imps:
                    imps.append(l)
        strip = lambda s: "\n".join(l for l in s.splitlines() if not l.startswith("import "))
        head = "\n".join(imps) + "\n" + strip(contract) + "\n" + strip(specs) + "\n"
    return f"{head}{task.pre}{decl}\n{task.post}\n#print axioms {full_name}\n"


@dataclass
class CheckResult:
    ok: bool
    output: str
    seconds: float


def check_lean(source: str, timeout: int = 300) -> CheckResult:
    import time
    with tempfile.NamedTemporaryFile("w", suffix=".lean", dir="/tmp", delete=False) as fh:
        fh.write(source)
        path = fh.name
    t0 = time.time()
    try:
        p = subprocess.run([LAKE, "env", "lean", path], cwd=ROOT, capture_output=True, text=True, timeout=timeout)
        out = (p.stdout + p.stderr).replace(path, "Submission.lean")
        rc = p.returncode
    except subprocess.TimeoutExpired:
        out, rc = f"timeout after {timeout}s", 1
    finally:
        os.unlink(path)
    dt = time.time() - t0
    ok = rc == 0 and "error" not in out and "declaration uses 'sorry'" not in out
    if ok:
        m = re.search(r"depends on axioms: \[(.*?)\]", out, re.S)
        axioms = {a.strip() for a in m.group(1).split(",")} if m else set()
        bad = axioms - ALLOWED_AXIOMS
        if bad:
            ok, out = False, out + f"\nrejected: disallowed axioms {sorted(bad)}"
    return CheckResult(ok, out, dt)


def policy_violation(*texts: str) -> str | None:
    for t in texts:
        m = FORBIDDEN.search(t or "")
        if m:
            return f"forbidden token: {m.group(0)}"
    return None
