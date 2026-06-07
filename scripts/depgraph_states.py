#!/usr/bin/env python3
"""Compute the four ground-truth node states from the real Lean dependency
graph (scripts/DepGraph.lean), shared by fix-sorries.py and the blueprint
recolour step.

States (written into the sorries.jsonl `c` / Status field):
  done          fully proven — no sorry / introduced axiom anywhere upstream
  sorry         the decl's own body directly introduces sorryAx (a direct sorry)
  sorry-dep     formalized, body clean, but a transitive dependency is unproven
  unformalized  no Lean declaration exists for this node (tex-only blueprint node)

DepGraph.lean emits one JSON line per project decl:
  {"n": name, "m": module, "s": 0|1 direct sorry, "x": 0|1 direct axiom, "d": [deps]}
`x` is the authoritative "this decl itself is unproven" flag (sorryAx is an
axiom, so it shows up in `x`). Transitive taint is a walk over `d`.
"""
from __future__ import annotations

import json
import subprocess
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
DEPGRAPH_LEAN = ROOT / "scripts" / "DepGraph.lean"


def run_depgraph(depgraph_file: str | None = None) -> list[dict]:
    """Return DepGraph records. Reads `depgraph_file` if given, else runs
    DepGraph.lean (fast single `lake env lean` pass; needs current oleans)."""
    if depgraph_file:
        text = Path(depgraph_file).read_text(encoding="utf-8")
    else:
        res = subprocess.run(
            ["lake", "env", "lean", "--run", str(DEPGRAPH_LEAN.relative_to(ROOT))],
            cwd=ROOT, capture_output=True, text=True,
        )
        if res.returncode != 0 or not res.stdout.strip():
            raise RuntimeError(
                "DepGraph.lean failed — is the build current? "
                "Run `lake build Jacobian.Solution` first.\n"
                + (res.stderr[-800:] if res.stderr else "")
            )
        text = res.stdout
    return [json.loads(l) for l in text.splitlines() if l.strip()]


def decl_states(recs: list[dict]) -> dict[str, str]:
    """Return {decl name -> 'done' | 'sorry' | 'sorry-dep'} over the full decl
    graph, propagating the direct-unproven flag (`x`) transitively over `d`."""
    by_name = {r["n"]: r for r in recs}
    UNKNOWN, CLEAN, TAINTED = 0, 1, 2
    mark: dict[str, int] = {}

    def taint(name: str, stack: set[str]) -> bool:
        r = by_name.get(name)
        if r is None:
            return False  # external/Mathlib dep: treated as given (clean)
        m = mark.get(name, UNKNOWN)
        if m == TAINTED:
            return True
        if m == CLEAN:
            return False
        if name in stack:  # cycle guard
            return r["x"] == 1
        if r["x"] == 1:
            mark[name] = TAINTED
            return True
        stack.add(name)
        t = any(taint(d, stack) for d in r["d"])
        stack.discard(name)
        mark[name] = TAINTED if t else CLEAN
        return t

    out: dict[str, str] = {}
    for r in recs:
        n = r["n"]
        if r["x"] == 1:
            out[n] = "sorry"
        elif taint(n, set()):
            out[n] = "sorry-dep"
        else:
            out[n] = "done"
    return out


def state_for_decl(name: str, states: dict[str, str]) -> str:
    """State for a single Lean decl name; 'unformalized' if absent from the
    graph (tex-only blueprint node, or a decl outside Solution's closure)."""
    return states.get(name, "unformalized")
