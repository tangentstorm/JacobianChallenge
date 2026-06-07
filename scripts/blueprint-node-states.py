#!/usr/bin/env python3
"""Compute the ground-truth proof state of every blueprint graph node and
emit node-states.json (label -> state).

The blueprint's node colours are normally driven by hand-written \\leanok
annotations, which drift from the Lean reality. This script ignores \\leanok
and derives each node's state from the actual Lean code, so the dependency
graph can be recoloured to tell the truth (see inject-depgraph-extras.py).

Four states (a node citing several decls takes the WORST of them):

  proven       — formalized and the proof's axiom closure is clean:
                 axioms ⊆ {propext, Classical.choice, Quot.sound}.
  sorry-dep    — formalized, the decl's own body is not a bare `sorry`, but
                 it transitively depends on `sorryAx` or any other introduced
                 axiom (a custom `axiom` decl).
  sorry        — the decl's own body is a direct `sorry`.
  unformalized — at least one cited project decl does not exist in Lean yet.

Nodes whose \\lean{...} names are all external (Mathlib/core) are reported as
`proven` (we cannot inspect Mathlib, and the project treats those as given).
Nodes with no \\lean{...} at all are omitted (the graph leaves them as-is).

Usage:
    scripts/blueprint-node-states.py [out.json]      # default: blueprint/web/node-states.json
"""
from __future__ import annotations

import json
import re
import subprocess
import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))
import blueprint_audit as ba  # noqa: E402

ROOT = ba.ROOT
STANDARD_AXIOMS = {"propext", "Classical.choice", "Quot.sound"}


def axioms_of(names: list[str]) -> dict[str, set[str]]:
    """`#print axioms` for each name in one elaboration pass.
    Returns {name -> set of axiom names}; '' for names that fail."""
    if not names:
        return {}
    lines = ["import Jacobian.Solution"]
    lines += [f"#print axioms {n}" for n in names]
    scratch = ROOT / "Jacobian" / "_NodeStateAxiomScratch.lean"
    scratch.write_text("\n".join(lines) + "\n", encoding="utf-8")
    try:
        res = subprocess.run(
            ["lake", "env", "lean", str(scratch.relative_to(ROOT))],
            cwd=ROOT, capture_output=True, text=True,
        )
    finally:
        scratch.unlink(missing_ok=True)
    blob = res.stdout + "\n" + res.stderr
    # Fail loudly on a stale/broken build: if the import itself errors (e.g. a
    # missing .olean), every `#print axioms` silently yields nothing and the
    # whole graph would be mis-classified as sorry-dep. Refuse rather than lie.
    if re.search(r"error:.*(does not exist|unknown (identifier|constant|module)|failed to)", blob):
        sys.stderr.write(
            "blueprint-node-states: Lean elaboration failed — the build looks stale.\n"
            "  Run `lake build Jacobian.Solution` first (oleans must be current).\n"
            "  First error:\n    "
            + next((ln for ln in blob.splitlines() if "error:" in ln), "(unknown)")
            + "\n"
        )
        raise SystemExit(2)
    out: dict[str, set[str]] = {}
    # 'Name' depends on axioms: [a, b, c]   |   'Name' does not depend on any axioms
    for m in re.finditer(
        r"'([^']+)' (?:depends on axioms: \[([^\]]*)\]|does not depend on any axioms)", blob
    ):
        name = m.group(1)
        if m.group(2) is None:
            out[name] = set()
        else:
            out[name] = {a.strip() for a in m.group(2).split(",") if a.strip()}
    return out


# `Jacobian/Challenge.lean` is the FROZEN PUBLIC SPEC: every decl there is
# `:= sorry` by design (it states the API to be implemented). The real proof
# lives in the implementation file (Solution.lean etc.), which is what the
# graph should judge. A `\lean{}` name typically resolves to BOTH a Challenge
# spec stub and a Solution implementation; counting the spec stub's `sorry`
# would mis-rank every public node as a direct sorry. So exclude spec sites
# from the direct-sorry check. (`#print axioms` already resolves to the real
# elaborated decl, so the proven-vs-sorry-dep axiom check is unaffected.)
SPEC_FILE = "Challenge.lean"


def decl_has_direct_sorry(name: str, index: dict) -> bool:
    """True if any *implementation* site for `name` has a literal `sorry`.
    Frozen-spec stubs in Challenge.lean are ignored. If the ONLY sites are
    spec stubs (no implementation exists), the decl is treated as a direct
    sorry — the API is stated but unimplemented."""
    sites = index.get(name, [])
    impl_sites = [(f, ln, b) for (f, ln, b) in sites if not f.endswith(SPEC_FILE)]
    if not impl_sites:
        # Only a frozen-spec stub exists; no implementation yet.
        return bool(sites)
    return any(not ba.body_is_sorry_free(b) for (_f, _ln, b) in impl_sites)


def node_state(names: list[str], index: dict, axioms: dict[str, set[str]]) -> str | None:
    """Aggregate state across a node's cited decls (worst wins). None if the
    node cites no decls at all."""
    project = [n for n in names if ba.is_project_name(n)]
    external = [n for n in names if not ba.is_project_name(n)]
    if not project and not external:
        return None
    # D: any project decl missing from the Lean index.
    missing = [n for n in project if n not in index]
    if missing:
        return "unformalized"
    # C: any project decl whose own body is a direct sorry.
    if any(decl_has_direct_sorry(n, index) for n in project):
        return "sorry"
    # B: any project decl with a non-standard axiom in its closure.
    for n in project:
        ax = axioms.get(n)
        if ax is None:
            # Failed to elaborate a #print axioms line: treat conservatively.
            return "sorry-dep"
        if not ax.issubset(STANDARD_AXIOMS):
            return "sorry-dep"
    # A: all clean (external-only nodes also land here).
    return "proven"


def main(argv: list[str]) -> int:
    out_path = Path(argv[0]) if argv else (ROOT / "blueprint" / "web" / "node-states.json")
    index = ba.index_lean_decls(ba.LEAN_DIR)

    # Gather (label -> cited decl names) for every blueprint block with a label.
    nodes: dict[str, list[str]] = {}
    for tex_dir in ba.TEX_DIRS:
        for tex in sorted(tex_dir.glob("*.tex")):
            for b in ba.parse_tex_blocks(tex.read_text(encoding="utf-8")):
                label = b.get("label")
                names = b.get("lean_names", [])
                if label and names:
                    nodes.setdefault(label, [])
                    nodes[label].extend(names)

    # One #print axioms pass over every project decl we might need.
    all_project = sorted({
        n for names in nodes.values() for n in names if ba.is_project_name(n)
    })
    axioms = axioms_of(all_project)

    states: dict[str, str] = {}
    for label, names in nodes.items():
        st = node_state(names, index, axioms)
        if st is not None:
            states[label] = st

    out_path.parent.mkdir(parents=True, exist_ok=True)
    out_path.write_text(json.dumps(states, indent=2, sort_keys=True) + "\n", encoding="utf-8")

    tally: dict[str, int] = {}
    for st in states.values():
        tally[st] = tally.get(st, 0) + 1
    print(f"node-states: wrote {len(states)} labelled nodes -> {out_path}")
    for st in ("proven", "sorry-dep", "sorry", "unformalized"):
        print(f"  {st:13s} {tally.get(st, 0)}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main(sys.argv[1:]))
