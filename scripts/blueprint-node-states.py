#!/usr/bin/env python3
"""Compute the ground-truth proof state of every blueprint graph node and
emit node-states.json (label -> state).

The blueprint's node colours are normally driven by hand-written \\leanok
annotations, which drift from the Lean reality. This script ignores \\leanok
and derives each node's state from the ACTUAL Lean dependency graph produced by
scripts/DepGraph.lean (a single fast `lake env lean` pass — see that file), so
the graph can be recoloured to tell the truth (see inject-depgraph-extras.py /
blueprint_recolor.py).

Four states (a node citing several decls takes the WORST of them):

  proven       — formalized; neither the decl nor any transitive dependency
                 introduces a sorry / non-standard axiom.
  sorry-dep    — formalized, its own body is not a direct sorry, but some
                 transitive dependency does introduce sorryAx / a custom axiom.
  sorry        — the decl's own body directly introduces sorryAx (a direct sorry).
  unformalized — the blueprint label's Lean decl does not exist in the graph.

DepGraph.lean emits, per project decl:  {"n": name, "s": 0|1, "x": 0|1, "d":[deps]}
  x = 1  the decl directly references a non-standard introduced axiom
         (`sorryAx` shows up here, since it is an axiom) — the authoritative
         "this decl itself is unproven" flag.
  s      direct sorryAx-in-body (kept for reference; x subsumes it for colouring).
  d      direct project-internal dependency edges.

Transitive "depends on an unproven decl" is a linear propagation over `d`.

Usage:
    scripts/blueprint-node-states.py [out.json] [--depgraph FILE]
        out.json     default: blueprint/web/node-states.json
        --depgraph   default: regenerate via `lake env lean --run scripts/DepGraph.lean`,
                     or read FILE if given (a depgraph.jsonl produced earlier).
"""
from __future__ import annotations

import json
import subprocess
import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))
import blueprint_audit as ba  # noqa: E402

ROOT = ba.ROOT
DEPGRAPH_LEAN = ROOT / "scripts" / "DepGraph.lean"


def load_depgraph(depgraph_file: str | None) -> list[dict]:
    """Return the DepGraph records. If `depgraph_file` is given, read it;
    otherwise run DepGraph.lean (fast, ~one env load — no per-decl work)."""
    if depgraph_file:
        text = Path(depgraph_file).read_text(encoding="utf-8")
    else:
        res = subprocess.run(
            ["lake", "env", "lean", "--run", str(DEPGRAPH_LEAN.relative_to(ROOT))],
            cwd=ROOT, capture_output=True, text=True,
        )
        if res.returncode != 0 or not res.stdout.strip():
            sys.stderr.write(
                "blueprint-node-states: DepGraph.lean failed — is the build current?\n"
                "  Run `lake build Jacobian.Solution` (oleans must exist) and retry.\n"
                + (res.stderr[-600:] if res.stderr else "")
                + "\n"
            )
            raise SystemExit(2)
        text = res.stdout
    return [json.loads(l) for l in text.splitlines() if l.strip()]


def compute_decl_states(recs: list[dict]) -> dict[str, str]:
    """Return {decl name -> 'sorry' | 'sorry-dep' | 'proven'} over the full
    decl graph, propagating the direct unproven flag (`x`) transitively over
    the dependency edges (`d`)."""
    by_name = {r["n"]: r for r in recs}
    # A decl is "tainted" if it transitively reaches any decl with x=1.
    # Compute reachability of the direct-flag set via memoised DFS.
    UNKNOWN, CLEAN, TAINTED = 0, 1, 2
    mark: dict[str, int] = {}

    def taint(name: str, stack: set[str]) -> bool:
        r = by_name.get(name)
        if r is None:
            return False  # external/missing dep: treated as clean (Mathlib given)
        m = mark.get(name, UNKNOWN)
        if m == TAINTED:
            return True
        if m == CLEAN:
            return False
        if name in stack:  # cycle guard: don't recurse, decide on this pass
            return r["x"] == 1
        if r["x"] == 1:
            mark[name] = TAINTED
            return True
        stack.add(name)
        tainted = any(taint(d, stack) for d in r["d"])
        stack.discard(name)
        mark[name] = TAINTED if tainted else CLEAN
        return tainted

    states: dict[str, str] = {}
    for r in recs:
        name = r["n"]
        if r["x"] == 1:
            states[name] = "sorry"            # direct: own body introduces sorryAx/axiom
        elif taint(name, set()):
            states[name] = "sorry-dep"        # transitive
        else:
            states[name] = "proven"
    return states


def main(argv: list[str]) -> int:
    depgraph_file = None
    out_args = []
    i = 0
    while i < len(argv):
        if argv[i] == "--depgraph":
            depgraph_file = argv[i + 1]; i += 2
        else:
            out_args.append(argv[i]); i += 1
    out_path = Path(out_args[0]) if out_args else (ROOT / "blueprint" / "web" / "node-states.json")

    recs = load_depgraph(depgraph_file)
    decl_states = compute_decl_states(recs)

    # Map blueprint labels -> their cited decls (from the tex), then to a state.
    states: dict[str, str] = {}
    for tex_dir in ba.TEX_DIRS:
        for tex in sorted(tex_dir.glob("*.tex")):
            for b in ba.parse_tex_blocks(tex.read_text(encoding="utf-8")):
                label = b.get("label")
                names = [n for n in b.get("lean_names", []) if ba.is_project_name(n)]
                if not label or not names:
                    continue
                # Worst state across the cited project decls.
                worst = "proven"
                for n in names:
                    st = decl_states.get(n)
                    if st is None:
                        worst = "unformalized"; break
                    if st == "sorry":
                        worst = "sorry"
                    elif st == "sorry-dep" and worst != "sorry":
                        worst = "sorry-dep"
                states[label] = worst

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
