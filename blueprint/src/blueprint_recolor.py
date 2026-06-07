"""Shared 4-state recolouring for the blueprint dependency graphs.

The node colour is derived from GROUND TRUTH (see scripts/fix-sorries.py (DepGraph.lean):
`#print axioms` + decl existence), NOT from hand-written \\leanok. Both the full
graph (inject-depgraph-extras.py) and the collapsible detail graphs
(build_collapsible_dep_graph.py) call `recolor_dot` so they tell the same story.

The four states and their swatches:

  proven        green fill   — formalized; axiom closure ⊆ {propext, Classical.choice, Quot.sound}
  sorry-dep     blue fill    — formalized, body not a direct sorry, but depends on sorryAx / a custom axiom
  sorry         orange fill  — the decl's own body is a direct `sorry`
  unformalized  grey, dashed — not reachable from the public Jacobian.Solution
                               build: either not written in Lean yet, or
                               formalized but not connected to the public path

States are written into `sorries.jsonl` (the `c` / Status field) by
scripts/fix-sorries.py, which colours every node from the real Lean dependency
graph (scripts/DepGraph.lean). `load_states` reads them from sorries.jsonl,
keyed by each row's blueprint ref `b` (returns {} if the DB is absent, leaving
the upstream leanblueprint colours untouched so the build still works standalone).
"""
from __future__ import annotations

import json
import re
from pathlib import Path

# DOT attribute strings per state, keyed by the sorries.jsonl `c` / Status
# vocabulary (done = proven). Ellipses (theorems/lemmas) and boxes
# (definitions) share fills; shape is set by leanblueprint, we only touch colour.
STATE_DOT = {
    "done":         'color="#5cb85c", fillcolor="#B0ECA3", style=filled',
    "sorry-dep":    'color="#1f77b4", fillcolor="#A3D6FF", style=filled',
    "sorry":        'color="#FFAA33", fillcolor="#fff5e6", style=filled',
    "unformalized": 'color="#888888", fillcolor="#f0f0f0", style="filled,dashed"',
}

# Human-readable legend rows (color-name, description) in display order.
LEGEND_ROWS = [
    ("done",         "Green fill",  "fully proven — no sorry and no introduced axioms"),
    ("sorry-dep",    "Blue fill",   "formalized, but its proof depends on a <code>sorry</code> / extra axiom somewhere upstream"),
    ("sorry",        "Orange fill", "the statement's own proof is a direct <code>sorry</code>"),
    ("unformalized", "Grey dashed", "not connected to the public build — not written yet, or formalized but not wired into the public path"),
]

_NODE_PAT = re.compile(r'("([^"]+)")\s*\[([^\]]*)\]')
# Attributes we strip from a node's existing attr list before re-applying ours,
# so we don't leave a stale color=/fillcolor=/style= behind.
_STRIP_ATTRS = re.compile(r'\b(color|fillcolor|style)\s*=\s*("[^"]*"|[A-Za-z0-9#]+)\s*,?\s*')


def load_states(web_dir: Path) -> dict[str, str]:
    """Return {blueprint label -> state} from sorries.jsonl (the single source
    of truth, coloured by fix-sorries.py). Each row carries its blueprint ref
    `b` and its state in `c`; map b -> c. A label appearing on several rows
    takes the worst state. Returns {} if the DB is absent (recolour no-ops)."""
    # sorries.jsonl lives at the repo root; web_dir is blueprint/web.
    root = Path(web_dir).resolve().parent.parent
    db = root / "sorries.jsonl"
    if not db.is_file():
        return {}
    # Worst-state-wins ordering when one label spans multiple rows.
    rank = {"done": 0, "unformalized": 1, "sorry-dep": 2, "sorry": 3}
    out: dict[str, str] = {}
    try:
        for line in db.read_text(encoding="utf-8").splitlines():
            line = line.strip()
            if not line:
                continue
            r = json.loads(line)
            if r.get("i") == "ID":  # header
                continue
            label, state = r.get("b"), r.get("c")
            if not label or state not in STATE_DOT:
                continue
            if label not in out or rank.get(state, 0) > rank.get(out[label], 0):
                out[label] = state
    except Exception:
        return {}
    return out


def recolor_dot(dot: str, states: dict[str, str]) -> str:
    """Rewrite node colour attributes in a graphviz DOT string by true state.

    Only nodes whose key (the blueprint label, e.g. "thm:foo") appears in
    `states` are touched; edges (which contain `->`) and unknown nodes are left
    as-is. If `states` is empty this is a no-op."""
    if not states:
        return dot

    def repl(m: re.Match) -> str:
        quoted, key, attrs = m.group(1), m.group(2), m.group(3)
        if "->" in key:  # not a node definition
            return m.group(0)
        st = states.get(key)
        if st is None or st not in STATE_DOT:
            return m.group(0)
        rest = _STRIP_ATTRS.sub("", attrs).strip().strip(",").strip()
        new_attrs = STATE_DOT[st] + (", " + rest if rest else "")
        return f"{quoted}\t[{new_attrs}]"

    return _NODE_PAT.sub(repl, dot)
