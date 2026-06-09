"""Shared 4-state recolouring for the blueprint dependency graphs.

The node colour is derived from GROUND TRUTH (see scripts/blueprint-node-states.py:
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

`node-states.json` is produced by scripts/blueprint-node-states.py and lives in
the web output dir; `load_states` reads it (returns {} if absent, leaving the
upstream leanblueprint colours untouched so the build still works standalone).
"""
from __future__ import annotations

import json
import re
from pathlib import Path

# DOT attribute strings per state. Ellipses (theorems/lemmas) and boxes
# (definitions) share fills; shape is set by leanblueprint, we only touch colour.
STATE_DOT = {
    "proven":       'color="#5cb85c", fillcolor="#B0ECA3", style=filled',
    "sorry-dep":    'color="#1f77b4", fillcolor="#A3D6FF", style=filled',
    "sorry":        'color="#FFAA33", fillcolor="#fff5e6", style=filled',
    "unformalized": 'color="#888888", fillcolor="#f0f0f0", style="filled,dashed"',
    # The "local root" the swarm is currently focused on. Overrides the node's
    # state colour (orange/blue/grey/green) so the chosen target is easy to pick
    # out. A purple that sits alongside the green/blue/orange palette (saturated
    # border + pale fill, penwidth boosted).
    "focus":        'color="#8e44ad", fillcolor="#efe1f5", style=filled, penwidth=2.5',
}

# Human-readable legend rows (color-name, description) in display order.
LEGEND_ROWS = [
    ("proven",       "Green fill",  "fully proven — no sorry and no introduced axioms"),
    ("sorry-dep",    "Blue fill",   "formalized, but its proof depends on a <code>sorry</code> / extra axiom somewhere upstream"),
    ("sorry",        "Orange fill", "the statement's own proof is a direct <code>sorry</code>"),
    ("unformalized", "Grey dashed", "not connected to the public build — not written yet, or formalized but not wired into the public path"),
    ("focus",        "Purple fill", "the 'local root' the swarm is currently focused on (overrides its state colour)"),
]

_NODE_PAT = re.compile(r'("([^"]+)")\s*\[([^\]]*)\]')
# Attributes we strip from a node's existing attr list before re-applying ours,
# so we don't leave a stale color=/fillcolor=/style= behind.
_STRIP_ATTRS = re.compile(r'\b(color|fillcolor|style)\s*=\s*("[^"]*"|[A-Za-z0-9#]+)\s*,?\s*')


def load_states(web_dir: Path) -> dict[str, str]:
    p = Path(web_dir) / "node-states.json"
    if not p.is_file():
        return {}
    try:
        return json.loads(p.read_text(encoding="utf-8"))
    except Exception:
        return {}


def load_focus(web_dir: Path) -> set[str]:
    """The set of blueprint-node labels to highlight as the 'local root' the
    swarm is focused on. Read from `<repo>/.sci/focus-node` (one label per line,
    e.g. `thm:uniformization-genus-zero-biholomorphism`), falling back to
    `<web_dir>/.focus-node`. Manager-controlled, like the hold sentinel: set/clear
    it to move the magenta highlight. Blank lines and `#` comments ignored."""
    repo_root = Path(web_dir).resolve().parents[1]  # blueprint/web -> repo root
    for cand in (repo_root / ".sci" / "focus-node", Path(web_dir) / ".focus-node"):
        if cand.is_file():
            try:
                out: set[str] = set()
                for line in cand.read_text(encoding="utf-8").splitlines():
                    s = line.strip()
                    if s and not s.startswith("#"):
                        out.add(s)
                return out
            except Exception:
                return set()
    return set()


def recolor_dot(dot: str, states: dict[str, str], focus: set[str] | None = None) -> str:
    """Rewrite node colour attributes in a graphviz DOT string by true state.

    Only nodes whose key (the blueprint label, e.g. "thm:foo") appears in
    `states` are touched; edges (which contain `->`) and unknown nodes are left
    as-is. Nodes whose key is in `focus` are coloured with the `focus` (purple)
    style regardless of state — this is the 'local root' highlight, applied even
    to nodes not yet in `states` (e.g. a freshly-added open node)."""
    focus = focus or set()
    if not states and not focus:
        return dot

    def repl(m: re.Match) -> str:
        quoted, key, attrs = m.group(1), m.group(2), m.group(3)
        if "->" in key:  # not a node definition
            return m.group(0)
        st = "focus" if key in focus else states.get(key)
        if st is None or st not in STATE_DOT:
            return m.group(0)
        rest = _STRIP_ATTRS.sub("", attrs).strip().strip(",").strip()
        new_attrs = STATE_DOT[st] + (", " + rest if rest else "")
        return f"{quoted}\t[{new_attrs}]"

    return _NODE_PAT.sub(repl, dot)
