#!/usr/bin/env python3
"""Post-process plastex's dep_graph_*.html to:

1. Recolour the dependency-graph nodes by GROUND TRUTH (the four states from
   scripts/fix-sorries.py (DepGraph.lean) / blueprint_recolor.py — proven / sorry-dep
   / sorry / unconnected), overriding the upstream \\leanok colours.

2. Replace the auto-generated legend with a tighter, color-name-led version
   describing those four states.

Idempotent.
"""
from __future__ import annotations

import re
import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))
from blueprint_recolor import load_states, recolor_dot  # noqa: E402

DOT_RENDER_PAT = re.compile(r"\.renderDot\(`(.*?)`\)", re.DOTALL)

MARKER = "<!-- DEPGRAPH-EXTRAS-INJECTED -->"

# Node colours are derived from GROUND TRUTH (scripts/fix-sorries.py (DepGraph.lean):
# #print axioms + decl existence), not from \leanok. The four states match
# blueprint/src/blueprint_recolor.py STATE_DOT:
#   green fill  #B0ECA3 / #5cb85c   proven
#   blue fill   #A3D6FF / #1f77b4   sorry-dep
#   orange fill #fff5e6 / #FFAA33   sorry
#   grey dashed #f0f0f0 / #888      unconnected
LEGEND_HTML = """
<details class="legend-details">
<summary>Legend</summary>
<dl class="legend">
  <dt class="legend-shape legend-box">Boxes</dt><dd>definitions</dd>
  <dt class="legend-shape legend-ellipse">Ellipses</dt><dd>theorems and lemmas</dd>
  <dt class="legend-swatch legend-green-fill">Green fill</dt>
    <dd>fully proven — no <span class="ttfamily">sorry</span> and no introduced axioms</dd>
  <dt class="legend-swatch legend-blue-fill">Blue fill</dt>
    <dd>formalized, but its proof depends on a <span class="ttfamily">sorry</span> / extra axiom somewhere upstream</dd>
  <dt class="legend-swatch legend-orange-fill">Orange fill</dt>
    <dd>the statement's own proof is a direct <span class="ttfamily">sorry</span></dd>
  <dt class="legend-swatch legend-grey-dashed">Grey, dashed</dt>
    <dd>not connected to the public build (not written yet, or formalized but not wired into the public path)</dd>
</dl>
</details>
"""

# Replace the auto-generated <dl class="legend">...</dl> block with ours.
LEGEND_REPLACE = re.compile(
    r'<dl class="legend">.*?</dl>', re.DOTALL
)

INJECTED_STYLE = """
<style id="depgraph-extras-style">
/* Compact legend layout — fit the page without scrolling. */
#Legend { font-size: 0.78em; }
/* Upstream heading is replaced by the details/summary below. */
#Legend #legend_title { display: none; }
#Legend details.legend-details > summary {
  cursor: pointer;
  font-size: 1.3em;
  font-weight: bold;
  user-select: none;
  list-style: revert;
}
/* The actual popup: upstream CSS gives `#Legend dl` position:absolute
   with top:6rem; left:1.5rem so it floats over the graph. Style that
   floating popup as a card. */
#Legend dl.legend {
  margin-top: 0.4em;
  padding: 0.75em 1em;
  border: 1px solid #d0d0d0;
  border-radius: 4px;
  box-shadow: 0 4px 12px rgba(0, 0, 0, 0.15);
  background: white;
}
#Legend dl.legend dt {
  margin-top: 0.25em;
  font-weight: 600;
  line-height: 1.2;
}
#Legend dl.legend dd {
  margin: 0 0 0 1.4em;
  line-height: 1.25;
  color: #333;
}
#Legend dl.legend dt::after { content: none; }
#Legend dl.legend dt::before {
  content: "";
  display: inline-block;
  width: 1em;
  height: 0.75em;
  margin-right: 0.4em;
  vertical-align: -2px;
  box-sizing: border-box;
}
.legend-box::before     { border: 2px solid #555; background: transparent; }
.legend-ellipse::before { border: 2px solid #555; border-radius: 50%; background: transparent; }

/* The four ground-truth fill states (see blueprint_recolor.STATE_DOT). */
.legend-green-fill::before        { border: 2px solid #5cb85c; background: #B0ECA3; }
.legend-blue-fill::before         { border: 2px solid #1f77b4; background: #A3D6FF; }
.legend-orange-fill::before       { border: 2px solid #FFAA33; background: #fff5e6; }
.legend-grey-dashed::before       { border: 2px dashed #888;    background: #f0f0f0; }
</style>
"""

def inject(html: str, path: Path, states: dict[str, str]) -> str:
    if MARKER in html:
        return html

    if path.name == "dep_graph_document.html":
        m_dot = DOT_RENDER_PAT.search(html)
        if m_dot:
            original_dot = m_dot.group(1)
            # Recolour by ground-truth node state (overrides \leanok colours).
            recoloured = recolor_dot(original_dot, states)
            html = html.replace(original_dot, recoloured, 1)

    new = LEGEND_REPLACE.sub(LEGEND_HTML.strip(), html, count=1)
    new = new.replace(
        "</body>",
        f"{INJECTED_STYLE}\n{MARKER}\n</body>",
        1,
    )
    return new


def main(argv: list[str]) -> int:
    if len(argv) != 2:
        print(f"usage: {argv[0]} <web-output-dir>", file=sys.stderr)
        return 2
    root = Path(argv[1])
    if not root.is_dir():
        print(f"error: not a directory: {root}", file=sys.stderr)
        return 1
        
    states = load_states(root)
    if states:
        print(f"inject-depgraph-extras: recolouring from sorries.jsonl ({len(states)} nodes)")
    else:
        print("inject-depgraph-extras: no sorries.jsonl states — keeping upstream \\leanok colours")

    n = 0
    for path in root.glob("dep_graph*.html"):
        original = path.read_text(encoding="utf-8")
        updated = inject(original, path, states)
        if updated != original:
            path.write_text(updated, encoding="utf-8")
            n += 1
    print(f"inject-depgraph-extras: updated {n} dep_graph*.html files under {root}")
    return 0



if __name__ == "__main__":
    sys.exit(main(sys.argv))
