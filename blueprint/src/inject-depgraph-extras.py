#!/usr/bin/env python3
"""Post-process plastex's dep_graph_*.html to:

1. Replace the auto-generated legend with a tighter, color-name-led
   version. Drops leanblueprint's ``Blue background'' entry, which
   refers to a state ("proof ready to formalize") that doesn't appear
   in this project's graph; relabels every other entry so the swatch's
   visible color matches its caption (the upstream legend instead
   echoes the project-specific ``can_state border'' description text,
   which doesn't tell a reader what color they're looking at).

2. Add a red-border highlight for the big classical-analysis-input
   umbrellas — Riemann-Roch, Stokes on a 2-manifold with boundary,
   Hodge / de Rham, Radó triangulation, Abel's theorem, divisors,
   degree-one isomorphism, finite-dimensionality, Riemann bilinear.
   These are each multi-month sub-projects, distinct in scale from
   ordinary `\notready` lemmas in flight.

Idempotent.
"""
from __future__ import annotations

import re
import sys
from pathlib import Path

# Labels that should get the RED-BORDER "major classical-input" highlight.
# Criteria: huge classical-analysis statement AND not in current Mathlib AND
# the project has not stubbed a Lean declaration for it (i.e. \notready).
# `\leanok` umbrellas like `input:riemann-roch`, `input:abel-theorem`,
# `input:divisors`, `input:finite-dimensionality`, `input:riemann-bilinear`,
# `input:degree-one-isomorphism`, and `thm:stokes-on-rs-with-boundary` carry
# at least a project-side Lean stub so they get the regular `\leanok` green
# border, not the red one — even though their *proofs* are still sorry-bound.
BIG_UMBRELLAS = [
    # The original eight red-border umbrellas (existing tex labels).
    "input:hodge-deRham",
    "input:rado-triangulation",
    "input:de-rham-theorem",
    "input:hodge-decomposition",
    "input:dolbeault",
    "input:tietze-normal-form",
    "thm:polygonal-model",
    "thm:serre-duality-rs",
    # Parallel `gap:R<N>-overview` labels introduced by
    # tex/sections/12-classical-analysis-gaps.tex — each is the
    # independent-build umbrella under Jacobian/Analysis/<Node>/.
    "gap:R1-overview",
    "gap:R2-overview",
    "gap:R3-overview",
    "gap:R4-overview",
    "gap:R5-overview",
    "gap:R6-overview",
    "gap:R7-overview",
    "gap:R8-overview",
    "gap:R9-overview",
    "gap:R10-overview",
]

MARKER = "<!-- DEPGRAPH-EXTRAS-INJECTED -->"

# Color reference (must match macros/web.tex + leanblueprint defaults):
#   blue          = #1f77b4
#   light blue    = #A3D6FF
#   orange        = #FFAA33
#   red           = #d62828
#   light green   = #B0ECA3 (background) / #5cb85c (border equivalent)
#   green         = #9CEC8B
#   dark green    = #1CAC78 (fill) / darkgreen (border)
LEGEND_HTML = """
<details class="legend-details">
<summary>Legend</summary>
<dl class="legend">
  <dt class="legend-shape legend-box">Boxes</dt><dd>definitions</dd>
  <dt class="legend-shape legend-ellipse">Ellipses</dt><dd>theorems and lemmas</dd>
  <dt class="legend-swatch legend-red-border">Red border</dt>
    <dd>major classical-analysis input — admitted, not in current Mathlib</dd>
  <dt class="legend-swatch legend-orange-border">Orange border</dt>
    <dd>blueprint statement still being refined or split into sub-leaves</dd>
  <dt class="legend-swatch legend-green-border">Green border</dt>
    <dd>Lean declaration for the statement exists in this project</dd>
  <dt class="legend-swatch legend-green-fill">Green fill</dt>
    <dd>proof formalized in this project</dd>
  <dt class="legend-swatch legend-darkgreen-fill">Dark-green fill</dt>
    <dd>proof and every ancestor formalized</dd>
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

.legend-red-border::before        { border: 3px solid #d62828; background: white; }
.legend-orange-border::before     { border: 2px solid #FFAA33; background: white; }
.legend-blue-border::before       { border: 2px solid #1f77b4; background: white; }
.legend-green-border::before      { border: 2px solid #5cb85c; background: white; }
.legend-green-fill::before        { border: 2px solid #5cb85c; background: #B0ECA3; }
.legend-darkgreen-fill::before    { border: 2px solid #1CAC78; background: #1CAC78; }

/* Big-umbrella highlight — applied via JS to specific nodes after the
   d3-graphviz render finishes. The .big-umbrella class is added to the
   <g class="node"> element. */
.node.big-umbrella ellipse,
.node.big-umbrella polygon,
.node.big-umbrella path {
  stroke: #d62828 !important;
  stroke-width: 3 !important;
}
</style>
"""

# JS adds a `.big-umbrella` class to specific node groups so the CSS
# above can target them. d3-graphviz emits each node as
# <g class="node"><title>label</title><ellipse/>...</g>, so we look up
# by <title> text. This runs after every render (the graph viewer
# re-renders on zoom/pan, but the class survives because we observe
# DOM mutations).
INJECTED_SCRIPT = """
<script id="depgraph-extras-script">
(function () {
  var BIG = %s;
  function tag() {
    var nodes = document.querySelectorAll('g.node');
    for (var i = 0; i < nodes.length; i++) {
      var n = nodes[i];
      var t = n.querySelector('title');
      if (!t) continue;
      var name = t.textContent.trim();
      if (BIG.indexOf(name) >= 0) n.classList.add('big-umbrella');
    }
  }
  // Run once when the SVG first appears, then re-run on subsequent
  // d3-graphviz transitions (zoom/pan can cause re-attach).
  var attempts = 0;
  function poll() {
    if (document.querySelector('g.node')) { tag(); }
    attempts++;
    if (attempts < 40) setTimeout(poll, 250);
  }
  poll();
  if (window.MutationObserver) {
    var graph = document.querySelector('#graph');
    if (graph) {
      new MutationObserver(tag).observe(graph, { childList: true, subtree: true });
    }
  }
})();
</script>
""" % (str(BIG_UMBRELLAS).replace("'", '"'),)


def inject(html: str) -> str:
    if MARKER in html:
        return html
    new = LEGEND_REPLACE.sub(LEGEND_HTML.strip(), html, count=1)
    new = new.replace(
        "</body>",
        f"{INJECTED_STYLE}{INJECTED_SCRIPT}\n{MARKER}\n</body>",
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
    n = 0
    for path in root.glob("dep_graph*.html"):
        original = path.read_text(encoding="utf-8")
        updated = inject(original)
        if updated != original:
            path.write_text(updated, encoding="utf-8")
            n += 1
    print(f"inject-depgraph-extras: updated {n} dep_graph*.html files under {root}")
    return 0


if __name__ == "__main__":
    sys.exit(main(sys.argv))
