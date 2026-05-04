#!/usr/bin/env python3
"""Generate `dep_graph_collapsible.html`: a section-collapsed view of
the leanblueprint dep graph, with click-to-expand drilldown to per-
section detail.

Pipeline (run after `python -m leanblueprint.client web` and after
`inject-depgraph-extras.py`):

  python blueprint/src/build_collapsible_dep_graph.py blueprint/web

Reads:
  - <web>/dep_graph_document.html   (for the embedded dot source)
  - tex/sections/*.tex + tex/statements/*.tex   (for label -> section
    mapping; in particular `\\subsection{R<N> -- <name>}` parsing in
    §12 to give R-overview boxes English names)

Writes:
  - <web>/dep_graph_collapsible.html

The script uses only the Python stdlib + pre-existing `<web>/js/` JS
assets (jquery.min.js, d3.min.js, hpcc.min.js, d3-graphviz.js,
graphvizlib.wasm) that leanblueprint already deploys for the existing
dep_graph viewer.

Idempotent.  Re-running produces the same HTML.
"""
from __future__ import annotations

import json
import pathlib
import re
import sys
from collections import defaultdict, Counter

# ---------------------------------------------------------------------------
# Configuration

# Sections to skip entirely (none, currently).
SKIP_SECTIONS: set[str] = set()

# tex/statements/*.tex files hold apex API declarations and cross-cutting
# `\uses{}` references (e.g. `thm:period-lattice` in `statement-bank.tex`,
# `def:analytic-jacobian` in `challenge-statement.tex`).  Functionally
# they are part of §10's apex assembly; fold them in so the section
# dependency chain stays connected.
MERGE_INTO_SECTION = {
    "challenge-statement": "10-main-theorem-assembly",
    "statement-bank": "10-main-theorem-assembly",
}

# §12 "classical analysis gaps" is split by `\subsection{R<N> -- ...}`
# headings.  Each R<N> is one big classical-analysis input (Radó, Tietze,
# de Rham, Hodge, ...) with an internal sub-leaf forest.  Collapse each
# R<N> to a single overview box.
COLLAPSE_SECTION = "12-classical-analysis-gaps"

# Coloring for the overview boxes.  These match the swatches the existing
# inject-depgraph-extras.py uses.
STATE_STYLE = {
    "darkgreen-fill":  'shape=box, style="rounded,filled", fillcolor="#1CAC78", color="#1CAC78", fontcolor=white',
    "green-fill":      'shape=box, style="rounded,filled", fillcolor="#B0ECA3", color="#5cb85c"',
    "green-border":    'shape=box, style="rounded,filled", fillcolor=white, color="#5cb85c", penwidth=2',
    "orange-border":   'shape=box, style="rounded,filled", fillcolor="#fff5e6", color="#FFAA33", penwidth=2',
    "unknown":         'shape=box, style="rounded,filled", fillcolor="#f0f0f0", color="#888"',
}

# Tie-break order when more than one state has the maximum count.
STATE_PRIORITY = ["orange-border", "green-border", "green-fill", "darkgreen-fill", "unknown"]


# ---------------------------------------------------------------------------
# Patterns

LABEL_PAT = re.compile(r"\\label\{([^}]+)\}")
SUBSECTION_R_PAT = re.compile(r"\\subsection\{R(\d+)\s*[—-]+\s*([^}]+)\}")
NODE_PAT = re.compile(r'"([^"]+:[^"]+)"\s*\[([^\]]*)\];')
EDGE_PAT = re.compile(r'"([^"]+)"\s*->\s*"([^"]+)"\s*\[([^\]]*)\];')
DOT_RENDER_PAT = re.compile(r"\.renderDot\(`(.*?)`\)", re.DOTALL)


# ---------------------------------------------------------------------------
# Build label -> section / R-number maps and R<N> name dictionary.

def build_label_maps(repo_root: pathlib.Path):
    label_to_section: dict[str, str] = {}
    label_to_subsection_r: dict[str, str] = {}
    r_to_name: dict[str, str] = {}
    for d in [repo_root / "tex" / "sections", repo_root / "tex" / "statements"]:
        if not d.is_dir():
            continue
        for f in sorted(d.glob("*.tex")):
            text = f.read_text(encoding="utf-8", errors="replace")
            if f.stem == COLLAPSE_SECTION:
                cur_r = None
                for line in text.splitlines():
                    m = SUBSECTION_R_PAT.search(line)
                    if m:
                        cur_r = m.group(1)
                        name = m.group(2).strip()
                        # Strip leading "The " for tighter labels
                        name = re.sub(r"^The\s+", "", name)
                        # Drop simple LaTeX wrappers
                        name = re.sub(r"\\[a-zA-Z]+\{([^}]*)\}", r"\1", name)
                        name = name.replace("\\(", "").replace("\\)", "")
                        r_to_name[cur_r] = name
                        continue
                    for lm in LABEL_PAT.finditer(line):
                        label_to_section[lm.group(1)] = f.stem
                        if cur_r:
                            label_to_subsection_r[lm.group(1)] = cur_r
            else:
                for lm in LABEL_PAT.finditer(text):
                    label_to_section[lm.group(1)] = f.stem
    return label_to_section, label_to_subsection_r, r_to_name


# ---------------------------------------------------------------------------
# Node / edge / vertex helpers.

def extract_dot_from_html(html: str) -> str:
    m = DOT_RENDER_PAT.search(html)
    if not m:
        raise SystemExit("error: could not find renderDot(`...`) in dep_graph HTML")
    return m.group(1)


def parse_real_nodes(dot_text: str) -> list[tuple[str, str]]:
    """Extract genuine node decls.  The same `"label" [attrs]` pattern
    matches edge-target endpoints (e.g. `"a" -> "b" [style=dashed];` would
    spuriously match starting at `"b"`); filter those out by requiring
    real node attrs."""
    real: list[tuple[str, str]] = []
    seen: set[str] = set()
    for label, attrs in NODE_PAT.findall(dot_text):
        is_real = (
            "shape=" in attrs
            or "fillcolor=" in attrs
            or "color=\"#FFAA33\"" in attrs
            or (re.search(r"color=", attrs) and not attrs.strip().startswith("style="))
        )
        if not is_real:
            continue
        if label in seen:
            continue
        seen.add(label)
        real.append((label, attrs))
    return real


def classify_node(attrs: str) -> str:
    if 'fillcolor="#1CAC78"' in attrs:
        return "darkgreen-fill"
    if 'fillcolor="#B0ECA3"' in attrs or 'fillcolor="#9CEC8B"' in attrs:
        return "green-fill"
    if 'color="#FFAA33"' in attrs or "color=\"#FFAA33\"" in attrs:
        return "orange-border"
    if "color=green" in attrs:
        return "green-border"
    if "color=darkgreen" in attrs:
        return "darkgreen-fill"
    return "unknown"


def majority(states: Counter) -> str:
    if not states:
        return "unknown"
    best = max(states.values())
    candidates = [s for s, c in states.items() if c == best]
    for s in STATE_PRIORITY:
        if s in candidates:
            return s
    return candidates[0]


def section_label(sec: str) -> str:
    m = re.match(r"(\d+)-(.*)", sec)
    if m:
        n = int(m.group(1))
        rest = m.group(2).replace("-", " ").title()
        return f"§{n} {rest}"
    return sec


def vertex_label(v: str, members_count: int, r_to_name: dict[str, str]) -> str:
    if v.startswith("gap_R"):
        rn = v[5:]
        name = r_to_name.get(rn, "")
        if name:
            return f"R{rn}: {name}\\n({members_count})"
        return f"R{rn}\\n({members_count})"
    if v == "gap_other":
        return f"§12 other\\n({members_count})"
    if v.startswith("section:"):
        return f"{section_label(v[8:])}\\n({members_count})"
    return v


# ---------------------------------------------------------------------------
# Transitive reduction (Python-only, no graphviz `tred` call).

def transitive_reduction(edges: list[tuple[str, str]]) -> list[tuple[str, str]]:
    succ: dict[str, set[str]] = defaultdict(set)
    for u, v in edges:
        succ[u].add(v)

    def has_indirect_path(u: str, target: str) -> bool:
        # BFS from u that *skips* the direct edge u->target.
        seen = {u}
        stack = [u]
        while stack:
            x = stack.pop()
            for y in succ[x]:
                if x == u and y == target:
                    continue  # ignore the direct edge we're testing
                if y == target:
                    return True
                if y not in seen:
                    seen.add(y)
                    stack.append(y)
        return False

    return [(u, v) for u, v in edges if not has_indirect_path(u, v)]


# ---------------------------------------------------------------------------
# Build overview + per-vertex detail dot strings.

def build_dots(dot_text: str, label_to_section, label_to_subsection_r, r_to_name):
    nodes = parse_real_nodes(dot_text)
    edges_raw = EDGE_PAT.findall(dot_text)
    label_attrs = {label: attrs for label, attrs in nodes}

    def vertex_of(label: str) -> str | None:
        sec = label_to_section.get(label, "other")
        if sec in SKIP_SECTIONS:
            return None
        sec = MERGE_INTO_SECTION.get(sec, sec)
        if sec == COLLAPSE_SECTION:
            rn = label_to_subsection_r.get(label)
            return f"gap_R{rn}" if rn else "gap_other"
        return f"section:{sec}"

    label_vertex = {label: vertex_of(label) for label in label_attrs}

    vertex_members: dict[str, list[str]] = defaultdict(list)
    vertex_states: dict[str, Counter] = defaultdict(Counter)
    for label, attrs in nodes:
        v = label_vertex.get(label)
        if v is None:
            continue
        vertex_members[v].append(label)
        vertex_states[v][classify_node(attrs)] += 1

    # Overview-level edges.
    seen_e: set[tuple[str, str]] = set()
    agg_edges: list[tuple[str, str]] = []
    for src, tgt, _ in edges_raw:
        sv = label_vertex.get(src)
        tv = label_vertex.get(tgt)
        if sv is None or tv is None or sv == tv:
            continue
        if (sv, tv) in seen_e:
            continue
        seen_e.add((sv, tv))
        agg_edges.append((sv, tv))

    agg_edges = transitive_reduction(agg_edges)

    # Overview dot
    o = []
    o.append('strict digraph "" {\n')
    o.append('  graph [bgcolor=transparent, rankdir=TB, nodesep=0.4, ranksep=0.8];\n')
    o.append('  node [fontname="Helvetica", fontsize=12];\n')
    o.append('  edge [arrowhead=vee];\n')
    for v in sorted(vertex_members):
        st = majority(vertex_states[v])
        style = STATE_STYLE[st]
        lbl = vertex_label(v, len(vertex_members[v]), r_to_name)
        o.append(f'  "{v}" [{style}, label="{lbl}"];\n')
    for s, t in agg_edges:
        o.append(f'  "{s}" -> "{t}";\n')
    o.append('}\n')
    overview_dot = "".join(o)

    # Per-vertex detail dots: full internal nodes/edges + adjacent
    # collapsed boxes for navigation.
    detail_dots: dict[str, str] = {}
    for v in sorted(vertex_members):
        members = set(vertex_members[v])
        internal_edges: list[tuple[str, str]] = []
        boundary_edges: list[tuple[str, str]] = []
        adjacent: set[str] = set()
        for src, tgt, _ in edges_raw:
            sv = label_vertex.get(src)
            tv = label_vertex.get(tgt)
            in_s = src in members
            in_t = tgt in members
            if in_s and in_t:
                internal_edges.append((src, tgt))
            elif in_s and tv is not None and tv != v:
                boundary_edges.append((src, tv))
                adjacent.add(tv)
            elif in_t and sv is not None and sv != v:
                boundary_edges.append((sv, tgt))
                adjacent.add(sv)

        d = []
        d.append('strict digraph "" {\n')
        d.append('  graph [bgcolor=transparent, rankdir=LR, nodesep=0.15, ranksep=0.5];\n')
        d.append('  node [label="\\N", penwidth=1.8, fontname="Helvetica", fontsize=11];\n')
        d.append('  edge [arrowhead=vee];\n')
        cluster_id = f"cluster_focus_{re.sub(r'[^a-zA-Z0-9]', '_', v)}"
        title = vertex_label(v, len(members), r_to_name).replace("\\n", " — ")
        d.append(f'  subgraph {cluster_id} {{\n')
        d.append(f'    label="{title}"; style="rounded,filled"; fillcolor="#f8f8f8"; color="#666"; fontsize=14;\n')
        for label in sorted(members):
            d.append(f'    "{label}" [{label_attrs.get(label, "shape=ellipse, color=gray")}];\n')
        d.append('  }\n')
        for ov in sorted(adjacent):
            st = majority(vertex_states[ov])
            d.append(f'  "{ov}" [{STATE_STYLE[st]}, label="{vertex_label(ov, len(vertex_members[ov]), r_to_name)}"];\n')
        for s, t in internal_edges:
            d.append(f'  "{s}" -> "{t}";\n')
        seen_b: set[tuple[str, str]] = set()
        for s, t in boundary_edges:
            if (s, t) in seen_b:
                continue
            seen_b.add((s, t))
            d.append(f'  "{s}" -> "{t}";\n')
        d.append('}\n')
        detail_dots[v] = "".join(d)

    return overview_dot, detail_dots, r_to_name


# ---------------------------------------------------------------------------
# Display names for the breadcrumb.

def display_names(detail_dots: dict[str, str], r_to_name: dict[str, str]) -> dict[str, str]:
    names = {"overview": "Overview"}
    for k in detail_dots:
        if k.startswith("section:"):
            names[k] = section_label(k[8:])
        elif k.startswith("gap_R"):
            rn = k[5:]
            nm = r_to_name.get(rn, "")
            names[k] = f"R{rn}: {nm}" if nm else f"R{rn}"
        elif k == "gap_other":
            names[k] = "§12 (other)"
        else:
            names[k] = k
    return names


# ---------------------------------------------------------------------------
# HTML wrapper template.

HTML_TEMPLATE = """<!DOCTYPE html>
<html>
<head>
<meta charset="utf-8">
<title>Dep Graph — Collapsible</title>
<script src="js/jquery.min.js"></script>
<script src="js/d3.min.js"></script>
<script src="js/hpcc.min.js"></script>
<script src="js/d3-graphviz.js"></script>
<style>
  body { font-family: -apple-system, "Helvetica Neue", sans-serif; margin: 0; }
  header {
    display: flex; align-items: center; gap: 1em;
    padding: 0.6em 1em;
    border-bottom: 1px solid #ddd;
    background: #fafafa;
    position: sticky; top: 0; z-index: 10;
  }
  header button {
    padding: 0.35em 0.8em; border: 1px solid #ccc; border-radius: 4px;
    background: white; cursor: pointer; font-size: 0.9em;
  }
  header button:hover { background: #f0f0f0; }
  header button:disabled { opacity: 0.4; cursor: default; }
  header a { color: #4183c4; text-decoration: none; font-size: 0.9em; }
  header a:hover { text-decoration: underline; }
  #breadcrumb { font-weight: 600; color: #333; }
  #breadcrumb .sep { color: #aaa; margin: 0 0.5em; font-weight: normal; }
  #spacer { flex: 1; }
  #graph { width: 100vw; height: calc(100vh - 50px); overflow: auto; padding: 1em; box-sizing: border-box; }
  #graph svg { display: block; margin: 0 auto; max-width: 100%; height: auto; }
  .clickable polygon, .clickable ellipse, .clickable path { cursor: pointer; }
  .clickable:hover > polygon, .clickable:hover > ellipse, .clickable:hover > path {
    stroke-width: 3 !important;
    filter: drop-shadow(0 1px 2px rgba(0,0,0,0.2));
  }
</style>
</head>
<body>
<header>
  <button id="back" disabled>← Back</button>
  <button id="overview">Overview</button>
  <span id="breadcrumb">Overview</span>
  <span id="spacer"></span>
  <a href="dep_graph_document.html">Full graph →</a>
</header>
<div id="graph"></div>

<script>
const DOTS = __DOTS_JSON__;
const NAMES = __NAMES_JSON__;
const DETAIL_KEYS = new Set(Object.keys(DOTS).filter(k => k !== "overview"));

let history = ["overview"];

function current() { return history[history.length - 1]; }

function tagClickable() {
  const nodes = document.querySelectorAll('#graph g.node');
  nodes.forEach(n => {
    const t = n.querySelector('title');
    if (!t) return;
    const key = t.textContent.trim();
    if (DETAIL_KEYS.has(key)) {
      n.classList.add('clickable');
      n.addEventListener('click', e => {
        e.preventDefault();
        navigate(key);
      });
    }
  });
}

function navigate(key) {
  if (key === current()) return;
  if (key === "overview") {
    history = ["overview"];
  } else {
    history.push(key);
  }
  render();
}

function render() {
  const key = current();
  document.getElementById('breadcrumb').textContent =
    history.map(k => NAMES[k] || k).join(' › ');
  document.getElementById('back').disabled = history.length <= 1;
  document.getElementById('overview').disabled = key === "overview";
  d3.select("#graph")
    .graphviz()
    .renderDot(DOTS[key])
    .on("end", tagClickable);
}

document.getElementById('back').addEventListener('click', () => {
  if (history.length > 1) {
    history.pop();
    render();
  }
});
document.getElementById('overview').addEventListener('click', () => {
  navigate("overview");
});

render();
</script>
</body>
</html>
"""


def main(argv: list[str]) -> int:
    if len(argv) != 2:
        print(f"usage: {argv[0]} <web-dir>", file=sys.stderr)
        return 2
    web = pathlib.Path(argv[1])
    if not web.is_dir():
        print(f"error: not a directory: {web}", file=sys.stderr)
        return 1

    src_html = web / "dep_graph_document.html"
    if not src_html.is_file():
        print(f"error: missing source HTML: {src_html}", file=sys.stderr)
        return 1

    # Locate the project root (it contains a tex/ directory).  Walk up
    # from the web dir.
    repo_root = web
    while repo_root.parent != repo_root:
        if (repo_root / "tex").is_dir():
            break
        repo_root = repo_root.parent
    if not (repo_root / "tex").is_dir():
        print("error: could not locate repo root with tex/ directory", file=sys.stderr)
        return 1

    label_to_section, label_to_subsection_r, r_to_name = build_label_maps(repo_root)
    dot_text = extract_dot_from_html(src_html.read_text(encoding="utf-8"))
    overview_dot, detail_dots, r_to_name = build_dots(
        dot_text, label_to_section, label_to_subsection_r, r_to_name
    )

    dots = {"overview": overview_dot, **detail_dots}
    names = display_names(detail_dots, r_to_name)
    html = HTML_TEMPLATE.replace("__DOTS_JSON__", json.dumps(dots)).replace(
        "__NAMES_JSON__", json.dumps(names)
    )
    out = web / "dep_graph_collapsible.html"
    out.write_text(html, encoding="utf-8")
    total_kb = sum(len(v) for v in dots.values()) // 1024
    print(f"build_collapsible_dep_graph: wrote {out} "
          f"({len(dots)} dots embedded, {total_kb} KB)")
    return 0


if __name__ == "__main__":
    sys.exit(main(sys.argv))
