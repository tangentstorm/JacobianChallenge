"""Build a browsable, syntax-highlighted HTML view of the project's Lean
sources, plus a doc-gen4-compatible `find/#doc/<DeclName>` redirector so
the blueprint's `\\lean{...}` annotations resolve.

Output layout (relative to OUT_DIR, which the Pages workflow mounts at
`<dochome>` = `/docs/`):

    index.html                     -- entry page (sidebar layout, empty main)
    site.css                       -- shared layout stylesheet
    app.js                         -- shared sidebar / outline / linker logic
    pygments.css                   -- shared syntax-highlight stylesheet
    tree.json                      -- file-tree manifest (sidebar)
    declarations.json              -- {fully-qualified decl name: relative URL}
    find/index.html                -- JS redirector (local or mathlib4_docs fallback)
    decls/<rel>.json               -- per-file outline {imports, decls}
    Jacobian/...                   -- one HTML page per .lean source file,
                                      mirroring the import path

Decl/namespace extraction is regex-based, not a real Lean parser. It is
deliberately conservative: missed names just mean the corresponding
`\\lean{...}` link falls through to the mathlib4_docs redirector, which
is the same outcome as for any other unrecognised symbol.
"""
from __future__ import annotations

import argparse
import html
import json
import re
import sys
from pathlib import Path

from pygments import highlight
from pygments.formatters import HtmlFormatter
from pygments.lexers import Lean4Lexer

DECL_KW = (
    r"(?:def|theorem|lemma|abbrev|instance|opaque|axiom|"
    r"structure|class|inductive|coinductive|example)"
)
MOD_KW = (
    r"(?:private|protected|noncomputable|unsafe|partial|nonrec|scoped|local)"
)
DECL_RE = re.compile(
    rf"^\s*(?:@\[[^\]]*\]\s*)*(?:{MOD_KW}\s+)*(?P<kw>{DECL_KW})\s+"
    rf"(?:\{{[^}}]*\}}\s*)?"
    rf"(?P<name>[A-Za-z_][A-Za-z0-9_'.]*)"
)
NAMESPACE_RE = re.compile(r"^\s*namespace\s+([A-Za-z_][A-Za-z0-9_'.]*)")
END_RE = re.compile(r"^\s*end(?:\s+([A-Za-z_][A-Za-z0-9_'.]*))?\s*$")
IMPORT_RE = re.compile(r"^\s*import\s+([A-Za-z_][A-Za-z0-9_'.]*)")


def strip_comments(src: str) -> str:
    """Drop `--` line comments and `/- ... -/` block comments (with nesting),
    preserving newlines so line numbers stay aligned."""
    out: list[str] = []
    i, n = 0, len(src)
    depth = 0
    while i < n:
        if depth == 0 and src.startswith("--", i):
            j = src.find("\n", i)
            if j < 0:
                break
            i = j
            continue
        if src.startswith("/-", i):
            depth += 1
            i += 2
            continue
        if depth > 0 and src.startswith("-/", i):
            depth -= 1
            i += 2
            continue
        if depth > 0:
            out.append("\n" if src[i] == "\n" else " ")
            i += 1
            continue
        out.append(src[i])
        i += 1
    return "".join(out)


def extract_decls(src: str) -> list[tuple[str, int, str]]:
    """Return [(fully_qualified_name, 1-based line number, kind), ...]."""
    cleaned = strip_comments(src)
    ns_stack: list[str] = []
    out: list[tuple[str, int, str]] = []
    for lineno, line in enumerate(cleaned.splitlines(), start=1):
        m = NAMESPACE_RE.match(line)
        if m:
            ns_stack.append(m.group(1))
            continue
        m = END_RE.match(line)
        if m:
            label = m.group(1)
            if label is not None:
                while ns_stack:
                    top = ns_stack.pop()
                    if top == label or top.split(".")[-1] == label:
                        break
            continue
        m = DECL_RE.match(line)
        if m:
            name = m.group("name")
            kind = m.group("kw")
            if name.startswith("_root_."):
                qual = name[len("_root_."):]
            else:
                ns = ".".join(ns_stack)
                qual = f"{ns}.{name}" if ns else name
            out.append((qual, lineno, kind))
    return out


def extract_imports(src: str) -> list[str]:
    """Return imported module names. Stops at first non-import, non-blank,
    non-comment line — Lean requires imports at the top of the file."""
    out: list[str] = []
    for raw in src.splitlines():
        line = raw.strip()
        if not line or line.startswith("--") or line.startswith("/-"):
            continue
        m = IMPORT_RE.match(raw)
        if m:
            out.append(m.group(1))
            continue
        break
    return out


# ---------------------------------------------------------------------------
# Templates
# ---------------------------------------------------------------------------

PAGE_TPL = """<!doctype html>
<html lang="en">
<head>
<meta charset="utf-8">
<title>{title}</title>
<link rel="stylesheet" href="{root_rel}pygments.css">
<link rel="stylesheet" href="{root_rel}site.css">
</head>
<body class="page">
<aside class="sidebar">
  <header><a href="{root_rel}index.html">browsable source</a></header>
  <nav class="tree" id="tree" aria-label="File tree"></nav>
  <nav class="outline" id="outline" aria-label="Declarations in this file"></nav>
</aside>
<main>
  <header>
    <code>{relpath}</code>
    <span class="sep">&middot;</span>
    <a href="{github_url}">view on GitHub</a>
  </header>
  <div class="source">{body}</div>
</main>
<script>window.PAGE = {{ relpath: "{relpath_js}", root: "{root_rel}" }};</script>
<script src="{root_rel}app.js"></script>
</body>
</html>
"""

INDEX_TPL = """<!doctype html>
<html lang="en">
<head>
<meta charset="utf-8">
<title>Jacobian Challenge — browsable source</title>
<link rel="stylesheet" href="site.css">
</head>
<body class="page">
<aside class="sidebar">
  <header><a href="index.html">browsable source</a></header>
  <nav class="tree" id="tree" aria-label="File tree"></nav>
</aside>
<main>
  <header><strong>Jacobian Challenge — source</strong></header>
  <div class="welcome">
    <p>Pick a file from the tree on the left.</p>
    <p>Identifier links from the <a href="../blueprint/">blueprint</a> resolve through
    <code>find/#doc/&lt;Name&gt;</code>; declarations defined in this repository jump
    here, anything else falls through to the
    <a href="https://leanprover-community.github.io/mathlib4_docs/">official Mathlib docs</a>.</p>
  </div>
</main>
<script>window.PAGE = { relpath: null, root: "" };</script>
<script src="app.js"></script>
</body>
</html>
"""

FIND_TPL = """<!doctype html>
<html lang="en">
<head>
<meta charset="utf-8">
<title>Find declaration</title>
<script>
(function () {
  var MATHLIB = "https://leanprover-community.github.io/mathlib4_docs/find/";
  var frag = window.location.hash || "";
  var name = "";
  var m = frag.match(/^#(?:doc\\/)?(.+)$/);
  if (m) name = decodeURIComponent(m[1]);
  if (!name) {
    var qs = new URLSearchParams(window.location.search);
    name = qs.get("pattern") || "";
  }
  if (!name) {
    document.body.textContent = "No declaration name given.";
    return;
  }
  fetch("../declarations.json", {cache: "force-cache"})
    .then(function (r) { return r.ok ? r.json() : {}; })
    .catch(function () { return {}; })
    .then(function (decls) {
      if (decls && Object.prototype.hasOwnProperty.call(decls, name)) {
        window.location.replace("../" + decls[name]);
      } else {
        window.location.replace(MATHLIB + "#doc/" + encodeURIComponent(name));
      }
    });
})();
</script>
</head>
<body>
<noscript>JavaScript is required to resolve declaration links.</noscript>
</body>
</html>
"""

SITE_CSS = """\
:root {
  --sidebar-w: 290px;
  --fg: #24292e;
  --muted: #6a737d;
  --link: #0366d6;
  --hl: #fff3b0;
  --border: #e1e4e8;
  --bg-alt: #fafbfc;
}
* { box-sizing: border-box; }
html, body { margin: 0; padding: 0; }
body {
  font-family: -apple-system, BlinkMacSystemFont, "Segoe UI", Helvetica, Arial, sans-serif;
  color: var(--fg);
  font-size: 14px;
  line-height: 1.5;
}
body.page {
  display: grid;
  grid-template-columns: var(--sidebar-w) 1fr;
  min-height: 100vh;
}
.sidebar {
  border-right: 1px solid var(--border);
  background: var(--bg-alt);
  position: sticky;
  top: 0;
  height: 100vh;
  overflow-y: auto;
  padding: 0.6em 0.8em;
  font-size: 13px;
}
.sidebar > header {
  font-weight: 600;
  padding-bottom: 0.4em;
  margin-bottom: 0.4em;
  border-bottom: 1px solid var(--border);
}
.sidebar a { color: var(--link); text-decoration: none; }
.sidebar a:hover { text-decoration: underline; }

.tree ul { list-style: none; padding-left: 0.9em; margin: 0; }
.tree > ul { padding-left: 0; }
.tree li { padding: 1px 0; }
.tree li.dir > .label {
  cursor: pointer;
  user-select: none;
  font-weight: 600;
  color: var(--fg);
}
.tree li.dir > .label::before { content: "\\25B8"; display: inline-block; width: 1em; color: var(--muted); }
.tree li.dir.open > .label::before { content: "\\25BE"; }
.tree li.dir > ul { display: none; }
.tree li.dir.open > ul { display: block; }
.tree a.current { background: var(--hl); padding: 0 2px; border-radius: 2px; font-weight: 600; }

.outline { margin-top: 1em; border-top: 1px solid var(--border); padding-top: 0.6em; }
.outline-heading { font-weight: 600; margin-bottom: 0.3em; color: var(--muted); text-transform: uppercase; font-size: 11px; letter-spacing: 0.05em; }
.outline ul { list-style: none; padding: 0; margin: 0; }
.outline li { padding: 0; }
.outline a { display: block; padding: 1px 2px; color: var(--fg); }
.outline a:hover { background: var(--bg-alt); text-decoration: none; }
.outline .kind { color: var(--muted); font-family: ui-monospace, SFMono-Regular, Menlo, monospace; font-size: 11px; margin-right: 0.4em; }
.outline .name { font-family: ui-monospace, SFMono-Regular, Menlo, monospace; }

main { padding: 0.6em 1.2em 2em; min-width: 0; }
main > header { padding: 0.4em 0; border-bottom: 1px solid var(--border); margin-bottom: 0.8em; }
main > header .sep { color: var(--muted); margin: 0 0.4em; }
main code { font-family: ui-monospace, SFMono-Regular, Menlo, monospace; font-size: 0.95em; }
.welcome { max-width: 50em; }
.source { overflow-x: auto; }
.source pre { font-size: 12.5px; line-height: 1.5; margin: 0; }
.highlight :target { background: var(--hl); }
.highlight .lineno { color: var(--muted); padding-right: 0.8em; user-select: none; }
.source a.id { color: inherit; text-decoration: none; border-bottom: 1px dotted #b8d8ff; }
.source a.id:hover { color: var(--link); border-bottom-style: solid; }

@media (max-width: 800px) {
  body.page { grid-template-columns: 1fr; }
  .sidebar { position: static; height: auto; max-height: 50vh; }
}
"""

APP_JS = """\
(function () {
  "use strict";
  var PAGE = window.PAGE || { relpath: null, root: "" };
  var ROOT = PAGE.root || "";

  fetch(ROOT + "tree.json", {cache: "force-cache"})
    .then(function (r) { return r.ok ? r.json() : null; })
    .catch(function () { return null; })
    .then(function (tree) {
      var el = document.getElementById("tree");
      if (el && tree) el.appendChild(renderTree(tree, "", PAGE.relpath || ""));
    });

  if (PAGE.relpath) {
    var declsUrl = ROOT + "decls/" + PAGE.relpath.replace(/\\.lean$/, ".json");
    fetch(declsUrl, {cache: "force-cache"})
      .then(function (r) { return r.ok ? r.json() : null; })
      .catch(function () { return null; })
      .then(function (data) {
        var el = document.getElementById("outline");
        if (el && data) renderOutline(el, data.decls || []);
      });

    fetch(ROOT + "declarations.json", {cache: "force-cache"})
      .then(function (r) { return r.ok ? r.json() : null; })
      .catch(function () { return null; })
      .then(function (decls) { if (decls) linkIdentifiers(decls); });
  }

  function renderTree(node, prefix, current) {
    var ul = document.createElement("ul");
    var entries = Object.keys(node)
      .filter(function (k) { return k !== "__file"; })
      .map(function (k) { return [k, node[k]]; });
    entries.sort(function (a, b) {
      var aDir = a[1] !== null, bDir = b[1] !== null;
      if (aDir !== bDir) return aDir ? -1 : 1;
      return a[0] < b[0] ? -1 : a[0] > b[0] ? 1 : 0;
    });
    for (var i = 0; i < entries.length; i++) {
      var name = entries[i][0], child = entries[i][1];
      var li = document.createElement("li");
      var leanRel = prefix + name + ".lean";
      // A node may be: a leaf file (null), a pure directory (object),
      // or a directory whose same-named .lean file also exists
      // (object with __file: true) — render the latter as both link
      // and expandable.
      var isFile = (child === null) || (child && child.__file === true);
      var hasChildren = (child !== null) && Object.keys(child).some(function (k) { return k !== "__file"; });
      if (!hasChildren) {
        var a = document.createElement("a");
        a.href = ROOT + prefix + name + ".html";
        a.textContent = name;
        if (leanRel === current) a.className = "current";
        li.appendChild(a);
      } else {
        li.className = "dir";
        var label = document.createElement("span");
        label.className = "label";
        if (isFile) {
          var labelLink = document.createElement("a");
          labelLink.href = ROOT + prefix + name + ".html";
          labelLink.textContent = name;
          if (leanRel === current) labelLink.className = "current";
          label.appendChild(labelLink);
        } else {
          label.textContent = name;
        }
        // Clicking the disclosure caret toggles; the link itself navigates.
        label.addEventListener("click", function (li_) {
          return function (ev) {
            if (ev.target.tagName === "A") return;
            li_.classList.toggle("open");
          };
        }(li));
        li.appendChild(label);
        var subPrefix = prefix + name + "/";
        li.appendChild(renderTree(child, subPrefix, current));
        if (current && (current.indexOf(subPrefix) === 0 || leanRel === current)) {
          li.classList.add("open");
        }
      }
      ul.appendChild(li);
    }
    return ul;
  }

  function renderOutline(root, decls) {
    var heading = document.createElement("div");
    heading.className = "outline-heading";
    heading.textContent = "In this file";
    root.appendChild(heading);
    var ul = document.createElement("ul");
    for (var i = 0; i < decls.length; i++) {
      var d = decls[i];
      var li = document.createElement("li");
      var a = document.createElement("a");
      a.href = "#" + d.name;
      a.title = d.name;
      var kind = document.createElement("span");
      kind.className = "kind";
      kind.textContent = d.kind;
      a.appendChild(kind);
      var nm = document.createElement("span");
      nm.className = "name";
      var parts = d.name.split(".");
      nm.textContent = parts[parts.length - 1];
      a.appendChild(nm);
      li.appendChild(a);
      ul.appendChild(li);
    }
    root.appendChild(ul);
  }

  // Walk the highlighted source and turn identifier tokens into links.
  //
  // Pygments' Lean4 lexer splits a dotted name like `Foo.bar.baz` into
  // separate `n` tokens with `bp` dots between them, so we walk the flat
  // span sequence and coalesce `name (. name)*` chains. For each chain
  // we try the longest joined form first, then prefixes, then the bare
  // leading name — taking the first that resolves.
  //
  // Resolution rules:
  //  - Exact key in the local declarations map → link to local source.
  //  - But: skip a *bare* token that's also a namespace prefix in the
  //    local map (e.g. `Jacobian`, which is both the def and the
  //    namespace holding `Jacobian.ofCurve`); almost always the user
  //    means the namespace, not the def.
  //  - Otherwise, if the candidate is dotted and starts with a letter,
  //    route through `find/` — local hits resolve there too, and
  //    everything else falls through to the Mathlib docs.
  //  - Bare unqualified names that aren't in the local map are left
  //    alone (variables, parameters, `open`-imported names).
  function linkIdentifiers(decls) {
    var pre = document.querySelector(".source pre");
    if (!pre) return;
    var nsPrefixes = collectNamespacePrefixes(decls);
    var node = pre.firstChild;
    while (node) {
      if (isNameSpan(node) && hasTextChild(node)) {
        // Build the longest `name (. name)*` chain starting here.
        var spans = [node];
        var parts = [node.textContent];
        var probe = node.nextSibling;
        while (probe && isDotSpan(probe)) {
          var after = probe.nextSibling;
          if (after && isNameSpan(after) && hasTextChild(after)) {
            spans.push(probe, after);
            parts.push(after.textContent);
            probe = after.nextSibling;
          } else {
            break;
          }
        }
        // Try the longest join first, then progressively shorter prefixes.
        var matched = null;
        for (var len = parts.length; len >= 1; len--) {
          var joined = parts.slice(0, len).join(".");
          var href = resolveHref(joined, decls, nsPrefixes);
          if (href) {
            matched = { href: href, len: len, text: joined };
            break;
          }
        }
        if (matched) {
          var endIdx = matched.len * 2 - 2;  // last span index in chain
          var lastWrapped = spans[endIdx];
          var afterChain = lastWrapped.nextSibling;  // before mutation
          var a = document.createElement("a");
          a.href = matched.href;
          a.className = "id";
          a.title = matched.text;
          var parent = node.parentNode;
          for (var k = 0; k <= endIdx; k++) a.appendChild(spans[k]);
          parent.insertBefore(a, afterChain);
          node = afterChain;
          continue;
        }
      }
      node = node.nextSibling;
    }
  }

  function resolveHref(text, decls, nsPrefixes, isJoined) {
    if (!text) return null;
    var dotted = text.indexOf(".") >= 0;
    if (Object.prototype.hasOwnProperty.call(decls, text)) {
      if (!dotted && nsPrefixes[text]) return null;
      return ROOT + decls[text];
    }
    if (dotted && /^[A-Za-z_]/.test(text)) {
      return ROOT + "find/#doc/" + encodeURIComponent(text);
    }
    return null;
  }

  function isNameSpan(n) {
    if (!n || n.nodeType !== 1) return false;
    var c = " " + (n.className || "") + " ";
    return c.indexOf(" n ") >= 0 || c.indexOf(" nf ") >= 0
        || c.indexOf(" nc ") >= 0 || c.indexOf(" nv ") >= 0;
  }
  function isDotSpan(n) {
    if (!n || n.nodeType !== 1) return false;
    if (n.textContent !== ".") return false;
    var c = " " + (n.className || "") + " ";
    return c.indexOf(" bp ") >= 0 || c.indexOf(" o ") >= 0 || c.indexOf(" p ") >= 0;
  }
  function hasTextChild(n) {
    return n.firstChild && n.firstChild.nodeType === 3 && n.textContent;
  }
  function collectNamespacePrefixes(decls) {
    var ns = Object.create(null);
    for (var k in decls) {
      var idx = k.indexOf(".");
      while (idx > 0) {
        ns[k.substring(0, idx)] = true;
        idx = k.indexOf(".", idx + 1);
      }
    }
    return ns;
  }
})();
"""


# ---------------------------------------------------------------------------
# Rendering
# ---------------------------------------------------------------------------

class AnchoredHtmlFormatter(HtmlFormatter):
    """Pygments formatter with `id="L<n>"` line anchors."""

    def _wrap_lineanchors(self, inner):
        s = self.lineanchors
        i = self.linenostart - 1
        for t, line in inner:
            if t:
                i += 1
                yield 1, f'<span id="{s}{i}"></span>' + line
            else:
                yield 0, line


def render_page(src_path: Path, rel: str, formatter: HtmlFormatter,
                decls: list[tuple[str, int, str]], github_url_base: str,
                depth: int) -> str:
    src = src_path.read_text(encoding="utf-8")
    body = highlight(src, Lean4Lexer(), formatter)
    # Place a <span id="<DeclName>"></span> alongside the line marker for
    # the decl's actual line, so jumping to #<DeclName> from the outline
    # or from declarations.json lands on the right line. Multiple decls
    # on the same line share the same line marker.
    by_line: dict[int, list[str]] = {}
    for name, line, _ in decls:
        by_line.setdefault(line, []).append(name)
    for line, names in by_line.items():
        marker = f'<span id="L{line}"></span>'
        injected = "".join(
            f'<span id="{html.escape(n, quote=True)}"></span>' for n in names
        )
        body = body.replace(marker, marker + injected, 1)
    root_rel = "../" * depth
    return PAGE_TPL.format(
        title=rel,
        relpath=html.escape(rel),
        relpath_js=rel.replace("\\", "\\\\").replace('"', '\\"'),
        root_rel=root_rel,
        github_url=f"{github_url_base}/{rel}",
        body=body,
    )


def build_tree(rel_paths_no_ext: list[str]) -> dict:
    """Return a nested dict for the file tree.

    Each entry is one of:
      - ``None``: a file-only leaf with no same-named subdirectory.
      - ``{...}``: a directory.
      - ``{"__file": True, ...}``: both a file (`Foo.lean`) and a directory
        (`Foo/`) exist at this level — common Mathlib-style "module +
        sub-modules" pattern (e.g. `Jacobian/AbelJacobi.lean` alongside
        `Jacobian/AbelJacobi/Defs.lean`). The label should render as
        both a link to the file and an expandable directory.
    """
    root: dict = {}
    for p in rel_paths_no_ext:
        parts = p.split("/")
        cur = root
        for part in parts[:-1]:
            existing = cur.get(part)
            if existing is None and part in cur:
                # Was a file-only leaf; upgrade in place to a dir-with-__file.
                cur[part] = {"__file": True}
            elif part not in cur:
                cur[part] = {}
            cur = cur[part]
        leaf = parts[-1]
        if leaf in cur and isinstance(cur[leaf], dict):
            # Subdirectory already populated; mark that the file also exists.
            cur[leaf]["__file"] = True
        else:
            cur[leaf] = None
    return root


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--src-root", default="Jacobian",
                    help="Directory containing .lean files (relative to repo root).")
    ap.add_argument("--out", required=True, help="Output directory.")
    ap.add_argument("--github-url", default="https://github.com/tangentstorm/JacobianChallenge/blob/main",
                    help="Base URL for the GitHub source link.")
    args = ap.parse_args()

    repo_root = Path(__file__).resolve().parent.parent
    src_root = (repo_root / args.src_root).resolve()
    out_dir = Path(args.out).resolve()
    out_dir.mkdir(parents=True, exist_ok=True)

    formatter = AnchoredHtmlFormatter(
        linenos="inline",
        lineanchors="L",
        nobackground=True,
    )
    (out_dir / "pygments.css").write_text(formatter.get_style_defs(".highlight"), encoding="utf-8")
    (out_dir / "site.css").write_text(SITE_CSS, encoding="utf-8")
    (out_dir / "app.js").write_text(APP_JS, encoding="utf-8")

    decls_dir = out_dir / "decls"
    decls_dir.mkdir(exist_ok=True)

    decls_index: dict[str, str] = {}
    rel_paths: list[str] = []  # without .lean extension
    for src_path in sorted(src_root.rglob("*.lean")):
        rel = src_path.relative_to(repo_root).as_posix()
        rel_no_ext = rel[:-len(".lean")]
        rel_html = rel_no_ext + ".html"
        depth = rel.count("/")

        src_text = src_path.read_text(encoding="utf-8")
        try:
            decls = extract_decls(src_text)
        except Exception as e:  # noqa: BLE001
            print(f"warn: decl scan failed for {rel}: {e}", file=sys.stderr)
            decls = []
        try:
            imports = extract_imports(src_text)
        except Exception as e:  # noqa: BLE001
            print(f"warn: import scan failed for {rel}: {e}", file=sys.stderr)
            imports = []

        for name, _, _ in decls:
            decls_index.setdefault(name, f"{rel_html}#{name}")

        page = render_page(src_path, rel, formatter, decls, args.github_url, depth)
        out_path = out_dir / rel_html
        out_path.parent.mkdir(parents=True, exist_ok=True)
        out_path.write_text(page, encoding="utf-8")

        # Per-file outline / imports JSON.
        per_file = {
            "imports": imports,
            "decls": [{"name": n, "line": ln, "kind": k} for n, ln, k in decls],
        }
        per_file_path = decls_dir / (rel_no_ext + ".json")
        per_file_path.parent.mkdir(parents=True, exist_ok=True)
        per_file_path.write_text(
            json.dumps(per_file, separators=(",", ":")), encoding="utf-8"
        )

        rel_paths.append(rel_no_ext)

    (out_dir / "declarations.json").write_text(
        json.dumps(decls_index, sort_keys=True, separators=(",", ":")),
        encoding="utf-8",
    )

    tree = build_tree(rel_paths)
    (out_dir / "tree.json").write_text(
        json.dumps(tree, sort_keys=True, separators=(",", ":")),
        encoding="utf-8",
    )

    find_dir = out_dir / "find"
    find_dir.mkdir(exist_ok=True)
    (find_dir / "index.html").write_text(FIND_TPL, encoding="utf-8")

    (out_dir / "index.html").write_text(INDEX_TPL, encoding="utf-8")

    print(f"wrote {len(rel_paths)} pages, {len(decls_index)} declarations -> {out_dir}",
          file=sys.stderr)
    return 0


if __name__ == "__main__":
    sys.exit(main())
