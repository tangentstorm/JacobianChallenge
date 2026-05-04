"""Build a browsable, syntax-highlighted HTML view of the project's Lean
sources, plus a doc-gen4-compatible `find/#doc/<DeclName>` redirector so
the blueprint's `\\lean{...}` annotations resolve.

Output layout (relative to OUT_DIR, which the Pages workflow mounts at
`<dochome>` = `/docs/`):

    index.html                     -- file tree
    declarations.json              -- {fully-qualified decl name: relative URL}
    find/index.html                -- JS redirector (local or mathlib4_docs fallback)
    pygments.css                   -- shared stylesheet
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
# Match a top-level decl: optional attributes + modifiers + keyword + name.
# `instance` may have no name; we accept that and skip those.
DECL_RE = re.compile(
    rf"^\s*(?:@\[[^\]]*\]\s*)*(?:{MOD_KW}\s+)*(?P<kw>{DECL_KW})\s+"
    rf"(?:\{{[^}}]*\}}\s*)?"
    rf"(?P<name>[A-Za-z_][A-Za-z0-9_'.]*)"
)
NAMESPACE_RE = re.compile(r"^\s*namespace\s+([A-Za-z_][A-Za-z0-9_'.]*)")
END_RE = re.compile(r"^\s*end(?:\s+([A-Za-z_][A-Za-z0-9_'.]*))?\s*$")


def strip_comments(src: str) -> str:
    """Drop `--` line comments and `/- ... -/` block comments (with nesting)."""
    out: list[str] = []
    i, n = 0, len(src)
    depth = 0
    while i < n:
        if depth == 0 and src.startswith("--", i):
            j = src.find("\n", i)
            if j < 0:
                break
            i = j  # keep the newline
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
            # preserve newlines so line numbers in our scanner stay aligned
            out.append("\n" if src[i] == "\n" else " ")
            i += 1
            continue
        out.append(src[i])
        i += 1
    return "".join(out)


def extract_decls(src: str) -> list[tuple[str, int]]:
    """Return [(fully_qualified_name, 1-based line number), ...]."""
    cleaned = strip_comments(src)
    ns_stack: list[str] = []
    out: list[tuple[str, int]] = []
    for lineno, line in enumerate(cleaned.splitlines(), start=1):
        m = NAMESPACE_RE.match(line)
        if m:
            # `namespace A.B` opens A, then B; track as one frame for clean pops.
            ns_stack.append(m.group(1))
            continue
        m = END_RE.match(line)
        if m:
            label = m.group(1)
            if label is None:
                # bare `end` closes a section (which we don't track) or a namespace
                # whose `namespace` form was anonymous (rare). Leave the stack alone.
                pass
            else:
                # pop frames until we drop one whose tail matches `label`.
                while ns_stack:
                    top = ns_stack.pop()
                    if top == label or top.endswith("." + label) or top.split(".")[-1] == label:
                        break
            continue
        m = DECL_RE.match(line)
        if m:
            name = m.group("name")
            if name.startswith("_root_."):
                qual = name[len("_root_."):]
            else:
                ns = ".".join(ns_stack)
                qual = f"{ns}.{name}" if ns else name
            out.append((qual, lineno))
    return out


PAGE_TPL = """<!doctype html>
<html lang="en">
<head>
<meta charset="utf-8">
<title>{title}</title>
<link rel="stylesheet" href="{css_rel}">
<style>
  body {{ font-family: -apple-system, BlinkMacSystemFont, "Segoe UI", sans-serif; margin: 0; }}
  header {{ padding: 0.6em 1em; background: #f5f5f5; border-bottom: 1px solid #ddd; }}
  header a {{ text-decoration: none; color: #0366d6; }}
  main {{ padding: 0 1em; }}
  .highlight pre {{ font-size: 13px; line-height: 1.45; }}
  .highlight .lineno {{ color: #999; padding-right: 0.8em; user-select: none; }}
  .highlight :target {{ background: #fff3b0; }}
</style>
</head>
<body>
<header>
  <a href="{root_rel}">browsable source</a> /
  <code>{relpath}</code>
  &middot; <a href="{github_url}">view on GitHub</a>
</header>
<main>
{body}
</main>
</body>
</html>
"""


INDEX_TPL = """<!doctype html>
<html lang="en">
<head>
<meta charset="utf-8">
<title>{title}</title>
<style>
  body {{ font-family: -apple-system, BlinkMacSystemFont, "Segoe UI", sans-serif;
          max-width: 60em; margin: 2em auto; padding: 0 1em; }}
  h1 {{ font-size: 1.4em; }}
  ul {{ list-style: none; padding-left: 1.2em; }}
  li.dir > span {{ font-weight: 600; }}
  a {{ text-decoration: none; color: #0366d6; }}
  a:hover {{ text-decoration: underline; }}
  code {{ font-size: 0.95em; }}
</style>
</head>
<body>
<h1>{title}</h1>
<p>Syntax-highlighted view of the Lean sources in this repository.
Identifier links from the <a href="../blueprint/">blueprint</a> resolve through
<code>find/#doc/&lt;Name&gt;</code>; unknown names fall through to
<a href="https://leanprover-community.github.io/mathlib4_docs/">mathlib4_docs</a>.</p>
{tree}
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
  // Accepted forms: "#doc/Foo.bar", "#Foo.bar", "?pattern=Foo.bar".
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
<noscript>JavaScript is required to resolve declaration links. The target name
appears in the URL fragment.</noscript>
</body>
</html>
"""


class AnchoredHtmlFormatter(HtmlFormatter):
    """Pygments formatter with `id="L<n>"` line anchors and clickable line numbers."""

    def __init__(self, **opts):
        super().__init__(**opts)

    def _wrap_lineanchors(self, inner):
        # Override: emit <span id="L1">...</span> wrappers so anchors land
        # exactly on the line, not on the table cell.
        s = self.lineanchors
        i = self.linenostart - 1
        for t, line in inner:
            if t:
                i += 1
                yield 1, f'<span id="{s}{i}"></span>' + line
            else:
                yield 0, line


def render_page(src_path: Path, rel: str, formatter: HtmlFormatter,
                decls: list[tuple[str, int]], github_url_base: str,
                depth: int) -> str:
    src = src_path.read_text(encoding="utf-8")
    body = highlight(src, Lean4Lexer(), formatter)
    # Inject decl-name anchors so `#<DeclName>` jumps even if the lookup
    # JS is bypassed (e.g. someone hand-types the URL).
    anchor_html = "".join(
        f'<span id="{html.escape(name, quote=True)}"></span>'
        for name, _ in decls
    )
    body = anchor_html + body
    css_rel = "../" * depth + "pygments.css"
    root_rel = "../" * depth + "index.html"
    return PAGE_TPL.format(
        title=rel,
        relpath=html.escape(rel),
        css_rel=css_rel,
        root_rel=root_rel,
        github_url=f"{github_url_base}/{rel}",
        body=body,
    )


def build_tree(rel_paths: list[str]) -> str:
    """Render an HTML <ul> tree of files, sorted, dirs before files."""
    root: dict = {}
    for p in rel_paths:
        parts = p.split("/")
        cur = root
        for part in parts[:-1]:
            cur = cur.setdefault(part, {})
        cur[parts[-1]] = None  # leaf

    def walk(node: dict, prefix: str) -> str:
        items = sorted(node.items(), key=lambda kv: (kv[1] is None, kv[0]))
        out = ["<ul>"]
        for name, child in items:
            if child is None:
                href = html.escape(prefix + name + ".html", quote=True)
                out.append(f'<li><a href="{href}"><code>{html.escape(name)}</code></a></li>')
            else:
                out.append(f'<li class="dir"><span>{html.escape(name)}/</span>')
                out.append(walk(child, prefix + name + "/"))
                out.append("</li>")
        out.append("</ul>")
        return "\n".join(out)

    return walk(root, "")


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

    decls_index: dict[str, str] = {}
    rel_paths: list[str] = []
    for src_path in sorted(src_root.rglob("*.lean")):
        rel = src_path.relative_to(repo_root).as_posix()  # e.g. Jacobian/Foo/Bar.lean
        rel_html = rel[:-len(".lean")] + ".html"
        depth = rel.count("/")  # for ../ to root

        try:
            decls = extract_decls(src_path.read_text(encoding="utf-8"))
        except Exception as e:  # noqa: BLE001
            print(f"warn: decl scan failed for {rel}: {e}", file=sys.stderr)
            decls = []

        for name, lineno in decls:
            # First occurrence wins; later duplicates (e.g. open-namespace re-exports)
            # are ignored. Anchor by name if present in the page; otherwise line.
            decls_index.setdefault(name, f"{rel_html}#{name}")
            # Also expose the line-anchor form, so a URL like `#L42` works.

        page = render_page(src_path, rel, formatter, decls, args.github_url, depth)
        out_path = out_dir / rel_html
        out_path.parent.mkdir(parents=True, exist_ok=True)
        out_path.write_text(page, encoding="utf-8")
        rel_paths.append(rel[:-len(".lean")])  # without extension, for tree

    (out_dir / "declarations.json").write_text(
        json.dumps(decls_index, sort_keys=True, indent=0, separators=(",", ":")),
        encoding="utf-8",
    )

    find_dir = out_dir / "find"
    find_dir.mkdir(exist_ok=True)
    (find_dir / "index.html").write_text(FIND_TPL, encoding="utf-8")

    tree_html = build_tree(rel_paths)
    (out_dir / "index.html").write_text(
        INDEX_TPL.format(title="Jacobian Challenge — source", tree=tree_html),
        encoding="utf-8",
    )

    print(f"wrote {len(rel_paths)} pages, {len(decls_index)} declarations -> {out_dir}",
          file=sys.stderr)
    return 0


if __name__ == "__main__":
    sys.exit(main())
