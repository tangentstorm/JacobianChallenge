#!/usr/bin/env python3
"""Inject the Plain-English toggle button + JS into every generated
blueprint HTML page.

Plastex doesn't (out of the box) support adding an arbitrary script
or DOM element to its HTML output, so we post-process the files
directly. The injection idempotently inserts a `<div id="layman-toggle">`
button + a small `<script>` immediately after the opening `<body>` tag.

The button toggles a `hide-layman` class on `<body>` and persists the
choice in `localStorage` so a reader's preference sticks across pages
and reloads. Default is visible.

Usage:
    python3 inject-layman-toggle.py path/to/blueprint/web

Idempotent — safe to run multiple times.
"""

from __future__ import annotations

import re
import sys
from pathlib import Path

INJECTION_HTML = """\
<div id="layman-toggle">
  <button type="button" aria-pressed="true"
          onclick="(function(b){var hide=b.classList.toggle('hide-layman');try{localStorage.setItem('hideLayman',hide);}catch(e){}var btn=document.querySelector('#layman-toggle button');if(btn){btn.setAttribute('aria-pressed',!hide);btn.textContent=hide?'Show Plain English':'Hide Plain English';}})(document.body)">
    Hide Plain English
  </button>
</div>
<script>
(function(){
  try {
    if (localStorage.getItem('hideLayman') === 'true') {
      document.body.classList.add('hide-layman');
      var btn = document.querySelector('#layman-toggle button');
      if (btn) { btn.setAttribute('aria-pressed','false'); btn.textContent='Show Plain English'; }
    }
  } catch (e) {}
})();
</script>
"""

# Marker we add so we can detect prior injection and avoid double-inserting.
MARKER = "<!-- LAYMAN-TOGGLE-INJECTED -->"


def inject(html: str) -> str:
    if MARKER in html:
        return html  # already injected
    # Insert immediately after the opening <body...> tag (any attributes).
    pattern = re.compile(r"(<body\b[^>]*>)", re.IGNORECASE)
    return pattern.sub(rf"\1\n{MARKER}\n{INJECTION_HTML}", html, count=1)


def main(argv: list[str]) -> int:
    if len(argv) != 2:
        print(f"usage: {argv[0]} <web-output-dir>", file=sys.stderr)
        return 2
    root = Path(argv[1])
    if not root.is_dir():
        print(f"error: not a directory: {root}", file=sys.stderr)
        return 1
    n_changed = 0
    for html_path in root.rglob("*.html"):
        original = html_path.read_text(encoding="utf-8")
        updated = inject(original)
        if updated != original:
            html_path.write_text(updated, encoding="utf-8")
            n_changed += 1
    print(f"inject-layman-toggle: injected into {n_changed} HTML files under {root}")
    return 0


if __name__ == "__main__":
    sys.exit(main(sys.argv))
