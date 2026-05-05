#!/usr/bin/env python3
"""Inject a 3-way light/dark/system theme toggle into every blueprint
page.  The toggle stores its choice in localStorage and applies it via
`<html data-theme="dark"|"light">`; CSS in `extra_styles.css` keys all
dark rules off `[data-theme="dark"]` (explicit) plus `@media
(prefers-color-scheme: dark)` (system, when no explicit choice).

Idempotent — second run is a no-op (marker check).

Usage:
    python blueprint/src/inject-theme-toggle.py blueprint/web
"""
from __future__ import annotations

import sys
from pathlib import Path

MARKER = "<!-- THEME-TOGGLE-INJECTED -->"

# Inline script that runs early (set the data-theme attribute before
# render to avoid a flash of wrong theme), plus the toggle widget HTML
# and the click-handler script.

EARLY_SCRIPT = """\
<script>
(function () {
  var KEY = "jc-blueprint-theme";
  var v = localStorage.getItem(KEY) || "system";
  if (v === "light" || v === "dark") document.documentElement.setAttribute("data-theme", v);
})();
</script>
"""

WIDGET_HTML = """\
<div id="theme-toggle">
  <button id="theme-toggle-btn" type="button" title="Theme: cycle light / dark / system">◐ System</button>
</div>
"""

LATE_SCRIPT = """\
<script>
(function () {
  var KEY = "jc-blueprint-theme";
  var NEXT = { system: "light", light: "dark", dark: "system" };
  var LABEL = { system: "◐ System", light: "☀ Light", dark: "☾ Dark" };
  function get() { return localStorage.getItem(KEY) || "system"; }
  function apply(v) {
    if (v === "light" || v === "dark") document.documentElement.setAttribute("data-theme", v);
    else document.documentElement.removeAttribute("data-theme");
  }
  function update() {
    var b = document.getElementById("theme-toggle-btn");
    if (!b) return;
    var v = get();
    b.textContent = LABEL[v] || LABEL.system;
    b.title = "Theme: " + v + " — click to cycle";
  }
  function set(v) { localStorage.setItem(KEY, v); apply(v); update(); }
  document.addEventListener("DOMContentLoaded", function () {
    update();
    var b = document.getElementById("theme-toggle-btn");
    if (b) b.addEventListener("click", function () { set(NEXT[get()]); });
  });
})();
</script>
"""


def inject(html: str) -> str:
    if MARKER in html:
        return html
    # Insert the early script immediately after <head> so it runs before paint.
    if "<head>" in html:
        html = html.replace("<head>", "<head>\n" + EARLY_SCRIPT.strip(), 1)
    # Insert the widget + late script immediately before </body>.
    if "</body>" in html:
        injection = WIDGET_HTML.strip() + "\n" + LATE_SCRIPT.strip() + "\n" + MARKER + "\n"
        html = html.replace("</body>", injection + "</body>", 1)
    return html


def main(argv: list[str]) -> int:
    if len(argv) != 2:
        print(f"usage: {argv[0]} <web-dir>", file=sys.stderr)
        return 2
    web = Path(argv[1])
    if not web.is_dir():
        print(f"error: not a directory: {web}", file=sys.stderr)
        return 1
    n = 0
    for path in sorted(web.glob("*.html")):
        text = path.read_text(encoding="utf-8")
        new = inject(text)
        if new != text:
            path.write_text(new, encoding="utf-8")
            n += 1
    print(f"inject-theme-toggle: updated {n} files under {web}")
    return 0


if __name__ == "__main__":
    sys.exit(main(sys.argv))
