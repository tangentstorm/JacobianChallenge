#!/bin/bash
# scripts/build-blueprint.sh
# One-shot local build of the Lean Blueprint HTML site.
#
# Runs the canonical leanblueprint web build, then re-applies the four
# post-processing inject scripts IN ORDER, then verifies that each injection
# actually landed on the expected number of pages. A bare `leanblueprint web`
# rebuild regenerates every HTML file from scratch and silently drops the
# injected extras (Plain-English toggle, light/dark/system theme picker,
# collapsible dependency-graph view) — so the inject + verify steps are not
# optional. This wrapper fails loudly if any step under-applies, instead of
# leaving you with a site that's missing its extras.
#
# Usage:
#   scripts/build-blueprint.sh
#
# Output lands in blueprint/web/ (gitignored). Open blueprint/web/index.html.

set -euo pipefail

REPO_ROOT="$(git rev-parse --show-toplevel 2>/dev/null)"
if [ -z "$REPO_ROOT" ]; then
  echo "error: not inside the JacobianChallenge git repo" >&2
  exit 1
fi
cd "$REPO_ROOT"

SRC="blueprint/src"
WEB="blueprint/web"

# --- TeX on PATH ------------------------------------------------------------
# plasTeX needs kpsewhich (to resolve the cross-directory \input{../../tex/...}
# paths) and pdflatex (for equation imaging). MacTeX/basictex installs to
# /Library/TeX/texbin, which is not always on a non-login shell's PATH.
if [ -d /Library/TeX/texbin ]; then
  export PATH="/Library/TeX/texbin:$PATH"
fi
# plastexdepgraph drives graphviz (`dot`, `tred`) for the dependency graph.
# Homebrew installs these to /opt/homebrew/bin (Apple Silicon) or
# /usr/local/bin (Intel), which a non-login shell may not have on PATH.
for d in /opt/homebrew/bin /usr/local/bin; do
  if [ -d "$d" ]; then export PATH="$d:$PATH"; fi
done
if ! command -v dot >/dev/null 2>&1; then
  echo "error: graphviz 'dot'/'tred' not found — required for the dependency" >&2
  echo "       graph. Install with: brew install graphviz" >&2
  exit 1
fi
if ! command -v kpsewhich >/dev/null 2>&1; then
  echo "error: kpsewhich not found — a TeX distribution (e.g. basictex) is" >&2
  echo "       required so plasTeX can resolve \\input paths. Install with:" >&2
  echo "         brew install --cask basictex   # then restart your shell" >&2
  exit 1
fi

# --- Python with leanblueprint --------------------------------------------
# leanblueprint is typically installed in a venv, not the system python3 that
# /Library/TeX/texbin or /usr/bin may resolve to. Find an interpreter that can
# actually import it so the wrapper works standalone (no manual `activate`).
PY=python3
if ! "$PY" -c "import leanblueprint" >/dev/null 2>&1; then
  found=""
  for cand in "${VIRTUAL_ENV:+$VIRTUAL_ENV/bin/python3}" \
              "$HOME/.venv/bin/python3" \
              "$REPO_ROOT/.venv/bin/python3"; do
    if [ -n "$cand" ] && [ -x "$cand" ] && \
       "$cand" -c "import leanblueprint" >/dev/null 2>&1; then
      found="$cand"
      break
    fi
  done
  if [ -z "$found" ]; then
    echo "error: leanblueprint not importable by '$PY' and no venv found." >&2
    echo "       Install it, or activate the venv that has it, e.g.:" >&2
    echo "         source ~/.venv/bin/activate" >&2
    exit 1
  fi
  PY="$found"
  # leanblueprint.client shells out to the bare `plastex` console script, so
  # the interpreter's bin/ must be on PATH too — not just the python3 binary.
  export PATH="$(dirname "$PY"):$PATH"
  echo "==> using leanblueprint from: $PY"
fi

# --- 1. Build ---------------------------------------------------------------
echo "==> [1/3] Building blueprint web site (leanblueprint web)"
# Capture output so we can surface unresolved-label errors as a hard failure;
# plasTeX itself exits 0 even when labels don't resolve.
build_log="$(mktemp)"
trap 'rm -f "$build_log"' EXIT
( cd "$SRC" && "$PY" -m leanblueprint.client web ) 2>&1 | tee "$build_log"

if grep -qiE "could not be resolved" "$build_log"; then
  echo "" >&2
  echo "error: blueprint build reported unresolved labels (see above)." >&2
  echo "       Fix the dangling \\ref/\\uses before relying on the site." >&2
  exit 1
fi

# --- 2. Inject (order matters) ---------------------------------------------
echo "==> [2/3] Injecting post-processing extras"
"$PY" "$SRC/inject-layman-toggle.py"      "$WEB"
"$PY" "$SRC/inject-theme-toggle.py"       "$WEB"
"$PY" "$SRC/inject-depgraph-extras.py"    "$WEB"
"$PY" "$SRC/build_collapsible_dep_graph.py" "$WEB"

# --- 3. Verify --------------------------------------------------------------
# A correct build injects each per-page marker into (almost) every page. If a
# rebuild→inject ordering bug under-applies, the counts collapse to 0/1 — catch
# that here rather than discovering it by eye in the browser.
echo "==> [3/3] Verifying injections"

total_pages="$(find "$WEB" -maxdepth 1 -name '*.html' | wc -l | tr -d ' ')"
# Most pages get the toggles; the dep-graph pages and a couple of generated
# stubs are the only legitimate misses, so require a comfortable supermajority.
min_pages=$(( total_pages * 3 / 4 ))

fail=0
check_marker () {
  local label="$1" marker="$2" min="$3"
  local n
  n="$(grep -l "$marker" "$WEB"/*.html 2>/dev/null | wc -l | tr -d ' ')"
  if [ "$n" -lt "$min" ]; then
    echo "  FAIL: $label injected on only $n/$total_pages pages (expected >= $min)" >&2
    fail=1
  else
    echo "  ok:   $label on $n/$total_pages pages"
  fi
}

check_marker "Plain-English toggle" "<!-- LAYMAN-TOGGLE-INJECTED -->"   "$min_pages"
check_marker "theme picker"         "<!-- THEME-TOGGLE-INJECTED -->"    "$min_pages"
check_marker "collapsible nav link" "dep_graph_collapsible"             "$min_pages"

# Artifacts that must exist outright.
for f in "$WEB/index.html" "$WEB/dep_graph_document.html" \
         "$WEB/dep_graph_collapsible.html" "$WEB/styles/extra_styles.css"; do
  if [ ! -s "$f" ]; then
    echo "  FAIL: missing or empty artifact: $f" >&2
    fail=1
  fi
done
# The theme picker / collapsible styles live in extra_styles.css; index must link it.
if ! grep -q "extra_styles.css" "$WEB/index.html"; then
  echo "  FAIL: index.html does not link styles/extra_styles.css" >&2
  fail=1
fi

if [ "$fail" -ne 0 ]; then
  echo "" >&2
  echo "error: blueprint post-processing under-applied (see FAILs above)." >&2
  exit 1
fi

echo ""
echo "Blueprint built: $WEB/index.html"
echo "  open $WEB/index.html"
