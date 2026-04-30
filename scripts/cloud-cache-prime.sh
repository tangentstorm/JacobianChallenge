#!/bin/bash
# SessionStart hook for Claude Code cloud sessions.
# Runs after the repo is cloned but before the agent's first turn.
# Primes the Mathlib precompiled olean cache so the agent doesn't have to
# spend hours compiling Mathlib from source.
#
# No-op locally; the env var CLAUDE_CODE_REMOTE=true is set only in cloud
# sessions.

set -euo pipefail

if [ "${CLAUDE_CODE_REMOTE:-}" != "true" ]; then
  exit 0
fi

echo "cloud-cache-prime: starting (cwd=$(pwd))"

if [ ! -f lake-manifest.json ]; then
  echo "cloud-cache-prime: ERROR no lake-manifest.json in $(pwd) — agent will see this in the env summary." >&2
  exit 1
fi

if ! grep -q '"name": "mathlib"' lake-manifest.json; then
  echo "cloud-cache-prime: project doesn't depend on Mathlib — skipping"
  exit 0
fi

# Make sure lean and lake are available.
for bin in lean lake; do
  if ! command -v "$bin" >/dev/null 2>&1; then
    echo "cloud-cache-prime: ERROR \`$bin\` not on PATH. Setup script broken." >&2
    exit 1
  fi
done
lean --version
lake --version

# Step 1: ensure Mathlib's source is fetched. `lake exe cache get` requires
# .lake/packages/mathlib/ to exist — without `lake update`, lake will lazily
# clone it on the first build, but we want the source in place BEFORE we
# fetch the precompiled olean cache.
echo "cloud-cache-prime: running \`lake update\` to fetch dependencies..."
lake update

# Step 2: fetch the precompiled olean cache. This is fast (~30s) when it
# works; if it fails we want to know loudly, not silently fall back to a
# multi-hour from-source compile.
echo "cloud-cache-prime: fetching Mathlib precompiled olean cache..."
if ! lake exe cache get; then
  echo "cloud-cache-prime: ERROR \`lake exe cache get\` failed. Agent should report this rather than waiting for a from-source Mathlib build." >&2
  exit 1
fi

# Step 3: confirm the cache actually landed. If the cache server returned
# zero files (e.g. Mathlib commit not in the cache), the previous step may
# have exited 0 anyway — verify by measuring the olean tree.
mathlib_lib=".lake/packages/mathlib/.lake/build/lib"
if [ ! -d "$mathlib_lib" ]; then
  echo "cloud-cache-prime: ERROR $mathlib_lib does not exist after \`lake exe cache get\` — cache prime did not land." >&2
  exit 1
fi
size=$(du -sh "$mathlib_lib" 2>/dev/null | cut -f1 || echo "?")
file_count=$(find "$mathlib_lib" -name '*.olean' 2>/dev/null | wc -l)
echo "cloud-cache-prime: ✅ done (Mathlib olean cache = $size, $file_count .olean files)"
if [ "$file_count" -lt 100 ]; then
  echo "cloud-cache-prime: WARNING only $file_count olean files cached — expected several thousand. The agent may still have to compile most of Mathlib from source." >&2
fi
