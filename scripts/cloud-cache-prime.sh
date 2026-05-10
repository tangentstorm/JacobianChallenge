#!/bin/bash
# SessionStart hook for Claude Code cloud sessions.
# Runs after the repo is cloned but before the agent's first turn.
# Primes the Mathlib precompiled olean cache so the agent doesn't have to
# spend hours compiling Mathlib from source.
#
# No-op locally; the env var CLAUDE_CODE_REMOTE=true is set only in cloud
# sessions.

if [ "$CLAUDE_CODE_REMOTE" != "true" ]; then
  exit 0
fi

# The cloud env's setup script is responsible for installing elan and the
# pinned Lean toolchain into /usr/local/bin. This hook just fetches Mathlib
# oleans into .lake/packages/mathlib/.lake/build/lib/.

if [ ! -f lake-manifest.json ]; then
  echo "cloud-cache-prime: no lake-manifest.json — skipping"
  exit 0
fi

if ! grep -q '"name": "mathlib"' lake-manifest.json; then
  echo "cloud-cache-prime: project doesn't depend on Mathlib — skipping"
  exit 0
fi

echo "cloud-cache-prime: fetching Mathlib precompiled olean cache..."
lake exe cache get || {
  echo "cloud-cache-prime: lake exe cache get failed; Mathlib will compile from source"
  exit 0
}
echo "cloud-cache-prime: done"
