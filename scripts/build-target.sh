#!/usr/bin/env bash
# Narrow-build wrapper — the ONLY sanctioned `lake build` for inner-loop work.
#
# Builds exactly the module(s) listed in `.sci/target-file` (one per line,
# `#` comments allowed). This file names your assigned narrow build target,
# e.g. `Jacobian.HolomorphicForms.GenusZeroUniformization`. It is set during
# task planning and checked at task approval; update it when your task moves
# to a different module.
#
#   bash scripts/build-target.sh                # narrow build (inner loop)
#   bash scripts/build-target.sh --integration  # full Jacobian.Solution build
#                                               # (ONLY at integration, once)
#
# Why: per-worker full builds are the swarm's scarcest resource. A narrow
# build recompiles your module + its few importers instead of the world.
# See rules/workflow-guide.md ("Build NARROW, not the whole solution").
set -euo pipefail

root="$(git rev-parse --show-toplevel)"
cd "$root"

if [[ "${1:-}" == "--integration" ]]; then
  echo "[build-target] INTEGRATION build: lake build Jacobian.Solution" >&2
  exec lake build Jacobian.Solution
fi

tf="$root/.sci/target-file"
if [[ ! -f "$tf" ]]; then
  {
    echo "ERROR: $tf not found."
    echo "Create it with your assigned narrow build target, e.g.:"
    echo "  echo 'Jacobian.HolomorphicForms.RiemannRoch' > .sci/target-file"
    echo "It should name the module your current task edits (see .sci/task.md)."
  } >&2
  exit 1
fi

# Strip comments/blank lines.
mapfile -t targets < <(sed -e 's/#.*$//' -e 's/^[[:space:]]*//' -e 's/[[:space:]]*$//' "$tf" | grep -v '^$')

if [[ ${#targets[@]} -eq 0 ]]; then
  echo "ERROR: $tf is empty — put your narrow build target in it." >&2
  exit 1
fi

for t in "${targets[@]}"; do
  if [[ "$t" == "Jacobian.Solution" || "$t" == "Jacobian" ]]; then
    echo "ERROR: '$t' is not a narrow target. Full builds run ONLY at" >&2
    echo "integration via: bash scripts/build-target.sh --integration" >&2
    exit 1
  fi
done

echo "[build-target] narrow build: lake build ${targets[*]}" >&2
exec lake build "${targets[@]}"
