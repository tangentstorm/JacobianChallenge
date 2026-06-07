#!/usr/bin/env bash
#
# mini-comparator.sh — a poor-man's stand-in for the official Lean comparator
# (https://github.com/leanprover/comparator).
#
# The comparator checks that each public theorem in `Jacobian.Solution` elaborates
# to the *same kernel-level type* as its `sorry` stub in `Jacobian.Challenge`. When
# CI fails with
#
#     Challenge and solution theorem statement do not match: '<name>'
#
# the two modules' stored types for `<name>` differ structurally. This script
# reproduces that signal locally without building the comparator binary:
#
#   1. For each module (Challenge, Solution) it generates a tiny stub that
#      `import`s that module and prints every listed theorem's *stored* type
#      (read from the environment via `env.find?`, NOT re-elaborated) with
#      `pp.all` so all implicits/instances/universes are explicit.
#   2. It normalises hygienic universe names (`u_1`, `u_2`, …) -> `u#N`, which the
#      official comparator ignores, so pure universe *renaming* never shows as a
#      diff.
#   3. It diffs the two dumps per theorem and reports which match / mismatch.
#
# IMPORTANT: each module is loaded ALONE (one `lake env lean` per module). Loading
# both at once re-resolves instances uniformly and hides exactly the per-module
# difference the comparator catches.
#
# Usage:
#   scripts/mini-comparator.sh                 # compare all theorems in the smoketest config
#   scripts/mini-comparator.sh NAME [NAME...]  # compare only the given fully-qualified names
#   scripts/mini-comparator.sh -v              # also print the full normalised dumps on mismatch
#
# Theorem names default to those in comparator/jacobian-smoketest.json.

set -euo pipefail

REPO_ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$REPO_ROOT"

CHALLENGE_MODULE="Jacobian.Challenge"
SOLUTION_MODULE="Jacobian.Solution"
CONFIG="comparator/jacobian-smoketest.json"

VERBOSE=0
NAMES=()
for arg in "$@"; do
  case "$arg" in
    -v|--verbose) VERBOSE=1 ;;
    -*) echo "unknown flag: $arg" >&2; exit 2 ;;
    *) NAMES+=("$arg") ;;
  esac
done

# Default theorem list from the smoketest config (strip JSON quoting/commas).
# Use a portable `while read` loop rather than `mapfile`, which is absent on the
# bash 3.2 that ships with macOS.
if [ "${#NAMES[@]}" -eq 0 ]; then
  if command -v python3 >/dev/null 2>&1; then
    while IFS= read -r line; do
      [ -n "$line" ] && NAMES+=("$line")
    done < <(python3 -c '
import json,sys
with open(sys.argv[1]) as f: cfg=json.load(f)
print("\n".join(cfg["theorem_names"]))
' "$CONFIG")
  else
    echo "python3 not found and no theorem names given" >&2
    exit 2
  fi
fi

if [ "${#NAMES[@]}" -eq 0 ]; then
  echo "no theorem names to compare" >&2
  exit 2
fi

WORK="$(mktemp -d)"
trap 'rm -rf "$WORK"' EXIT

# Build the `#[`Name1, `Name2, …]` array literal for the Lean stub.
name_array=""
for n in "${NAMES[@]}"; do
  if [ -z "$name_array" ]; then
    name_array="\`$n"
  else
    name_array="$name_array, \`$n"
  fi
done

gen_stub() {
  # $1 = module to import, $2 = output .lean path
  #
  # We emit TWO renderings per theorem:
  #   * a `pp.all` pretty-print (human-readable, but the printer can collapse
  #     genuinely-distinct kernel terms), and
  #   * a RAW structural serialization of the stored `Expr` (constructor tree
  #     with constant names + universe levels), which is what actually decides
  #     the kernel-level (in)equality the official comparator reports.
  # The raw form is authoritative; the pretty form is for eyeballing the diff.
  # Use a QUOTED heredoc so the shell does NOT interpret the Lean body — in
  # particular the backticks in `pp.all`, `Expr`, and the `Name` literals in the
  # `#[...]` array. The import module and the name-array literal are injected
  # afterwards via placeholders (@@IMPORT@@ / @@NAMES@@).
  cat > "$2" <<'STUB_EOF'
import @@IMPORT@@
open Lean Elab Meta

/-- Canonical structural serialization of an `Expr`. Distinguishes terms that
`pp.all` may render identically (e.g. different instance `const`s, differing
universe instantiations). Universe param *names* are left as-is here and
canonicalised downstream by the driver. -/
partial def serLevel : Level → String
  | .zero => "0"
  | .succ l => s!"(S {serLevel l})"
  | .max a b => s!"(max {serLevel a} {serLevel b})"
  | .imax a b => s!"(imax {serLevel a} {serLevel b})"
  | .param n => s!"(p {n})"
  | .mvar m => s!"(?{m.name})"

partial def serExpr : Expr → String
  | .bvar i => s!"(bvar {i})"
  | .fvar f => s!"(fvar {f.name})"
  | .mvar m => s!"(mvar {m.name})"
  | .sort l => s!"(sort {serLevel l})"
  | .const n ls => s!"(const {n} [{String.intercalate "," (ls.map serLevel)}])"
  | .app f a => s!"(app {serExpr f} {serExpr a})"
  | .lam _ t b _ => s!"(lam {serExpr t} {serExpr b})"
  | .forallE _ t b _ => s!"(pi {serExpr t} {serExpr b})"
  | .letE _ t v b _ => s!"(let {serExpr t} {serExpr v} {serExpr b})"
  | .lit (.natVal v) => s!"(litN {v})"
  | .lit (.strVal v) => s!"(litS {v})"
  | .mdata _ e => serExpr e
  | .proj n i e => s!"(proj {n} {i} {serExpr e})"

run_cmd Command.liftTermElabM do
  let names : Array Name := #[@@NAMES@@]
  let env ← getEnv
  for nm in names do
    IO.println s!"===BEGIN {nm}==="
    match env.find? nm with
    | none => IO.println s!"<<MISSING: {nm}>>"
    | some ci =>
      let pp ← withOptions (fun o => o.setBool `pp.all true |>.setBool `pp.universes true) do
        let fmt ← ppExpr ci.type
        pure (toString fmt)
      IO.println "---LEVELPARAMS---"
      IO.println s!"{ci.levelParams}"
      IO.println "---PP---"
      IO.println pp
      IO.println "---RAW---"
      IO.println (serExpr ci.type)
    IO.println s!"===END {nm}==="
STUB_EOF
  # Inject the import module and the name array (sed -i needs a backup arg on BSD;
  # write to a temp and move to stay portable).
  python3 - "$2" "$1" "$name_array" <<'PY'
import sys
path, imp, names = sys.argv[1], sys.argv[2], sys.argv[3]
text = open(path).read()
text = text.replace("@@IMPORT@@", imp).replace("@@NAMES@@", names)
open(path, "w").write(text)
PY
}

# Normalise hygienic universe param names so renaming alone is not a diff.
# pp prints universe params like `u_1`, `u_2`; map each distinct one (in order of
# first appearance) to a stable `u#1`, `u#2`. Done per-file so the two modules use
# the same canonical scheme.
normalise() {
  python3 - "$1" <<'PY'
import re, sys
text = open(sys.argv[1]).read()
seen = {}
def repl(m):
    name = m.group(0)
    if name not in seen:
        seen[name] = f"u#{len(seen)+1}"
    return seen[name]
# match universe params: u_<digits> (and the common single-letter u/v with .{...})
text = re.sub(r'\bu_\d+\b', repl, text)
sys.stdout.write(text)
PY
}

CH_RAW="$WORK/challenge.lean"
SO_RAW="$WORK/solution.lean"
gen_stub "$CHALLENGE_MODULE" "$CH_RAW"
gen_stub "$SOLUTION_MODULE" "$SO_RAW"

echo "==> building $CHALLENGE_MODULE and $SOLUTION_MODULE ..." >&2
lake build "$CHALLENGE_MODULE" "$SOLUTION_MODULE"

run_dump() {
  # $1 = module name, $2 = generated Lean stub, $3 = stdout path, $4 = stderr path
  local module="$1"
  local stub="$2"
  local out="$3"
  local err="$4"
  if ! lake env lean "$stub" > "$out" 2> "$err"; then
    echo "lake env lean failed on $module:" >&2
    if [ -s "$err" ]; then
      echo "--- stderr ---" >&2
      cat "$err" >&2
    fi
    if [ -s "$out" ]; then
      echo "--- stdout ---" >&2
      cat "$out" >&2
    fi
    exit 1
  fi
}

echo "==> dumping $CHALLENGE_MODULE ..." >&2
run_dump "$CHALLENGE_MODULE" "$CH_RAW" "$WORK/challenge.out" "$WORK/challenge.err"
echo "==> dumping $SOLUTION_MODULE ..." >&2
run_dump "$SOLUTION_MODULE" "$SO_RAW" "$WORK/solution.out" "$WORK/solution.err"

normalise "$WORK/challenge.out" > "$WORK/challenge.norm"
normalise "$WORK/solution.out" > "$WORK/solution.norm"

# Split a dump into per-theorem block files.
split_blocks() {
  # $1 = dump, $2 = output dir
  python3 - "$1" "$2" <<'PY'
import re, sys, os
text = open(sys.argv[1]).read()
outdir = sys.argv[2]
os.makedirs(outdir, exist_ok=True)
for m in re.finditer(r'===BEGIN (.+?)===\n(.*?)\n===END \1===', text, re.S):
    name, body = m.group(1), m.group(2)
    with open(os.path.join(outdir, name + ".block"), "w") as f:
        f.write(body.strip() + "\n")
PY
}

# LITERAL blocks (universe names intact) — this is what the real comparator
# compares: it diffs the whole `ConstantVal`, universe-parameter *names* and all.
split_blocks "$WORK/challenge.out" "$WORK/ch"
split_blocks "$WORK/solution.out" "$WORK/so"
# NORMALISED blocks (universe names canonicalised) — used only to classify a
# literal mismatch as "universe-name-only" vs a genuine structural difference.
split_blocks "$WORK/challenge.norm" "$WORK/chn"
split_blocks "$WORK/solution.norm" "$WORK/son"

echo
echo "mini-comparator: $CHALLENGE_MODULE  vs  $SOLUTION_MODULE"
echo "(literal ConstantVal comparison — matches the real comparator,"
echo " which does NOT ignore universe-parameter names)"
echo "------------------------------------------------------------"

fail=0
for n in "${NAMES[@]}"; do
  chf="$WORK/ch/$n.block"
  sof="$WORK/so/$n.block"
  if [ ! -f "$chf" ]; then echo "  MISSING in Challenge : $n"; fail=1; continue; fi
  if [ ! -f "$sof" ]; then echo "  MISSING in Solution  : $n"; fail=1; continue; fi
  if diff -q "$chf" "$sof" >/dev/null; then
    printf "  MATCH    %s\n" "$n"
  else
    # Classify: structural (universe-name-insensitive) or a real difference?
    if diff -q "$WORK/chn/$n.block" "$WORK/son/$n.block" >/dev/null; then
      printf "  MISMATCH %s  (universe-name-only: structurally identical)\n" "$n"
    else
      printf "  MISMATCH %s  (structural difference)\n" "$n"
    fi
    fail=1
    if [ "$VERBOSE" -eq 1 ]; then
      echo "    --- per-line diff (< Challenge / > Solution) ---"
      diff "$chf" "$sof" | sed 's/^/    /'
      echo "    -----------------------------------------------"
    fi
  fi
done

echo "------------------------------------------------------------"
if [ "$fail" -eq 0 ]; then
  echo "ALL MATCH ✓"
else
  echo "MISMATCHES FOUND ✗  (re-run with -v to see the diff)"
fi
exit "$fail"
