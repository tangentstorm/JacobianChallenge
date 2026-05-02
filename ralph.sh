#!/usr/bin/env bash
# ralph.sh — autonomous codex loop for JacobianChallenge
#
# Inspired by https://github.com/snarktank/ralph
# - reads tasks from a newline-separated text file
# - each iteration: pick first non-done task, spawn `codex exec`, push if it
#   committed, mark the task done on push, append to progress log, repeat
# - stops when all tasks are done, MAX_ITERS reached, or `.ralph-stop` exists
#
# Usage:
#   ./ralph.sh                                 # uses ralph-polygonal-model.txt, 10 iters
#   ./ralph.sh ralph-polygonal-model.txt       # explicit task file
#   ./ralph.sh ralph-polygonal-model.txt 20    # explicit task file + max iters
#
# Stop early: `touch .ralph-stop` from another shell.
#
# Tasks file format (one per line):
#   # comments OK
#   <task description, used verbatim as part of the codex prompt>
#   DONE: <task>      # automatically prefixed by ralph after a successful iter
#
# Memory: ralph-progress.txt accumulates per-iter notes; git history is the
# real persistence layer. Each `codex exec` runs with clean context — the
# script feeds it just the prompt, the working directory, and the conventions.

set -euo pipefail

TASK_FILE="${1:-ralph-polygonal-model.txt}"
MAX_ITERS="${2:-10}"

if [[ ! -f "$TASK_FILE" ]]; then
  echo "ralph: task file '$TASK_FILE' not found" >&2
  exit 1
fi

if ! command -v codex >/dev/null 2>&1; then
  echo "ralph: 'codex' CLI not on PATH" >&2
  exit 1
fi

PROGRESS=ralph-progress.txt
LOG_DIR=ralph-logs
DONE_MARK="DONE: "

mkdir -p "$LOG_DIR"

note() {
  printf '[%(%Y-%m-%d %H:%M:%S)T] %s\n' -1 "$*" | tee -a "$PROGRESS"
}

# ---- main loop ---------------------------------------------------------------

note "ralph: starting (task_file=$TASK_FILE max_iters=$MAX_ITERS)"

for ((i = 1; i <= MAX_ITERS; i++)); do

  # Stop file?
  if [[ -f .ralph-stop ]]; then
    note "ralph: .ralph-stop detected, exiting"
    rm -f .ralph-stop
    break
  fi

  # Pick the first task that doesn't start with DONE: or # and isn't blank.
  TASK="$(grep -vE "^(${DONE_MARK}|#|$)" "$TASK_FILE" | head -1 || true)"
  if [[ -z "$TASK" ]]; then
    note "ralph: all tasks complete, exiting"
    break
  fi

  TS=$(date +%Y%m%d-%H%M%S)
  LOG="$LOG_DIR/iter-$i-$TS.log"
  note "ralph: iter $i/$MAX_ITERS — task: $TASK"

  # Capture HEAD before codex runs so we can detect what (if anything) it
  # committed.
  HEAD_BEFORE="$(git rev-parse HEAD)"

  PROMPT="Working dir: $(pwd). Lean 4 / Mathlib v4.28.0 (commit 8f9d9cff). Repository conventions: see CLAUDE.md and ref/methodology.md.

The currently active task is:

  $TASK

After making changes:
  1. Run a narrow lake build (e.g. lake build Jacobian.Blueprint.Sec03.SomeFile if obvious from context, else lake build Jacobian.Blueprint).
  2. If green: git add the touched files, git commit with a clear message, and git push origin main.
  3. If red: revert, and write a one-paragraph note explaining what failed.

Forbidden:
  - import Mathlib (cardinal sin — narrow Mathlib.Topic.Subtopic only)
  - touching Jacobian/Challenge.lean or Jacobian/Solution.lean
  - introducing axiom declarations
  - leaving the working tree dirty if you don't commit

Read ref/plans/polygonal-model.md for the polygonal-model project's structural decomposition. Other relevant plans live under ref/plans/.

Make one focused, narrow change toward the task. If the task is too big for one iteration, split it and tackle the smallest sub-piece — the loop will run again."

  if codex exec "$PROMPT" 2>&1 | tee "$LOG"; then
    HEAD_AFTER="$(git rev-parse HEAD)"
    if [[ "$HEAD_BEFORE" != "$HEAD_AFTER" ]]; then
      note "ralph: iter $i committed $(git rev-list --count "$HEAD_BEFORE..HEAD") commit(s)"
      # ensure we're pushed
      if ! git push origin main 2>&1 | tee -a "$LOG"; then
        note "ralph: push failed (see $LOG)"
      fi
      # mark task done
      python -c "
import sys
task = sys.argv[1]
path = sys.argv[2]
mark = sys.argv[3]
with open(path, 'r', encoding='utf-8') as f:
    lines = f.readlines()
out = []
done_one = False
for ln in lines:
    if not done_one and ln.rstrip('\n') == task:
        out.append(mark + ln)
        done_one = True
    else:
        out.append(ln)
with open(path, 'w', encoding='utf-8') as f:
    f.writelines(out)
" "$TASK" "$TASK_FILE" "$DONE_MARK"
      note "ralph: marked done — $TASK"
    else
      note "ralph: iter $i — codex did not commit; leaving task in queue"
    fi
  else
    note "ralph: iter $i — codex returned non-zero (see $LOG)"
  fi

  sleep 3
done

note "ralph: loop ended after $((i - 1)) iteration(s)"
