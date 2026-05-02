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

  # Snapshot the working tree BEFORE codex runs. We compare new/modified
  # files (excluding ralph's own scratch dirs) against this baseline to
  # decide whether codex actually produced shippable work — git author/log
  # is unreliable because ralph runs concurrently with manual commits.
  STATUS_BEFORE="$(git status --porcelain | grep -vE '^\?\? (ralph-logs/|ralph-progress\.txt|\.ralph-stop)' || true)"

  PROMPT="Working dir: $(pwd). Lean 4 / Mathlib v4.28.0 (commit 8f9d9cff). Repository conventions: see CLAUDE.md and ref/methodology.md.

The currently active task is:

  $TASK

Workflow:
  1. Make narrow, focused changes toward the task.
  2. Run a narrow lake build (e.g. lake build Jacobian.Blueprint.Sec03.SomeFile if obvious, else lake build Jacobian.Blueprint or lake build Jacobian.Periods).
  3. If green: leave the changes in the working tree. Do NOT git add / git commit / git push — the parent shell (ralph) will commit and push on your behalf after you exit. Your sandbox may not have permission to write to .git/index.lock anyway.
  4. If red: revert your changes and exit cleanly.

Forbidden:
  - import Mathlib (cardinal sin — narrow Mathlib.Topic.Subtopic only)
  - touching Jacobian/Challenge.lean or Jacobian/Solution.lean
  - introducing axiom declarations
  - leaving partially-broken work in the tree (build red ⇒ revert before exiting)

Read ref/plans/polygonal-model.md for the polygonal-model project's structural decomposition. Other relevant plans live under ref/plans/.

Make one focused, narrow change toward the task. If the task is too big for one iteration, split it and tackle the smallest sub-piece — the loop will run again."

  if codex exec "$PROMPT" 2>&1 | tee "$LOG"; then
    # Compute working-tree delta vs. baseline (excluding ralph's scratch).
    STATUS_AFTER="$(git status --porcelain | grep -vE '^\?\? (ralph-logs/|ralph-progress\.txt|\.ralph-stop)' || true)"
    if [[ -z "$STATUS_AFTER" ]]; then
      note "ralph: iter $i — codex left a clean tree; no shippable work, leaving task in queue"
    elif [[ "$STATUS_BEFORE" == "$STATUS_AFTER" ]]; then
      note "ralph: iter $i — working tree unchanged from before codex ran; leaving task in queue"
    else
      # codex produced shippable working-tree changes — commit on its behalf.
      note "ralph: iter $i — committing codex's work on its behalf"
      git add -A -- ':!ralph-logs' ':!ralph-progress.txt' ':!.ralph-stop' 2>>"$LOG"
      if git commit -m "ralph iter $i: $TASK

Co-Authored-By: codex (via ralph) <noreply@openai.com>" 2>&1 | tee -a "$LOG"; then
        if git push origin main 2>&1 | tee -a "$LOG"; then
          note "ralph: iter $i pushed"
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
          note "ralph: push failed (see $LOG); leaving task in queue, working tree dirty for inspection"
        fi
      else
        note "ralph: commit failed (see $LOG); leaving task in queue"
      fi
    fi
  else
    note "ralph: iter $i — codex returned non-zero (see $LOG)"
  fi

  sleep 3
done

note "ralph: loop ended after $((i - 1)) iteration(s)"
