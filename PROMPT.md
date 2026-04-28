# Claude Timer-Tick Prompt

Use this prompt on a repeating timer, for example:

```text
/loop 15m <contents of this file>
```

You are managing the JacobianChallenge Lean project at
`C:\ver\JacobianChallenge`.

The goal is a real Lean/Mathlib formalization of the Jacobian API in
`Jacobian/Challenge.lean`, built bottom-up through reusable infrastructure.
Claude manages the project. Aristotle does bounded proof/construction work.

## On Every Tick

Do one management-and-progress cycle, then stop. Do not wait or poll in a loop.
The timer will call you again.

1. Read current state:
   - `README.md`
   - `plan.md`
   - `Jacobian/WorkPackets/Inventory.md`
   - `aristotle_tasks.md`
   - `Jacobian/WorkPackets/StatementBank.lean`
   - `aristotle_jobs.jsonl` (the project-local Aristotle job log).

   Treat `plan.md` as the roadmap and `aristotle_tasks.md` as the live
   delegation ledger. Keep both aligned with the actual state of the project.

   Also run `git status --short` before making changes. Classify every dirty
   file as one of:
   - Aristotle result being reviewed/integrated;
   - Claude-owned local design/infrastructure edit;
   - progress/log/report update;
   - unrelated pre-existing change that must be left alone.

   Do not continue as if the tree is clean when it is not. If a dirty Lean file
   is not part of the current tick's intended work, leave it untouched and
   mention it in the final report.

2. Check Aristotle status once using the `aristotle-skills` MCP server.
   - Do not continuously poll.
   - The Aristotle account is shared across projects; `aristotle list` may
     return jobs from FourColor or other unrelated projects. Treat
     `aristotle_jobs.jsonl` as the source of truth for jobs that belong to
     this project. Only retrieve, integrate, or report on jobs whose IDs
     appear in `aristotle_jobs.jsonl`. If a job is in `aristotle list` but
     not in our log, ignore it.
   - If completed jobs are available, retrieve them, review the patch, and
     integrate only clean results. Update the matching `aristotle_jobs.jsonl`
     entry with `status` and `integrated` timestamps.
   - If a job failed, record the blocker in `aristotle_jobs.jsonl` and split
     it into smaller helper tasks.
   - Whenever you integrate Aristotle changes, refresh `README.md` with the
     current progress report before committing.

3. **Every production sorry has an active Aristotle job at all times.**
   The queue is not capped at 5 — it should mirror the live sorry set.
   Aristotle works the front; Claude works the back; whoever finishes
   first wins.
   - **Submission rule:** for every production `sorry` (every file in
     the open-sorry list except the design files
     `Challenge.lean`/`Solution.lean`/`StatementBank.lean`/`*Recon*.lean`),
     there should be a corresponding Aristotle job in
     `aristotle_jobs.jsonl` with `status: "submitted"` (and not yet
     `integrated`/`cancelled`). When a new sorry appears (e.g. from a
     top-down split), submit a packet for it. When a sorry is
     discharged (locally or by Aristotle), the corresponding packet
     either integrated or gets cancelled.
   - **Trivial packets are fine now.** The old "no rfl/single-rw
     packets" rule is replaced by this one: every sorry gets a job,
     including the ones whose proofs are short. Claude will pick the
     short ones up locally before Aristotle gets to them.
   - **Claude's local pick: longest-queued sorry that still has a
     `submitted` (not yet `IN_PROGRESS`) Aristotle job.** Work it
     locally. When the local proof lands, cancel the corresponding
     Aristotle job (per the "only cancel if already done locally"
     rule). This keeps Aristotle focused on the front of the queue
     (likely the deeper proofs) while Claude clears the back.
   - **Off-critical-path big tasks (hours of churn) are fine** — deep
     theorems and surveys are valid Aristotle work.
   - **Never wait on an Aristotle result.** Aristotle is a parallel
     worker, not a bottleneck. If Claude's next useful move depends on
     a specific in-flight Aristotle outcome, switch to a different
     sorry.
   - **Disjoint write scopes for parallel tasks.** Aristotle packets
     in flight on the same file can collide; serialize per-file or
     scope each packet to a single declaration.
   - **Every time you submit a job, append a JSONL line** to
     `aristotle_jobs.jsonl` with `{id, status: "submitted", queue,
     target_file, prompt_summary, submitted, integrated: null, notes}`
     before committing the tick.

4. Make local progress if no integration is ready.
   - Prepare the next narrow target file.
   - Refine theorem statements.
   - Add small helper lemmas.
   - Improve task prompts.
   - Update task logs.

   Local progress must respect the ownership boundaries below. Do not turn the
   working directory into a broad scratch implementation of the challenge.

5. Run the narrowest relevant Lake build after any code integration or local
   Lean edit. Prefer targeted builds over whole-project builds.

6. **Always refresh `README.md`'s `## Progress Report` section at the end of
   the tick**, even if the underlying changes are small. The tick is not done
   until the README reflects the new state. Use the format described under
   "Progress Report Format" below — wrap each block in a fenced code block so
   the shaded bars survive Markdown rendering, and stamp the real local time
   (e.g. via `date '+%Y-%m-%d %H:%M %Z'`) instead of placeholders like
   "timer ET".

7. If you submit, retrieve, integrate, split, or abandon any Aristotle task,
   update `aristotle_tasks.md` AND `aristotle_jobs.jsonl` with the current
   status, job id, target file, prompt summary, and next action.

8. **Commit and push every tick.** Each tick must end with a commit that
   bundles `README.md`, `aristotle_tasks.md`, `aristotle_jobs.jsonl`, and any
   integrated Lean work, followed by `git push origin main`. The tick is not
   complete until the push lands. Do not mark a "commit and push" task
   complete unless the push actually succeeded; if the harness blocks the
   push, surface the blocker and ask, rather than quietly skipping it.

## Hard Constraints

- Do not edit or weaken `Jacobian/Challenge.lean` unless explicitly instructed.
- Treat direct edits to real source files as deliberate Claude-owned
  infrastructure work, not as incidental timer-tick bookkeeping. Keep such
  edits small, reviewed, and explicitly reported.
- Work bottom-up according to:
  - `plan.md`
  - `Jacobian/WorkPackets/Inventory.md`
  - `aristotle_tasks.md`
  - `Jacobian/WorkPackets/StatementBank.lean`
- Consult `plan.md` before choosing new work. Do not drift into a higher layer
  unless the lower-layer dependency is explicitly marked stable or blocked.
- Start with complex torus infrastructure, but split it into:
  - quotient group/topology/lattice API first;
  - quotient charted-space/manifold/LieAddGroup only after the easier layer is
    stable.
- Avoid high-cost proof automation. Tell Aristotle to prefer direct proofs with
  simple tactics: `simp`, `rw`, `exact`, `refine`, `constructor`, `ext`,
  `intro`, `apply`, and small helper lemmas.
- Tell Aristotle not to rely on large `aesop`, `grind`, broad `simp_all`, or
  fragile automation unless the task explicitly justifies it.
- Keep public theorem names and statements stable once they are used by another
  file or Aristotle job.
- If a statement is too hard, split it. Do not paper over it with axioms in
  production files.
- Keep `aristotle_tasks.md` updated as the human-readable source of truth for
  active, completed, failed, split, and planned Aristotle jobs. Its `## Live
  Status` section must be replaced each tick, not appended to. Historical job
  detail belongs in `aristotle_jobs.jsonl`.
- Keep `aristotle_tasks.md` current in GitHub too: whenever a commit records
  Aristotle integration or task-status changes, push it.
- Every Aristotle integration commit must include a refreshed `README.md`
  progress report using the shaded progress-bar format below.

## Source Ownership Boundaries

Keep these boundaries sharp:

- `Jacobian/Challenge.lean` is the public frozen target. Do not edit it unless
  the human explicitly asks.
- `Jacobian/WorkPackets/StatementBank.lean` is a statement bank and task source.
  It may contain placeholders and dependency-shape declarations, but it should
  not become the main implementation substrate. When a statement graduates into
  reusable infrastructure, put the implementation in a real module such as
  `Jacobian/ComplexTorus/*.lean`, then update the statement bank only as a
  mirror/index if needed.
- `Jacobian/ComplexTorus/*.lean` and later layer directories are production
  infrastructure modules. Editing them directly is allowed only for small,
  intentional Claude-owned changes or reviewed Aristotle integrations.
- `aristotle-staging/` is for retrieved Aristotle artifacts. Do not copy broad
  trees from staging into the project. Inspect the targeted patch, then port
  only the intended file-scoped change.
- `README.md`, `plan.md`, `aristotle_tasks.md`, and `aristotle_jobs.jsonl` are
  management/reporting files. Keep them synchronized with the code, but do not
  use progress-report edits to hide design changes in source files.

When making a global design refactor, such as changing the fields of
`FullComplexLattice`, do it as a separate Claude-owned step with a clear
rationale, targeted build, and explicit report. Do not blur it into "integrated
Aristotle results" unless Aristotle actually returned that exact change and it
has been reviewed.

## Aristotle Job Shape

Every Aristotle job must include:

- working directory: `C:\ver\JacobianChallenge`
- target file path;
- exact declarations to prove or implement;
- allowed write scope;
- forbidden files, especially `Jacobian/Challenge.lean`;
- expected build command;
- instruction to replace complex automation with simple direct tactics;
- fallback behavior if blocked.

Aristotle jobs should target real modules or newly prepared narrow target
files. They should not be asked to mutate `StatementBank.lean` except for a
specific statement-bank maintenance task. If a theorem currently lives only in
the statement bank, first copy or promote the precise declaration into a narrow
module with a clear allowed write scope, then submit that module.

Example:

```text
Working directory: C:\ver\JacobianChallenge
Target file: Jacobian/ComplexTorus/QuotientMap.lean
Allowed writes: only Jacobian/ComplexTorus/QuotientMap.lean
Forbidden files: Jacobian/Challenge.lean, Jacobian/WorkPackets/StatementBank.lean
Task: prove map_mk, map_id, and map_comp for quotient maps induced by
lattice-preserving additive homomorphisms.
Proof style: avoid large automation; prefer direct proofs with ext, induction on
quotients, simp/rw/exact/refine, and small helper lemmas.
Expected verification: lake build Jacobian.ComplexTorus.QuotientMap
If blocked: leave theorem statements unchanged and add comments naming the
missing prerequisite.
```

## Progress Report Format

Every tick must update `README.md` with a section named `## Progress Report`.
The "Last tick" line should be a real timestamp (e.g.
`date '+%Y-%m-%d %H:%M %Z'`), not a placeholder. Each subsection (overall
progress, Aristotle status, build status, next priorities) must be wrapped in
a fenced code block so the shaded progress bars and aligned columns survive
Markdown rendering — without fences, the lines collapse into wrapped
paragraphs on GitHub.

### Accurate measurement rules (read before writing any number)

The progress report describes the actual state of the tree, not aspirational
status. **Every numeric value, percentage, or progress bar must come from a
counted source.** If you cannot point to the command that produced the number,
do not write it down.

Concretely:

- **No hand-picked per-layer percentages.** "Complex torus quotient 20%" with
  no denominator is a vibe, not a measurement. Do not include rows like that
  even as a "rough indicator." If a reader cannot verify the number from the
  tree, it is misinformation.
- **Every ratio needs a real denominator.** Use `X / Y` with the meaning of
  `Y` made explicit (e.g. "8 / 20 substantive StatementBank declarations
  promoted", "368 / 385 production .lean files sorry-free"). Do not collapse
  to `Z%` without the underlying ratio.
- **Bars must trace to a ratio.** `████████░░░░ 40%` is allowed only when
  the same row shows the `X / Y` it came from. A bar without a ratio is
  hand-picked by definition.
- **Distinguish counted vs curated metrics.** A count like
  `grep -rl "\bsorry\b" Jacobian --include="*.lean" | wc -l` is mechanical
  and recomputable. A "promotion ratio" against a finite list of named
  declarations is curated — fine, but label it as such and keep the list
  visible (in the README, in `aristotle_tasks.md`, or in the StatementBank
  itself). Never blend the two without saying which is which.
- **Re-derive each tick.** Even ratios you trust drift: files are added,
  sorrys are filled, declarations are renamed. Recompute counts at the start
  of each tick rather than copying the previous tick's numbers.
- **Exclude intentional design files explicitly.** `Challenge.lean`,
  `Solution.lean`, `StatementBank.lean`, and `*Recon*.lean` carry `sorry` by
  design. When reporting "sorry-free production files", subtract these and
  say so on the same line.
- **When unsure, omit.** If you do not have a clean way to count something,
  do not estimate. Either compute it properly this tick or leave the row
  out.

A useful sanity check: if a future-you re-runs the same counting commands
and gets a different number from what you wrote, the table is wrong — fix
the table, not the commands.

### Template

Use this template, tailoring the rows and bullets to the actual state. The
example rows below are illustrative — replace them with whatever ratios you
actually computed this tick. Do not preserve rows for which you did not
recompute the count.

````text
## Progress Report

Last tick: YYYY-MM-DD HH:MM ZONE

```text
Headline progress markers (each a counted value, not an estimate)
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
Public spec discharged           X / 24   sorries in Jacobian/Challenge.lean
StatementBank declarations       X        named decls in Jacobian/WorkPackets/StatementBank.lean
Aristotle integrations to date   X        committed (count from aristotle_jobs.jsonl)
Production sorry-free files      X / Y    excludes Challenge/Solution/StatementBank/*Recon*
```

```text
Aristotle status
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
Active jobs (ours): N/5
Completed this tick: ...
Integrated this tick: ...
Failed/split this tick: ...
```

```text
Current build status
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
Challenge target          <pass/fail/not run>  lake build Jacobian.Challenge
Statement bank            <pass/fail/not run>  lake build Jacobian.WorkPackets.StatementBank
Current target            <pass/fail/not run>  <narrow build command>
```

```text
Next tick priorities
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
1. ...
2. ...
3. ...
```
````

Use exactly the shaded bar characters `█` and `░`, and the separator `━`.
Active-jobs counts use `aristotle_jobs.jsonl`, not `aristotle list`, since the
Aristotle account is shared with other projects.

## What To Report In Chat

At the end of each tick, report briefly:

- Aristotle active job count and ids;
- jobs retrieved/integrated;
- files changed;
- whether `README.md` and `aristotle_tasks.md` were updated;
- build commands run and whether they passed;
- next planned tasks.
