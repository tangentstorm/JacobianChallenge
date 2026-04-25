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

3. Keep Aristotle busy.
   - Aim for 5 active Aristotle tasks (counted from `aristotle_jobs.jsonl`,
     not from `aristotle list`).
   - Submit enough new independent tasks to bring the active count back
     toward 5, but only if there are safe, file-scoped tasks available.
   - Use disjoint write scopes for parallel tasks.
   - Every time you submit a job, append a JSONL line to
     `aristotle_jobs.jsonl` with `{id, status: "submitted", queue,
     target_file, prompt_summary, submitted, integrated: null, notes}`
     before committing the tick.

4. Make local progress if no integration is ready.
   - Prepare the next narrow target file.
   - Refine theorem statements.
   - Add small helper lemmas.
   - Improve task prompts.
   - Update task logs.

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
  active, completed, failed, split, and planned Aristotle jobs.
- Keep `aristotle_tasks.md` current in GitHub too: whenever a commit records
  Aristotle integration or task-status changes, push it.
- Every Aristotle integration commit must include a refreshed `README.md`
  progress report using the shaded progress-bar format below.

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

Use this template, tailoring the percentages and bullets to the actual state:

````text
## Progress Report

Last tick: YYYY-MM-DD HH:MM ZONE

```text
Overall Jacobian infrastructure progress
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
Project scaffolding       ████████████████████  100%  Lake project, cache, root modules
Mathlib inventory         ████████████████████  100%  pinned v4.28.0 audit complete
Complex torus quotient    ████░░░░░░░░░░░░░░░░   20%  quotient/lattice API starting
Quotient manifold layer   ░░░░░░░░░░░░░░░░░░░░    0%  blocked on new charted-space work
Holomorphic forms         ░░░░░░░░░░░░░░░░░░░░    0%  type absent in Mathlib
Path integration/periods  ░░░░░░░░░░░░░░░░░░░░    0%  largest missing infrastructure
Abel-Jacobi API           ░░░░░░░░░░░░░░░░░░░░    0%  waits on periods
Trace/degree/push-pull    ░░░░░░░░░░░░░░░░░░░░    0%  local analytic theory partly present
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
