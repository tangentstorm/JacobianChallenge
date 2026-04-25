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
   - any local Aristotle task log if one exists.

   Treat `plan.md` as the roadmap and `aristotle_tasks.md` as the live
   delegation ledger. Keep both aligned with the actual state of the project.

2. Check Aristotle status once using the `aristotle-skills` MCP server.
   - Do not continuously poll.
   - If completed jobs are available, retrieve them, review the patch, and
     integrate only clean results.
   - If a job failed, record the blocker and split it into smaller helper tasks.
   - Whenever you integrate Aristotle changes, refresh `README.md` with the
     current progress report before committing.

3. Keep Aristotle busy.
   - Aim for 5 active Aristotle tasks.
   - Submit enough new independent tasks to bring the active count back toward
     5, but only if there are safe, file-scoped tasks available.
   - Use disjoint write scopes for parallel tasks.

4. Make local progress if no integration is ready.
   - Prepare the next narrow target file.
   - Refine theorem statements.
   - Add small helper lemmas.
   - Improve task prompts.
   - Update task logs.

5. Run the narrowest relevant Lake build after any code integration or local
   Lean edit. Prefer targeted builds over whole-project builds.

6. If you make any changes, update `README.md` with a progress report using
   UTF-8 shaded progress bars. Report this at every tick where you touch files.

7. If you submit, retrieve, integrate, split, or abandon any Aristotle task,
   update `aristotle_tasks.md` with the current status, job id if available,
   target file, prompt summary, and next action.

8. If you commit merged Aristotle work, include the updated `README.md` and
   `aristotle_tasks.md` in the same commit when relevant, then push the branch
   to GitHub so the task ledger and progress report stay current remotely.

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

When you edit files, update `README.md` with a section named
`## Progress Report`. Use this format and tailor the percentages to the actual
state:

```text
## Progress Report

Last tick: YYYY-MM-DD HH:MM ET

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

Aristotle status
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
Active jobs: N/5
Completed this tick: ...
Integrated this tick: ...
Failed/split this tick: ...

Current build status
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
Challenge target          <pass/fail/not run>  `lake build Jacobian.Challenge`
Statement bank            <pass/fail/not run>  `lake build Jacobian.WorkPackets.StatementBank`
Current target            <pass/fail/not run>  `<narrow build command>`

Next tick priorities
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
1. ...
2. ...
3. ...
```

Use exactly the shaded bar characters `█` and `░`, and the separator `━`. Keep
the progress report concise and factual.

## What To Report In Chat

At the end of each tick, report briefly:

- Aristotle active job count and ids;
- jobs retrieved/integrated;
- files changed;
- whether `README.md` and `aristotle_tasks.md` were updated;
- build commands run and whether they passed;
- next planned tasks.
