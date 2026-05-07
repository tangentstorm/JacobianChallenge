# Claude Timer-Tick Prompt

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
     Aristotle job (per the "cancel if proven locally" rule below).
     This keeps Aristotle focused on the front of the queue (likely
     the deeper proofs) while Claude clears the back.
   - **Aristotle packets are only ever cancelled for two reasons,
     and no others:**
     1. **The target sorry no longer exists locally** — discharged
        outright OR lifted to a different named obligation by a
        TOPDOWN refactor / split / restructuring. "Lifted" counts as
        "proven locally": the packet is grinding on a target that
        doesn't exist anymore, and any patch it produces will be a
        stale-baseline revert. Don't waste Aristotle's wall-clock.
     2. **Explicit user instruction** — e.g. "cancel <id>".

     Anything else is **not** a cancel signal. Specifically: do
     **not** cancel based on stuckness ("0% for hours"), slow
     progress, looking blocked, "approaching some threshold",
     packet-looks-redundant-with-another, or your own judgment that
     it's "probably hopeless". Aristotle is a parallel worker — let
     packets that still have a live target run regardless of how
     stuck they look. If unsure whether a target was discharged or
     lifted, err toward cancel; if unsure whether a target is still
     live, err toward letting it run.
   - **At least two sub-agents must always be running, in their own
     git worktrees, on the two sorries at the END of the Aristotle
     queue** — i.e. the two **newest-submitted** `submitted` jobs that
     are still `QUEUED` (not yet `IN_PROGRESS`). Aristotle drains
     FIFO from the front (oldest first), so the newest submissions
     are what Aristotle will work on last; racing those with
     sub-agents is what actually shortens the time-to-zero-sorries.
     Do **not** target the oldest-queued packets — Aristotle will
     get there on its own. Use the Agent tool with
     `isolation: "worktree"` so each sub-agent gets an isolated copy
     of the repo and cannot collide with the master or with each
     other. **Do not include a `Working directory: C:\ver\JacobianChallenge`
     line in the sub-agent prompt** — that line directs the agent
     back to the main checkout (via absolute-path Edit calls) and
     defeats the worktree isolation. The agent's cwd is already its
     worktree (`.claude/worktrees/agent-…`); leave it implicit, or
     say "use your current working directory (your worktree)" if you
     must mention it. At the start of every tick, check which background
     sub-agents you launched are still alive (you'll have received
     completion notifications for any that finished); if fewer than
     two are running, launch replacements *this tick* on the now-
     newest QUEUED sorries (skipping any sorry already covered by a
     live sub-agent — disjoint targets). When a sub-agent finishes,
     integrate its patch via cherry-pick (or by porting the targeted
     file edit), then immediately spawn its replacement so the count
     stays ≥ 2.
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

6. Progress is tracked via the blueprint dependency graph
   (`https://tangentstorm.github.io/JacobianChallenge/blueprint/dep_graph_collapsible.html`),
   which rebuilds from `tex/` and Lean `\lean{...}` annotations on every
   push to `main`. Do **not** add bar-chart status sections, "Progress
   Report" templates, or shaded `█/░` bars to `README.md` or any other
   doc. Keep `README.md` describing the project, not the latest tick's
   counts.

7. If you submit, retrieve, integrate, split, or abandon any Aristotle task,
   update `aristotle_tasks.md` AND `aristotle_jobs.jsonl` with the current
   status, job id, target file, prompt summary, and next action.

8. **Commit and push every tick.** Each tick must end with a commit that
   bundles `aristotle_tasks.md`, `aristotle_jobs.jsonl`, and any integrated
   Lean work, followed by `git push origin main`. The tick is not complete
   until the push lands. Do not mark a "commit and push" task complete
   unless the push actually succeeded; if the harness blocks the push,
   surface the blocker and ask, rather than quietly skipping it.

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
- **Always credit Aristotle on integration commits.** When a commit
  integrates Aristotle output (clean diff, partial discharge, or even
  a rejected stale-baseline review), add this trailer line in addition
  to Claude's `Co-Authored-By:`:

  ```
  Co-authored-by: Aristotle (Harmonic) <aristotle-harmonic@harmonic.fun>
  ```

  This applies to every commit that touches `aristotle_jobs.jsonl`
  with an `"integrated"` or `"rejected"` status update, plus any Lean
  file changes derived from an Aristotle result. On heartbeat /
  cleanup commits with no Aristotle content, the trailer is not
  required.
- **Imports are minimal and load-bearing.** `import Mathlib` is a cardinal
  sin — it pulls in the entire library, blowing up build times by an order
  of magnitude. Every Aristotle / sub-agent / Codex prompt must explicitly
  forbid `import Mathlib` and any `import Mathlib.Foo` not strictly required
  by the proof. New imports must be the narrowest possible
  `import Mathlib.Topic.Subtopic.SpecificFile`, and only when a needed
  declaration is genuinely absent from the file's existing imports. Review
  every retrieved diff for unnecessary imports before integration; if a
  result adds `import Mathlib` or otherwise broadens the import surface, it
  is rejected by default.
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
  management/reporting files. Keep them synchronized with the code. Progress
  itself is read from the blueprint dependency graph, not from these files.

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

### When the target is blocked by a placeholder upstream

The default single-file allowed-writes scope is correct when the target
has all its prerequisites in place and just needs a proof. It is **wrong**
when the target sorry is gated on an upstream stub — `True := trivial`
placeholder leaves, `noncomputable opaque` definitions with no axioms
connecting them to anything, `EdgeWordPresentation := PUnit` style
data-trivial structures, etc. With a single-file scope, Aristotle
correctly identifies the upstream stub as the blocker and returns a
clean BLOCKER triage; this is honest but does not advance the project.

Repeated empirical pattern (2026-05-07 saturation wave): of 14 packets
dispatched with default single-file scope, 7 returned clean BLOCKER
triages identifying upstream stubs (`RSLineBundleDegree` opaque,
`periodPairing := 0`, `sidePairingRel` stub, `basisAnalyticPullbackBundle`
opaque, `EdgeWordPresentation := PUnit`, `eulerChar_additive_ses_point`
`True := trivial`, etc.). All ran for ~30 minutes of wall-clock; all
produced no Lean changes.

**For targets known to be blocked by an upstream stub, prefer the
implement-the-prerequisite framing**:

- Identify the upstream file containing the stub.
- Add it to the allowed-writes scope explicitly.
- Tell Aristotle the goal is to **make the upstream definition real**
  (replace `True := trivial` with the genuine statement; replace
  `:= 0` placeholder bodies with the real construction; refine
  `:= PUnit` data-trivial types into the right structure).
- Spell out the constraints: existing call sites must still type-check;
  no existing sorry-free declaration may become sorry; new content
  must build.

Two valid framings, in order of preference:

1. **Refine the placeholder**: allow writes to both the target file and
   the upstream-stub file, with the explicit task "give the upstream
   definition real content so the target's proof goes through".
2. **Build new infrastructure in a fresh file**: allow creation of a
   new module (`Jacobian/Periods/HurewiczMap.lean` is the prototype
   from 2026-05-07) where Aristotle assembles the missing prerequisite
   from existing primitives. Cleaner write scope, no risk of breaking
   existing call sites, but only works when the new file does not need
   to mutate existing types.

Example (placeholder-refinement framing):

```text
Working directory: C:\ver\JacobianChallenge
Target file: Jacobian/HolomorphicForms/EulerCharLineBundle.lean
Target sorry: theorem h0_minus_h1_ge_riemann (line ~163)
Upstream stub blocking it:
  Jacobian/HolomorphicForms/Serre/RSLineBundleDegree.lean
  has `noncomputable opaque RSLineBundleDegree` with no axioms
  connecting it to sheaf cohomology dimensions.
Allowed writes: BOTH the target file AND the upstream stub file.
Forbidden files: Jacobian/Challenge.lean, all other .lean files.
Task: give `RSLineBundleDegree` real content (e.g. wire it to a
canonical degree formula via a divisor witness), then close the
target sorry. Existing sorry-free call sites of `RSLineBundleDegree`
must still type-check.
Proof style: direct tactics; no `aesop`/`grind`/broad `simp_all`.
Expected verification: `lake build Jacobian.HolomorphicForms.EulerCharLineBundle`
plus a build of the upstream module.
If still blocked: clean triage with a precise list of additional
upstream stubs that would need refinement; do NOT introduce
false-statement helpers behind sorry.
```

The "if blocked" fallback is preserved as a safety valve against the
b9fcfdb4 false-statement-helper anti-pattern, but the **primary
framing pushes Aristotle to implement the missing piece, not triage
it away**.

## Progress Tracking

Progress is read from the blueprint dependency graph
(`https://tangentstorm.github.io/JacobianChallenge/blueprint/dep_graph_collapsible.html`),
which is rebuilt from `tex/` sources and Lean `\lean{...}` annotations
on every push to `main`. Do not duplicate that information as bar charts,
counted ratios, or "Progress Report" sections in `README.md` or anywhere
else — those drift, the graph does not.

When integrating new Lean infrastructure, update the corresponding
blueprint nodes (`\lean{decl_name}`, `\leanok`, `\uses{…}`) so the graph
reflects the new state. The TeX audit scripts under `scripts/` enforce
that `\lean{…}` annotations point at real declarations and that the
dependency graph is acyclic.

## What To Report In Chat

At the end of each tick, report briefly:

- Aristotle active job count and ids;
- jobs retrieved/integrated;
- files changed;
- whether `aristotle_tasks.md` was updated;
- build commands run and whether they passed;
- next planned tasks.
