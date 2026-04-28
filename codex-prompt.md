# Codex prompt: introduce periodSubgroup_isZLattice opaque and refine basisAlignedPeriodSubgroup_isDiscrete

This is a single-round top-down refinement task in the spirit of `TOPDOWN.md`.
The earlier in-process `codex exec` invocation appeared to hang silently
(stdout never flushed); user is firing this manually instead.

## How to run

From `C:\ver\JacobianChallenge`:

```bash
codex exec "$(cat codex-prompt.md)"
```

Or pipe the file body:

```bash
codex exec < codex-prompt.md
```

(Strip this `## How to run` header section first if codex doesn't ignore it.)

---

## Prompt body

Working directory: C:\ver\JacobianChallenge

Read `TOPDOWN.md` first; you are a Claude sub-agent doing one round of
top-down refinement following its sub-agent prompt convention. Then
read `Jacobian/Periods/PeriodLattice.lean` — specifically the docstring
of `basisAlignedPeriodSubgroup_isDiscrete` (lines ~67–180) which
already contains a ~110-line blocker analysis from a recent Aristotle
survey (commit `cf6cb10`). That survey's three-step plan recommended:

1. Declare a discreteness / IsZLattice property as an opaque alongside
   `periodPairing` in `Jacobian/Periods/PeriodFunctional.lean`.
2. Derive `DiscreteTopology` from (1).
3. Wire the instance.

A second Aristotle survey (commit `763c4ef`) on
`periodFundamentalDomain_isCompact` confirmed the same blocker and
also recommended un-opaquing `periodFundamentalDomain` itself. THAT
larger refactor is OUT OF SCOPE for this round — leave the
`opaque periodFundamentalDomain` and the two
`periodFundamentalDomain_*` lemmas (`_isCompact`, `_covers`)
untouched.

Round name:
`Periods: introduce periodSubgroup_isZLattice opaque and refine
basisAlignedPeriodSubgroup_isDiscrete`

Targeted declaration:

* `basisAlignedPeriodSubgroup_isDiscrete` (currently sorry-d in
  `Jacobian/Periods/PeriodLattice.lean`).

Allowed file edits (no other files):

* `Jacobian/Periods/PeriodFunctional.lean` — ADD a new opaque
  declaration. Do not touch the existing `periodPairing` opaque or
  its surrounding API.
* `Jacobian/Periods/PeriodLattice.lean` — ONLY refine
  `basisAlignedPeriodSubgroup_isDiscrete`. Do NOT touch
  `periodFundamentalDomain` (the opaque),
  `periodFundamentalDomain_isCompact`,
  `periodFundamentalDomain_covers`, or
  `periodFullComplexLattice`. Do NOT touch any other declaration.

Forbidden files:

* `Jacobian/Challenge.lean`
* `Jacobian/WorkPackets/StatementBank.lean`
* `Jacobian/Solution.lean`
* every other `.lean` file in the project.

The new opaque should be named exactly:

```lean
opaque periodSubgroup_isZLattice
    (E : Type*) [...] (X : Type) [...] :
    DiscreteTopology (basisAlignedPeriodSubgroupConcrete X)
```

(Use the simpler `DiscreteTopology` form rather than the heavier
`IsZLattice ℝ` form — this is the minimum sufficient declaration for
discharging `_isDiscrete`. The richer `IsZLattice` form can come later
once it actually pays for compactness/covers as well.)

Place the opaque in `PeriodFunctional.lean` at a sensible location
(probably right after the existing `periodPairing` opaque). Add a
short docstring naming the bottom-up content (integrality of the
period pairing image; the image is a free ℤ-module of rank 2g spanned
by 2g ℝ-linearly independent period vectors).

Then refine `basisAlignedPeriodSubgroup_isDiscrete` in
`PeriodLattice.lean` to:

```lean
instance basisAlignedPeriodSubgroup_isDiscrete :
    DiscreteTopology (basisAlignedPeriodSubgroup X) :=
  periodSubgroup_isZLattice ℂ X
```

(or equivalent one-liner — the type definitionally unfolds because
`basisAlignedPeriodSubgroup X = basisAlignedPeriodSubgroupConcrete X`
post-keystone refactor; verify this is the case before committing).

Update the docstring of `_isDiscrete` to remove the now-stale
'sorry retained' implication and replace it with a one-line note
that the proof now delegates to `periodSubgroup_isZLattice` declared
in `PeriodFunctional.lean`. Keep the existing 110-line blocker
analysis in place as historical record (it documents what the new
opaque captures).

Update `Jacobian/WorkPackets/TopDown.md`'s Declaration Map: the row
for `T2Space` and `CompactSpace` (which depend on
`periodFullComplexLattice.isClosed` and the fundamental-domain
properties) — add a brief note that `_isDiscrete` is now
discharged via the new opaque, which is now the leaf
obligation. Keep the format consistent with existing rows.

Verification: `lake build Jacobian.Periods.PeriodLattice` must pass.
Run this build at the end (single narrow build, NOT iterative).

Hard rules (from TOPDOWN.md):

* Do not edit `Jacobian/Challenge.lean`.
* Do not introduce `axiom` (use `opaque`).
* Mark `noncomputable` if Lean asks for it.
* Use small named pieces, not bundled bodies.
* Public declaration names and signatures stay stable.

Do NOT commit. The master will review your diff and commit.

Report at the end: what you refined, what new opaque you added,
sorry-count delta on each file you touched, build status, and the
exact declarations you did NOT touch (so the master can verify scope).
