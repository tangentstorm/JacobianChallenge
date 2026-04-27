# Jacobian Challenge

A Lean 4 / Mathlib formalization of the Jacobian variety of a compact Riemann surface (see _About_ below for scope).

## Progress Report

Last tick: 2026-04-27 16:11 EDT

```text
Headline progress markers (every value below is a fresh count from this tick)
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
Public spec discharged          0 / 24    sorries in Jacobian/Challenge.lean (frozen target)
StatementBank declarations     22         named decls in Jacobian/WorkPackets/StatementBank.lean
                                          (excluding 2 Inventory metadata items)
Aristotle integrations to date 87         `"status":"integrated"` lines in aristotle_jobs.jsonl
Production sorry-free files  379 / 387    using the precise count (real `sorry` tactics; doc-comment
                                          matches and intentional design files excluded).
                                          The 8 production files with real sorries:
                                            Claude-owned (3 files, 7 sorries):
                                              HolomorphicForms/CompactRiemannSurface  (1, Riemann-Roch — submitted to Aristotle)
                                              HolomorphicForms/GenusZeroClassification (1, uniformization)
                                              Periods/PeriodLattice                   (5, blocked on opaque,
                                                                                       parallel concrete defn now exists in
                                                                                       BasisAlignedPeriodSubgroup.lean)
                                            User-WIP (5 files, 22 sorries) — Claude leaves untouched:
                                              AbelJacobi/AnalyticOfCurveBasis         (6)
                                              ComplexTorus/ULiftTransport             (6)
                                              TraceDegree/PullbackBasis               (6)
                                              TraceDegree/PushforwardBasis            (3)
                                              TraceDegree/AnalyticDegree              (1)

Reproduction:
  for f in $(grep -rl "\bsorry\b" Jacobian --include="*.lean" |
              grep -vE "(Challenge|Solution|StatementBank|Recon)\.lean$"); do
    real=$(grep -E "\bsorry\b" "$f" | grep -vE "^\s*--|\`sorry|sorry\`" | wc -l)
    [ "$real" -gt 0 ] && echo "$f $real"
  done
```

```text
StatementBank promotion (curated ratio: how many named declarations have a
real production-module implementation? Denominator is the StatementBank
itself, not a count of the tree.)
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
                          promoted / total   notes
Inventory                    2 / 2           metadata only — counted separately
ComplexTorus                 3 / 3           Prop placeholders backed by IsManifold + LieAddGroup instances
HolomorphicForms             3 / 3           abbrev/def used directly as the working types
Periods                      1 / 6           IntegralOneCycle abbrev concrete; periodFunctional still
                                             `opaque`; period_homology/period_pairing_full_rank still
                                             `Prop := True`; periodFullComplexLattice not yet
AnalyticJacobian             1 / 3           AnalyticJacobianType ✓ (= AnalyticJacobianGroup);
                                             equivChallenge + homeomorph_challenge still placeholders
AbelJacobi                   0 / 2           pathIntegralFunctional opaque; analyticOfCurve still a stub
TraceDegree                  0 / 3           pullbackForms / traceForms / analyticDegree all opaque
                          ────────
Substantive total            8 / 20  (40%)   excludes 2 Inventory metadata items
```

```text
Aristotle status
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
Active jobs (ours):     1 / 5  `72ac3a75` (Riemann-Roch finite-dimensionality theorem) is
                        IN_PROGRESS at 3% (~15 min into the run). Per PROMPT.md "check
                        Aristotle status once" — not polling further. Will check next
                        tick; deep theorem, expected to take hours.
Integrated this tick:   None from Aristotle (still IN_PROGRESS).
```

```text
Local cadence this tick (Claude-owned, substantive infrastructure refactor)
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
Jacobian/Periods/PeriodLattice.lean — rename `periodSubgroup` to
`basisAlignedPeriodSubgroup` (and similarly for the 2 of-the-subgroup
lemmas: `_isClosed`, `_isDiscrete`). This frees the
`JacobianChallenge.Periods.periodSubgroup` fully-qualified name for the
functional-space concrete definition in PeriodFunctional.lean,
resolving the long-standing same-name conflict where the two
declarations coexisted only because nobody imported both.

Concrete result: `Jacobian/Periods.lean` umbrella now imports BOTH
PeriodFunctional (with `periodSubgroup E X` functional-space) AND
PeriodLattice (with `basisAlignedPeriodSubgroup X`) AND
BasisAlignedPeriodSubgroup (with `basisAlignedPeriodSubgroupConcrete X`)
with NO name conflict. This was structurally impossible before this tick.

Builds:
  lake build Jacobian.Periods.PeriodLattice ✓ (5 sorries — all renamed)
  lake build Jacobian.Periods                ✓
  lake build Jacobian.Solution              ✓ (no changes needed; only
                                              uses `periodFullComplexLattice`,
                                              which still exists with the same
                                              shape, just now built atop the
                                              renamed `basisAlignedPeriodSubgroup`)

Universe-mismatch deferred: routing `basisAlignedPeriodSubgroup` to
`basisAlignedPeriodSubgroupConcrete` (i.e. unfreezing the opaque) was
attempted but blocked by `Type` vs `Type*`. PeriodFunctional uses
`(X : Type)` (inheriting from `IntegralOneCycle`), but PeriodLattice
+ Solution + AnalyticOfCurveBasis all use `(X : Type*)`. Resolving
this requires a Type/Type* generalization in IntegralOneCycle and
PeriodFunctional — a separate Claude-owned refactor tick.

PRIOR TICK (still standing):
NEW Jacobian/Periods/BasisAlignedPeriodSubgroup.lean (1 def + 2 theorems):

  `basisAlignedPeriodSubgroupConcrete X
      : AddSubgroup (Fin (analyticGenus ℂ X) → ℂ)
      = AddSubgroup.map (holomorphicOneFormDualEquiv ℂ X).toLinearMap.toAddMonoidHom
                        (periodSubgroup ℂ X)`
    The CONCRETE basis-aligned period subgroup, defined as the image of
    the existing functional-space `periodSubgroup ℂ X`
    (= `(periodPairing ℂ X).range`) under the basis-aligned dual equiv
    introduced last tick. Builds against the deferred-instance
    `[FiniteDimensionalHolomorphicOneForms ℂ X]`.

  `mem_basisAlignedPeriodSubgroupConcrete_iff` — characterizes
    membership as "image of some functional-space period under the
    dual equivalence" (existential characterization).

  `zero_mem_basisAlignedPeriodSubgroupConcrete` — sanity check.

Why a NEW file with a NEW name (rather than replacing
`PeriodLattice.lean`'s opaque): Lean 4 does not allow two declarations
with the same fully-qualified name to coexist in a single elaboration
context. `Jacobian/Periods/PeriodFunctional.lean` already declares
`JacobianChallenge.Periods.periodSubgroup (E X) [...]` (functional-space)
and `Jacobian/Periods/PeriodLattice.lean` declares
`opaque JacobianChallenge.Periods.periodSubgroup X (basis-aligned)` —
they presently coexist only because nobody imports both. Renaming
`PeriodLattice`'s opaque is a separate refactor that touches Solution.lean
and AnalyticOfCurveBasis.lean (the only two files that import
PeriodLattice). For this tick we deliver the concrete definition under
`basisAlignedPeriodSubgroupConcrete` (uniquely named, no conflict);
a future tick can do the rename + route `periodFullComplexLattice`
through this file's def.

Wired into `Jacobian/Periods.lean` umbrella (also added the
previously-orphaned `PeriodSubgroupRange` import from the integrated
6c252557 packet).

Builds:
  lake build Jacobian.Periods.BasisAlignedPeriodSubgroup ✓
  lake build Jacobian.Periods                            ✓
  lake build Jacobian.Solution                           ✓
```

```text
Build status — recomputed each tick from the tree
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
Challenge target          pass         lake build Jacobian.Challenge
Statement bank            pass         lake build Jacobian.WorkPackets.StatementBank
Periods umbrella          pass         lake build Jacobian.Periods
Solution                  pass         lake build Jacobian.Solution
This tick's new file      pass         lake build Jacobian.Periods.BasisAlignedPeriodSubgroup

Per-directory production sorry-free counts (recomputed):
                                  ratio
  HolomorphicForms             27 / 29
  AnalyticJacobian             23 / 23
  AbelJacobi                   19 / 20
  TraceDegree                  81 / 84   (3 user-WIP files)
  Periods                     170 / 172  (+1 prod file: BasisAlignedPeriodSubgroup)
  ComplexTorus                 47 / 53

Reproduction (per dir):
  total  = `find <dir> -maxdepth 1 -name "*.lean" | wc -l`
  recon  = `find <dir> -maxdepth 1 -name "*Recon*.lean" | wc -l`
  with-sorry-word = (grep -lE "\bsorry\b" <dir>/*.lean) minus Recon files
  ratio = (total − recon − with-sorry-word) / (total − recon)
```

```text
Next tick priorities
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
1. Check the Aristotle Riemann-Roch packet (`72ac3a75`); IN_PROGRESS
   at 3% as of this tick.  If COMPLETE, retrieve and review whatever
   sketch it produced (partial results are useful — they surface
   Mathlib API gaps).
2. Type/Type* generalization. To unfreeze
   `opaque basisAlignedPeriodSubgroup` and route it through
   `basisAlignedPeriodSubgroupConcrete`, lift `IntegralOneCycle` and
   `periodPairing`/`periodSubgroup` in PeriodFunctional from
   `(X : Type)` to `(X : Type*)`. Verify all transitive consumers
   (the AnalyticJacobian/AbelJacobi work) still build.
3. Once that lands, replace `opaque basisAlignedPeriodSubgroup` with
   `noncomputable def := basisAlignedPeriodSubgroupConcrete X` and
   the 2 sorry'd lemmas (`_isClosed`, `_isDiscrete`) become
   provable-in-principle — package one as a substantive Aristotle
   task.
4. Continue ignoring the 5 user-WIP files (AnalyticOfCurveBasis,
   ULiftTransport, PullbackBasis, PushforwardBasis, AnalyticDegree)
   per PROMPT.md.
```

## About

A Lean 4 / Mathlib formalization project targeting the Jacobian variety of a
compact Riemann surface.

The public specification lives in `Jacobian/Challenge.lean` and asks for:

- `genus X` for a compact Riemann surface `X`;
- `Jacobian X` as a compact complex Lie additive group of dimension `genus X`;
- the Abel-Jacobi map `Jacobian.ofCurve`;
- pushforward and pullback maps along holomorphic maps;
- the degree of a holomorphic map of compact Riemann surfaces;
- the identity `pushforward f (pullback f P) = degree f • P`.

Approach: the analytic period-lattice construction
`Jacobian X = H0(X, Ω¹)* / H1(X, Z)`, built up through reusable layers
(complex tori, holomorphic forms, period integration, Abel-Jacobi, degree).

See `plan.md` for the full roadmap, phase breakdown, anti-hack audit, and
delegation strategy for Aristotle.
