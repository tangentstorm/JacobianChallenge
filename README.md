# Jacobian Challenge

A Lean 4 / Mathlib formalization of the Jacobian variety of a compact Riemann surface (see _About_ below for scope).

## Progress Report

Last tick: 2026-04-27 15:35 EDT

```text
Headline progress markers (every value below is a fresh count from this tick)
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
Public spec discharged          0 / 24    sorries in Jacobian/Challenge.lean (frozen target)
StatementBank declarations     22         named decls in Jacobian/WorkPackets/StatementBank.lean
                                          (excluding 2 Inventory metadata items)
Aristotle integrations to date 87         `"status":"integrated"` lines in aristotle_jobs.jsonl
Production sorry-free files  378 / 386    using the precise count (real `sorry` tactics; doc-comment
                                          matches and intentional design files excluded).
                                          The 8 production files with real sorries:
                                            Claude-owned (3 files, 7 sorries):
                                              HolomorphicForms/CompactRiemannSurface  (1, Riemann-Roch)
                                              HolomorphicForms/GenusZeroClassification (1, uniformization)
                                              Periods/PeriodLattice                   (5, blocked on opaque)
                                            User-WIP (5 files, 22 sorries) — Claude leaves untouched:
                                              AbelJacobi/AnalyticOfCurveBasis         (6)
                                              ComplexTorus/ULiftTransport             (6)
                                              TraceDegree/PullbackBasis               (6)
                                              TraceDegree/PushforwardBasis            (3)
                                              TraceDegree/AnalyticDegree              (1, untracked)

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
Active jobs (ours):     1 / 5  Off-critical-path big task submitted this tick per user feedback
                        "just give aristotle something off the critical path, even if it's big":
                        `72ac3a75` compactRiemannSurface_finiteDimensionalHolomorphicOneForms
                                   (HolomorphicForms/CompactRiemannSurface.lean) — the deep
                                   classical theorem that H⁰(X, Ω¹) is finite-dimensional for
                                   a compact connected Riemann surface (Hodge / Riemann-Roch).
                                   Expected to take hours; partial sketch + named blocker is
                                   an acceptable outcome.
Integrated this tick:   None from Aristotle.
```

```text
Local cadence this tick (Claude-owned, substantive bottom-up infrastructure)
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
NEW Jacobian/HolomorphicForms/BasisAlignedDualEquiv.lean (3 defs + 1 theorem):

  `holomorphicOneFormFinBasis E X` — an arbitrary
    `Module.Basis (Fin (analyticGenus E X)) ℂ (HolomorphicOneForm E X)`
    via `Module.finBasis`. Non-canonical (uses `Module.Free.chooseBasis`).

  `holomorphicOneFormDualFinBasis E X` — the dual basis (in the linear
    dual space `HolomorphicOneForm E X →ₗ[ℂ] ℂ`).

  `holomorphicOneFormDualEquiv E X :
     (HolomorphicOneForm E X →ₗ[ℂ] ℂ) ≃ₗ[ℂ] (Fin (analyticGenus E X) → ℂ)`
    — the basis-aligned dual equivalence; the bridge between the
    intrinsic functional-space description used throughout the
    AnalyticJacobian/AbelJacobi work and the basis-aligned model used
    in `Jacobian/Periods/PeriodLattice.lean` and `Jacobian/Solution.lean`.

  `holomorphicOneFormDualEquiv_dualBasis_apply` — pointwise check that
    the equiv sends a dual basis vector at index i to `Pi.single i 1`.
    Proof: by_cases on `i = j`, then `Module.Basis.equivFun_self` +
    `Pi.single_apply` (~6 lines real content, not 1-line filler).

Wired into `Jacobian/HolomorphicForms.lean` umbrella. Builds clean.

Why this matters: it is the bottom-up infrastructure piece that lets a
future tick replace `opaque periodSubgroup` in
`Jacobian/Periods/PeriodLattice.lean` with the concrete definition
`AddSubgroup.map holomorphicOneFormDualEquiv.toAddMonoidHom
  (JacobianChallenge.Periods.periodSubgroup ℂ X)` — i.e., the image of
the existing functional-space periodSubgroup under this basis bridge.
Once the opaque is unfrozen, the 5 PeriodLattice sorries (closedness,
discreteness, fundamental-domain compactness, coverage) become
provable rather than literally-sorry-only, and at least some of them
become substantive Aristotle-sized tasks.
```

```text
Build status — recomputed each tick from the tree
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
Challenge target          pass         lake build Jacobian.Challenge
Statement bank            pass         lake build Jacobian.WorkPackets.StatementBank
HolomorphicForms umbrella pass         lake build Jacobian.HolomorphicForms
This tick's new file      pass         lake build Jacobian.HolomorphicForms.BasisAlignedDualEquiv

Per-directory production sorry-free counts (recomputed):
                                  ratio
  HolomorphicForms             27 / 29
  AnalyticJacobian             23 / 23
  AbelJacobi                   19 / 20
  TraceDegree                  81 / 84   (3 user-WIP files added since last tick)
  Periods                     169 / 171
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
1. Use the new `holomorphicOneFormDualEquiv` to actually unfreeze
   `opaque periodSubgroup` in `Jacobian/Periods/PeriodLattice.lean`.
   Concrete plan: replace the opaque with
     `noncomputable def periodSubgroup (X) [...] :=
        AddSubgroup.map (holomorphicOneFormDualEquiv ℂ X).toLinearMap.toAddMonoidHom
          (JacobianChallenge.Periods.periodSubgroup ℂ X)`.
   That converts 5 unprovable-while-opaque sorries into bounded
   topology obligations on `AddSubgroup.map` of a discrete subgroup.
2. Once unfrozen, package `periodSubgroup_isClosed` (and similar)
   as substantive Aristotle tasks — these will be 15-30+ line proofs
   about closures of subgroup images, not 1-line trivials.
3. Continue ignoring the 5 user-WIP files (AnalyticOfCurveBasis,
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
