# Blueprint Audit (Phase A)

Audit of all `\label{...}` declarations in `tex/sections/0{0..8}-*.tex` against
the Lean codebase under `Jacobian/`.

The goal: every node in the blueprint dependency graph should be
"pick-up-able" — a contributor should be able to look up its statement
in Lean (real decl or `sorry`-stub) and see all dependencies.

## Summary

| Category                                         | Count |
|--------------------------------------------------|-------|
| Total `\label{...}` excluding `sec:*`            |    57 |
| Already annotated with `\lean{...}`              |    11 |
| Dangling `\uses{...}` references (no `\label`)   |     8 |
| Existing decl found, can add `\lean{}`           |    ~5 |
| Needs fresh stub                                 |   ~41 |

## Table 1 — Already annotated `\lean{}`

| Label                                              | Lean decl                                                                                       |
|----------------------------------------------------|-------------------------------------------------------------------------------------------------|
| `prop:genus-zero-degree-one-map`                   | `JacobianChallenge.HolomorphicForms.homeomorphic_sphere_of_analyticGenus_eq_zero` (NB: actually points at the wrong proposition; that decl is the assembled `thm:genus-zero-classification`) |
| `lem:period-homology-invariance`                   | `JacobianChallenge.Periods.period_homology_invariance_statement`                                |
| `input:riemann-bilinear`                           | `JacobianChallenge.Periods.period_vectors_linearIndependent_of_symplectic`                      |
| `prop:complex-torus-package`                       | `JacobianChallenge.ComplexTorus.{FullComplexLattice, quotient, quotient_addCommGroup, ...}`     |
| `lem:aj-path-independence`                         | `JacobianChallenge.AbelJacobi.analyticOfCurve`                                                  |
| `lem:aj-self`                                      | `Jacobian.ofCurve_self`                                                                          |
| `lem:aj-holomorphic`                               | `Jacobian.ofCurve_contMDiff`                                                                    |
| `input:abel-theorem`                               | `JacobianChallenge.AbelJacobi.pathIntegralFunctional_separates_points`                          |
| `lem:pullback-forms`                               | `JacobianChallenge.TraceDegree.pullbackFormsLinearMap`                                          |
| `lem:trace-forms`                                  | `JacobianChallenge.TraceDegree.analyticPushforward`                                             |
| `lem:push-pull-descend`                            | `Jacobian.pullback`, `Jacobian.pushforward`                                                     |
| `thm:challenge-api`                                | `genus, genus_eq_zero_iff_homeo, Jacobian, Jacobian.ofCurve, Jacobian.pushforward, Jacobian.pullback, Jacobian.pushforward_pullback` |

(Counted as 11 unique blueprint labels; the first row of mismatch is fixed in Phase B by adding the
proper `\lean{}` for `prop:genus-zero-degree-one-map` referencing `RiemannRoch` data and re-pointing
the `\lean{...analyticGenus_eq_zero...}` annotation into the new `thm:genus-zero-classification` block.)

## Table 2 — Dangling `\uses{...}` references (need new `\label`)

These names appear in `\uses{...}` but no `\label{...}` defines them in `tex/sections/`.
Phase B adds a `\label`+statement block for each, with `\lean{}` pointing at a Lean decl
(existing or new stub).

| Dangling label                       | Used in                                                                | Section to add | Existing Lean? |
|--------------------------------------|------------------------------------------------------------------------|----------------|----------------|
| `def:period-pairing`                 | `lem:aj-path-independence` (sec05)                                     | sec03          | partial — `JacobianChallenge.Periods.periodFunctional` exists |
| `def:analytic-jacobian`              | `lem:aj-holomorphic` (sec05), `lem:push-pull-descend` (sec06), `thm:challenge-api` (sec07) | sec04          | yes — `JacobianChallenge.AnalyticJacobian.AnalyticJacobianType` |
| `def:abel-jacobi`                    | `lem:aj-self`, `lem:aj-holomorphic`, `thm:aj-divisor-hom` (sec05), `thm:challenge-api` | sec05          | yes — `Jacobian.ofCurve` / `JacobianChallenge.AbelJacobi.analyticOfCurve` |
| `thm:abel-jacobi-injective`          | `thm:challenge-api`; also referenced by trailing `\proof[Proof of Theorem~\ref{thm:abel-jacobi-injective}]` in sec05 | sec05  | yes — `Jacobian.ofCurve_inj` |
| `thm:fd-holomorphic-one-forms`       | `thm:challenge-api`                                                    | sec02          | partial — `analyticGenus` def, `FiniteDimensionalHolomorphicOneForms` class |
| `thm:genus-zero-classification`      | `thm:challenge-api`; current `\lean{}` annotation on `prop:genus-zero-degree-one-map` (line 152 of sec02) is mis-attached — really points at this | sec02 | yes — `JacobianChallenge.HolomorphicForms.analyticGenus_eq_zero_iff_homeomorphic_sphere` |
| `thm:pushforward-pullback`           | `thm:challenge-api`; trailing `\proof[Proof of Theorem~\ref{thm:pushforward-pullback}]` in sec06 | sec06 | yes — `Jacobian.pushforward_pullback` |
| `thm:push-pull-functoriality`        | `thm:challenge-api`; trailing `\proof[Proof of Theorem~\ref{thm:push-pull-functoriality}]` in sec06 | sec06 | yes — implicit through `Jacobian.pushforward_id_apply`, `Jacobian.pushforward_comp_apply`, `Jacobian.pullback_id_apply`, `Jacobian.pullback_comp_apply` |

Two additional dangling references discovered while checking:

- `def:analytic-genus` — used in sec02 line 6 ("Definition~\ref{def:analytic-genus}") but no `\label{def:analytic-genus}` block exists. NB: not in `\uses{}` directly.
- `thm:trace-pullback` — `\proof[Proof of Theorem~\ref{thm:trace-pullback}]` in sec06 (line 45) and `\ref{thm:trace-pullback}` in sec06 line 96 reference it but no `\label`.
- `thm:period-lattice` — `\proof[Proof of Theorem~\ref{thm:period-lattice}]` in sec03 (line 172) and ref in sec04 line 32 reference it but no `\label`.

These three are picked up in Phase B as well (treat them as dangling refs).

## Table 3 — Has existing decl, can add `\lean{}`

(After examining the codebase: many of the unannotated leaves in sec01 and sec02 do **not**
have matching real decls — only placeholder substrate. So this list is short.)

| Label                                  | Existing decl                                                                |
|----------------------------------------|------------------------------------------------------------------------------|
| `def:divisor`                          | `JacobianChallenge.HolomorphicForms.Divisor` (in `Jacobian/HolomorphicForms/Divisor.lean`) |
| `def:divisor-degree`                   | `JacobianChallenge.HolomorphicForms.Divisor.degree`                          |
| `thm:fd-from-riesz`                    | `JacobianChallenge.HolomorphicForms.FiniteDimensionalHolomorphicOneForms`+`analyticGenus` (the class is the named target; the proof is `sorry` — so this is actually equivalent to `notready`+`\lean{}`) |
| `thm:compact-bijection-homeo`          | Mathlib has `Continuous.homeoOfEquivCompactToT2` — could point at it; more useful to make a `JacobianChallenge.Blueprint` re-export stub for picky-up-ability |
| `def:meromorphic-function`             | partial: `JacobianChallenge.HolomorphicForms.MeromorphicMapToSphere` exists but is a different shape (map to OnePoint ℂ, not the field of germs); leave as fresh stub |

## Table 4 — Needs fresh stub (Phase C)

These labels have no plausible existing Lean decl. Phase C creates one
`Jacobian/Blueprint/Sec0X/<Name>.lean` per label with a single `sorry`-stubbed
declaration matching the blueprint statement.

### sec01

- `def:vanishing-order`
- `lem:divisor-discrete`
- `lem:divisor-finite-support`
- `def:meromorphic-function`
- `def:principal-divisor`
- `def:principal-divisors`
- `thm:principal-degree-zero`
- `def:meromorphic-to-cp1`
- `thm:meromorphic-as-cp1-map`
- `def:riemann-roch-space`
- `lem:riemann-roch-space-vector`
- `input:divisors`

### sec02

- `def:cotangent-fiber-norm`
- `def:holomorphic-sup-norm`
- `lem:chart-coefficient-bound`
- `lem:montel-compactness`
- `thm:hone-unit-ball-compact`
- `input:finite-dimensionality`
- `def:sheaf-cohomology-rs`
- `thm:serre-duality-rs`
- `thm:euler-char-line-bundle`
- `input:riemann-roch`
- `def:branched-degree`
- `lem:branch-locus-finite`
- `lem:degree-one-no-ramification`
- `thm:local-biholo-unramified`
- `thm:degree-one-bijective`
- `input:degree-one-isomorphism`
- `def:analytic-genus` (Phase B)
- `thm:fd-holomorphic-one-forms` (Phase B; pointable at existing class)
- `thm:genus-zero-classification` (Phase B; pointable at existing decl)

### sec03

- `lem:holomorphic-form-is-closed`
- `thm:stokes-on-rs-with-boundary`
- `def:symplectic-basis`
- `thm:polygonal-model`
- `lem:primitive-on-polygon`
- `thm:bilinear-from-stokes`
- `thm:hermitian-positivity`
- `thm:period-vectors-full-real-rank`
- `def:period-pairing` (Phase B)
- `thm:period-lattice` (Phase B; new refnode)

### sec05

- `thm:aj-divisor-hom`
- `thm:abel-existence`
- `lem:principal-deg0-simple-support-deg1`
- `thm:riemann-hurwitz-deg1`
- `thm:abel-point-separation`

### sec06

- `thm:trace-pullback` (Phase B; new refnode)
- `thm:push-pull-functoriality` (Phase B; pointable at existing decls)
- `thm:pushforward-pullback` (Phase B; pointable at existing decl)

(sec04, sec07, sec08 have all labels covered; sec00 is intro.)

## Phase D — Handoff completeness pass (2026-04-30)

Short answer: **not fully complete yet** for blind implementation by other agents.
The Sec01/Sec02 leaf files now have useful local proof sketches, but the
global graph still misses an explicit "for each node, what exact Lean target
should be implemented next?" table.

This section adds that implementation contract.

### D.1 Blueprint graph nodes currently imported by `Jacobian/Blueprint.lean`

Each row records: (i) declaration status, (ii) expected implementation shape,
(iii) intended production/mathlib landing spot.

#### Sec01

| Node file | Decl status | Implementation target (next action) | Landing/API target |
|---|---|---|---|
| `Sec01/VanishingOrder.lean` | Stub with sketch + `sorry` | Define via chart-local `meromorphicOrderAt`; prove chart-independence lemma | `Jacobian.HolomorphicForms.VanishingOrder` + Mathlib `meromorphicOrderAt` |
| `Sec01/Divisor.lean` | Concrete structure scaffold | Keep as lightweight blueprint alias | `Jacobian.HolomorphicForms.Divisor` |
| `Sec01/DivisorDegree.lean` | Concrete scaffold | Connect to `Finsupp.total`-style sum over finite support | `Divisor.degree` API |
| `Sec01/DivisorDiscrete.lean` | Stub with sketch + `sorry` | Reduce to isolated zeros/poles in charts, then transfer globally | local complex analysis + manifold chart-change |
| `Sec01/DivisorFiniteSupport.lean` | Stub with sketch + `sorry` | Use compactness + discrete support to get finiteness | `Set.Finite` / compact-discrete argument |
| `Sec01/MeromorphicFunction.lean` | Abstract placeholder type | Decide final representation (`X →ₘ OnePoint ℂ` vs local-germ class) | production `MeromorphicMapToSphere` |
| `Sec01/PrincipalDivisor.lean` | Stub with sketch + `sorry` | Package vanishing-order coefficients + finite support | `Divisor` constructor |
| `Sec01/PrincipalDivisors.lean` | Stub with sketch + `sorry` | Build `AddSubgroup`; multiplication/inversion ↔ add/neg identities | `AddSubgroup` closure lemmas |
| `Sec01/PrincipalDegreeZero.lean` | Stub with sketch + `sorry` | Prove `degree (principalDivisor f)=0` via residue/order conservation | divisor degree API |
| `Sec01/MeromorphicToCp1.lean` | Definition scaffold | keep; wire coercions/eval notation | map-to-sphere interface |
| `Sec01/MeromorphicAsCp1Map.lean` | Stub with sketch + `sorry` | Build continuous map to `ℂP¹` and prove nonconstancy | production `MeromorphicDegree` helpers |
| `Sec01/RiemannRochSpace.lean` | Definition scaffold | finalize as `Submodule` of meromorphic functions with divisor bound | RR space API |
| `Sec01/RiemannRochSpaceVector.lean` | Theorem scaffold | prove vector-space instance closure | submodule machinery |
| `Sec01/InputDivisors.lean` | Umbrella statement | assemble sec01 endpoint theorem | section-level import glue |

#### Sec02

| Node file | Decl status | Implementation target (next action) | Landing/API target |
|---|---|---|---|
| `Sec02/CotangentFiberNorm.lean` | Stub with sketch + `sorry` | Pick Hermitian metric model and prove chart invariance | `SectionMetric`/`SectionFiberNorm` production files |
| `Sec02/HolomorphicSupNorm.lean` | Stub with sketch + `sorry` | Define sup over compact base; prove finiteness/compatibility | `SectionSupNorm` production file |
| `Sec02/ChartCoefficientBound.lean` | Stub with sketch + `sorry` | Cauchy estimate in chart balls with explicit constants | `ChartCoeffExtractionRecon` + `Periods/ChartBallAtPoint` helpers |
| `Sec02/MontelCompactness.lean` | Stub with sketch + `sorry` | Arzelà–Ascoli/Montel subsequence extraction on atlas cover | `CompactRiemannSurface` Montel obligations |
| `Sec02/HoneUnitBallCompact.lean` | Stub with sketch + `sorry` | combine coefficient bounds + Montel to compact closed unit ball | Banach-data compactness leaf |
| `Sec02/FdFromRiesz.lean` | Stub with sketch + `sorry` | direct wrapper of `FiniteDimensional.of_isCompact_closedBall₀` | Mathlib finite-dimensionality theorem |
| `Sec02/InputFiniteDimensionality.lean` | Stub with sketch + `sorry` | one-line assembly: previous row + unit ball compact | section endpoint theorem |
| `Sec02/FdHolomorphicOneForms.lean` | Stub with sketch + `sorry` | transfer FD result to analytic genus API | `analyticGenus` / `FiniteDimensionalHolomorphicOneForms` |

### D.2 Remaining graph-level gap (critical for handoff)

Status update (2026-04-30, later pass): `Blueprint/Sec03`–`Sec07` stub files
have now been created and imported in `Jacobian/Blueprint.lean`, so the graph is
no longer missing whole sections at the file level.

Remaining risk is now **statement fidelity** (some newly created stubs are
intentionally coarse placeholders and should be tightened to match the exact TeX
quantifiers/types before implementation sprinting begins).

### D.3 Acceptance checklist for "complete enough"

Mark handoff complete only when all are true:

- [ ] Every `\label{...}` node in sec01–sec07 has exactly one Lean declaration
      in `Jacobian/Blueprint/SecXX`.
- [ ] Every declaration has either a real proof or a `PROOF SKETCH` naming the
      concrete API lemmas expected to discharge it.
- [ ] `Jacobian/Blueprint.lean` imports all node files, with no missing section.
- [ ] Each dangling TeX `\uses{...}` reference has either a new label or has
      been removed/renamed consistently.
- [ ] Theorem names in blueprint stubs match production-facing names sufficiently
      to allow `rw`/`exact` assembly without ad hoc translation layers.

## Phase E — Exact handoff signatures (cloud-worker ready)

This section records the **exact target statement shape** each remaining coarse
stub should be upgraded to before implementation.

| Blueprint stub | Target Lean statement/API |
|---|---|
| `Sec02/AnalyticGenusDef` | `noncomputable def analyticGenus (𝕜 X) : ℕ := FiniteDimensional.finrank 𝕜 (HolomorphicOneForm 𝕜 X)` |
| `Sec02/FdHolomorphicOneFormsThm` | theorem `[FiniteDimensional ℂ (HolomorphicOneForm ℂ X)]` via `compactRiemannSurface_finiteDimensionalHolomorphicOneForms` |
| `Sec02/GenusZeroClassification` | `analyticGenus ℂ X = 0 ↔ Nonempty (X ≃ₜ OnePoint ℂ)` (or sphere-homeomorphic equivalent) |
| `Sec03/PeriodPairing` | `periodPairing : H₁(X,ℤ) →+ (HolomorphicOneForm ℂ X →ₗ[ℂ] ℂ)` |
| `Sec03/PeriodLattice` | theorem `IsFullLattice` for `AddSubgroup.range periodPairing` (bridge: `periodFullComplexLattice`) |
| `Sec04/AnalyticJacobian` | `def analyticJacobian := quotient (Hdual / periods)` compatible with `AnalyticJacobianType` |
| `Sec05/AbelJacobiDef` | `abelJacobi (P : X) : X → analyticJacobian X` |
| `Sec05/AbelJacobiInjective` | `(0 < analyticGenus ℂ X) → Function.Injective (abelJacobi (X:=X) P)` |
| `Sec05/AbelPointSeparation` | point-separation functional theorem (`pathIntegralFunctional_separates_points`) |
| `Sec06/TracePullback` | `analyticPushforward f hf (analyticPullback f hf η) = (ContMDiff.degree f hf) • η` |
| `Sec06/PushPullFunctoriality` | id/comp laws + holomorphicity for descended `pushforward`/`pullback` |
| `Sec06/PushforwardPullback` | `pushforward f hf (pullback f hf P) = (ContMDiff.degree f hf) • P` |

Recommended worker protocol per node:
1. Replace placeholder type/`True` statement with the target signature above.
2. Add a bridge lemma naming the production declaration used for discharge.
3. Keep one intentional `sorry` only if upstream API is genuinely missing.

Operational assignment cards for less-capable agents are tracked in:
`ref/cloud-worker-handoff.md`.
