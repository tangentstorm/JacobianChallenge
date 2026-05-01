# Scope-out: remaining unproved blueprint dep-graph nodes

Classification scale (per integrator policy 2026-04-30):

- **TRIVIAL** — one-liner (`exact` / `apply` / definitional unfold).
- **SHORT** — 5–20 LOC plumbing, single helper.
- **MEDIUM** — 20–80 LOC real proof structure, no Mathlib decomposition.
- **HARD** — 80+ LOC, isolated cloud worker, OR in-Mathlib-but-deep.
- **DECOMPOSE** — would require formalizing missing Mathlib chunks first;
  proof factors into new sub-nodes (named in Sketch) that themselves need
  to be scoped out by a follow-up worker.
- **DONE** — discharged on this branch (or already sorry-free upstream).
- **WORKER** — assigned to a dedicated cloud worker; do not touch.
- **?** — could not classify in this pass.

`Decl` column: `<missing>` means no Lean stub exists yet. `Sketch` is one
line max. `Strategy reviewer` is the human/agent best placed to validate
the chosen breakdown.

## sec01 — Compact Riemann surfaces

| Label | Decl | File | Class | Sketch |
|---|---|---|---|---|
| `def:vanishing-order` | `Blueprint.vanishingOrder` | `Jacobian/Blueprint/Sec01/VanishingOrder.lean` | DONE | delegated to production `HolomorphicForms.VanishingOrder.orderAt` |
| `lem:divisor-discrete` | `Blueprint.divisor_discrete` | `Sec01/DivisorDiscrete.lean` | MEDIUM | isolated zeros of analytic germs in chart, transfer along chart change |
| `lem:divisor-finite-support` | `Blueprint.divisor_finite_support` | `Sec01/DivisorFiniteSupport.lean` | SHORT | compact + discrete-no-accumulation ⇒ finite |
| `def:divisor` | `Blueprint.Divisor` | `Sec01/Divisor.lean` | DONE | abbrev for `X →₀ ℤ`, no proof obligation |
| `def:divisor-degree` | `Blueprint.Divisor.degree` | `Sec01/DivisorDegree.lean` | DONE | `Finsupp.sum` definition, no proof obligation |
| `def:meromorphic-function` | `Blueprint.MeromorphicFunctionType` | `Sec01/MeromorphicFunction.lean` | DECOMPOSE | sub-leaves: meromorphic-germ-sheaf, field-of-fractions on Riemann surface |
| `def:principal-divisor` | `Blueprint.principalDivisor` | `Sec01/PrincipalDivisor.lean` | MEDIUM | `Finsupp.onFinset` over `divisor_finite_support`, coefficients = `vanishingOrder` |
| `def:principal-divisors` | `Blueprint.principalDivisors` | `Sec01/PrincipalDivisors.lean` | SHORT | `AddSubgroup.closure (range principalDivisor)` or direct subgroup with `add/neg` closure lemmas |
| `thm:principal-degree-zero` | `Blueprint.principal_degree_zero` | `Sec01/PrincipalDegreeZero.lean` | DECOMPOSE | sub-leaves: residue-theorem on RS, divisor-degree-as-integral, argument-principle |
| `def:meromorphic-to-cp1` | `Blueprint.meromorphicToCp1` | `Sec01/MeromorphicToCp1.lean` | DONE | identity on placeholder type |
| `thm:meromorphic-as-cp1-map` | `Blueprint.meromorphic_as_cp1_map` | `Sec01/MeromorphicAsCp1Map.lean` | DONE | definitionally trivial on placeholder |
| `def:riemann-roch-space` | `Blueprint.riemannRochSpace` | `Sec01/RiemannRochSpace.lean` | DONE | scaffold submodule definition |
| `lem:riemann-roch-space-vector` | `Blueprint.riemann_roch_space_vector` | `Sec01/RiemannRochSpaceVector.lean` | DONE | submodule machinery, no proof obligation |
| `input:divisors` | `Blueprint.input_divisors` | `Sec01/InputDivisors.lean` | SHORT | umbrella import; assemble degree-zero principal subgroup |

## sec02 — Holomorphic forms and genus

| Label | Decl | File | Class | Sketch |
|---|---|---|---|---|
| `def:cotangent-fiber-norm` | `Blueprint.cotangentFiberNormAt` | `Sec02/CotangentFiberNorm.lean` | DONE | merged via sec02-trivial-batch |
| `def:holomorphic-sup-norm` | `Blueprint.holomorphicSupNorm` | `Sec02/HolomorphicSupNorm.lean` | DONE | merged via sec02-trivial-batch |
| `lem:chart-coefficient-bound` | `Blueprint.chart_coefficient_bound` | `Sec02/ChartCoefficientBound.lean` | DONE | Worker C landed; body is sorry-free `‖ω x‖ ≤ 1 · holomorphicSupNorm X ω` via `SectionSupNorm.bddAbove_range_norm` + `le_ciSup` |
| `lem:montel-compactness` | `Blueprint.montel_compactness` | `Sec02/MontelCompactness.lean` | DONE | Worker M landed; umbrella body sorry-free assembly above private leaf `montel_pointwise_extraction` (which carries the 1 remaining genuine math sorry) |
| `thm:hone-unit-ball-compact` | `Blueprint.hone_unit_ball_compact` | `Sec02/HoneUnitBallCompact.lean` | DONE | Worker H landed; full file is sorry-free |
| `thm:fd-from-riesz` | `Blueprint.fd_from_riesz` | `Sec02/FdFromRiesz.lean` | DONE | merged via sec02-trivial-batch |
| `input:finite-dimensionality` | `Blueprint.input_finite_dimensionality` | `Sec02/InputFiniteDimensionality.lean` | DONE | discharged this branch (one-liner via `fd_from_riesz` + `hone_unit_ball_compact`) |
| `thm:fd-holomorphic-one-forms` | `Blueprint.fd_holomorphic_one_forms` | `Sec02/FdHolomorphicOneForms.lean` | SHORT | Banach-data realisation + transport via `LinearEquiv.finiteDimensional`; needs T2/Connected typeclass aligned with production `compactRiemannSurface_finiteDimensionalHolomorphicOneForms` |
| `def:sheaf-cohomology-rs` | `<missing>` | `<missing>` | DECOMPOSE | sub-leaves: sheaf, sheafification, Čech cohomology, derived functors on RS |
| `thm:serre-duality-rs` | `<missing>` | `<missing>` | DECOMPOSE | sub-leaves: sheaf-cohomology, dualizing sheaf, Hodge star, Serre-pairing nondegeneracy |
| `thm:euler-char-line-bundle` | `<missing>` | `<missing>` | DECOMPOSE | sub-leaves: line bundles on RS, Euler characteristic, divisor↔line-bundle correspondence |
| `input:riemann-roch` | `<missing>` | `<missing>` | DECOMPOSE | sub-leaves: euler-char-line-bundle + serre-duality-rs (assembly is short) |
| `prop:genus-zero-degree-one-map` | `HolomorphicForms.homeomorphic_sphere_of_analyticGenus_eq_zero` | `Jacobian/HolomorphicForms/GenusZeroClassification.lean` | WORKER | Aristotle/Codex on RiemannRoch+MeromorphicDegree cluster |
| `def:branched-degree` | `<missing>` | `<missing>` | DECOMPOSE | sub-leaves: ramification index, local degree of holomorphic map, branch points finite |
| `lem:branch-locus-finite` | `<missing>` | `<missing>` | DECOMPOSE | sub-leaves: ramification-index ≥ 2 set is closed-discrete (analytic), then compact+discrete ⇒ finite |
| `lem:degree-one-no-ramification` | `<missing>` | `<missing>` | MEDIUM | unramified ↔ derivative nonzero; degree=1 forces every fiber size 1 hence no branching |
| `thm:local-biholo-unramified` | `<missing>` | `<missing>` | MEDIUM | inverse function theorem on complex 1-manifolds; Mathlib has `HasFDerivAt.localHomeomorph` machinery to wire |
| `thm:degree-one-bijective` | `<missing>` | `<missing>` | SHORT | degree=1 ⇒ injective (covering with one sheet); combine with surjective-from-properness |
| `thm:compact-bijection-homeo` | Mathlib `Continuous.homeoOfEquivCompactToT2` | (re-export) | DONE | sorry-free Mathlib; add `\lean{}` re-export stub if blueprint wants its own name |
| `input:degree-one-isomorphism` | `<missing>` | `<missing>` | SHORT | umbrella combining `degree-one-bijective` + `local-biholo-unramified` + `compact-bijection-homeo` |

## sec03 — Periods and Riemann bilinear

| Label | Decl | File | Class | Sketch |
|---|---|---|---|---|
| `lem:period-homology-invariance` | `Periods.period_homology_invariance_statement` | `Jacobian/Periods/PeriodFunctional.lean` | HARD | production decl is sorry; needs Stokes + closed-form lemma |
| `lem:holomorphic-form-is-closed` | `<missing>` | `<missing>` | MEDIUM | `dω = 0` for holomorphic 1-form via Cauchy-Riemann in chart; chart-invariance via pullback compatibility |
| `thm:stokes-on-rs-with-boundary` | `<missing>` | `<missing>` | DECOMPOSE | sub-leaves: manifold-with-corners on RS, integration of forms, Stokes on simplex/box, partition-of-unity assembly |
| `def:symplectic-basis` | `<missing>` (related: `Periods.symplectic_basis_of_cycles`) | (Periods file) | DECOMPOSE | sub-leaves: H₁(X,ℤ), intersection pairing, existence of symplectic basis (homology rank 2g) |
| `thm:polygonal-model` | `<missing>` | `<missing>` | DECOMPOSE | sub-leaves: triangulation of compact surface, cut-along-cycles, fundamental polygon |
| `lem:primitive-on-polygon` | `<missing>` | `<missing>` | DECOMPOSE | sub-leaves: simply-connected ⇒ closed-form-has-primitive (Mathlib has on `ℂ`, not on polygon manifold) |
| `thm:bilinear-from-stokes` | `<missing>` | `<missing>` | DECOMPOSE | sub-leaves: stokes-on-rs-with-boundary, primitive-on-polygon, polygonal-model identification |
| `thm:hermitian-positivity` | `<missing>` | `<missing>` | MEDIUM | once bilinear-from-stokes reduces it: `∫_X ω∧conj(ω) > 0` for `ω≠0` via local positivity in chart |
| `thm:period-vectors-full-real-rank` | `Periods.period_vectors_linearIndependent_of_symplectic` (sorry) | `Jacobian/Periods/PeriodVectorsLinearIndependent.lean` | HARD | depends on hermitian-positivity + bilinear-from-stokes |
| `input:riemann-bilinear` | `Periods.period_vectors_linearIndependent_of_symplectic` | (same) | SHORT | umbrella; assembly once dependencies land |
| `def:period-pairing` (dangling) | `Periods.periodFunctional` (partial) | `Jacobian/Periods/PeriodFunctional.lean` | SHORT | add blueprint label + `\lean{}` annotation pointing at existing decl |
| `thm:period-lattice` (dangling) | `Periods.periodSubgroup_isZLattice` (sorry) | `Jacobian/Periods/PeriodFunctional.lean` | HARD | production is sorry; depends on `period_vectors_linearIndependent_of_symplectic` |

## sec04 — Complex tori and Jacobians

All labels covered by `prop:complex-torus-package` (`\leanok` in blueprint, sorry-free production decls in `JacobianChallenge.ComplexTorus.*`). Dangling ref `def:analytic-jacobian` already maps to `AnalyticJacobian.AnalyticJacobianType`.

| Label | Decl | File | Class | Sketch |
|---|---|---|---|---|
| `prop:complex-torus-package` | `ComplexTorus.{FullComplexLattice, quotient, ...}` | `Jacobian/ComplexTorus/*.lean` | DONE | `\leanok` |
| `def:analytic-jacobian` (dangling) | `AnalyticJacobian.AnalyticJacobianType` | `Jacobian/AnalyticJacobian/*.lean` | SHORT | add blueprint label + `\lean{}` annotation |

## sec05 — Abel-Jacobi map

| Label | Decl | File | Class | Sketch |
|---|---|---|---|---|
| `lem:aj-path-independence` | `AbelJacobi.analyticOfCurve` | `Jacobian/AbelJacobi/*.lean` | DONE | `\leanok` |
| `lem:aj-self` | `Jacobian.ofCurve_self` | `Jacobian/Solution.lean` | DONE | `\leanok` |
| `lem:aj-holomorphic` | `Jacobian.ofCurve_contMDiff` | `Jacobian/Solution.lean` | DONE | `\leanok` |
| `thm:aj-divisor-hom` | `<missing>` | `<missing>` | MEDIUM | `AJ` extends to `Divisor X →+ Jacobian X` by ℤ-linearity from pointwise definition; production-side `Jacobian.ofCurve` already separates points |
| `thm:abel-existence` | `<missing>` | `<missing>` | DECOMPOSE | sub-leaves: Abel's theorem (deep), theta-function/Riemann-existence, line-bundle-of-divisor degree-zero ⇒ has section |
| `lem:principal-deg0-simple-support-deg1` | `<missing>` | `<missing>` | SHORT | combinatorial: degree=0 + 2-point support + Z-coefficients ⇒ one +1, one -1 |
| `thm:riemann-hurwitz-deg1` | `<missing>` | `<missing>` | DECOMPOSE | sub-leaves: Riemann-Hurwitz formula (genus + ramification), branched-degree theory, degree-one specialisation |
| `thm:abel-point-separation` | `AbelJacobi.pathIntegralFunctional_separates_points` | `Jacobian/AbelJacobi/AnalyticOfCurveBasis.lean` | HARD | production is sorry-free assembly above `period_congruence_distinct_implies_genus_zero` (which is sorry, depending on Abel + Riemann-Hurwitz) |
| `input:abel-theorem` | `AbelJacobi.pathIntegralFunctional_separates_points` | (same) | SHORT | umbrella; same as above |
| `thm:abel-jacobi-injective` (dangling) | `Jacobian.ofCurve_inj` | `Jacobian/Solution.lean` | SHORT | add blueprint label + `\lean{}` annotation; production decl exists |

## sec06 — Degree, trace, push-pull

| Label | Decl | File | Class | Sketch |
|---|---|---|---|---|
| `lem:pullback-forms` | `TraceDegree.pullbackFormsLinearMap` | `Jacobian/TraceDegree/*.lean` | DONE | `\leanok` |
| `lem:trace-forms` | `TraceDegree.analyticPushforward` | `Jacobian/TraceDegree/*.lean` | DONE | `\leanok` |
| `lem:push-pull-descend` | `Jacobian.{pullback, pushforward}` | `Jacobian/Solution.lean` | DONE | `\leanok` |
| `thm:trace-pullback` (dangling) | `<missing>` (related: `TraceDegree.analyticPushforward_pullback`?) | `Jacobian/TraceDegree/*.lean` | HARD | trace-pullback identity `tr_f(f^* η) = deg f · η`; production-side decl is sorry-bearing |
| `thm:push-pull-functoriality` (dangling) | `Jacobian.{pullback_id_apply, pullback_comp_apply, pushforward_id_apply, pushforward_comp_apply}` | `Jacobian/Solution.lean` | SHORT | id/comp laws; add blueprint label collecting four existing decls |
| `thm:pushforward-pullback` (dangling) | `Jacobian.pushforward_pullback` | `Jacobian/Solution.lean` / `Challenge.lean` | HARD | production sorry; depends on `thm:trace-pullback` and degree definition |

## sec07 — Main theorem assembly

| Label | Decl | File | Class | Sketch |
|---|---|---|---|---|
| `thm:challenge-api` | public API in `Challenge.lean` | `Jacobian/Challenge.lean` | DONE | `\leanok`; sorry-bearing internally but covered by other rows |

## TRIVIAL nodes discharged on this branch

- `input_finite_dimensionality` (commit a6e8efe)
- `vanishingOrder` (commit 560e1b0)
- `meromorphic_as_cp1_map` (commit 2d929d1)

## Suggested next pickups

- **Easiest SHORT**: `principalDivisors` (AddSubgroup wrapper), `input_divisors` (umbrella), `input_riemann_bilinear` (umbrella once deps land), `input_degree_one_isomorphism` (umbrella).
- **Easiest MEDIUM**: `divisor_finite_support` (compact+discrete ⇒ finite), `principalDivisor` (Finsupp on finite-support set), `principal_deg0_simple_support_deg1` (combinatorial).
- **First DECOMPOSE worker should target**: `def:sheaf-cohomology-rs` (largest dependency cluster — feeds Serre duality, Riemann-Roch, eventually genus-zero classification).
- **Stokes chain (DECOMPOSE)**: `thm:stokes-on-rs-with-boundary` is the single biggest classical-input gap; once decomposed it unlocks `thm:bilinear-from-stokes` → `thm:period-vectors-full-real-rank` → `thm:period-lattice`.
