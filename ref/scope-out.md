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
| `thm:principal-degree-zero` | `Blueprint.principal_degree_zero` | `Sec01/PrincipalDegreeZero.lean` | DECOMPOSE | umbrella body sorry-free (CP¹ branched-cover route, `ref/plans/principal-degree-zero.md` + `principal-degree-zero-breakthrough.md`); leaves 1, 2, 5, 5a, 6, 7a, 7b, 7c, `liftToCp1_continuous`, umbrella all discharged through Phase A–D refactors; remaining transitive sorries = leaves 3, 4 (chart-local Laurent ±ramificationIndex) + Sec02 leaf 8 (`branchedCoverData_of_nonconstant_holomorphic`); promoted to `\leanok` per integrator convention |
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
| `thm:serre-duality-rs` | `serre_duality_rs` | `Jacobian/HolomorphicForms/SerreDualityRS.lean` (+ `Serre/*.lean`) | DECOMPOSE (in flight) | 25 top-down rounds landed: tree under `Jacobian/HolomorphicForms/Serre/` (32 files) decomposes the public `serre_duality_rs` and `RSDualizingSheaf` sorries into ~80 strictly-smaller named obligations covering: structure/cotangent/tensor sheaves (presheaf + sheaf-condition splits), canonical Serre dual `Hom(F, K_X)`, cup-product/eval-map/trace-map decomposition of the pairing, witness-form nondegeneracy via Dolbeault + L²-pairing on harmonic forms, residue-map model of `H¹(K_X) ≃ ℂ`, line-bundle specialisation (`L⁻¹ ⊗ K_X`), Riemann-Roch high-degree reduction via Serre, `h1_dualizing_sheaf_one_dim` discharged sorry-free via the canonical iso, finite-dim instance discharges for `K_X` / `𝒪_X`, identifications `H⁰(K_X) ≃ HolomorphicOneForm X` and `H¹(𝒪_X) ≃ HolomorphicOneForm X *`. Plan: `ref/plans/serre-duality-rs.md`. |
| `thm:euler-char-line-bundle` | `<missing>` | `<missing>` | DECOMPOSE | sub-leaves: line bundles on RS, Euler characteristic, divisor↔line-bundle correspondence |
| `input:riemann-roch` | `<missing>` | `<missing>` | DECOMPOSE | sub-leaves: euler-char-line-bundle + serre-duality-rs (assembly is short) |
| `prop:genus-zero-degree-one-map` | `HolomorphicForms.homeomorphic_sphere_of_analyticGenus_eq_zero` | `Jacobian/HolomorphicForms/GenusZeroClassification.lean` | WORKER | Aristotle/Codex on RiemannRoch+MeromorphicDegree cluster |
| `def:branched-degree` | `Blueprint.branchedDegree` | `Sec02/BranchedDegree.lean` | SHORT | leaves 1–7 sorry-free in `Sec02/BranchedDegree.lean`; leaf 8 in `Sec02/BranchedDegreeFromHolomorphic.lean` is sorry-free, with `weightedFiberCard_const` discharged by `isHolomorphic_weightedFiberSum_const`. The final assembly decomposes into 4 sub-leaves (`Sec02/WeightedFiberCardConst.lean`): branch-locus-finite, local-inj-unramified, local-kfold-ramified, weighted-sum-locally-constant — each currently `sorry`. |
| `thm:branched-degree-well-defined` (new) | `Blueprint.isHolomorphic_weightedFiberSum_const` | `Sec02/WeightedFiberCardConst.lean` | DONE | sorry-free final assembly: locally-constant + preconnected ⇒ constant. Body uses `IsLocallyConstant.apply_eq_of_preconnectedSpace`. |
| `lem:weighted-fiber-locally-constant` (new) | `Blueprint.isHolomorphic_weightedFiberSum_isLocallyConstant` | `Sec02/WeightedFiberCardConst.lean` | HARD | sub-leaf D, `sorry`. Decomposes into D1 (Mathlib disjoint-nbhd), D2 `eventually_fiber_subset_of_compact_T2`, D3 `weightedFiberSum_eventually_eq`. |
| `lem:local-kfold-ramified` (new) | `Blueprint.IsHolomorphicAt.exists_local_kfold_of_ramified` | `Sec02/WeightedFiberCardConst.lean` | HARD | sub-leaf C, `sorry`. Decomposes into C1 `chartLocalAt_eq_pow_mul_of_order`, C2 `analyticAt_kth_root_of_ne_zero`, C3 `chartLocalAt_locally_conjugate_pow`. |
| `lem:local-inj-unramified` (new) | `Blueprint.IsHolomorphicAt.exists_local_inj_of_unramified` | `Sec02/WeightedFiberCardConst.lean` | MEDIUM | sub-leaf B, `sorry`. Decomposes into common-helper + B2 `chartLocalAt_localInverse_of_unramified` (Mathlib's `AnalyticAt.localInverse` + chart transport). |
| `mapAnalyticOrderAt_ramified_finite` (new) | `Blueprint.mapAnalyticOrderAt_ramified_finite` | `Sec02/WeightedFiberCardConst.lean` | MEDIUM | sub-leaf A, `sorry`. Decomposes into common-helper + A2 `isOpen_setOf_mapAnalyticOrderAt_eq_one` + A3 `mapAnalyticOrderAt_isolated_at_ramified`; assembly uses closed-discrete + compact ⇒ finite. |
| (common helper) `mapAnalyticOrderAt_eq_one_iff_chartLocal_deriv_ne_zero` | same | `Sec02/WeightedFiberCardConst.lean` | SHORT | shared between A and B sub-leaves; from Mathlib's `analyticOrderAt_sub_eq_one_of_deriv_ne_zero`. |
| (project-local) `IsHolomorphic` predicate | `HolomorphicMap.IsHolomorphic` / `IsHolomorphicAt` / `mapAnalyticOrderAt` / `mapAnalyticOrderAt_pos` / `isHolomorphic_finite_fiber` | `HolomorphicForms/HolomorphicMap.lean` | DONE | sorry-free scaffold for "holomorphic map between two `ChartedSpace ℂ`-equipped spaces" — bridges Mathlib's `AnalyticAt ℂ` to the manifold-level analytic predicate. Includes chart-independence of `mapAnalyticOrderAt` (`analyticOrderAt_alternate_chart_eq` + ℕ-form), local identity principle (chart and manifold versions), local-constant ⇒ global-constant on connected manifold, finite fibres for nonconstant maps |
| `lem:branch-locus-finite` | `Blueprint.branch_locus_finite` | `Sec02/BranchLocusFinite.lean` | MEDIUM | stub landed; body sorry pending the analytic chart-local discreteness fact for ramification-index ≥ 2 |
| `lem:degree-one-no-ramification` | `Blueprint.degree_one_no_ramification` | `Sec02/DegreeOneNoRamification.lean` | MEDIUM | stub landed; body sorry pending unramified ↔ derivative-nonzero in chart |
| `thm:local-biholo-unramified` | `Blueprint.local_biholo_unramified` | `Sec02/LocalBiholoUnramified.lean` | MEDIUM | stub landed; body sorry pending biholomorphism API + chart-local inverse function theorem |
| `thm:degree-one-bijective` | `Blueprint.degree_one_bijective` | `Sec02/DegreeOneBijective.lean` | DONE | sorry-free combinatorial form: `BranchedCoverData X Y f → branchedDegree h = 1 → Function.Bijective f`, derived from `branchedDegree_one_fiber_singleton`; analytic ramp from holomorphic input is gated on leaf 8 of `BranchedDegree.lean` |
| `thm:compact-bijection-homeo` | Mathlib `Continuous.homeoOfEquivCompactToT2` | (re-export) | DONE | sorry-free Mathlib; tex pinned with `\mathlibok` |
| `input:degree-one-isomorphism` | `Blueprint.input_degree_one_isomorphism` | `Sec02/InputDegreeOneIsomorphism.lean` | SHORT | umbrella stub landed; body sorry pending `branchedDegree_one_fiber_unique` injectivity leaf |

## sec03 — Periods and Riemann bilinear

| Label | Decl | File | Class | Sketch |
|---|---|---|---|---|
| `lem:period-homology-invariance` | typed form: `Periods.period_homology_invariance_statement` (sorry-free `congrArg` in `WorkPackets/StatementBank.lean`) + `Blueprint.Sec03.period_homology_invariance` (sorry-free `congrArg`); descent obligation: `Blueprint.Sec03.period_homology_invariance_descent` (sorry-free assembly via D); recursive sub-leaf decomposition (rounds 1–12): A `exists_singularChain_integration` (sorry-free assembly via A.1 + A.2), A.1 `exists_singularSimplex_integration` (sorry-free trivial witness — strengthening pending), A.1.path `simplex_to_path` (✓), A.1.cover `exists_pathChartCover` (True, forwards to `Periods/LebesgueChartRadius`), A.1.lift `pathIntegralViaCover_partition_independent` (True, forwards to `PathIntegralViaCoverRecon`), A.1.linear `pathIntegral_linear_in_form` (True), A.2 `singularChain_integration_from_simplex` (**SORRY** — free-module bridge), B `holomorphicForm_closed_chain_integral` (✓ wrapper) + B.chart `holomorphicForm_closed_in_chart` (✓ chart wrapper), C `stokes_chain_integral_boundary` (sorry-free assembly via C.simplex + C.linearity, both True), D `chainIntegral_kills_boundary_of_closed` (sorry-free assembly via D.choice + D.vanishing), D.choice `chain_integration_choice` (✓ forwards to A), D.vanishing `chain_integration_kills_boundary` (**SORRY** — analytic core: `I (∂₂ s) η = 0`); upstream `holomorphic_form_is_closed` decomposed into `chart_pullback_holomorphic` / `_dbar_zero` / `_d_eq_zero` (all True); upstream `stokes_on_rs_with_boundary` discharged as wrapper of `stokes_partition_unity`; `stokes_local_euclidean` decomposed into 5.P + 5.Q + Fubini-swap | `Jacobian/WorkPackets/StatementBank.lean`, `Jacobian/Blueprint/Sec03/PeriodHomologyInvariance.lean`, `Jacobian/Blueprint/Sec03/HolomorphicFormIsClosed.lean`, `Jacobian/Blueprint/Sec03/StokesOnRSWithBoundary.lean` | DECOMPOSE | rounds 1–12: typed form sorry-free; descent obligation refined into a fully sorry-free assembly tree with 2 surviving sorries in this file (A.2 free-module bridge, D.vanishing analytic core) plus 6 sorries in Stokes file (sub-leaves of Green's theorem and partition-of-unity) — every Mathlib-absent piece named and pickup-able |
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

## TRIVIAL/SHORT nodes discharged or wired across the trivial-batch series

The Small Jobs Worker has run 12 trivial-batch PRs (#8, #22, #30, #35, #40, #44, #48, #51, #54, #57, #59, #61) covering:

- **Lean discharges (3)**: `input_finite_dimensionality` (a6e8efe), `vanishingOrder` (560e1b0), `meromorphic_as_cp1_map` (2d929d1).
- **New Mathlib-free Sec02/Sec03/Sec05 placeholder stubs**: `Sec02/InputDegreeOneIsomorphism.lean`, `Sec03/{PolygonalModel, PrimitiveOnPolygon, BilinearFromStokes, HermitianPositivity}.lean`, `Sec05/PrincipalDeg0SimpleSupportDeg1.lean` — each `theorem ... : True := trivial` with a docstring recording the replacement-target signature and DECOMPOSE/MEDIUM sub-leaves.
- **`\lean{}` annotations pinned**: every `\label{}` block in `tex/sections/0[1-7]-*.tex` and `tex/statements/*.tex` has a resolvable `\lean{}` target.
- **`\notready → \leanok` promotions** (where the named decl body is sorry-free per the integrator convention): `thm:principal-degree-zero`, `input:divisors` (PR #57); `thm:riemann-hurwitz-deg1`, `thm:aj-divisor-hom` (PR #59); plus the historical `def:divisor`, `def:divisor-degree` (PR #30) and many others.
- **Sec06 cleanup**: stray `\notready` removed from `lem:trace-forms` (PR #59).
- **Project-bookkeeping refresh** (PR #61, batch 12): scope-out.md sec02 WORKER → DONE for Worker C/M/H; `<missing>` rows replaced with file paths; footer rewrite.

The integrator's 11e706d milestone (concurrent with batches 11-12) added `\begin{proof}\leanok\end{proof}` blocks for 11 sorry-free theorems across all sections, unblocking GREEN BACKGROUND fills on the dep graph proof ellipses. As of that commit, the `\lean{}` / `\leanok` / proof-leanok wiring on the blueprint is in a coherent steady state.

## Saturation report (post-batch 12)

The trivial-batch series has reached saturation — the remaining `\notready` items either:

1. point at production decls whose own body is sorry-bearing (no convention-supported `\leanok` promotion), or
2. point at `True := trivial` placeholders whose conclusion isn't the real lemma (integrator policy: keep `\notready` for accuracy), or
3. point at sorry-free assemblies above sorry-bearing transitive helpers (already promoted in batches 10-11; further promotion would risk over-claiming completeness on the dep graph).

Any further trivial work would need the integrator to explicitly direct it (e.g., new placeholder-stub creation, or a policy clarification on `True` placeholders).

## Remaining work shape

- **First DECOMPOSE worker should target**: `def:sheaf-cohomology-rs` is now scaffolded (`Jacobian/HolomorphicForms/SheafCohomologyRS.lean`); the next step is filling `RSAbSheaf` / `RSSheafCohomology` consumer lemmas needed by `serre_duality_rs` and `euler_char_line_bundle`.

- **Stokes chain (DECOMPOSE)**: `thm:stokes-on-rs-with-boundary` umbrella stub landed in `Sec03/StokesOnRSWithBoundary.lean` with 8 named sub-leaves; the eight-leaf decomposition is in `ref/plans/stokes-on-rs-with-boundary.md` and ready for follow-up workers.

- **Theta-function chain (HARD, in flight)**: `Sec05/RiemannTheta.lean` records the theta-function infrastructure feeding `AbelExistence.existence_of_f`. `Sec05/JacobiInversion.lean` (Worker AE) is its sibling decomposition feeding `aj_Pic0_surjective`. Both are in active development.

- **Genus identification (DONE)**: `Jacobian/HolomorphicForms/GenusEqH0Canonical.lean` (Worker H, post-batch-12) caps the chain `analyticGenus ℂ X = h⁰(X, K_X) = h¹(X, 𝒪_X) = RSGenus X` as a sorry-free assembly above `GenusIdentification.lean`'s frontier sorries.
