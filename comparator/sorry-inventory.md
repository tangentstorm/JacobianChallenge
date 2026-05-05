# Sorry inventory for `Jacobian/Solution.lean`

**Generated:** 2026-05-05 via static analysis of the full import closure,
confirmed by `lake build Jacobian.Solution` (exit 0, 59 sorry warnings).
**Post-rebase update:** Branch was rebased onto `origin/main` (+680 commits).
The import chain is significantly larger than the original 25-sorry baseline.

The previous 4 "dead" sorry declarations (#16–18 in old inventory:
`wedge_integration_pairing_exists`, `riemann_bilinear_identity`,
`hodge_form_posDef`; and `pathIntegralViaCover_pullbackFormsBundledLM`
in PullbackNaturality) are **gone** — the 680 commits either discharged
them or refactored the sorry into new named obligations.

No dead-code audit has been performed on the new files from the rebase.
All 59 sorry-bearing declarations below are in files that are transitively
imported by `Solution.lean`.

---

## Import chain (direct imports of `Solution.lean`)

```
Solution.lean
  ├── Jacobian.HolomorphicForms.CompactRiemannSurface
  │     └── (see below)
  ├── Jacobian.HolomorphicForms.GenusZeroClassification
  │     ├── Jacobian.HolomorphicForms.MeromorphicDegree
  │     │     └── Jacobian.HolomorphicForms.RiemannRoch
  │     └── (others sorry-free)
  ├── Jacobian.Periods.PeriodLattice
  │     └── Jacobian.Periods.BasisAlignedPeriodSubgroup
  │           └── Jacobian.Periods.PeriodFunctional
  │                 ├── Jacobian.HolomorphicForms.CompactRiemannSurface (sorry-bearing)
  │                 ├── Jacobian.Periods.IntegralOneCycle
  │                 │     ├── Jacobian.Periods.IntegralOneCycleRank
  │                 │     │     └── Jacobian.Periods.CellularHomologyRS  ← NEW
  │                 │     └── Jacobian.HolomorphicForms.DeRhamSingular
  │                 │           └── Jacobian.HolomorphicForms.DeRhamComparisonMap  ← NEW
  │                 ├── Jacobian.Periods.SurfaceClassification
  │                 │     ├── Jacobian.Periods.TietzeReduction  ← NEW
  │                 │     ├── Jacobian.Periods.Polygon4gCellular  ← NEW
  │                 │     └── Jacobian.Periods.SingularH1Homotopy  ← NEW
  │                 └── Jacobian.HolomorphicForms.HodgeDeRhamRank
  │                       └── Jacobian.HolomorphicForms.DeRhamSingular (see above)
  ├── Jacobian.ComplexTorus.ULiftTransport  (sorry-free)
  ├── Jacobian.AbelJacobi.AnalyticOfCurveBasis  (sorry-bearing, see below)
  ├── Jacobian.TraceDegree.PullbackBasis  (sorry-bearing, see below)
  ├── Jacobian.TraceDegree.PushforwardBasis  (sorry-free)
  └── Jacobian.TraceDegree.AnalyticDegree  (sorry-free)
```

Five files added to the import chain by the +680-commit rebase:
`CellularHomologyRS`, `DeRhamComparisonMap`, `TietzeReduction`,
`Polygon4gCellular`, `SingularH1Homotopy`.

---

## Complete list of `sorry` obligations

### `Jacobian/HolomorphicForms/RiemannRoch.lean`
*(imported via GenusZeroClassification → MeromorphicDegree)*

| # | Declaration | Line | Mathematical content |
|---|---|---|---|
| 1 | `MeromorphicMapToSphere.toMap_ne_infty_of_no_poles` | 72 | A meromorphic map with empty pole divisor takes finite values everywhere |
| 2 | `MeromorphicMapToSphere.toFiniteFun_mdiff_of_lift_eq` | 113 | The finite-value function inherits smoothness from the meromorphic map when a smooth lift exists |
| 3 | `MeromorphicMapToSphere.zeros_poles_disjoint_support` | 161 | Zero and pole divisors of a meromorphic map have disjoint support |
| 4 | `MeromorphicMapToSphere.poles_le_point_of_mem_L_point` | 177 | Membership in the Riemann-Roch space L([P]) implies pole divisor ≤ [P] |
| 5 | `MeromorphicMapToSphere.poles_effective` | 232 | The pole divisor of a meromorphic map is effective |
| 6 | `riemannRochSpace_dim_ge_two_implies_nonconstant_meromorphic` | 306 | Riemann-Roch space dimension ≥ 2 implies existence of a nonconstant meromorphic function |

**Mathlib blocker:** no Riemann-Roch theorem, no divisor theory for
compact Riemann surfaces.

---

### `Jacobian/HolomorphicForms/MeromorphicDegree.lean`

| # | Declaration | Line | Mathematical content |
|---|---|---|---|
| 7 | `MeromorphicMapToSphere.toMap_ne_infty_off_pole` | 48 | A meromorphic map is finite outside its pole divisor support |
| 8 | `MeromorphicMapToSphere.continuousOn_of_no_infty_on` | 63 | Continuity on a set where the map is finite |
| 9 | `MeromorphicMapToSphere.toMap_pole_eq_infty_of_poleDivisor_point` | 93 | Value at a simple-pole point is ∞ |
| 10 | `MeromorphicMapToSphere.modulus_diverges_at_simple_pole` | 110 | Modulus diverges to infinity at a simple pole |
| 11 | `MeromorphicMapToSphere.exists_branchedCoverData_of_pole_degree_one` | 251 | Degree-1 pole divisor implies existence of branched-cover data |

**Mathlib blocker:** no degree/ramification theory for maps between
compact Riemann surfaces.

---

### `Jacobian/Periods/CellularHomologyRS.lean` *(new in chain)*
*(imported via IntegralOneCycle → IntegralOneCycleRank)*

| # | Declaration | Line | Mathematical content |
|---|---|---|---|
| 12 | `cellular_iso_singular_h1` | 133 | CW cellular chain complex is quasi-isomorphic to singular chain complex (Mathlib gap: cellular chain complex vs singular chain complex comparison) |
| 13 | `cellularH1_finite_singularIsoData` | 147 | Packages cellular H₁ finiteness + singular H₁ isomorphism data into a single witness |

**Mathlib blocker:** cellular chain complex / singular chain complex
comparison absent in v4.28.0.

---

### `Jacobian/HolomorphicForms/DeRhamComparisonMap.lean` *(new in chain)*
*(imported via IntegralOneCycle → DeRhamSingular)*

| # | Declaration | Line | Mathematical content |
|---|---|---|---|
| 14 | `deRhamComparisonMap1_prescribed_period_correct` | 131 | Integration of the de Rham-comparison-constructed closed form agrees with the input singular cocycle |
| 15 | `deRhamComparisonMap1_zero_period_potential` | 168 | A form with zero de Rham periods has a global potential function |

**Mathlib blocker:** chart-wise primitive construction; de Rham / singular
comparison map absent in v4.28.0.

---

### `Jacobian/Periods/TietzeReduction.lean` *(new in chain)*
*(imported via SurfaceClassification)*

| # | Declaration | Line | Mathematical content |
|---|---|---|---|
| 16 | `wordQuotient_homeomorph_of_inverseCancel_step` | 187 | InverseCancel Tietze step preserves the disk-quotient up to homeomorphism |
| 17 | `wordQuotient_homeomorph_of_handleSwap_step` | 194 | HandleSwap Tietze step preserves the disk-quotient up to homeomorphism |
| 18 | `edgeWord_wordQuotient_homeomorph_M` | 285 | The raw-word quotient of a surface's edge-word presentation is homeomorphic to the surface |

**Mathlib blocker:** no surface classification / Tietze equivalence
formalization in v4.28.0; requires triangulation and CW-structure results.

---

### `Jacobian/Periods/Polygon4gCellular.lean` *(new in chain)*
*(imported via SurfaceClassification)*

| # | Declaration | Line | Mathematical content |
|---|---|---|---|
| 19 | `polygon4g_succ_singularH1_free` | 232 | H₁(Polygon4g(g+1), ℤ) is a free ℤ-module (via UCT / Hurewicz, absent in Mathlib) |
| 20 | `polygon4g_succ_singularH1_finrank_eq` | 243 | H₁(Polygon4g(g+1), ℤ) has rank 2(g+1) |

**Mathlib blocker:** no packaged surface-genus rank computation for
`singularH1` in v4.28.0.

---

### `Jacobian/Periods/SingularH1Homotopy.lean` *(new in chain)*
*(imported via SurfaceClassification)*

| # | Declaration | Line | Mathematical content |
|---|---|---|---|
| 21 | `singularH1_inducedLinearMap_id` | 264 | The identity map induces the identity on H₁(X, ℤ) |
| 22 | `singularH1_inducedLinearMap_comp` | 271 | H₁(−, ℤ) is compositionally functorial as a linear map |
| 23 | `singularH1_inducedLinearMap_eq_of_homotopic` | 282 | Homotopic maps induce the same linear map on H₁(X, ℤ) |

**Mathlib blocker:** `singularH1_inducedLinearMap` is currently defined
as the zero map (sorry placeholder); the functoriality sorries are blocked
on providing the actual induced-map construction.

---

### `Jacobian/HolomorphicForms/CompactRiemannSurface.lean`

| # | Declaration | Line | Mathematical content |
|---|---|---|---|
| 24 | `holomorphicOneForm_fiberNorm_continuous_via_eval_at_one` | 251 | Fiberwise norm `x ↦ ‖σ(x)‖` of a holomorphic 1-form is continuous (chart trivialization argument) |
| 25 | `holomorphicOneForm_supNorm_cauchySeq_tendsto_via_steps` | 350 | Sup-norm convergence to the pointwise/holomorphic limit (Weierstrass convergence) |
| 26 | `holomorphicOneForm_arzela_ascoli` | 923 | Equibounded + equicontinuous family of holomorphic 1-forms is relatively compact in sup-norm (Arzelà–Ascoli) |

**Mathlib blocker for 25–26:** no Weierstrass convergence theorem for
holomorphic functions in Mathlib v4.28.0.

---

### `Jacobian/HolomorphicForms/GenusZeroClassification.lean`

| # | Declaration | Line | Mathematical content |
|---|---|---|---|
| 27 | `ContMDiffSection_localRepr_identityChart_contDiff` | 252 | Identity-chart local representation of a holomorphic 1-form on `OnePoint ℂ` is C^∞ |
| 28 | `ContMDiffSection_localRepr_inversionChart_continuousAt_zero` | 346 | Inversion-chart local representation is continuous at 0 (i.e. at ∞) |
| 29 | `holomorphicOneForm_chartOverlap_pullback` | 415 | Cotangent transition formula between identity and inversion charts: `f(w⁻¹) = −w² · g(w)` |
| 30 | `exists_biholomorphism_to_OnePointCx_of_homeoSphere` | 782 | A compact Riemann surface homeomorphic to S² is biholomorphic to `OnePoint ℂ` (uniformization) |
| 31 | `holomorphicOneForm_linearEquiv_of_biholo_to_OnePointCx` | 803 | A biholomorphism to `OnePoint ℂ` induces a linear equivalence on holomorphic 1-forms |

**Mathlib blocker for 27–29:** cotangent-bundle chart trivialization API
(`ContMDiffSection.contDiff_localRepr`) absent in v4.28.0.
**Blocker for 30:** uniqueness of complex structure on the topological
2-sphere.

---

### `Jacobian/Periods/PeriodFunctional.lean`

| # | Declaration | Line | Mathematical content |
|---|---|---|---|
| 32 | `riemann_classical_real_LI_input` | 487 | The Riemann bilinear relations imply that the period vectors are ℝ-linearly independent (requires differential forms on manifolds, wedge product, Stokes on the polygon model) |

**Note:** This is the sole surviving sorry in this file. The former dead
sorries (`wedge_integration_pairing_exists`, `riemann_bilinear_identity`,
`hodge_form_posDef`) were discharged or restructured by the +680 commits.

**Mathlib blockers:** differential forms on manifolds (`Ω^p(X)`), wedge
product, integration, Stokes' theorem — absent in v4.28.0.

---

### `Jacobian/AbelJacobi/AnalyticOfCurveBasis.lean`

*(This file expanded greatly. The 18 sorries are sub-goals in the proof of
Abel's theorem / period-congruence direction.)*

| # | Declaration | Line | Mathematical content |
|---|---|---|---|
| 33 | `serre_vanishing_high_degree` | 626 | Serre vanishing for high-degree divisors: `h¹(D) = 0` when `deg D > 2g - 2` |
| 34 | `rr_collapses_in_high_degree` | 633 | Apply Serre vanishing to get `ℓ(D) = d - g + 1` in high degree |
| 35 | `serre_duality_h1_eq_ℓKD` | 657 | Serre duality: `h¹(D) = ℓ(K − D)` |
| 36 | `euler_char_identity_low_degree` | 664 | Euler characteristic identity `χ(𝒪(D)) = ℓ(D) - h¹(D) = d - g + 1` in low degree |
| 37 | `extract_triple_from_RR` | 714 | Extract (ℓD, ℓKD, g) triple from the Riemann-Roch existence hypothesis |
| 38 | `rewrite_arithmetic_rr` | 720 | Rewrite the arithmetic RR relation for downstream use |
| 39 | `dim_geq_two_genus_zero` | 769 | Genus-0 case of dim ≥ 2: `3 - 0 = 3 ≥ 2` |
| 40 | `dim_geq_two_genus_one` | 775 | Genus-1 case of dim ≥ 2: `3 - 1 = 2 ≥ 2` |
| 41 | `dim_geq_two_high_genus` | 792 | High-genus case (g ≥ 2) of dim ≥ 2 via Brill-Noether / Mittag-Leffler |
| 42 | `two_point_divisor_degree` | 801 | Degree of `[Q₁] + [Q₂]` equals 2 |
| 43 | `pick_n_geq_two` | 808 | Extract a concrete witness `n ≥ 2` from an existence hypothesis |
| 44 | `build_constant_meromorphicMap` | 886 | Construct a constant meromorphic map to `OnePoint ℂ` with zero divisors |
| 45 | `two_point_effective` | 892 | The divisor `[Q₁] + [Q₂]` is effective |
| 46 | `constant_in_RR_space_for_effective` | 899 | The constant map lies in the two-point Riemann-Roch space |
| 47 | `nonconstant_extracted_from_dim_quotient` | 918 | Dimension ≥ 2 implies existence of a nonconstant element in the Riemann-Roch space |
| 48 | `thirdKindData_from_genus_zero` | 1052 | On a genus-0 surface, construct third-kind meromorphic data (simple poles at Q₁, Q₂) |
| 49 | `wrap_two_pole_into_raw` | 1063 | Package a meromorphic map as `RawMeromorphicWithPrincipal` data |
| 50 | `pole_full_two_point_of_nonconstant_in_RR_space_aux` | 1096 | A nonconstant element of the two-point Riemann-Roch space has full pole at both Q₁ and Q₂ |

**Mathlib blockers:** no Riemann-Roch theorem, no Serre duality, no
divisor theory, no Abel's theorem, no Riemann-Hurwitz in v4.28.0.

---

### `Jacobian/Periods/PullbackNaturality.lean`

| # | Declaration | Line | Mathematical content |
|---|---|---|---|
| 51 | `periodPairing_chainLevel_repr` | 125 | Any `IntegralOneCycle` can be represented as a finite ℤ-linear combination of paths |
| 52 | `cyclePushforward_chainLevel_repr` | 138 | The chain-level representation is compatible with `cyclePushforward` (path-mapping) |
| 53 | `pathIntegralViaCover_trans_eq_add` | 294 | Integration is additive under path concatenation |
| 54 | `pathIntegralViaCover_pullback_chart_segment` | 311 | Chart-level chain rule: pullback of form integrates as integral of original form along pushed path |
| 55 | `pathIntegralViaCover_partition_compat_under_smooth` | 327 | A chart partition of γ on X admits a compatible refinement as partition of f∘γ on Y |
| 56 | `pathIntegralViaCoverWith_refinement_invariant` | 344 | The `pathIntegralViaCoverWith` value is invariant under chart-partition refinement |
| 57 | `pathIntegralViaCoverWith_pullback_via_common_partition` | 363 | Segment-by-segment chart rule: pullback-integral equals original integral along pushed path |

**Note:** The top-level `periodPairing_pullbackFormsBundledLM` (line 780)
is now **sorry-free**, assembling from `periodPairing_pullbackFormsBundledLM_via_pathLevel`
(itself sorry-free, but calling #51 and #52) and
`pathIntegralViaCover_pullbackFormsBundledLM` (sorry-free, calling #57
via `pathIntegralViaCoverWith_pullbackFormsBundledLM`). All 7 sorries are
in the live proof chain.

**Mathlib blocker:** Stokes' theorem for path integrals / integration
naturality for pullback of differential forms; chain-level representation
of `singularH1`-valued cycles.

---

### `Jacobian/TraceDegree/PullbackBasis.lean`

| # | Declaration | Line | Mathematical content |
|---|---|---|---|
| 58 | `pullbackFormsMap_eq_matrix_AddHom` | 237 | `pullbackFormsMap` equals the matrix `AddMonoidHom` given by `basisAlignedFormPullbackMatrix` |
| 59 | `basisAnalyticPullbackBundle_dualPullback_eq_matrix_AddHom` | 251 | The basis-aligned form-pullback from `basisAnalyticPullbackBundle` equals the same matrix `AddMonoidHom` |

**Blocker:** `basisAnalyticPullbackBundle` is an opaque using
`Classical.choice` from its `Inhabited` instance; these sorries are the
proof obligations that the concrete `pullbackFormsMap` matches the opaque
bundle's spec. Pure linear algebra once the concrete map is supplied.

---

## Opaque declarations (not `sorry` but load-bearing named obligations)

These contribute no `sorryAx` to the axiom set; they use `Classical.choice`
via their `Inhabited` witness (zero/trivial value). Mathematically hollow
until replaced by a concrete construction.

| Declaration | File | Content |
|---|---|---|
| `pathIntegralFunctionalBundle` | `AbelJacobi/AnalyticOfCurveBasis.lean:88` | Multi-chart path integration in basis coordinates + self-spec |
| `basisAnalyticPullbackBundle` | `TraceDegree/PullbackBasis.lean:110` | Bundled analytic pullback with all specs: `mk_eq`, `contMDiff_pull`, `degree`, `trace_pullback_spec` |

---

## Summary

**Total sorry obligations: 59** across 13 files (compiler count, post-rebase).

| File | Sorries | Notes |
|---|---|---|
| `HolomorphicForms/RiemannRoch.lean` | 6 | Riemann-Roch / divisor theory |
| `HolomorphicForms/MeromorphicDegree.lean` | 5 | Degree / ramification theory |
| `Periods/CellularHomologyRS.lean` | 2 | **NEW** — cellular vs. singular H₁ |
| `HolomorphicForms/DeRhamComparisonMap.lean` | 2 | **NEW** — de Rham / singular comparison |
| `Periods/TietzeReduction.lean` | 3 | **NEW** — surface classification (Tietze) |
| `Periods/Polygon4gCellular.lean` | 2 | **NEW** — polygon H₁ rank |
| `Periods/SingularH1Homotopy.lean` | 3 | **NEW** — H₁ functoriality |
| `HolomorphicForms/CompactRiemannSurface.lean` | 3 | Weierstrass / Montel |
| `HolomorphicForms/GenusZeroClassification.lean` | 5 | Uniformization / cotangent API |
| `Periods/PeriodFunctional.lean` | 1 | Riemann bilinear relations (down from 7) |
| `AbelJacobi/AnalyticOfCurveBasis.lean` | 18 | Abel's theorem sub-goals (up from 1) |
| `Periods/PullbackNaturality.lean` | 7 | Path integral naturality (up from 2) |
| `TraceDegree/PullbackBasis.lean` | 2 | Pullback bundle spec matching |
| **Total** | **59** | |

### Change summary relative to previous inventory (25 sorries)

- **Discharged / refactored away (−5):** `wedge_integration_pairing_exists`,
  `riemann_bilinear_identity`, `hodge_form_posDef` (dead scaffolding removed),
  `pathIntegralViaCover_pullbackFormsBundledLM` (old dead sorry),
  `genusZero_exists_nonconstant_mem_L_point` / `genusZero_poleDivisor_eq_point_of_nonconstant_mem_L_point`
  (refactored into a longer chain in RiemannRoch + AbelJacobi).
- **New files in import chain (+5 files, +15 sorries):** CellularHomologyRS,
  DeRhamComparisonMap, TietzeReduction, Polygon4gCellular, SingularH1Homotopy.
- **Expanded proof chains in existing files (+24 sorries):**
  AnalyticOfCurveBasis (1→18) and PullbackNaturality (2→7) had their top-level
  sorry replaced by detailed sub-goal scaffolding.

### Deepest blockers (no path without new Mathlib infrastructure)

- **#32** `riemann_classical_real_LI_input` (Riemann bilinear / differential forms)
- **#30** `exists_biholomorphism_to_OnePointCx_of_homeoSphere` (uniformization)
- **#33–50** Abel's theorem cluster in `AnalyticOfCurveBasis`
  (Riemann-Roch, Serre duality, divisor theory)
- **#51–57** Path integral naturality cluster in `PullbackNaturality`
  (Stokes / chain-level representation)
- **#12–23** New topology/homology cluster
  (cellular H₁, de Rham comparison, surface classification, H₁ functoriality)

### Sorries most tractable without new Mathlib

- **#58–59** `PullbackBasis` (pure linear algebra once concrete pullbackFormsMap supplied)
- **#24** `holomorphicOneForm_fiberNorm_continuous_via_eval_at_one`
  (chart trivialization argument, ~20 lines)
- **#27–29** `GenusZeroClassification` leaf sorries
  (pending `ContMDiffSection.contDiff_localRepr` or equivalent)
