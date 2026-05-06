# Sorry inventory for `Jacobian/Solution.lean`

**Generated:** 2026-05-06 — after rebasing `claude/lean-comparator-sorries-EKW4G` onto
`origin/main` (5 new commits). Build: `lake build Jacobian.Solution` exits 0 with **35
sorry warnings** across 12 files. Prior count was 47 (after the +680-commit rebase of
the previous session). The current rebase's 5 commits resolved several Mathlib-adjacent
gaps (MeromorphicDegree fully discharged; RiemannRoch down from 6 → 1; PullbackNaturality
down from 7 → 5). One net new sorry was introduced: `build_constant_meromorphicMap` now
exposes 2 internal sorry fields added when `MeromorphicMapToSphere` gained 8 new
required fields from main.

---

## Summary by file

| File (relative to `Jacobian/`) | Sorries |
|---|---|
| HolomorphicForms/RiemannRoch.lean | 1 |
| HolomorphicForms/CompactRiemannSurface.lean | 3 |
| HolomorphicForms/DeRhamComparisonMap.lean | 2 |
| HolomorphicForms/GenusZeroClassification.lean | 5 |
| Periods/CellularHomologyRS.lean | 2 |
| Periods/TietzeReduction.lean | 3 |
| Periods/Polygon4gCellular.lean | 2 |
| Periods/SingularH1Homotopy.lean | 3 |
| Periods/PeriodFunctional.lean | 1 |
| Periods/PullbackNaturality.lean | 5 |
| AbelJacobi/AnalyticOfCurveBasis.lean | 6 |
| TraceDegree/PullbackBasis.lean | 2 |
| **Total** | **35** |

---

## Per-file sorry list

### 1. `HolomorphicForms/RiemannRoch.lean` (1 sorry)

| # | Line | Declaration | Mathematical content |
|---|---|---|---|
| 1 | 433 | `riemannRochSpace_dim_ge_two_implies_nonconstant_meromorphic` | Existence of a non-constant meromorphic function from dim(L(D)) ≥ 2 |

**Blocker:** Riemann-Roch theorem content; needs Serre duality or direct construction.

---

### 2. `HolomorphicForms/CompactRiemannSurface.lean` (3 sorries)

| # | Line | Declaration | Mathematical content |
|---|---|---|---|
| 2 | 251 | `holomorphicOneForm_fiberNorm_continuous_via_eval_at_one` | Norm of holomorphic 1-form fibre is continuous in evaluation |
| 3 | 350 | `holomorphicOneForm_supNorm_cauchySeq_tendsto_via_steps` | Sup-norm Cauchy sequences of holomorphic forms converge |
| 4 | 923 | `holomorphicOneForm_arzela_ascoli` | Arzelà-Ascoli compactness for holomorphic 1-forms |

**Blocker:** Functional analysis / compact operator theory for holomorphic forms on compact Riemann surfaces (Arzelà-Ascoli style).

---

### 3. `HolomorphicForms/DeRhamComparisonMap.lean` (2 sorries)

| # | Line | Declaration | Mathematical content |
|---|---|---|---|
| 5 | 131 | `deRhamComparisonMap1_prescribed_period_correct` | de Rham comparison map has the correct periods |
| 6 | 168 | `deRhamComparisonMap1_zero_period_potential` | A form with zero periods is exact (Poincaré lemma-style) |

**Blocker:** de Rham isomorphism / period integration theory.

---

### 4. `HolomorphicForms/GenusZeroClassification.lean` (5 sorries)

| # | Line | Declaration | Mathematical content |
|---|---|---|---|
| 7 | 252 | `ContMDiffSection_localRepr_identityChart_contDiff` | Local representative in identity chart is smooth |
| 8 | 346 | `ContMDiffSection_localRepr_inversionChart_continuousAt_zero` | Local representative continuous at 0 under inversion chart |
| 9 | 415 | `holomorphicOneForm_chartOverlap_pullback` | Holomorphic 1-form pullback agrees on chart overlaps |
| 10 | 782 | `exists_biholomorphism_to_OnePointCx_of_homeoSphere` | Existence of biholomorphism from genus-0 surface to ℂ∪{∞} |
| 11 | 803 | `holomorphicOneForm_linearEquiv_of_biholo_to_OnePointCx` | Linear equivalence of holomorphic forms via biholomorphism |

**Blocker:** Genus-0 uniformisation (Riemann mapping theorem for Riemann surfaces); smooth section local coordinate computations.

---

### 5. `Periods/CellularHomologyRS.lean` (2 sorries)

| # | Line | Declaration | Mathematical content |
|---|---|---|---|
| 12 | 133 | `cellular_iso_singular_h1` | Cellular H₁ is isomorphic to singular H₁ |
| 13 | 147 | `cellularH1_finite_singularIsoData` | The isomorphism data is finite/computable |

**Blocker:** Cellular-to-singular homology comparison (needs CW-complex structure on Riemann surfaces).

---

### 6. `Periods/TietzeReduction.lean` (3 sorries)

| # | Line | Declaration | Mathematical content |
|---|---|---|---|
| 14 | 187 | `wordQuotient_homeomorph_of_inverseCancel_step` | Cancelling inverse pairs in edge word gives homeomorphic quotient |
| 15 | 194 | `wordQuotient_homeomorph_of_handleSwap_step` | Swapping handles in edge word gives homeomorphic quotient |
| 16 | 285 | `edgeWord_wordQuotient_homeomorph_M` | Edge word reduction produces a polygon homeomorphic to standard 4g-gon |

**Blocker:** Combinatorial topology of surface presentations (Tietze-style surface classification).

---

### 7. `Periods/Polygon4gCellular.lean` (2 sorries)

| # | Line | Declaration | Mathematical content |
|---|---|---|---|
| 17 | 232 | `polygon4g_succ_singularH1_free` | Singular H₁ of polygon 4g is free abelian |
| 18 | 243 | `polygon4g_succ_singularH1_finrank_eq` | Singular H₁ of polygon 4g has rank 2g |

**Blocker:** CW-complex homology computation for the standard 4g-gon.

---

### 8. `Periods/SingularH1Homotopy.lean` (3 sorries)

| # | Line | Declaration | Mathematical content |
|---|---|---|---|
| 19 | 264 | `singularH1_inducedLinearMap_id` | The induced map on H₁ of the identity is the identity |
| 20 | 271 | `singularH1_inducedLinearMap_comp` | The induced map on H₁ is functorial (composition) |
| 21 | 282 | `singularH1_inducedLinearMap_eq_of_homotopic` | Homotopic maps induce the same map on H₁ |

**Blocker:** `singularH1_inducedLinearMap` is `noncomputable opaque` — needs replacement with
a concrete definition wrapping Mathlib's `singularChainComplexFunctor.map`. All 3 sorry-bearing
theorems depend on this definition being made explicit.

---

### 9. `Periods/PeriodFunctional.lean` (1 sorry)

| # | Line | Declaration | Mathematical content |
|---|---|---|---|
| 22 | 501 | `riemann_classical_real_LI_input` | Real linear independence of the period input for the Riemann period relations |

**Blocker:** Real linear independence of holomorphic vs anti-holomorphic 1-forms (Riemann bilinear relations).

---

### 10. `Periods/PullbackNaturality.lean` (5 sorries)

| # | Line | Declaration | Mathematical content |
|---|---|---|---|
| 23 | 222 | `pathIntegralViaCover_trans_eq_add` | Path integral over concatenated path = sum of integrals |
| 24 | 239 | `pathIntegralViaCover_pullback_chart_segment` | Pullback formula for path integral on a single chart segment |
| 25 | 255 | `pathIntegralViaCover_partition_compat_under_smooth` | Partition compatibility of path integrals under smooth pullback |
| 26 | 272 | `pathIntegralViaCoverWith_refinement_invariant` | Path integral is invariant under refinement of the cover |
| 27 | 291 | `pathIntegralViaCoverWith_pullback_via_common_partition` | Path integral pullback via a common partition |

**Blocker:** Multi-chart path integration naturality (change of variables for smooth 1-forms along paths).

---

### 11. `AbelJacobi/AnalyticOfCurveBasis.lean` (6 sorries)

| # | Line | Declaration | Mathematical content |
|---|---|---|---|
| 28 | 915 | `build_constant_meromorphicMap` | Constant function assembles into `MeromorphicMapToSphere`; 2 new fields (`toFiniteFun_mdifferentiable`, `hasBranchedCoverDataOfPoleDegree`) need discharging |
| 29 | 972 | `nonconstant_extracted_from_dim_quotient` | Extract non-constant meromorphic function from dim ≥ 2 quotient |
| 30 | 1168 | `thirdKindData_from_genus_zero` | Third-kind differential data from genus-0 classification |
| 31 | 1248 | `pole_full_two_point_of_nonconstant_in_RR_space_aux` | Auxiliary: non-constant function in L(Q₁+Q₂) has poles exactly at Q₁,Q₂ |
| 32 | 1879 | `assemble_meromorphicMap` | Assemble a meromorphic map from divisor data |
| 33 | 2047 | `meromorphicMapToSphere_package_of_two_point_principal` | Package meromorphic map with two-point principal divisor |

**Blocker:** `build_constant_meromorphicMap` (#28): the 2 sorry fields are `toFiniteFun_mdifferentiable`
(needs `MDifferentiable.const`-style argument through `OnePoint.coe` injectivity) and
`hasBranchedCoverDataOfPoleDegree` (constant function is not a branched cover — structurally
impossible without a different approach). The remaining 5 sorries are downstream of Riemann-Roch
and genus-0 classification infrastructure.

---

### 12. `TraceDegree/PullbackBasis.lean` (2 sorries)

| # | Line | Declaration | Mathematical content |
|---|---|---|---|
| 34 | 237 | `pullbackFormsMap_eq_matrix_AddHom` | Pullback of holomorphic forms = matrix AddHom |
| 35 | 251 | `basisAnalyticPullbackBundle_dualPullback_eq_matrix_AddHom` | Dual pullback of analytic basis bundle = matrix AddHom |

**Blocker:** Trace/degree matrix formulation for the pullback of holomorphic forms; needs basis
compatibility lemmas for the analytic pullback bundle.

---

## Discharged since last count (47 → 35: −12 net)

Main branch commits resolved:
- `HolomorphicForms/MeromorphicDegree.lean`: all 5 sorries discharged (−5)
- `HolomorphicForms/RiemannRoch.lean`: 5 of 6 sorries discharged (−5)
- `Periods/PullbackNaturality.lean`: 2 of 7 sorries discharged (−2)

New sorry introduced:
- `AbelJacobi/AnalyticOfCurveBasis.lean:build_constant_meromorphicMap`: `MeromorphicMapToSphere`
  structure gained 8 new required fields from main; 2 internal sorry fields added (+1 sorry
  declaration).
