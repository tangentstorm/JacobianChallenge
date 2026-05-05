# Sorry inventory for `Jacobian/Solution.lean`

**Generated:** 2026-05-05 via static analysis of the full import closure,
confirmed by `lake build Jacobian.Solution` (exit 0, 25 sorry warnings).
**Comparator binary:** not installed; staged-config smoke-test deferred.

The compiler emits `declaration uses 'sorry'` for every sorry-bearing
declaration in every compiled module, regardless of whether that
declaration is actually *used* by `Solution.lean`. A secondary usage
audit (grep + proof-term tracing) identified 4 declarations that are
declared with `sorry` but never called from any live proof chain:
items 16, 17, 18, and 22 below (marked **DEAD**). The remaining 21 are
in the live chain.

---

## Import chain (direct imports of `Solution.lean`)

```
Solution.lean
  ├── Jacobian.HolomorphicForms.CompactRiemannSurface
  │     └── Jacobian.HolomorphicForms.FiniteDimensional
  │     └── Jacobian.HolomorphicForms.SectionMetric  (sorry-free)
  ├── Jacobian.HolomorphicForms.GenusZeroClassification
  │     ├── Jacobian.HolomorphicForms.AnalyticGenus  (sorry-free)
  │     ├── Jacobian.HolomorphicForms.MeromorphicDegree
  │     │     └── Jacobian.HolomorphicForms.RiemannRoch
  │     ├── Jacobian.HolomorphicForms.OnePointCxIsManifold  (sorry-free)
  │     ├── Jacobian.HolomorphicForms.Ext  (sorry-free)
  │     └── Jacobian.HolomorphicForms.EntireZero  (sorry-free)
  ├── Jacobian.Periods.PeriodLattice
  │     ├── Jacobian.ComplexTorus.Defs  (sorry-free)
  │     ├── Jacobian.HolomorphicForms.AnalyticGenus  (sorry-free)
  │     └── Jacobian.Periods.BasisAlignedPeriodSubgroup
  │           ├── Jacobian.HolomorphicForms.BasisAlignedDualEquiv  (sorry-free)
  │           └── Jacobian.Periods.PeriodFunctional
  │                 ├── Jacobian.HolomorphicForms.CompactRiemannSurface
  │                 └── Jacobian.Periods.IntegralOneCycle  (sorry-free)
  ├── Jacobian.ComplexTorus.ULiftTransport
  │     ├── Jacobian.ComplexTorus.ChartedSpace  (sorry-free)
  │     ├── Jacobian.ComplexTorus.IsManifold    (sorry-free)
  │     └── Jacobian.ComplexTorus.LieAddGroup   (sorry-free)
  ├── Jacobian.AbelJacobi.AnalyticOfCurveBasis
  │     └── Jacobian.Periods.PeriodLattice
  ├── Jacobian.TraceDegree.PullbackBasis
  │     └── Jacobian.TraceDegree.PushforwardBasis
  │           ├── Jacobian.HolomorphicForms.PullbackBundled  (sorry-free)
  │           ├── Jacobian.HolomorphicForms.BasisAlignedDualEquiv  (sorry-free)
  │           └── Jacobian.Periods.PullbackNaturality
  │                 └── Jacobian.Periods.PeriodFunctional
  ├── Jacobian.TraceDegree.PushforwardBasis  (see above)
  └── Jacobian.TraceDegree.AnalyticDegree  (sorry-free assembly)
```

Files that have `sorry` comments but are **not** in the import chain
and are therefore irrelevant: `ComplexTorus/ManifoldRecon.lean`,
`HolomorphicForms/ChartCoeffExtractionRecon.lean`,
`HolomorphicForms/SectionTopologyConstructionRecon.lean`.

---

## Complete list of `sorry` obligations

### `Jacobian/HolomorphicForms/RiemannRoch.lean`
*(imported via GenusZeroClassification → MeromorphicDegree)*

| # | Declaration | Line | Mathematical content |
|---|---|---|---|
| 1 | `genusZero_exists_nonconstant_mem_L_point` | 54 | Riemann-Roch: on a genus-0 compact Riemann surface, L([P]) contains a nonconstant meromorphic function |
| 2 | `genusZero_poleDivisor_eq_point_of_nonconstant_mem_L_point` | 71 | Pole divisor of a nonconstant element of L([P]) is exactly [P] |

**Mathlib blocker:** no Riemann-Roch theorem, no divisor theory for
compact Riemann surfaces.

---

### `Jacobian/HolomorphicForms/MeromorphicDegree.lean`

| # | Declaration | Line | Mathematical content |
|---|---|---|---|
| 3 | `meromorphicMapToSphere_continuous_of_poleDivisor_point` | 40 | A meromorphic map with pole divisor [P] extends continuously to the Riemann sphere |
| 4 | `meromorphicMapToSphere_bijective_of_poleDivisor_degree_one` | 66 | A continuous meromorphic map to `OnePoint ℂ` with degree-1 pole divisor is bijective |

**Mathlib blocker:** no degree/ramification theory for maps between
compact Riemann surfaces.

---

### `Jacobian/HolomorphicForms/GenusZeroClassification.lean`

| # | Declaration | Line | Mathematical content |
|---|---|---|---|
| 5 | `holomorphicOneFormIdentityChartCoeffContDiff` | 252 | The identity-chart coefficient of a holomorphic 1-form on `OnePoint ℂ` is C^∞ |
| 6 | `holomorphicOneFormInversionChartCoeffContinuousAtZero` | 329 | The inversion-chart coefficient is continuous at 0 (i.e. at ∞) |
| 7 | `holomorphicOneForm_identityInversionTransition_eventually` | 369 | Cotangent transition formula between identity and inversion charts: `f(w⁻¹) = −w² · g(w)` |
| 8 | `holomorphicOneFormCoeffTendstoZeroOfTransition` | 385 | Identity-chart coefficient tends to 0 at infinity, given continuity + transition formula |
| 9 | `holomorphicOneForm_infty_vanishing_of_inversionCoeff` | 476 | If the inversion coefficient is continuous at 0 and vanishes away from 0, the form vanishes at ∞ |
| 10 | `homeoSphereHolomorphicOneFormVanishing` | 631 | A compact Riemann surface homeomorphic to S² has no nonzero holomorphic 1-forms (uniformization-lite) |

**Mathlib blocker for 5–9:** cotangent-bundle chart trivialization API for
`ContMDiffSection` (`ContMDiffSection.contDiff_localRepr`) absent in v4.28.0.
**Blocker for 10:** uniqueness of complex structure on the topological 2-sphere,
transport of holomorphic 1-forms along the resulting biholomorphism.

---

### `Jacobian/HolomorphicForms/CompactRiemannSurface.lean`

| # | Declaration | Line | Mathematical content |
|---|---|---|---|
| 11 | `holomorphicOneForm_fiberNorm_continuous` | 161 | Fiberwise norm `x ↦ ‖σ(x)‖` of a holomorphic 1-form is continuous |
| 12 | `holomorphicOneForm_supNorm_cauchySeq_tendsto` | 229 | Every Cauchy sequence of holomorphic 1-forms in the sup-norm converges (Weierstrass convergence theorem for holomorphic sections) |
| 13 | `holomorphicOneForm_closedBall_totallyBounded` | 656 | The closed unit ball in holomorphic 1-forms is totally bounded (core of Montel's theorem: equibounded + equicontinuous → Arzelà–Ascoli) |

**Mathlib blocker for 12–13:** no Weierstrass convergence theorem for
holomorphic functions (limits of uniform sequences of holomorphic
functions are holomorphic) in Mathlib v4.28.0.

---

### `Jacobian/Periods/PeriodFunctional.lean`

| # | Declaration | Line | Mathematical content |
|---|---|---|---|
| 14 | `h1_free_of_compact_surface` | 90 | H₁(X, ℤ) of a compact Riemann surface is free ℤ-module of rank 2g (requires surface classification and CW structure) |
| 15 | `analyticGenus_eq_topologicalGenus` | 105 | Analytic genus = topological genus (Hodge decomposition, de Rham theorem, Serre duality) |
| 16 | `wedge_integration_pairing_exists` (**DEAD**) | 192 | Declared as a blocker for `period_functionals_ℝ_linearIndependent`, but that theorem is itself a bare `sorry` and never calls this declaration |
| 17 | `riemann_bilinear_identity` (**DEAD**) | 216 | Same situation as #16 — only in proof-sketch comments, never called |
| 18 | `hodge_form_posDef` (**DEAD**) | 231 | Same situation as #16 — only in proof-sketch comments, never called |
| 19 | `period_functionals_ℝ_linearIndependent` | 253 | The period functionals `γ ↦ ∫_γ ωᵢ` are ℝ-linearly independent (analytic core of Riemann bilinear relations) |
| 20 | `periodSubgroup_eq_zspan_of_basis` | 329 | The period subgroup is the ℤ-span of 2g ℝ-linearly independent vectors (via `exact ⟨b, hli, sorry⟩`) |

**Mathlib blockers:** differential forms on manifolds (`Ω^p(X)`, wedge
product, integration), Stokes' theorem on fundamental polygons, Hodge
decomposition, de Rham theorem — all absent in v4.28.0.

---

### `Jacobian/Periods/PullbackNaturality.lean`

| # | Declaration | Line | Mathematical content |
|---|---|---|---|
| 21 | `periodPairing_pullbackFormsBundledLM` | 139 | Naturality: `∫_γ (f*η) = ∫_{f_* γ} η` (Stokes theorem / integration naturality) — called at `PushforwardBasis.lean:326` |
| 22 | `pathIntegralViaCover_pullbackFormsBundledLM` (**DEAD**) | 239 | Path integral of pulled-back form equals integral along pushed-forward path — declared as a sub-goal for #21 but `#21` is itself a `sorry`; this declaration is never called from any proof |

**Mathlib blocker:** Stokes' theorem for path integrals / integration
naturality for pullback of differential forms.

---

### `Jacobian/AbelJacobi/AnalyticOfCurveBasis.lean`

| # | Declaration | Line | Mathematical content |
|---|---|---|---|
| 23 | `period_congruence_distinct_implies_genus_zero` | 264 | Abel's theorem (genus-0 direction): if J(Q₁) = J(Q₂) and Q₁ ≠ Q₂ then genus(X) = 0 |

**Mathlib blocker:** no Abel's theorem, no divisor theory, no
Riemann-Hurwitz formula. Uses `pathIntegralFunctionalBundle` (opaque).

---

### `Jacobian/TraceDegree/PullbackBasis.lean`

| # | Declaration | Line | Mathematical content |
|---|---|---|---|
| 24 | `basisAnalyticPullbackBundle_id_dualPullback` | 180 | The dual form-pullback along `id` is the identity `AddMonoidHom` (pure linear algebra via concrete `pullbackFormsMap`) |
| 25 | `basisAnalyticPullbackBundle_comp_dualPullback` | 269 | The dual form-pullback is contravariant: `(g ∘ f)* = f* ∘ g*` as `AddMonoidHom` |

**Blocker:** the `basisAnalyticPullbackBundle` opaque uses `Classical.choice`
from its `Inhabited` instance (zero pullback); these sorries are the named
proof obligations that the *actual* geometric pullback satisfies
`id`-functoriality and composition-functoriality. Pure linear algebra once the
concrete `pullbackFormsMap` is supplied.

---

## Opaque declarations (not `sorry` but load-bearing named obligations)

These contribute no `sorryAx` to the axiom set; they use `Classical.choice`
via their `Inhabited` witness (zero/trivial value). They are mathematically
hollow until replaced by a concrete construction.

| Declaration | File | Content |
|---|---|---|
| `pathIntegralFunctionalBundle` | `AbelJacobi/AnalyticOfCurveBasis.lean:88` | Multi-chart path integration in basis coordinates + self-spec |
| `basisAnalyticPullbackBundle` | `TraceDegree/PullbackBasis.lean:110` | Bundled analytic pullback with all specs: `mk_eq`, `contMDiff_pull`, `degree`, `trace_pullback_spec` |

---

## Summary

**Total sorry obligations: 25** across 7 files (compiler count).
**Actually live (in chain): 21. Dead (declared but uncalled): 4.**

| File | Total | Live | Dead |
|---|---|---|---|
| `HolomorphicForms/RiemannRoch.lean` | 2 | 2 | — |
| `HolomorphicForms/MeromorphicDegree.lean` | 2 | 2 | — |
| `HolomorphicForms/GenusZeroClassification.lean` | 6 | 6 | — |
| `HolomorphicForms/CompactRiemannSurface.lean` | 3 | 3 | — |
| `Periods/PeriodFunctional.lean` | 7 | 4 | 3 (#16,17,18) |
| `Periods/PullbackNaturality.lean` | 2 | 1 | 1 (#22) |
| `AbelJacobi/AnalyticOfCurveBasis.lean` | 1 | 1 | — |
| `TraceDegree/PullbackBasis.lean` | 2 | 2 | — |
| **Total** | **25** | **21** | **4** |

The 4 dead declarations (#16 `wedge_integration_pairing_exists`,
#17 `riemann_bilinear_identity`, #18 `hodge_form_posDef`,
#22 `pathIntegralViaCover_pullbackFormsBundledLM`) are scaffolding
stubs that document what a proof *would* need but are never called
because the proof they would support (#19 and #21 respectively) is
itself a bare `sorry` that doesn't invoke them.

### Highest-priority / deepest blockers

The following sorries have no path to discharge without substantial new
Mathlib infrastructure:

- **#15** `analyticGenus_eq_topologicalGenus` (Hodge + de Rham)
- **#16–19** Riemann bilinear / Hodge theory cluster in `PeriodFunctional.lean`
- **#12** `holomorphicOneForm_supNorm_cauchySeq_tendsto` (Weierstrass convergence)
- **#23** `period_congruence_distinct_implies_genus_zero` (Abel's theorem)
- **#21–22** `PullbackNaturality` (Stokes naturality for path integrals)

The following sorries are pure linear algebra / continuity assembly that
should be provable without new Mathlib:

- **#24–25** `basisAnalyticPullbackBundle_{id,comp}_dualPullback`
  (once a concrete `pullbackFormsMap` is defined)
- **#11** `holomorphicOneForm_fiberNorm_continuous`
  (chart trivialization argument, ~20 lines)
- **#5–9** `GenusZeroClassification` leaf sorries
  (pending `ContMDiffSection.contDiff_localRepr` or equivalent)
