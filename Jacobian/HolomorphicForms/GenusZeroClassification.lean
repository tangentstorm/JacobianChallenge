import Jacobian.HolomorphicForms.AnalyticGenus
import Jacobian.HolomorphicForms.MeromorphicDegree
import Jacobian.HolomorphicForms.OnePointCxIsManifold
import Jacobian.HolomorphicForms.Ext
import Jacobian.HolomorphicForms.EntireZero
import Mathlib.Analysis.InnerProductSpace.EuclideanDist
import Mathlib.Topology.Compactification.OnePoint.Sphere

/-!
# Genus-zero classification

A compact connected Riemann surface has analytic genus zero iff it is
homeomorphic to the standard 2-sphere `Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1`.

Proof deferred — this is the genus-zero classification (uniformization
theorem / Riemann–Roch + classification of compact connected oriented
surfaces). One of the project's anti-hack theorems.

Top-down obligation: pointed to by `Jacobian/Solution.lean` for the
`genus_eq_zero_iff_homeo` lemma.
-/

namespace JacobianChallenge.HolomorphicForms

open scoped Manifold

/-!
### Blocker analysis for `analyticGenus_eq_zero_of_homeomorphic_sphere`

**Status (2026-04-27):** sorry — all three required ingredients are absent
from Mathlib v4.28.0 (commit `8f9d9cff6bd728b17a24e163c9402775d9e6a365`).

#### Proof sketch

1. **Uniqueness of smooth structure on S².** Every topological 2-sphere
   admits a unique smooth structure up to diffeomorphism (Radó 1925 /
   Morse 1960). Given `X ≃ₜ S²`, transfer the smooth structure on `X`
   (from its complex charts) to `S²` and apply uniqueness to get a
   *diffeomorphism* `X ≃ₘ S²`.
   - **Mathlib gap:** No `SmoothManifoldWithCorners` structure on
     `Metric.sphere … 1` in `ℝ³`; no smooth classification of compact
     surfaces; no `Diffeomorph` between abstract smooth manifolds and
     concrete spheres. Searched: `ComplexProjectiveLine`,
     `RiemannSphere`, `cotangentSpace_finrank` — all absent.

2. **Uniqueness of complex structure on S².** A smooth compact oriented
   2-manifold diffeomorphic to `S²` carries a unique complex structure up
   to biholomorphism (consequence of the uniformization theorem: every
   simply connected Riemann surface is biholomorphic to `ℂ`, `𝔻`, or
   `ℂℙ¹`; compactness forces `ℂℙ¹`). So `X` is biholomorphic to `ℂℙ¹`.
   - **Mathlib gap:** No uniformization theorem; no `ℂℙ¹` as a complex
     manifold; no biholomorphism API for Riemann surfaces.

3. **H⁰(ℂℙ¹, Ω¹) = 0.** On `ℂℙ¹`, the canonical sheaf `Ω¹` has
   degree `−2`. A line bundle of negative degree on a compact Riemann
   surface has no nonzero global sections. Hence the space of holomorphic
   1-forms is trivial and `analyticGenus = 0`.
   - **Mathlib gap:** No sheaf-cohomology or divisor-degree theory; no
     definition of `ℂℙ¹` as a Riemann surface; no Riemann–Roch theorem.

#### Lemmas searched in Mathlib (all absent)

- `ComplexProjectiveLine` / `RiemannSphere` — not defined.
- `Diffeomorph.ofHomeomorphSphere` — no smooth classification of surfaces.
- `cotangentSpace_finrank` — no dimension computation for cotangent spaces.
- `Module.finrank_holomorphicOneForms_sphere` — not available.
- `IsManifold.sphere` (for `Metric.sphere` in `ℝ³` with `ℂ`-charts) — absent.

#### Dependency graph blocker

```
analyticGenus_eq_zero_of_homeomorphic_sphere
  │
  ├─► [MISSING] smooth_structure_unique_on_S2
  │     └─► [MISSING] IsManifold instance for Metric.sphere in ℝ³
  │
  ├─► [MISSING] complex_structure_unique_on_S2
  │     └─► [MISSING] uniformization_theorem
  │           └─► [MISSING] ℂℙ¹ as complex manifold
  │
  └─► [MISSING] holomorphicOneForms_CP1_subsingleton
        ├─► [MISSING] ℂℙ¹ definition + ChartedSpace instance
        ├─► [MISSING] canonical_sheaf_degree_CP1 = -2
        └─► [MISSING] negative_degree_line_bundle_no_sections
```

#### 3-step Mathlib-API plan for a future job

**Step 1 — Define `ℂℙ¹` as a complex manifold.**
Define `ℂℙ¹` (e.g. as `Projectivization ℂ (Fin 2 → ℂ)` or as the
one-point compactification `AlexandrovCompactification ℂ`). Equip it
with `ChartedSpace ℂ` and `IsManifold` instances using the standard
two-chart atlas (`z ↦ z`, `z ↦ 1/z`). Prove it is compact, connected,
T2, and homeomorphic to `Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1`.

**Step 2 — Compute `H⁰(ℂℙ¹, Ω¹) = 0` directly.**
Bypass the general Riemann–Roch machinery: show that any holomorphic
1-form on `ℂℙ¹` restricts to `f(z) dz` on the standard chart `U₀ ≅ ℂ`,
and the transition to the chart `U₁` forces `f(z) = 0` (by Liouville's
theorem applied to the resulting entire function with growth constraint).
Conclude `Subsingleton (HolomorphicOneForm ℂ ℂℙ¹)`.

**Step 3 — Transport along homeomorphism.**
For compact Riemann surfaces `X ≃ₜ ℂℙ¹`, the homeomorphism lifts to a
biholomorphism (by uniqueness of complex structure on `S²`), giving an
isomorphism of 1-form spaces. Transport the subsingleton result from
Step 2 to `X` and apply `analyticGenus_eq_zero_of_subsingleton`.

An alternative shortcut for **Step 3** (avoiding uniformization): if
we only need genus 0, prove directly that `Module.finrank` of sections
of a bundle is invariant under biholomorphism, and show the
homeomorphism `X ≃ₜ S²` lifts to a biholomorphism `X ≃ₕ ℂℙ¹` using
the fact that every orientation-preserving homeomorphism between
Riemann surfaces is homotopic to a biholomorphism (Earle–Eells).
-/

/-! ### Refined decomposition of the easy direction

The easy direction `analyticGenus_eq_zero_of_homeomorphic_sphere` is now
assembled from three smaller named obligations, each Aristotle-shaped:

* `holomorphicOneForm_onePointCx_subsingleton` — the space of holomorphic
  1-forms on `ℂℙ¹ = OnePoint ℂ` is a subsingleton (i.e. only the zero
  form exists).  This is the substantive analytic content
  (Liouville-style argument on the inversion chart).
* `analyticGenus_onePointCx_eq_zero` — pure corollary of the subsingleton
  fact via `analyticGenus_eq_zero_of_subsingleton`.
* `analyticGenus_eq_of_homeomorphic_sphere_of_onePointCx` — the
  uniformization-lite transport step: a compact Riemann surface
  homeomorphic to `S²` has the same analytic genus as `OnePoint ℂ`.
  This bundles the deep "every complex structure on `S²` is biholomorphic
  to `ℂℙ¹`" content into a single named obligation.

The original `analyticGenus_eq_zero_of_homeomorphic_sphere` becomes pure
assembly of these three pieces. The hard direction
`homeomorphic_sphere_of_analyticGenus_eq_zero` below is unchanged.
-/

/-! #### Proof plan for `holomorphicOneForm_onePointCx_subsingleton`

A holomorphic 1-form on `OnePoint ℂ` pulled back to
the identity chart is `f(z) dz` for some entire function `f : ℂ → ℂ`;
under the inversion-chart transition `w = z⁻¹`, it becomes
`-f(1/w) / w² dw`. Holomorphicity at `w = 0` forces `f(1/w) / w²` to be
bounded near zero, which by Liouville's theorem forces `f ≡ 0`.

This is decomposed into:
1. `entire_tendsto_zero_eq_zero` — Liouville-based vanishing of entire
   functions that tend to 0 at infinity. Available sorry-free in
   `EntireZero.lean`.
2. `holomorphicOneForm_onePointCx_toFun_finite_eq_zero` — the substantive
   chart-pullback + Liouville application on the identity chart
   (finite points). Carries the chart-extraction Mathlib gap.
3. `holomorphicOneForm_onePointCx_toFun_infty_eq_zero` — vanishing at
   the point at infinity, via the inversion chart. Continuity of the
   smooth section forces `g(0) = lim_{w→0} g(w) = 0`.
4. `holomorphicOneForm_onePointCx_toFun_eq_zero` — sorry-free assembly
   via `cases x using OnePoint.rec` of leaves (2) and (3).
5. `holomorphicOneForm_onePointCx_subsingleton` — sorry-free assembly
   via `ext_toFun`. -/

/-- An entire function `f : ℂ → ℂ` that tends to `0` along `cocompact ℂ`
(i.e. as `|z| → ∞`) is identically zero.

This is the Liouville-application building block of the Liouville core.
The proof is provided sorry-free in
`Jacobian/HolomorphicForms/EntireZero.lean` as
`Differentiable.eq_zero_of_tendsto_zero_cocompact`. -/
theorem entire_tendsto_zero_eq_zero (f : ℂ → ℂ) (hf : Differentiable ℂ f)
    (h : Filter.Tendsto f (Filter.cocompact ℂ) (nhds 0)) :
    f = 0 :=
  hf.eq_zero_of_tendsto_zero_cocompact h

/-! #### Refined chart-extraction split

The original single `holomorphicOneForm_onePointCx_toFun_eq_zero` sorry
is now split into two named leaves keyed to the two charts of
`OnePoint ℂ` (identity chart on `{∞}ᶜ` and inversion chart on `{↑0}ᶜ`).

Both leaves carry the same chart-extraction Mathlib gap, but they are
analytically distinct: the finite-chart leaf is the substantive Liouville
application, while the infinity-chart leaf is a continuity argument
(the inversion-chart coefficient `g(w) = -f(1/w)/w²` extends across
`w = 0` to `g(0) = 0`).

Splitting them lets two separate Aristotle/sub-agent jobs target each
leaf with disjoint reasoning patterns. -/

/-!
### TOPDOWN decomposition for `holomorphicOneForm_onePointCx_toFun_finite_eq_zero`
(integrated from Aristotle 76c01cf9)

The proof is split into two named sub-obligations + sorry-free assembly:

* `holomorphicOneForm_coeff_entire` — the coefficient function
  `holomorphicOneForm_coeff ω` is entire (carries the chart-extraction gap).
* `holomorphicOneForm_coeff_tendsto_zero` — the coefficient function tends
  to `0` along `cocompact ℂ` (carries the chart-extraction + chart-transition
  formula gap).

Assembly: apply `Differentiable.eq_zero_of_tendsto_zero_cocompact` (Liouville)
to `holomorphicOneForm_coeff ω`, then `ω.toFun (↑z) = 0` follows because
`ℂ →L[ℂ] ℂ` is determined by its value at `1` (via `ext`).
-/

/-- The chart-local coefficient of a holomorphic 1-form on `OnePoint ℂ`
in the identity chart: `f(z) = (ω.toFun ↑z) 1`. -/
noncomputable def holomorphicOneForm_coeff
    (ω : HolomorphicOneForm ℂ (OnePoint ℂ)) : ℂ → ℂ :=
  fun z => ω.toFun (↑z : OnePoint ℂ)
    (show TangentSpace (modelWithCornersSelf ℂ ℂ) (↑z : OnePoint ℂ) from (1 : ℂ))

private lemma onePointCx_identityChart_symm_apply (z : ℂ) :
    (identityChart.symm : ℂ → OnePoint ℂ) z = ↑z := by
  rw [identityChart]
  simp [Topology.IsOpenEmbedding.toOpenPartialHomeomorph]

private lemma onePointCx_inversionChart_symm_apply (w : ℂ) :
    (inversionChart.symm : ℂ → OnePoint ℂ) w = invBwd w := rfl

/-- The coefficient obtained by first reading `ω` in `identityChart` and
then evaluating the resulting covector on `1 : ℂ`.

This is intentionally separate from `holomorphicOneForm_coeff`: the bridge
between the project-internal direct formula and Mathlib's chart API is one
of the chart-extraction leaves below. -/
noncomputable def holomorphicOneForm_identityChartCoeff
    (ω : HolomorphicOneForm ℂ (OnePoint ℂ)) : ℂ → ℂ :=
  fun z => ω.toFun (identityChart.symm z)
    (show TangentSpace (modelWithCornersSelf ℂ ℂ) (identityChart.symm z) from (1 : ℂ))

/-- **Sub-obligation 1.** The coefficient function is entire.

Blocker (chart-extraction gap): requires reading the `ContMDiff ⊤` section
through the identity-chart trivialization to obtain `ContDiff ℂ ⊤` of the
local representative, then composing with evaluation at `1`. Mathlib
v4.28.0 lacks `ContMDiffSection.contDiff_localRepr`. See
`ChartCoeffExtractionRecon.lean`. -/
structure HolomorphicOneFormCoeffEntireData
    (ω : HolomorphicOneForm ℂ (OnePoint ℂ)) where
  differentiable_coeff : Differentiable ℂ (holomorphicOneForm_coeff ω)

/-- **Identity-chart extraction leaf.** The coefficient read directly from
the identity-chart local representative is `C^∞`.

Bottom-up content: expose a chart-trivialization API for `ContMDiffSection`
on the cotangent bundle, specialized to `identityChart`, and compose the
local representative with evaluation at `1 : ℂ`. -/
theorem holomorphicOneFormIdentityChartCoeffContDiff
    (ω : HolomorphicOneForm ℂ (OnePoint ℂ)) :
    ContDiff ℂ (⊤ : WithTop ℕ∞) (holomorphicOneForm_identityChartCoeff ω) := by
  sorry

/-- **Identity-chart identification leaf.** The chart-local coefficient
agrees with the direct finite-point formula used by the Liouville assembly.

Bottom-up content: unfold `identityChart.symm` from
`OnePointCxChartedSpace.lean`, transport the tangent-space trivialization,
and reduce the chart expression to evaluation at `↑z`. -/
theorem holomorphicOneForm_coeff_eq_identityChartCoeff
    (ω : HolomorphicOneForm ℂ (OnePoint ℂ)) :
    holomorphicOneForm_coeff ω = holomorphicOneForm_identityChartCoeff ω := by
  funext z
  unfold holomorphicOneForm_coeff holomorphicOneForm_identityChartCoeff
  rw [onePointCx_identityChart_symm_apply]

/-- **Assembly of the identity-chart extraction split.** -/
theorem holomorphicOneFormCoeffContDiff
    (ω : HolomorphicOneForm ℂ (OnePoint ℂ)) :
    ContDiff ℂ (⊤ : WithTop ℕ∞) (holomorphicOneForm_coeff ω) := by
  rw [holomorphicOneForm_coeff_eq_identityChartCoeff]
  exact holomorphicOneFormIdentityChartCoeffContDiff ω

/-- **Assembly from chart extraction to differentiability.** The actual
chart-extraction obligation is `holomorphicOneFormCoeffContDiff`; this
packages the standard `ContDiff.differentiable` consequence needed by
Liouville. -/
def holomorphicOneFormCoeffEntireData
    (ω : HolomorphicOneForm ℂ (OnePoint ℂ)) :
    HolomorphicOneFormCoeffEntireData ω where
  differentiable_coeff :=
    (holomorphicOneFormCoeffContDiff ω).differentiable (by simp)

/-- **Sub-obligation 1 wrapper (sorry-free).** Extracts differentiability of
the identity-chart coefficient from `holomorphicOneFormCoeffEntireData`. -/
theorem holomorphicOneForm_coeff_entire
    (ω : HolomorphicOneForm ℂ (OnePoint ℂ)) :
    Differentiable ℂ (holomorphicOneForm_coeff ω) :=
  (holomorphicOneFormCoeffEntireData ω).differentiable_coeff

/-- **Sub-obligation 2.** The coefficient function tends to `0` along
`cocompact ℂ` (i.e. as `|z| → ∞`).

Blocker (chart-extraction + chart-transition gap): requires the
inversion-chart formula `g(w) = -f(1/w)/w²` for the cotangent bundle
and smoothness at `w = 0`. Both absent in v4.28.0. -/
noncomputable def holomorphicOneForm_inversionCoeff
    (ω : HolomorphicOneForm ℂ (OnePoint ℂ)) : ℂ → ℂ :=
  fun w => ω.toFun (invBwd w)
    (show TangentSpace (modelWithCornersSelf ℂ ℂ) (invBwd w) from (1 : ℂ))

/-- The coefficient obtained by reading `ω` in `inversionChart` and then
evaluating on `1 : ℂ`.

This keeps the Mathlib chart expression separate from the direct formula
using `invBwd`, so the bottom-up work can prove the chart identification
without being entangled with continuity of the local representative. -/
noncomputable def holomorphicOneForm_inversionChartCoeff
    (ω : HolomorphicOneForm ℂ (OnePoint ℂ)) : ℂ → ℂ :=
  fun w => ω.toFun (inversionChart.symm w)
    (show TangentSpace (modelWithCornersSelf ℂ ℂ) (inversionChart.symm w) from (1 : ℂ))

structure HolomorphicOneFormCoeffTendstoZeroData
    (ω : HolomorphicOneForm ℂ (OnePoint ℂ)) where
  tendsto_coeff_zero :
    Filter.Tendsto (holomorphicOneForm_coeff ω)
      (Filter.cocompact ℂ) (nhds 0)

/-- **Inversion-chart extraction leaf.** The inversion-chart coefficient of
a holomorphic 1-form is continuous at the point `w = 0`, i.e. at infinity of
`OnePoint ℂ`.

Bottom-up content: expose the cotangent-bundle chart trivialization for
`ContMDiffSection` in the inversion chart and identify its coefficient by
evaluation at `1 : ℂ`. -/
theorem holomorphicOneFormInversionChartCoeffContinuousAtZero
    (ω : HolomorphicOneForm ℂ (OnePoint ℂ)) :
    ContinuousAt (holomorphicOneForm_inversionChartCoeff ω) 0 := by
  sorry

/-- **Inversion-chart identification leaf.** The chart-local inversion
coefficient agrees with the direct `invBwd` formula.

Bottom-up content: unfold `inversionChart.symm`, use the definition of
`invBwd`, and transport the tangent-space trivialization. -/
theorem holomorphicOneForm_inversionCoeff_eq_inversionChartCoeff
    (ω : HolomorphicOneForm ℂ (OnePoint ℂ)) :
    holomorphicOneForm_inversionCoeff ω = holomorphicOneForm_inversionChartCoeff ω := by
  funext w
  unfold holomorphicOneForm_inversionCoeff holomorphicOneForm_inversionChartCoeff
  rw [onePointCx_inversionChart_symm_apply]

/-- **Assembly of the inversion-chart extraction split.** -/
theorem holomorphicOneFormInversionCoeffContinuousAtZero
    (ω : HolomorphicOneForm ℂ (OnePoint ℂ)) :
    ContinuousAt (holomorphicOneForm_inversionCoeff ω) 0 := by
  rw [holomorphicOneForm_inversionCoeff_eq_inversionChartCoeff]
  exact holomorphicOneFormInversionChartCoeffContinuousAtZero ω

/-- The punctured-neighborhood transition statement between identity and
inversion coefficients. For `w ≠ 0`, the cotangent transition law is
equivalently `f(w⁻¹) = -w² * g(w)`. -/
def holomorphicOneForm_identityInversionTransition
    (ω : HolomorphicOneForm ℂ (OnePoint ℂ)) : Prop :=
  ∀ᶠ w in nhdsWithin (0 : ℂ) ({0}ᶜ : Set ℂ),
    holomorphicOneForm_coeff ω (w⁻¹) =
      -w ^ 2 * holomorphicOneForm_inversionCoeff ω w

/-- **Möbius-pullback step (pointwise).** For `w ≠ 0`, the identity-chart
and inversion-chart coefficient functions are related by the Jacobian
factor of the chart transition `z = w⁻¹`: `d(w⁻¹) = -w⁻² dw`.

This is the chart-pullback computation on the cotangent bundle; it requires
showing that the `ContMDiffSection` local representatives in the identity
and inversion charts are related by the cotangent bundle transition
function, then extracting the `-w²` Jacobian factor via evaluation at
`1 : ℂ`.

(Aristotle a577e2ce named-helper extraction.) -/
private lemma moebiusPullback_cotangent_pointwise
    (ω : HolomorphicOneForm ℂ (OnePoint ℂ)) (w : ℂ) (hw : w ≠ 0) :
    holomorphicOneForm_coeff ω (w⁻¹) =
      -w ^ 2 * holomorphicOneForm_inversionCoeff ω w := by
  sorry

/-- **Cotangent transition formula leaf.** On the overlap of the identity
and inversion charts, the two coefficient functions are related by the
Jacobian factor of `z = w⁻¹`.

(Aristotle a577e2ce, sorry-free assembly via moebiusPullback_cotangent_pointwise
+ eventually_nhdsWithin_of_forall.) -/
theorem holomorphicOneForm_identityInversionTransition_eventually
    (ω : HolomorphicOneForm ℂ (OnePoint ℂ)) :
    holomorphicOneForm_identityInversionTransition ω := by
  unfold holomorphicOneForm_identityInversionTransition
  exact eventually_nhdsWithin_of_forall fun w hw => by
    simp only [Set.mem_compl_iff, Set.mem_singleton_iff] at hw
    exact moebiusPullback_cotangent_pointwise ω w hw

/-- **Analytic decay leaf.** A continuous inversion coefficient at `0`,
together with the punctured cotangent-transition formula, forces the
identity-chart coefficient to tend to zero at infinity.

Bottom-up content: use continuity to make `g(w)` bounded near `0`, multiply
by `w² → 0`, and transfer the resulting `f(w⁻¹) → 0` statement through
the inversion homeomorphism between punctured neighborhoods of zero and
the cocompact filter on `ℂ`. -/
theorem holomorphicOneFormCoeffTendstoZeroOfTransition
    (ω : HolomorphicOneForm ℂ (OnePoint ℂ)) :
    ContinuousAt (holomorphicOneForm_inversionCoeff ω) 0 →
    holomorphicOneForm_identityInversionTransition ω →
    Filter.Tendsto (holomorphicOneForm_coeff ω)
      (Filter.cocompact ℂ) (nhds 0) := by
  -- BLOCKER: Aristotle b19e41ad's tendsto-arithmetic proof was integrated
  -- in f2279b4 but does not typecheck against current Mathlib v4.28.0
  -- (typeclass resolution failure on `Filter.Tendsto.mul` — `ContinuousMul`
  -- can't be inferred when arguments are metavariables, plus unsolved goals
  -- on the cocompact↔nhdsWithin transport). Reverted to `sorry` to restore
  -- a green build; the b19e41ad strategy is still correct in spirit and can
  -- be re-attempted with explicit type annotations.
  sorry

/-- **Chart-transition assembly.** Continuity and the explicit transition
formula are the remaining leaves; the old broad decay obligation is no
longer load-bearing. -/
theorem holomorphicOneFormCoeffTendstoZeroFromInversion
    (ω : HolomorphicOneForm ℂ (OnePoint ℂ)) :
    ContinuousAt (holomorphicOneForm_inversionCoeff ω) 0 →
    Filter.Tendsto (holomorphicOneForm_coeff ω)
      (Filter.cocompact ℂ) (nhds 0) :=
  fun hcont =>
    holomorphicOneFormCoeffTendstoZeroOfTransition ω hcont
      (holomorphicOneForm_identityInversionTransition_eventually ω)

/-- **Assembly for coefficient decay.** The remaining work is split into
inversion-chart continuity and the transition-formula decay lemma. -/
def holomorphicOneFormCoeffTendstoZeroData
    (ω : HolomorphicOneForm ℂ (OnePoint ℂ)) :
    HolomorphicOneFormCoeffTendstoZeroData ω where
  tendsto_coeff_zero :=
    holomorphicOneFormCoeffTendstoZeroFromInversion ω
      (holomorphicOneFormInversionCoeffContinuousAtZero ω)

/-- **Sub-obligation 2 wrapper (sorry-free).** Extracts the decay of the
identity-chart coefficient from `holomorphicOneFormCoeffTendstoZeroData`. -/
theorem holomorphicOneForm_coeff_tendsto_zero
    (ω : HolomorphicOneForm ℂ (OnePoint ℂ)) :
    Filter.Tendsto (holomorphicOneForm_coeff ω)
      (Filter.cocompact ℂ) (nhds 0) :=
  (holomorphicOneFormCoeffTendstoZeroData ω).tendsto_coeff_zero

theorem holomorphicOneForm_onePointCx_toFun_finite_eq_zero
    (ω : HolomorphicOneForm ℂ (OnePoint ℂ)) (z : ℂ) :
    ω.toFun (↑z : OnePoint ℂ) = 0 := by
  have hzero : holomorphicOneForm_coeff ω = 0 :=
    (holomorphicOneForm_coeff_entire ω).eq_zero_of_tendsto_zero_cocompact
      (holomorphicOneForm_coeff_tendsto_zero ω)
  ext
  simp only [ContinuousLinearMap.zero_apply]
  exact congr_fun hzero z

/-- Vanishing of a holomorphic 1-form at the point at infinity of
`OnePoint ℂ`.

**Substantive content (continuity of inversion-chart coefficient).**
On the inversion chart (source `(OnePoint ℂ) \ {↑0}`, forward map
`↑z ↦ z⁻¹`, `∞ ↦ 0`), the section `ω` reads as `g(w) dw` for some
`g : ℂ → ℂ`, where `g(w) = (ω.toFun ((·⁻¹) w)) 1` for `w ≠ 0` and
`g(0) = (ω.toFun ∞) 1`.

By `holomorphicOneForm_onePointCx_toFun_finite_eq_zero`, for `w ≠ 0`
the value `ω.toFun ↑(w⁻¹) = 0`, so `g(w) = 0` on `{w | w ≠ 0}`.
Continuity of the bundle-trivialised section at `w = 0` then forces
`g(0) = 0`, i.e. `(ω.toFun ∞) 1 = 0`. Since the cotangent fiber over
`∞` is `ℂ →L[ℂ] ℂ` (also determined by its value at `1`), we conclude
`ω.toFun ∞ = 0`.

**Mathlib gap:** same as the finite case — no user-facing
`ContMDiffSection` chart-trivialisation API. The continuity argument
itself is elementary once the trivialisation is set up.

**Note:** this lemma takes `holomorphicOneForm_onePointCx_toFun_finite_eq_zero`
as a *hypothesis* through the calling order (the assembly theorem
provides it via `cases x using OnePoint.rec`). The two leaves carry
disjoint analytic content. -/
structure HolomorphicOneFormOnePointCxInfinityVanishingData
    (ω : HolomorphicOneForm ℂ (OnePoint ℂ)) where
  infinity_vanishing : ω.toFun (OnePoint.infty : OnePoint ℂ) = 0

/-- Away from `w = 0` in the inversion chart, the inversion coefficient
vanishes by the finite-chart Liouville argument. -/
theorem holomorphicOneForm_inversionCoeff_eq_zero_of_ne_zero
    (ω : HolomorphicOneForm ℂ (OnePoint ℂ)) {w : ℂ} (hw : w ≠ 0) :
    holomorphicOneForm_inversionCoeff ω w = 0 := by
  unfold holomorphicOneForm_inversionCoeff
  rw [invBwd_ne_zero hw]
  rw [holomorphicOneForm_onePointCx_toFun_finite_eq_zero]
  simp only [ContinuousLinearMap.zero_apply]

/-- **Removable-singularity leaf.** If the inversion coefficient is
continuous at `0` and vanishes away from `0`, then the holomorphic 1-form
vanishes at infinity.

Bottom-up content: convert punctured-neighborhood vanishing plus continuity
of the inversion-chart coefficient into `g(0) = 0`, then use that a
continuous linear map `ℂ →L[ℂ] ℂ` is determined by its value on `1`. -/
theorem holomorphicOneForm_infty_vanishing_of_inversionCoeff
    (ω : HolomorphicOneForm ℂ (OnePoint ℂ)) :
    ContinuousAt (holomorphicOneForm_inversionCoeff ω) 0 →
    (∀ {w : ℂ}, w ≠ 0 → holomorphicOneForm_inversionCoeff ω w = 0) →
    ω.toFun (OnePoint.infty : OnePoint ℂ) = 0 := by
  -- Aristotle 0f24ef1b: continuity + punctured-vanishing → inversionCoeff 0 = 0.
  intro h1 h2
  have h3 : holomorphicOneForm_inversionCoeff ω 0 = 0 := by
    have h_punct : Filter.Tendsto (fun w : ℂ => holomorphicOneForm_inversionCoeff ω w)
        (nhdsWithin 0 {0}ᶜ) (nhds 0) := by
      exact tendsto_const_nhds.congr'
        (Filter.eventuallyEq_of_mem self_mem_nhdsWithin fun x hx => by aesop)
    exact tendsto_nhds_unique (h1.mono_left nhdsWithin_le_nhds) h_punct
  ext
  convert h3 using 1
  unfold holomorphicOneForm_inversionCoeff
  norm_num
  unfold invBwd
  grind +splitIndPred

/-- **Assembly for infinity vanishing.** The remaining leaf is the
removable-singularity step from the inversion coefficient. -/
def holomorphicOneFormOnePointCxInfinityVanishingData
    (ω : HolomorphicOneForm ℂ (OnePoint ℂ)) :
    HolomorphicOneFormOnePointCxInfinityVanishingData ω
    where
  infinity_vanishing :=
    holomorphicOneForm_infty_vanishing_of_inversionCoeff ω
      (holomorphicOneFormInversionCoeffContinuousAtZero ω)
      (fun {w} hw => holomorphicOneForm_inversionCoeff_eq_zero_of_ne_zero ω (w := w) hw)

/-- **Infinity vanishing of holomorphic 1-forms on `OnePoint ℂ`.**

Direct proof (integrated from Aristotle 50ed9388, salvaged via the
bundle-trivialization + density argument): use the local trivialization
of the cotangent bundle around `OnePoint.infty` to translate
the bundle-section vanishing into a continuous function `phi` on the
trivialization base set; show `phi` vanishes at every finite point
(via the existing `holomorphicOneForm_onePointCx_toFun_finite_eq_zero`);
conclude by density of `OnePoint.some : ℂ → OnePoint ℂ`.

This bypasses the inversion-chart route — `holomorphicOneFormOnePointCxInfinityVanishingData`
and the inversion-chart leaves it depends on are no longer load-bearing for
this theorem (they remain useful for `holomorphicOneForm_coeff_tendsto_zero`). -/
theorem holomorphicOneForm_onePointCx_toFun_infty_eq_zero
    (ω : HolomorphicOneForm ℂ (OnePoint ℂ)) :
    ω.toFun (OnePoint.infty : OnePoint ℂ) = 0 := by
  set e := trivializationAt (CotangentModelFiber ℂ) (CotangentSpace ℂ (OnePoint ℂ))
    (OnePoint.infty : OnePoint ℂ) with he_def
  have h_mem : (OnePoint.infty : OnePoint ℂ) ∈ e.baseSet :=
    FiberBundle.mem_baseSet_trivializationAt' _
  let phi : OnePoint ℂ → CotangentModelFiber ℂ :=
    fun x => (e (Bundle.TotalSpace.mk' (CotangentModelFiber ℂ) x (ω.toFun x))).2
  have hphi_cont : ContinuousOn phi e.baseSet := by
    apply ContinuousOn.comp continuous_snd.continuousOn
    · apply ContinuousOn.comp e.continuousOn
        (Continuous.continuousOn (ω.contMDiff.continuous))
      intro x hx
      rw [Trivialization.mem_source]
      exact hx
    · exact Set.mapsTo_univ _ _
  have hphi_fin : ∀ z : ℂ, (↑z : OnePoint ℂ) ∈ e.baseSet → phi (↑z : OnePoint ℂ) = 0 := by
    intro z hz
    show (e (Bundle.TotalSpace.mk' (CotangentModelFiber ℂ) (↑z : OnePoint ℂ)
      (ω.toFun (↑z : OnePoint ℂ)))).2 = 0
    rw [holomorphicOneForm_onePointCx_toFun_finite_eq_zero ω z]
    rw [← Trivialization.linearEquivAt_apply (R := ℂ) e (↑z : OnePoint ℂ) hz]
    exact map_zero _
  suffices h_phi_infty : phi OnePoint.infty = 0 by
    have htriv : (e.linearEquivAt ℂ OnePoint.infty h_mem) (ω.toFun OnePoint.infty) = 0 := by
      rw [Trivialization.linearEquivAt_apply (R := ℂ)]
      exact h_phi_infty
    exact (e.linearEquivAt ℂ OnePoint.infty h_mem).injective (by rw [htriv, map_zero])
  by_contra h
  have hopen : IsOpen (e.baseSet ∩ phi ⁻¹' {(0 : CotangentModelFiber ℂ)}ᶜ) :=
    hphi_cont.isOpen_inter_preimage e.open_baseSet isClosed_singleton.isOpen_compl
  have hne : (e.baseSet ∩ phi ⁻¹' {(0 : CotangentModelFiber ℂ)}ᶜ).Nonempty := by
    exact ⟨OnePoint.infty, h_mem, fun hmem => h (Set.mem_singleton_iff.mp hmem)⟩
  have hdense : DenseRange (OnePoint.some : ℂ → OnePoint ℂ) := OnePoint.denseRange_coe
  obtain ⟨z, hz⟩ := hdense.exists_mem_open hopen hne
  exact hz.2 (hphi_fin z hz.1)

/-- Every holomorphic 1-form on `OnePoint ℂ` (= ℂℙ¹) evaluates to zero
at every point.

Sorry-free assembly via `cases x using OnePoint.rec` of the two leaves
`holomorphicOneForm_onePointCx_toFun_finite_eq_zero` and
`holomorphicOneForm_onePointCx_toFun_infty_eq_zero`. -/
theorem holomorphicOneForm_onePointCx_toFun_eq_zero
    (ω : HolomorphicOneForm ℂ (OnePoint ℂ)) (x : OnePoint ℂ) :
    ω.toFun x = 0 := by
  cases x using OnePoint.rec
  · exact holomorphicOneForm_onePointCx_toFun_infty_eq_zero ω
  · exact holomorphicOneForm_onePointCx_toFun_finite_eq_zero ω _

theorem holomorphicOneForm_onePointCx_subsingleton :
    Subsingleton (HolomorphicOneForm ℂ (OnePoint ℂ)) :=
  ⟨fun a b => ext_toFun (fun x => by
    rw [holomorphicOneForm_onePointCx_toFun_eq_zero a x,
        holomorphicOneForm_onePointCx_toFun_eq_zero b x])⟩

/-- An auxiliary `FiniteDimensionalHolomorphicOneForms` instance on
`OnePoint ℂ`, derived from the subsingleton fact above.  Needed in
order to apply the `analyticGenus` definition.

A subsingleton module is trivially finite-dimensional (the empty set is
a spanning set), so this is purely a typeclass-level lemma. -/
noncomputable instance finiteDimensionalHolomorphicOneForms_onePointCx :
    FiniteDimensionalHolomorphicOneForms ℂ (OnePoint ℂ) where
  finiteDimensional := by
    haveI : Subsingleton (HolomorphicOneForm ℂ (OnePoint ℂ)) :=
      holomorphicOneForm_onePointCx_subsingleton
    refine ⟨?_⟩
    -- A subsingleton module has `⊤ = ⊥`, and `⊥` is finitely generated.
    have htop : (⊤ : Submodule ℂ (HolomorphicOneForm ℂ (OnePoint ℂ))) = ⊥ := by
      rw [Submodule.eq_bot_iff]
      intro x _
      exact Subsingleton.elim x 0
    rw [htop]
    exact Submodule.fg_bot

/-- The analytic genus of `OnePoint ℂ` (= ℂℙ¹) is zero.

Pure corollary of `holomorphicOneForm_onePointCx_subsingleton` via
`analyticGenus_eq_zero_of_subsingleton`. -/
theorem analyticGenus_onePointCx_eq_zero :
    analyticGenus ℂ (OnePoint ℂ) = 0 := by
  haveI : Subsingleton (HolomorphicOneForm ℂ (OnePoint ℂ)) :=
    holomorphicOneForm_onePointCx_subsingleton
  exact analyticGenus_eq_zero_of_subsingleton

/-!
### TOPDOWN decomposition of `holomorphicOneFormLinearEquivOfHomeoSphere`
(integrated from Aristotle 88effa1c)

Reduced to a single sub-obligation
`subsingleton_holomorphicOneForm_of_homeo_sphere`. The linear
equivalence is then constructed via `LinearEquiv.ofSubsingleton`,
using the existing `holomorphicOneForm_onePointCx_subsingleton` for
the codomain.

Mathlib gaps for the sub-obligation: uniformization at genus 0,
pullback of holomorphic 1-forms along biholomorphisms, simply-connected
instance for `Metric.sphere` / `OnePoint ℂ`. All absent in v4.28.0.
-/

/-- **Sub-obligation (uniformization-lite core).** A compact connected
Riemann surface homeomorphic to S² has a subsingleton space of
holomorphic 1-forms.

This is the deep content: the homeomorphism to S² combined with
uniqueness of complex structure on S² (uniformization at genus 0)
implies X is biholomorphic to `OnePoint ℂ ≃ ℂℙ¹`, which has
`H⁰(Ω¹) = 0`. -/
structure HomeoSphereHolomorphicOneFormVanishing
    (X : Type*) [TopologicalSpace X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X] where
  subsingleton : Subsingleton (HolomorphicOneForm ℂ X)

/-- **Uniformization-lite helper.** A compact connected Riemann surface
topologically homeomorphic to `OnePoint ℂ` has subsingleton holomorphic
1-forms. This encapsulates the deep content: the uniqueness of the
complex structure on the topological 2-sphere forces X to be
biholomorphic to `OnePoint ℂ ≃ ℂℙ¹`, whose canonical bundle has
negative degree, yielding `H⁰(Ω¹) = 0`.

Mathlib gaps: uniqueness of smooth/complex structure on S², pullback of
holomorphic 1-forms along biholomorphisms.

(Aristotle 22577167 named-helper extraction.) -/
theorem subsingleton_holomorphicOneForm_of_homeo_onePointCx
    (X : Type*) [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X]
    [FiniteDimensionalHolomorphicOneForms ℂ X]
    (_e : Nonempty (X ≃ₜ OnePoint ℂ)) :
    Subsingleton (HolomorphicOneForm ℂ X) := by
  sorry

/-- **Opaque data obligation (uniformization-lite core).** A compact
connected Riemann surface homeomorphic to S² has no nonzero holomorphic
1-forms.

Reduced to `subsingleton_holomorphicOneForm_of_homeo_onePointCx` by
composing the given homeomorphism `X ≃ₜ S²` with the inverse of
`onePointEquivSphereOfFinrankEq`. (Aristotle 22577167.) -/
theorem homeoSphereHolomorphicOneFormVanishing
    (X : Type*) [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X]
    [FiniteDimensionalHolomorphicOneForms ℂ X]
    (_h : Nonempty (X ≃ₜ Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1)) :
    Subsingleton (HolomorphicOneForm ℂ X) := by
  exact subsingleton_holomorphicOneForm_of_homeo_onePointCx X
    (_h.map (fun e => e.trans
      (onePointEquivSphereOfFinrankEq
        (by simp [Complex.finrank_real_complex])).symm))

/-- **Sub-obligation wrapper (sorry-free).** Extracts the subsingleton
consequence from `homeoSphereHolomorphicOneFormVanishing`. -/
theorem subsingleton_holomorphicOneForm_of_homeo_sphere
    (X : Type*) [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X]
    [FiniteDimensionalHolomorphicOneForms ℂ X]
    (h : Nonempty (X ≃ₜ Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1)) :
    Subsingleton (HolomorphicOneForm ℂ X) := by
  exact homeoSphereHolomorphicOneFormVanishing X h

/-- **Bottom-up obligation (uniformization-lite).** A compact connected
Riemann surface `X` homeomorphic to the standard 2-sphere `S²` admits
a ℂ-linear equivalence between its space of holomorphic 1-forms and
that of `OnePoint ℂ`.

Reduced to `subsingleton_holomorphicOneForm_of_homeo_sphere` (the sole
remaining sorry) plus `holomorphicOneForm_onePointCx_subsingleton`
(sorry-free), assembled via `LinearEquiv.ofSubsingleton`. -/
noncomputable def holomorphicOneFormLinearEquivOfHomeoSphere
    (X : Type*) [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X]
    [FiniteDimensionalHolomorphicOneForms ℂ X]
    (_h : Nonempty (X ≃ₜ Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1)) :
    HolomorphicOneForm ℂ X ≃ₗ[ℂ] HolomorphicOneForm ℂ (OnePoint ℂ) := by
  haveI : Subsingleton (HolomorphicOneForm ℂ X) :=
    subsingleton_holomorphicOneForm_of_homeo_sphere X _h
  haveI : Subsingleton (HolomorphicOneForm ℂ (OnePoint ℂ)) :=
    holomorphicOneForm_onePointCx_subsingleton
  exact LinearEquiv.ofSubsingleton _ _

/-- Transport step: a compact Riemann surface `X` homeomorphic to the
standard 2-sphere has the same analytic genus as `OnePoint ℂ`.

This is the "uniformization-lite" content: a topological homeomorphism
from `X` to `S²`, combined with the existing complex structure on `X`
and the canonical complex structure on `OnePoint ℂ` (from
`OnePointCxIsManifold`), forces a biholomorphism `X ≃ OnePoint ℂ` (since
every complex structure on the topological 2-sphere is biholomorphic to
`ℂℙ¹` — uniformization at genus 0). The biholomorphism induces a
ℂ-linear isomorphism of holomorphic 1-form spaces, hence equality of
analytic genera.

Stated as an equality of natural numbers, since both sides are defined
once their `FiniteDimensionalHolomorphicOneForms` instances are
available (`X`'s comes from the hypothesis, `OnePoint ℂ`'s comes from
`finiteDimensionalHolomorphicOneForms_onePointCx` above).

Bottom-up content for a future job: build a complex-structure-transfer
API for homeomorphisms between Riemann surfaces (Mathlib gap), or — more
realistically — go via `onePointCxHomeoS2` and the uniqueness of complex
structure on `S²` (deep, see the survey above). -/
theorem analyticGenus_eq_of_homeomorphic_sphere_of_onePointCx
    (X : Type*) [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X]
    [FiniteDimensionalHolomorphicOneForms ℂ X]
    (_h : Nonempty (X ≃ₜ Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1)) :
    analyticGenus ℂ X = analyticGenus ℂ (OnePoint ℂ) := by
  -- Decompose via a ℂ-linear equivalence of holomorphic 1-form spaces;
  -- existence is the deep uniformization-lite content sorry'd out to
  -- `holomorphicOneFormLinearEquivOfHomeoSphere`.
  have e := holomorphicOneFormLinearEquivOfHomeoSphere X _h
  exact e.finrank_eq

/-- The "easy" direction: if `X` is homeomorphic to the standard 2-sphere
then `analyticGenus ℂ X = 0`.

Pure assembly of `analyticGenus_eq_of_homeomorphic_sphere_of_onePointCx`
(the uniformization-lite transport step) and
`analyticGenus_onePointCx_eq_zero` (the analytic core
`H⁰(ℂℙ¹, Ω¹) = 0`).

Bottom-up content: a compact Riemann surface homeomorphic to `S²` has
the complex structure of `ℂℙ¹` (every smooth structure on `S²` is unique,
and the complex structure on a smooth compact 2-manifold is determined by
its conformal class which is unique on `S²`); on `ℂℙ¹` the canonical
sheaf has degree `-2 < 0`, so `H⁰(ℂℙ¹, Ω¹) = 0` by elementary
divisor-degree considerations. -/
theorem analyticGenus_eq_zero_of_homeomorphic_sphere
    (X : Type*) [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X]
    [FiniteDimensionalHolomorphicOneForms ℂ X]
    (h : Nonempty (X ≃ₜ Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1)) :
    analyticGenus ℂ X = 0 := by
  rw [analyticGenus_eq_of_homeomorphic_sphere_of_onePointCx X h]
  exact analyticGenus_onePointCx_eq_zero

/-!
### Blocker analysis for `homeomorphic_sphere_of_analyticGenus_eq_zero`

**Status (2026-04-27):** sorry — all core ingredients are absent from
Mathlib v4.28.0 (commit `8f9d9cff6bd728b17a24e163c9402775d9e6a365`).
This is strictly harder than the easy direction; it requires the
*forward* implication of uniformization at genus 0.

#### Mathematical content

A compact connected Riemann surface `X` with `analyticGenus ℂ X = 0`
(i.e. `H⁰(X, Ω¹) = 0`, equivalently
`Subsingleton (HolomorphicOneForm ℂ X)` by
`analyticGenus_eq_zero_iff_subsingleton`) is homeomorphic to `S²`.

The standard proof runs through the following chain:

1. **Genus 0 ⟹ simply connected.** By the topological classification
   of compact oriented surfaces, the topological genus equals the
   analytic genus (Hodge theory / de Rham). A compact oriented surface
   of topological genus 0 is simply connected.

2. **Simply connected compact Riemann surface ⟹ biholomorphic to ℂℙ¹.**
   The uniformization theorem says every simply connected Riemann surface
   is biholomorphic to ℂ, 𝔻, or ℂℙ¹. Compactness rules out ℂ and 𝔻.

3. **ℂℙ¹ ≃ₜ S².** The one-point compactification of ℂ (= ℂℙ¹ as a
   topological space) is homeomorphic to the standard 2-sphere in ℝ³
   via stereographic projection.

An alternative route avoids uniformization entirely by using Riemann–Roch
+ a rational function argument:

1'. **Genus 0 + Riemann–Roch ⟹ ∃ meromorphic function of degree 1.**
    With `g = 0`, Riemann–Roch gives `ℓ(D) - ℓ(K-D) ≥ deg D + 1` for
    any divisor `D`. Taking `D` = a single point gives a meromorphic
    function with a single simple pole, i.e. of degree 1.

2'. **Degree-1 meromorphic function ⟹ biholomorphism to ℂℙ¹.**
    A meromorphic function of degree 1 on a compact Riemann surface is a
    biholomorphism onto ℂℙ¹.

3'. Same as step 3.

#### Mathlib API survey

| Concept searched | Found? | Notes |
|---|---|---|
| `uniformization` | ❌ | No uniformization theorem in any form. |
| `RiemannSurface` | ❌ | No dedicated Riemann surface type. |
| `ComplexProjectiveLine` / `RiemannSphere` | ❌ | Not defined as a type or manifold. |
| `Projectivization` | ✅ | `Projectivization ℂ (Fin 2 → ℂ)` exists but has no manifold or complex-analytic structure. |
| `OnePoint` (one-point compactification) | ✅ | `OnePoint ℂ` exists, is `CompactSpace`, but has no `T2Space`, `ChartedSpace`, or `IsManifold` instance. No homeomorphism to `Metric.sphere`. |
| `stereographic` / `stereographic'` | ✅ | Stereographic projection exists for `Metric.sphere (0 : E) 1` in a real inner product space `E`. Gives `ChartedSpace (EuclideanSpace ℝ (Fin n))` and `IsManifold (𝓡 n)` for the `n`-sphere in `ℝⁿ⁺¹`. The 2-sphere is charted over `EuclideanSpace ℝ (Fin 2)`, **not** over `ℂ`. |
| `EuclideanSpace.instChartedSpaceSphere` | ✅ | Gives `ChartedSpace (EuclideanSpace ℝ (Fin 2))` on `Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1`. The model is *real*, not complex. |
| `IsManifold` for sphere | ✅ | `IsManifold (𝓡 2) ⊤` on `S²` exists (real smooth manifold). No complex manifold instance. |
| `SimplyConnectedSpace` | ✅ | Class exists. No instance for `S²` or `OnePoint ℂ`. |
| `IsCoveringMap` | ✅ | Covering map API exists with path-lifting. No universal covering construction for Riemann surfaces. |
| `MeromorphicAt` | ✅ | Pointwise meromorphic function API exists (orders, trailing coefficients). No global meromorphic function type on manifolds; no divisor theory. |
| `Divisor` / `RiemannRoch` | ❌ | No divisor theory, no Riemann–Roch theorem. |
| `Hodge` / `deRham` / `topologicalGenus` | ❌ | No Hodge theory, no de Rham cohomology, no topological genus. |
| `Homeomorph.compactificationToSphere` | ❌ | No homeomorphism `OnePoint ℂ ≃ₜ S²`. |
| `EuclideanSpace ℝ (Fin 2) ≃ₗᵢ[ℝ] ℂ` | Partial | `Complex.measurableEquiv` and `Complex.isometry_ofReal` exist but a full `LinearIsometryEquiv` from `EuclideanSpace ℝ (Fin 2)` to `ℂ` is not directly available as a named lemma. |

#### Dependency graph

```
homeomorphic_sphere_of_analyticGenus_eq_zero
  │
  ├─► analyticGenus_eq_zero_iff_subsingleton  [AVAILABLE ✅]
  │     (converts hypothesis to Subsingleton (HolomorphicOneForm ℂ X))
  │
  ├─► [MISSING ❌] genus_zero_implies_simply_connected
  │     ├─► [MISSING ❌] analytic_genus_eq_topological_genus (Hodge theory)
  │     │     ├─► [MISSING ❌] de Rham cohomology
  │     │     └─► [MISSING ❌] Hodge decomposition
  │     └─► [MISSING ❌] topological classification of compact oriented surfaces
  │           └─► [MISSING ❌] surface_genus_zero_iff_simply_connected
  │
  ├─► [MISSING ❌] uniformization_compact_simply_connected
  │     ├─► [MISSING ❌] uniformization_theorem
  │     │     ├─► [MISSING ❌] universal covering of Riemann surface
  │     │     ├─► [MISSING ❌] Riemann mapping theorem (for ℂ and 𝔻)
  │     │     └─► [MISSING ❌] Koebe's theorem / Perron's method
  │     └─► [MISSING ❌] compactness rules out ℂ and 𝔻
  │
  ├─► [MISSING ❌] CP1_def : ℂℙ¹ as a complex manifold
  │     ├─► [PARTIAL] Projectivization ℂ (Fin 2 → ℂ) (no manifold structure)
  │     └─► [PARTIAL] OnePoint ℂ (no T2, no manifold structure)
  │
  └─► [MISSING ❌] CP1_homeomorph_sphere : ℂℙ¹ ≃ₜ S²
        ├─► [PARTIAL] stereographic / stereographic' (real model only)
        └─► [MISSING ❌] OnePoint ℂ ≃ₜ Metric.sphere 0 1 in ℝ³
```

**Alternative route via Riemann–Roch:**

```
homeomorphic_sphere_of_analyticGenus_eq_zero
  │
  ├─► [AVAILABLE ✅] analyticGenus_eq_zero_iff_subsingleton
  │
  ├─► [MISSING ❌] riemann_roch_genus_zero_degree_one_function
  │     ├─► [MISSING ❌] Riemann–Roch theorem
  │     │     ├─► [MISSING ❌] sheaf cohomology on Riemann surfaces
  │     │     └─► [MISSING ❌] Serre duality
  │     └─► [MISSING ❌] divisor theory
  │
  ├─► [MISSING ❌] degree_one_meromorphic_iff_biholomorphic_CP1
  │     └─► [MISSING ❌] global meromorphic functions on manifolds
  │
  └─► [MISSING ❌] CP1_homeomorph_sphere (same as above)
```

#### 3-step Mathlib-API plan for a future job

**Step 1 — Build `ℂℙ¹` as a complex manifold and prove `ℂℙ¹ ≃ₜ S²`.**

Define `ℂℙ¹` as `OnePoint ℂ` (the Alexandrov one-point compactification
of `ℂ`). Equip it with:
- A `T2Space` instance (requires locally compact + T2 of `ℂ`, which
  Mathlib already has).
- A `ChartedSpace ℂ` instance via two charts: `z ↦ z` on `ℂ ⊂ OnePoint ℂ`
  and `z ↦ 1/z` on `(OnePoint ℂ) \ {0}`.
- An `IsManifold (modelWithCornersSelf ℂ ℂ) ⊤` instance by showing chart
  transitions are holomorphic (they are `z ↦ 1/z` on `ℂ \ {0}`).
- A `Homeomorph` from `OnePoint ℂ` to `Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1`
  by composing the identification `ℂ ≅ ℝ²` with the inverse of
  stereographic projection and extending continuously to the point at
  infinity.

**Estimated difficulty:** Medium-hard. The topological parts (compact,
connected, T2) are close to what Mathlib has for `OnePoint`. The main
work is constructing the complex atlas and proving the homeomorphism
with `S²`. The latter requires showing that `stereographic'⁻¹ ∘ (ℂ → ℝ²)`
extends continuously to a bijection `OnePoint ℂ → S²`. Roughly 300–600
lines of new Lean code.

**Step 2 — Prove `H⁰(ℂℙ¹, Ω¹) = 0` directly (no Riemann–Roch).**

Show `Subsingleton (HolomorphicOneForm ℂ (OnePoint ℂ))` by a direct
argument: a holomorphic 1-form on `OnePoint ℂ` restricts to `f(z) dz`
on the standard chart `ℂ`, where `f : ℂ → ℂ` is entire. On the chart at
infinity, the transition gives `f(z) dz = -f(1/w) / w² dw`, which must
be holomorphic at `w = 0`. By Liouville's theorem (available in Mathlib:
`Complex.liouville_theorem`), `f` is constant, and the holomorphicity
condition at infinity forces the constant to be zero.

**Estimated difficulty:** Medium. Liouville's theorem is available.
The main challenge is formalizing what "holomorphic 1-form on a charted
space" means in terms of the chart transition — this depends on the
project's `HolomorphicOneForm` API and may require additional interface
lemmas.

**Step 3 — The actual uniformization step (genus 0 ⟹ biholomorphic to ℂℙ¹).**

This is the hardest step and has two possible sub-approaches:

**(3a) Via uniformization theorem (very hard).** Prove the uniformization
theorem for compact Riemann surfaces: every simply connected Riemann
surface is biholomorphic to ℂ, 𝔻, or ℂℙ¹. This is a major theorem
requiring Perron's method, Dirichlet problem on Riemann surfaces,
normal families, and the Riemann mapping theorem. Estimated at 2000+
lines of new Lean code. Then show `genus 0 ⟹ simply connected`
(requires Hodge theory or classification of surfaces).

**(3b) Via Riemann–Roch (hard).** Prove the Riemann–Roch theorem for
compact Riemann surfaces. Then the argument is: genus 0 ⟹ degree-1
meromorphic function exists ⟹ biholomorphism to ℂℙ¹. This avoids
uniformization but requires sheaf cohomology, Serre duality, and
divisor theory. Estimated at 1500+ lines.

**(3c) Via direct Mittag-Leffler–style argument (moderately hard).**
Avoid both uniformization and full Riemann–Roch. Use the vanishing
of `H¹(X, 𝒪)` (which follows from `H⁰(X, Ω¹) = 0` by Serre duality —
but Serre duality itself is nontrivial). Then Mittag-Leffler–type
arguments produce a meromorphic function of degree 1. This still
requires substantial analytic machinery not in Mathlib.

#### Honest assessment

This theorem is **not realistically formalizable** with the current
Mathlib API (v4.28.0). The gap is enormous:

- **ℂℙ¹ as a complex manifold** does not exist. Building it (Step 1)
is a self-contained project of moderate size (~500 lines) and is the
only step that could plausibly be completed in a focused effort.

- **The uniformization theorem** (or any equivalent, such as
Riemann–Roch for Riemann surfaces) is entirely absent and represents
one of the deepest results in complex analysis / algebraic geometry.
No path through Mathlib's current API gets close.

- **The bridge from analytic genus to topological genus** (Hodge theory /
de Rham cohomology) is also absent. Without it, even the implication
"genus 0 ⟹ simply connected" cannot be stated.

- **Comparison with the easy direction:** the easy direction
(`analyticGenus_eq_zero_of_homeomorphic_sphere`) requires showing
`H⁰(ℂℙ¹, Ω¹) = 0`, which can be done with Steps 1–2 alone (no
uniformization). The hard direction additionally requires Step 3,
which is strictly more demanding.

**Verdict:** This theorem should be classified as a **Phase 4+ deferred
dependency**. It is a deep uniformization-level result. A realistic
formalization would require either (a) formalizing the uniformization
theorem from scratch (~2000+ lines of new Lean), or (b) formalizing
Riemann–Roch for compact Riemann surfaces (~1500+ lines). Neither is
feasible in the near term without a dedicated multi-month effort.

The sorry should remain. The `analyticGenus_eq_zero_iff_homeomorphic_sphere`
biconditional that assembles both directions will carry two sorries
(one from each direction) until the relevant Mathlib infrastructure
matures.

#### Nearest Mathlib footholds (for future work)

- `OnePoint` (one-point compactification): good starting point for
  defining `ℂℙ¹` topologically.
- `stereographic` / `stereographic'` / `EuclideanSpace.instChartedSpaceSphere`:
  real manifold structure on `S²`, needed for Step 1's homeomorphism.
- `Complex.liouville_theorem`: Liouville's theorem for bounded entire
  functions, needed for Step 2.
- `MeromorphicAt`: pointwise meromorphic function API, useful building
  block for Steps 2–3.
- `SimplyConnectedSpace`: the class exists, though no instance for `S²`.
- `IsCoveringMap` + path lifting: covering space theory, relevant if
  pursuing uniformization via universal covers.
-/

/-- The one-point compactification of `ℂ` is homeomorphic to the unit
2-sphere `S² ⊂ ℝ³`.  This uses `onePointEquivSphereOfFinrankEq` from
`Mathlib.Topology.Compactification.OnePoint.Sphere`, instantiated with
`V = ℂ` (which has `Module.finrank ℝ ℂ = 2`) and `ι = Fin 3`. -/
noncomputable def onePointCx_homeomorph_sphere :
    OnePoint ℂ ≃ₜ Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1 :=
  onePointEquivSphereOfFinrankEq (by simp [Complex.finrank_real_complex])

/-- The Riemann-Roch output in genus zero: a meromorphic map to `OnePoint ℂ`
whose pole divisor is the point divisor `[pole]`. -/
structure GenusZeroSimplePoleMeromorphicMap
    (X : Type*) [TopologicalSpace X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X] where
  meromorphicMap : MeromorphicMapToSphere X
  pole : X
  simple_pole_cert : meromorphicMap.poles = Divisor.point pole

namespace GenusZeroSimplePoleMeromorphicMap

/-- The underlying map to the Riemann sphere. -/
def toMap {X : Type*} [TopologicalSpace X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X]
    (f : GenusZeroSimplePoleMeromorphicMap X) : X → OnePoint ℂ :=
  f.meromorphicMap.toMap

end GenusZeroSimplePoleMeromorphicMap

/-- Placeholder data after the compactness/properness step: the genus-zero
meromorphic map is a degree-one map to `OnePoint ℂ`.

The fields are the topological consequences needed by the final assembly:
continuity and bijectivity. A future refinement should replace this bridge by
properness plus the local degree calculation, then derive these fields. -/
structure GenusZeroProperDegreeOneMap
    (X : Type*) [TopologicalSpace X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X] where
  toMap : X → OnePoint ℂ
  continuous_toMap : Continuous toMap
  bijective_toMap : Function.Bijective toMap
  degree_one_data : ∃ f : MeromorphicMapToSphere X,
    toMap = f.toMap ∧ Nonempty (MeromorphicDegreeOneData X f)

/-- Placeholder data for the last analytic step: a degree-one meromorphic map
is a biholomorphic parametrization of `X` by `OnePoint ℂ`.

At the topological surface needed here, this is represented by the resulting
homeomorphism. Future work can strengthen the structure with a biholomorphism
type once the project has one. -/
structure GenusZeroBiholomorphicParametrization
    (X : Type*) [TopologicalSpace X] where
  toHomeomorph : X ≃ₜ OnePoint ℂ

/-!
### TOPDOWN decomposition for `genus_zero_homeomorph_onePointCx`

The previous single uniformization-level sorry is split into three named
obligations matching the standard Riemann-Roch route:

1. `genus_zero_exists_simplePole_meromorphicMap` — from
   `analyticGenus = 0`, Riemann-Roch produces a meromorphic function with one
   simple pole.
2. `simplePole_meromorphicMap_proper_degreeOne` — compactness/properness and
   divisor-degree bookkeeping promote that function to a proper degree-one map
   to `OnePoint ℂ`.
3. `proper_degreeOne_meromorphicMap_biholomorphic` — a proper degree-one
   holomorphic map is a biholomorphic parametrization, hence a homeomorphism.

The original `genus_zero_homeomorph_onePointCx` is now pure assembly of these
smaller leaves.
-/

/-- Fixed-pole Riemann-Roch output, now backed by the production
meromorphic/divisor substrate. -/
abbrev GenusZeroRiemannRochFixedPoleData
    (X : Type*) [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X]
    [FiniteDimensionalHolomorphicOneForms ℂ X]
    (P : X)
    (h : analyticGenus ℂ X = 0) : Type _ :=
  GenusZeroFixedPoleMeromorphicData X P h

/-- **Fixed-pole Riemann-Roch existence leaf.** If a compact connected
Riemann surface has analytic genus zero, then for any prescribed point `P`
there is a meromorphic function with a single simple pole at `P`.

Bottom-up content: divisor theory on compact Riemann surfaces and the
Riemann-Roch calculation `ℓ(P) = 2` when `g = 0`, producing a nonconstant
meromorphic function whose pole divisor is exactly `[P]`. -/
theorem genusZeroRiemannRochFixedPoleData_nonempty
    (X : Type*) [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X]
    [FiniteDimensionalHolomorphicOneForms ℂ X]
    (P : X)
    (h : analyticGenus ℂ X = 0) :
    Nonempty (GenusZeroRiemannRochFixedPoleData X P h) := by
  exact genusZero_fixedPole_meromorphicData_nonempty X P h

/-- **Fixed-pole Riemann-Roch data assembly.** Extracts the map/certificate
package from the named existence leaf. -/
noncomputable def genusZeroRiemannRochFixedPoleData
    (X : Type*) [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X]
    [FiniteDimensionalHolomorphicOneForms ℂ X]
    (P : X)
    (h : analyticGenus ℂ X = 0) :
    GenusZeroRiemannRochFixedPoleData X P h :=
  Classical.choice (genusZeroRiemannRochFixedPoleData_nonempty X P h)

/-- **Fixed-pole Riemann-Roch map projection.** -/
noncomputable def genusZeroRiemannRochNonconstantMapAt
    (X : Type*) [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X]
    [FiniteDimensionalHolomorphicOneForms ℂ X]
    (P : X)
    (h : analyticGenus ℂ X = 0) :
    X → OnePoint ℂ :=
  (genusZeroRiemannRochFixedPoleData X P h).meromorphicMap.toMap

/-- **Fixed-pole divisor/order certificate projection.** The Riemann-Roch
map produced at `P` has exactly one simple pole, located at `P`, and no
other poles. -/
theorem genusZeroRiemannRochSimplePoleAt
    (X : Type*) [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X]
    [FiniteDimensionalHolomorphicOneForms ℂ X]
    (P : X)
    (h : analyticGenus ℂ X = 0) :
    (genusZeroRiemannRochFixedPoleData X P h).meromorphicMap.poles =
      Divisor.point P := by
  exact (genusZeroRiemannRochFixedPoleData X P h).poleDivisor_eq_point

/-- **Fixed-pole Riemann-Roch assembly.** The map part of the fixed-pole
simple-pole statement; the pole certificate is kept separately as
`genusZeroRiemannRochSimplePoleAt`.

This definition exists so callers that only need the eventual meromorphic map
do not depend directly on the certificate packaging. -/
noncomputable def genusZeroSimplePoleMeromorphicMapAt
    (X : Type*) [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X]
    [FiniteDimensionalHolomorphicOneForms ℂ X]
    (P : X)
    (h : analyticGenus ℂ X = 0) :
    X → OnePoint ℂ :=
  genusZeroRiemannRochNonconstantMapAt X P h

/-- **Assembly for the Riemann-Roch leaf.** Choose any point of the connected
surface and package the fixed-pole Riemann-Roch map at that point.

The remaining Riemann-Roch leaf is now the single fixed-pole existence
statement `genusZeroRiemannRochFixedPoleData_nonempty`: for a prescribed
point `P`, genus zero Riemann-Roch produces a meromorphic map whose only pole
is simple and located at `P`. -/
noncomputable def simplePoleMeromorphicMapOfGenusZero
    (X : Type*) [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X]
    [FiniteDimensionalHolomorphicOneForms ℂ X]
    (h : analyticGenus ℂ X = 0) :
    GenusZeroSimplePoleMeromorphicMap X :=
  let P : X := Classical.choice (inferInstance : Nonempty X)
  let data := genusZeroRiemannRochFixedPoleData X P h
  { meromorphicMap := data.meromorphicMap
    pole := P
    simple_pole_cert := genusZeroRiemannRochSimplePoleAt X P h }

/-- **Sub-obligation 1 wrapper (sorry-free).** Existence form of
`simplePoleMeromorphicMapOfGenusZero`. -/
theorem genus_zero_exists_simplePole_meromorphicMap
    (X : Type*) [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X]
    [FiniteDimensionalHolomorphicOneForms ℂ X]
    (h : analyticGenus ℂ X = 0) :
    Nonempty (GenusZeroSimplePoleMeromorphicMap X) := by
  exact ⟨simplePoleMeromorphicMapOfGenusZero X h⟩

/-- **Properness/degree data existence leaf.** A one-simple-pole map has
some proper degree-one promotion.

This refines the old properness/degree opaque into a named existence
statement. Bottom-up content: prove continuity of the extended map,
compactness-driven properness, and the divisor-degree computation giving
bijectivity. -/
theorem properDegreeOneMapOfSimplePole_nonempty
    (X : Type*) [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X]
    [FiniteDimensionalHolomorphicOneForms ℂ X]
    (_f : GenusZeroSimplePoleMeromorphicMap X) :
    Nonempty (GenusZeroProperDegreeOneMap X) := by
  let hdegree :=
    meromorphicDegreeOneData_of_poleDivisor_point X _f.meromorphicMap _f.pole
      _f.simple_pole_cert
  refine hdegree.elim ?_
  intro data
  exact ⟨
    { toMap := _f.meromorphicMap.toMap
      continuous_toMap := data.continuous_toMap
      bijective_toMap := data.bijective_toMap
      degree_one_data := ⟨_f.meromorphicMap, rfl, ⟨data⟩⟩ }⟩

/-- **Properness/degree data assembly.** Extracts the degree-one promotion
from the named existence leaf. -/
noncomputable def properDegreeOneMapOfSimplePole
    (X : Type*) [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X]
    [FiniteDimensionalHolomorphicOneForms ℂ X]
    (f : GenusZeroSimplePoleMeromorphicMap X) :
    GenusZeroProperDegreeOneMap X :=
  Classical.choice (properDegreeOneMapOfSimplePole_nonempty X f)

/-- **Sub-obligation 2 wrapper (sorry-free).** Existence form of
`properDegreeOneMapOfSimplePole`. -/
theorem simplePole_meromorphicMap_proper_degreeOne
    (X : Type*) [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X]
    [FiniteDimensionalHolomorphicOneForms ℂ X]
    (f : GenusZeroSimplePoleMeromorphicMap X) :
    Nonempty (GenusZeroProperDegreeOneMap X) := by
  exact ⟨properDegreeOneMapOfSimplePole X f⟩

/-- **Sub-obligation 3 (degree one implies parametrization).** A proper
degree-one meromorphic map from a compact connected Riemann surface to
`OnePoint ℂ` is a biholomorphic parametrization.

Bottom-up content: a holomorphic map of degree one is bijective with
nonvanishing local degree, hence a biholomorphism; forgetting the analytic
structure gives the recorded homeomorphism. -/
theorem proper_degreeOne_meromorphicMap_biholomorphic
    (X : Type*) [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X]
    [FiniteDimensionalHolomorphicOneForms ℂ X]
    (f : GenusZeroProperDegreeOneMap X) :
    Nonempty (GenusZeroBiholomorphicParametrization X) := by
  let e : X ≃ OnePoint ℂ := Equiv.ofBijective f.toMap f.bijective_toMap
  have he : Continuous e := by
    simpa [e] using f.continuous_toMap
  exact ⟨⟨he.homeoOfEquivCompactToT2⟩⟩

/-- **Uniformization (genus zero):** a compact connected Riemann surface
with `analyticGenus = 0` is homeomorphic to the one-point
compactification of `ℂ`.

Pure assembly of the three Riemann-Roch route leaves above:
simple-pole meromorphic function, proper degree-one map, and degree-one
biholomorphic parametrization. -/
theorem genus_zero_homeomorph_onePointCx
    (X : Type*) [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X]
    [FiniteDimensionalHolomorphicOneForms ℂ X]
    (h : analyticGenus ℂ X = 0) :
    Nonempty (X ≃ₜ OnePoint ℂ) := by
  let ⟨f⟩ := genus_zero_exists_simplePole_meromorphicMap X h
  let ⟨g⟩ := simplePole_meromorphicMap_proper_degreeOne X f
  let ⟨b⟩ := proper_degreeOne_meromorphicMap_biholomorphic X g
  exact ⟨b.toHomeomorph⟩

/-- The "hard" direction: if `analyticGenus ℂ X = 0` then `X` is
homeomorphic to the standard 2-sphere.

Decomposes into two obligations:
1. `genus_zero_homeomorph_onePointCx` — Riemann-Roch route assembly through
   simple-pole existence, proper degree-one map, and biholomorphic
   parametrization.
2. `onePointCx_homeomorph_sphere` — the standard homeomorphism
   `OnePoint ℂ ≃ₜ S²` via inverse stereographic projection (proved
   sorry-free using `onePointEquivSphereOfFinrankEq`). -/
theorem homeomorphic_sphere_of_analyticGenus_eq_zero
    (X : Type*) [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X]
    [FiniteDimensionalHolomorphicOneForms ℂ X]
    (_h : analyticGenus ℂ X = 0) :
    Nonempty (X ≃ₜ Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1) :=
  let ⟨e⟩ := genus_zero_homeomorph_onePointCx X _h
  ⟨e.trans onePointCx_homeomorph_sphere⟩

/-- A compact connected Riemann surface has analytic genus zero iff it is
homeomorphic to the standard 2-sphere.

Pure assembly of the two directions
`analyticGenus_eq_zero_of_homeomorphic_sphere` and
`homeomorphic_sphere_of_analyticGenus_eq_zero`; this declaration adds
no new sorry. -/
theorem analyticGenus_eq_zero_iff_homeomorphic_sphere
    (X : Type*) [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X]
    [FiniteDimensionalHolomorphicOneForms ℂ X] :
    analyticGenus ℂ X = 0 ↔
      Nonempty (X ≃ₜ Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1) :=
  ⟨homeomorphic_sphere_of_analyticGenus_eq_zero X,
   analyticGenus_eq_zero_of_homeomorphic_sphere X⟩

end JacobianChallenge.HolomorphicForms
