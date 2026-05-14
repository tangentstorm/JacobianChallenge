import Jacobian.HolomorphicForms.VanishingOrder
import Jacobian.HolomorphicForms.AnalyticLocalMapping
import Jacobian.HolomorphicForms.CotangentBundle
import Mathlib.Analysis.Analytic.Order
import Mathlib.Geometry.Manifold.ContMDiff.Defs
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.Analytic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

/-!
# Holomorphic maps between charted-on-`ℂ` spaces

A project-local definition of "holomorphic at a point" / "holomorphic"
for maps `f : X → Y` between two `ChartedSpace ℂ`-equipped spaces.
Mathlib `v4.28.0` does not provide a manifold-level analytic predicate
(no `MAnalyticAt`, no `Holomorphic*`), so we roll our own using the
canonical chart `chartAt ℂ` on each side and Mathlib's
`AnalyticAt ℂ` for the chart-local expression.
-/

namespace JacobianChallenge.HolomorphicForms

open scoped Manifold Topology ContDiff BigOperators
open Set Filter

variable {X Y Z : Type*}
  [TopologicalSpace X] [ChartedSpace ℂ X]
  [TopologicalSpace Y] [ChartedSpace ℂ Y]
  [TopologicalSpace Z] [ChartedSpace ℂ Z]

/-- Canonical chart-local presentation of `f : X → Y` at `p`. -/
noncomputable def chartLocalAt (f : X → Y) (p : X) : ℂ → ℂ :=
  chartAt ℂ (f p) ∘ f ∘ (chartAt ℂ p).symm

/-- `f : X → Y` is *holomorphic at* `p`. -/
def IsHolomorphicAt (f : X → Y) (p : X) : Prop :=
  AnalyticAt ℂ (chartLocalAt f p) (chartAt ℂ p p)

/-- **Holomorphic addition.** -/
theorem IsHolomorphicAt.add
    {f g : X → ℂ} {p : X} (_hf : IsHolomorphicAt f p)
    (_hg : IsHolomorphicAt g p) : IsHolomorphicAt (f + g) p := by
  sorry

/-- **Holomorphic scalar multiplication.** -/
theorem IsHolomorphicAt.smul
    {f : X → ℂ} {p : X} (c : ℂ) (_hf : IsHolomorphicAt f p) :
    IsHolomorphicAt (c • f) p := by
  sorry

/-- **Holomorphic finite sum.** -/
theorem IsHolomorphicAt.sum {ι : Type*} {s : Finset ι} {f : ι → X → ℂ} {p : X}
    (_hf : ∀ i ∈ s, IsHolomorphicAt (f i) p) :
    IsHolomorphicAt (fun x => Finset.sum s (fun i => f i x)) p := by
  sorry

/-- **Holomorphic linear combination.** -/
theorem IsHolomorphicAt.sum_smul {ι : Type*} {s : Finset ι} {f : ι → X → ℂ} {c : ι → ℂ} {p : X}
    (_hf : ∀ i ∈ s, IsHolomorphicAt (f i) p) :
    IsHolomorphicAt (fun x => Finset.sum s (fun i => c i • f i x)) p :=
  sorry

/-- **Holomorphic composition.** -/
theorem IsHolomorphicAt.comp
    {f : X → Y} {g : Y → Z} {p : X}
    (_hg : IsHolomorphicAt g (f p)) (_hf : IsHolomorphicAt f p) :
    IsHolomorphicAt (g ∘ f) p := by
  sorry

/-- **Holomorphic congruence.** -/
theorem IsHolomorphicAt.congr_of_eventuallyEq
    {f g : X → Y} {p : X} (_hf : IsHolomorphicAt f p)
    (_hfg : f =ᶠ[𝓝 p] g) : IsHolomorphicAt g p := by
  sorry


/-- The *chart-local order of vanishing*. -/
noncomputable def mapAnalyticOrderAt (f : X → Y) (p : X) : ℕ :=
  analyticOrderNatAt
    (fun t => chartLocalAt f p t - chartLocalAt f p (chartAt ℂ p p))
    (chartAt ℂ p p)

/-- `f : X → Y` is *holomorphic*. -/
structure IsHolomorphic (f : X → Y) : Prop where
  continuous : Continuous f
  holomorphicAt : ∀ p, IsHolomorphicAt f p
  local_kfold_ramified :
    ∀ [IsManifold 𝓘(ℂ) ω X] [IsManifold 𝓘(ℂ) ω Y]
      {x : X} {k : ℕ}, 0 < k → mapAnalyticOrderAt f x = k →
      ∃ U : Set X, IsOpen U ∧ x ∈ U ∧
      ∃ V : Set Y, IsOpen V ∧ f x ∈ V ∧
      ∀ y ∈ V, y ≠ f x →
      ∃ s : Finset X, s.card = k ∧ ↑s ⊆ U ∧
        (∀ x' ∈ s, f x' = y ∧ mapAnalyticOrderAt f x' = 1) ∧
        (∀ x' ∈ U, f x' = y → x' ∈ s)
  weightedFiberSum_eventually_eq :
    ∀ [IsManifold 𝓘(ℂ) ω X] [IsManifold 𝓘(ℂ) ω Y]
      [CompactSpace X] [T2Space X] [PreconnectedSpace X] [T2Space Y],
      (¬ ∃ y₀ : Y, ∀ x, f x = y₀) →
      (finite_fiber : ∀ y : Y, (f ⁻¹' {y}).Finite) →
      ∀ y₀ : Y, ∀ᶠ y in 𝓝 y₀,
        (Finset.sum (finite_fiber y).toFinset (mapAnalyticOrderAt f)) =
        (Finset.sum (finite_fiber y₀).toFinset (mapAnalyticOrderAt f))

/-- The chart-local presentation evaluated at the chart image of `p`
yields the chart image of `f p`. -/
@[simp]
theorem chartLocalAt_chartAt_self (f : X → Y) (p : X) :
    chartLocalAt f p (chartAt ℂ p p) = chartAt ℂ (f p) (f p) := by
  unfold chartLocalAt
  have : (chartAt ℂ p).symm (chartAt ℂ p p) = p :=
    (chartAt ℂ p).left_inv (mem_chart_source ℂ p)
  simp [this]

section LocalInverse

variable [IsManifold 𝓘(ℂ) ω X] [IsManifold 𝓘(ℂ) ω Y]

/-- A continuous linear map between complex normed spaces is analytic. -/
theorem _root_.ContinuousLinearMap.analyticAt_ℂ {E F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℂ E]
    [NormedAddCommGroup F] [NormedSpace ℂ F]
    (f : E →L[ℂ] F) (x : E) : AnalyticAt ℂ f x :=
  ⟨f.fpowerSeries x, f.hasFPowerSeriesAt x⟩



/-- Identification between the cotangent fiber and ℂ. -/
noncomputable def cotangentFiberIso : (ℂ →L[ℂ] ℂ) ≃L[ℂ] ℂ :=
  sorry

/-- **Plan leaf 15 (NEW).** CotangentModelFiber ℂ is a manifold over ℂ. -/
noncomputable instance instChartedSpaceCotangentModelFiber :
    ChartedSpace ℂ (CotangentModelFiber ℂ) :=
  sorry

noncomputable instance instIsManifoldCotangentModelFiber :
    IsManifold 𝓘(ℂ, ℂ) ⊤ (CotangentModelFiber ℂ) :=
  sorry

/-- Manifold-level local inverse of a holomorphic map. -/
noncomputable def IsHolomorphicAt.localInverse
    {f : X → Y} {p : X} (hf : IsHolomorphicAt f p)
    (hderiv : deriv (chartLocalAt f p) (chartAt ℂ p p) ≠ 0) : Y → X :=
  fun y => (chartAt ℂ p).symm
    (hf.hasStrictDerivAt.localInverse (chartLocalAt f p)
      (deriv (chartLocalAt f p) (chartAt ℂ p p)) (chartAt ℂ p p) hderiv
      (chartAt ℂ (f p) y))

/-- **Plan leaf 11 (NEW).** The local inverse is holomorphic. -/
theorem IsHolomorphicAt.localInverse_isHolomorphicAt
    {f : X → Y} {p : X} (hf : IsHolomorphicAt f p)
    (hderiv : deriv (chartLocalAt f p) (chartAt ℂ p p) ≠ 0) :
    IsHolomorphicAt (hf.localInverse hderiv) (f p) := by
  sorry

end LocalInverse

section ChartIndependence

variable [IsManifold 𝓘(ℂ) ω X] [IsManifold 𝓘(ℂ) ω Y]

open JacobianChallenge.HolomorphicForms.VanishingOrder

/-- Swap of `transition_deriv_ne_zero`. -/
theorem chartAt_symm_transition_deriv_ne_zero
    {Z : Type*} [TopologicalSpace Z] [ChartedSpace ℂ Z]
    [IsManifold 𝓘(ℂ) ω Z]
    {q : Z} (e : OpenPartialHomeomorph Z ℂ)
    (he : e ∈ IsManifold.maximalAtlas 𝓘(ℂ) ω Z) (hq : q ∈ e.source) :
    deriv ((⇑e) ∘ (chartAt ℂ q).symm) (chartAt ℂ q q) ≠ 0 := by
  sorry

/-- The chart-local order of vanishing is independent of choice of charts. -/
theorem mapAnalyticOrderAt_congr_of_maximalAtlas
    {f_ : X → Y} {p : X} {e₁ : OpenPartialHomeomorph X ℂ} {e₂ : OpenPartialHomeomorph Y ℂ}
    (_he₁ : e₁ ∈ IsManifold.maximalAtlas 𝓘(ℂ) ω X) (_hp₁ : p ∈ e₁.source)
    (_he₂ : e₂ ∈ IsManifold.maximalAtlas 𝓘(ℂ) ω Y) (_hp₂ : f_ p ∈ e₂.source) :
    analyticOrderNatAt (fun t => e₂ (f_ (e₁.symm t)) - e₂ (f_ p)) (e₁ p) =
    mapAnalyticOrderAt f_ p := by
  sorry

/-- Backwards-compatible name for the chart-independence theorem. -/
theorem mapAnalyticOrderAt_eq_of_mem_maximalAtlas
    {f_ : X → Y} (_hf : IsHolomorphic f_) {p : X}
    {e₁ : OpenPartialHomeomorph X ℂ}
    (he₁ : e₁ ∈ IsManifold.maximalAtlas 𝓘(ℂ) ω X) (hp₁ : p ∈ e₁.source)
    {e₂ : OpenPartialHomeomorph Y ℂ}
    (he₂ : e₂ ∈ IsManifold.maximalAtlas 𝓘(ℂ) ω Y) (hp₂ : f_ p ∈ e₂.source) :
    analyticOrderNatAt (fun t => e₂ (f_ (e₁.symm t)) - e₂ (f_ p)) (e₁ p) =
    mapAnalyticOrderAt f_ p :=
  mapAnalyticOrderAt_congr_of_maximalAtlas he₁ hp₁ he₂ hp₂

end ChartIndependence

section Compatibility

/-- Local constancy of a holomorphic map on a preconnected source forces global constancy. -/
theorem IsHolomorphic.eq_const_of_eventuallyEq
    [PreconnectedSpace X] [T2Space Y]
    {f : X → Y} (_hf : IsHolomorphic f) {y₀ : Y} {x₁ : X}
    (_h_local : ∀ᶠ x in 𝓝 x₁, f x = y₀) :
    ∀ x, f x = y₀ := by
  sorry

/-- Finite fibres of a nonconstant holomorphic map on a compact source. -/
theorem isHolomorphic_finite_fiber
    [CompactSpace X] [PreconnectedSpace X] [T2Space Y]
    {f : X → Y} (_hf : IsHolomorphic f)
    (_hnonconst : ¬ ∃ y₀ : Y, ∀ x, f x = y₀) (y : Y) :
    (f ⁻¹' {y}).Finite := by
  sorry

/-- Positivity of the local analytic order for a nonconstant holomorphic map. -/
theorem mapAnalyticOrderAt_pos
    [PreconnectedSpace X] [T2Space Y]
    {f : X → Y} (_hf : IsHolomorphic f)
    (_hnonconst : ¬ ∃ y₀ : Y, ∀ x, f x = y₀) (x : X) :
    0 < mapAnalyticOrderAt f x := by
  sorry

/-- Smooth maps between complex manifolds are holomorphic in the project-local sense. -/
theorem isHolomorphic_of_contMDiff
    [IsManifold 𝓘(ℂ) ω X] [IsManifold 𝓘(ℂ) ω Y]
    {f : X → Y} (_hf : ContMDiff 𝓘(ℂ) 𝓘(ℂ) (⊤ : WithTop ℕ∞) f) :
    IsHolomorphic f := by
  sorry

end Compatibility

end JacobianChallenge.HolomorphicForms
