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
  unfold IsHolomorphicAt chartLocalAt at *
  simpa [Pi.add_apply, Function.comp_def] using _hf.add _hg

/-- **Holomorphic scalar multiplication.** -/
theorem IsHolomorphicAt.smul
    {f : X → ℂ} {p : X} (c : ℂ) (_hf : IsHolomorphicAt f p) :
  IsHolomorphicAt (c • f) p := by
  unfold IsHolomorphicAt chartLocalAt at *
  simpa [Pi.smul_apply, Function.comp_def] using (_hf.const_smul (c := c))

/-- **Holomorphic finite sum.** -/
theorem IsHolomorphicAt.sum {ι : Type*} {s : Finset ι} {f : ι → X → ℂ} {p : X}
    (_hf : ∀ i ∈ s, IsHolomorphicAt (f i) p) :
    IsHolomorphicAt (fun x => Finset.sum s (fun i => f i x)) p := by
  classical
  revert _hf
  refine Finset.induction_on s ?_ ?_
  · intro _hf
    change IsHolomorphicAt (fun _ : X => (0 : ℂ)) p
    unfold IsHolomorphicAt chartLocalAt
    simpa using (analyticAt_const :
      AnalyticAt ℂ (fun _ : ℂ => chartAt ℂ (0 : ℂ) (0 : ℂ)) (chartAt ℂ p p))
  · intro a s ha ih hfs
    simpa [Finset.sum_insert, ha] using
      IsHolomorphicAt.add (hfs a (Finset.mem_insert_self a s))
        (ih fun i hi => hfs i (Finset.mem_insert_of_mem hi))

/-- **Holomorphic linear combination.** -/
theorem IsHolomorphicAt.sum_smul {ι : Type*} {s : Finset ι} {f : ι → X → ℂ} {c : ι → ℂ} {p : X}
    (_hf : ∀ i ∈ s, IsHolomorphicAt (f i) p) :
    IsHolomorphicAt (fun x => Finset.sum s (fun i => c i • f i x)) p :=
  IsHolomorphicAt.sum (fun i hi => IsHolomorphicAt.smul (c i) (_hf i hi))

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
  have hfp : f p = g p := _hfg.self_of_nhds
  unfold IsHolomorphicAt at *
  refine _hf.congr ?_
  have hsymm :
      Tendsto (fun z => (chartAt ℂ p).symm z) (𝓝 (chartAt ℂ p p)) (𝓝 p) :=
    by
      have hcont := (chartAt ℂ p).continuousAt_symm
        ((chartAt ℂ p).map_source (mem_chart_source ℂ p))
      change Tendsto (fun z => (chartAt ℂ p).symm z) (𝓝 (chartAt ℂ p p))
        (𝓝 ((chartAt ℂ p).symm (chartAt ℂ p p))) at hcont
      simpa [(chartAt ℂ p).left_inv (mem_chart_source ℂ p)] using hcont
  have hfg_chart :
      ∀ᶠ z in 𝓝 (chartAt ℂ p p), f ((chartAt ℂ p).symm z) = g ((chartAt ℂ p).symm z) :=
    hsymm.eventually _hfg
  filter_upwards [hfg_chart] with z hz
  simp [chartLocalAt, Function.comp_def, hfp, hz]


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
  (ContinuousLinearMap.toSpanSingletonCLE (𝕜 := ℂ) (E := ℂ)).symm

/-- **Plan leaf 15 (NEW).** CotangentModelFiber ℂ is a manifold over ℂ. -/
noncomputable instance instChartedSpaceCotangentModelFiber :
    ChartedSpace ℂ (CotangentModelFiber ℂ) :=
  cotangentFiberIso.toHomeomorph.toOpenPartialHomeomorph.singletonChartedSpace
    (by simp [Homeomorph.toOpenPartialHomeomorph])

noncomputable instance instIsManifoldCotangentModelFiber :
    IsManifold 𝓘(ℂ, ℂ) ⊤ (CotangentModelFiber ℂ) :=
  cotangentFiberIso.toHomeomorph.toOpenPartialHomeomorph.isManifold_singleton
    (by simp [Homeomorph.toOpenPartialHomeomorph])

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
  have hg : AnalyticAt ℂ (chartAt ℂ q ∘ e.symm) (e q) :=
    transition_analyticAt e he hq
  have hgep : (chartAt ℂ q ∘ e.symm) (e q) = chartAt ℂ q q := by
    simp [Function.comp_apply, e.left_inv hq]
  have hg' : AnalyticAt ℂ (e ∘ (chartAt ℂ q).symm) (chartAt ℂ q q) :=
    analyticAt_transition_of_mem_maximalAtlas
      (IsManifold.chart_mem_maximalAtlas q) he (mem_chart_source ℂ q) hq
  have hid : (e ∘ (chartAt ℂ q).symm) ∘ (chartAt ℂ q ∘ e.symm) =ᶠ[𝓝 (e q)] id := by
    have hmem : e.target ∩ e.symm ⁻¹' (chartAt ℂ q).source ∈ 𝓝 (e q) :=
      target_inter_preimage_mem_nhds e hq
    filter_upwards [hmem] with y hy
    obtain ⟨hy₁, hy₂⟩ := hy
    show e ((chartAt ℂ q).symm ((chartAt ℂ q) (e.symm y))) = y
    rw [(chartAt ℂ q).left_inv hy₂, e.right_inv hy₁]
  have hg_d : HasDerivAt (chartAt ℂ q ∘ e.symm)
      (deriv (chartAt ℂ q ∘ e.symm) (e q)) (e q) :=
    hg.differentiableAt.hasDerivAt
  have hg'_d : HasDerivAt (e ∘ (chartAt ℂ q).symm)
      (deriv (e ∘ (chartAt ℂ q).symm) (chartAt ℂ q q)) (chartAt ℂ q q) :=
    hg'.differentiableAt.hasDerivAt
  have hcomp : HasDerivAt ((e ∘ (chartAt ℂ q).symm) ∘ (chartAt ℂ q ∘ e.symm))
      (deriv (e ∘ (chartAt ℂ q).symm) (chartAt ℂ q q) *
        deriv (chartAt ℂ q ∘ e.symm) (e q)) (e q) :=
    HasDerivAt.comp_of_eq (e q) hg'_d hg_d hgep.symm
  have hcomp1 : HasDerivAt ((e ∘ (chartAt ℂ q).symm) ∘ (chartAt ℂ q ∘ e.symm))
      (1 : ℂ) (e q) :=
    (hasDerivAt_id (e q)).congr_of_eventuallyEq hid
  have hprod :
      deriv (e ∘ (chartAt ℂ q).symm) (chartAt ℂ q q) *
        deriv (chartAt ℂ q ∘ e.symm) (e q) = 1 :=
    hcomp.unique hcomp1
  intro h
  rw [h, zero_mul] at hprod
  exact zero_ne_one hprod

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
  let z₀ := chartAt ℂ x x
  let F : ℂ → ℂ := fun z => chartLocalAt f x z - chartLocalAt f x z₀
  have hF_an : AnalyticAt ℂ F z₀ := (_hf.holomorphicAt x).sub analyticAt_const
  have hF_zero : F z₀ = 0 := by
    simp [F, z₀]
  have horder_ne_zero : analyticOrderAt F z₀ ≠ 0 := by
    intro h0
    exact (hF_an.analyticOrderAt_eq_zero.mp h0) hF_zero
  have horder_ne_top : analyticOrderAt F z₀ ≠ ⊤ := by
    intro htop
    have h_const_chart : ∀ᶠ z in 𝓝 z₀, chartLocalAt f x z = chartLocalAt f x z₀ := by
      have hzero : ∀ᶠ z in 𝓝 z₀, F z = 0 := analyticOrderAt_eq_top.mp htop
      simpa [F, sub_eq_zero] using hzero
    have h_source : ∀ᶠ x' in 𝓝 x, x' ∈ (chartAt ℂ x).source :=
      (chartAt ℂ x).open_source.mem_nhds (mem_chart_source ℂ x)
    have h_chart_tendsto :
        Tendsto (fun x' => chartAt ℂ x x') (𝓝 x) (𝓝 z₀) :=
      (chartAt ℂ x).continuousAt (mem_chart_source ℂ x)
    have h_chart_eq : ∀ᶠ x' in 𝓝 x,
        x' ∈ (chartAt ℂ x).source ∧
          chartLocalAt f x (chartAt ℂ x x') = chartLocalAt f x z₀ :=
      Filter.Eventually.and h_source (h_chart_tendsto.eventually h_const_chart)
    have h_target : ∀ᶠ x' in 𝓝 x, f x' ∈ (chartAt ℂ (f x)).source :=
      _hf.continuous.continuousAt.preimage_mem_nhds
        ((chartAt ℂ (f x)).open_source.mem_nhds (mem_chart_source ℂ (f x)))
    have h_local : ∀ᶠ x' in 𝓝 x, f x' = f x := by
      filter_upwards [h_chart_eq, h_target] with x' hx' hfx'
      have hchart : chartAt ℂ (f x) (f x') = chartAt ℂ (f x) (f x) := by
        simpa [chartLocalAt, Function.comp_def, z₀,
          (chartAt ℂ x).left_inv hx'.1] using hx'.2
      exact (chartAt ℂ (f x)).injOn hfx' (mem_chart_source ℂ (f x)) hchart
    exact _hnonconst ⟨f x, fun x' => _hf.eq_const_of_eventuallyEq h_local x'⟩
  unfold mapAnalyticOrderAt analyticOrderNatAt
  change 0 < (analyticOrderAt F z₀).toNat
  exact Nat.pos_of_ne_zero fun hnat0 => by
    have hcast : (analyticOrderAt F z₀).toNat = analyticOrderAt F z₀ :=
      ENat.coe_toNat horder_ne_top
    have horder_zero : analyticOrderAt F z₀ = 0 := by
      rw [← hcast, hnat0]
      simp
    exact horder_ne_zero horder_zero

/-- Smooth maps between complex manifolds are holomorphic in the project-local sense. -/
theorem isHolomorphic_of_contMDiff
    [IsManifold 𝓘(ℂ) ω X] [IsManifold 𝓘(ℂ) ω Y]
    {f : X → Y} (_hf : ContMDiff 𝓘(ℂ) 𝓘(ℂ) (⊤ : WithTop ℕ∞) f) :
    IsHolomorphic f := by
  sorry

end Compatibility

end JacobianChallenge.HolomorphicForms
