import Jacobian.HolomorphicForms.VanishingOrder
import Jacobian.HolomorphicForms.AnalyticLocalMapping
import Jacobian.HolomorphicForms.CotangentBundle
import Mathlib.Analysis.Analytic.Order
import Mathlib.Geometry.Manifold.ContMDiff.Defs
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.Analytic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Topology.Connected.Clopen

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

/-- **Holomorphic composition.**

The continuity hypothesis supplies the chart-source locality needed to
rewrite the intermediate chart roundtrip. -/
theorem IsHolomorphicAt.comp
    {f : X → Y} {g : Y → Z} {p : X}
    (_hg : IsHolomorphicAt g (f p)) (_hf : IsHolomorphicAt f p)
    (hf_cont : ContinuousAt f p) :
    IsHolomorphicAt (g ∘ f) p := by
  unfold IsHolomorphicAt at *
  have hfp :
      chartLocalAt f p (chartAt ℂ p p) = chartAt ℂ (f p) (f p) := by
    unfold chartLocalAt
    have : (chartAt ℂ p).symm (chartAt ℂ p p) = p :=
      (chartAt ℂ p).left_inv (mem_chart_source ℂ p)
    simp [Function.comp_def, this]
  have hcomp :
      AnalyticAt ℂ (chartLocalAt g (f p) ∘ chartLocalAt f p)
        (chartAt ℂ p p) :=
    _hg.comp_of_eq _hf hfp
  refine hcomp.congr ?_
  have hsymm :
      Tendsto (fun z => (chartAt ℂ p).symm z) (𝓝 (chartAt ℂ p p)) (𝓝 p) :=
    by
      have hcont := (chartAt ℂ p).continuousAt_symm
        ((chartAt ℂ p).map_source (mem_chart_source ℂ p))
      change Tendsto (fun z => (chartAt ℂ p).symm z) (𝓝 (chartAt ℂ p p))
        (𝓝 ((chartAt ℂ p).symm (chartAt ℂ p p))) at hcont
      simpa [(chartAt ℂ p).left_inv (mem_chart_source ℂ p)] using hcont
  have hsrc_nhds :
      (chartAt ℂ (f p)).source ∈ 𝓝 (f p) :=
    (chartAt ℂ (f p)).open_source.mem_nhds (mem_chart_source ℂ (f p))
  have hsrc :
      ∀ᶠ z in 𝓝 (chartAt ℂ p p),
        f ((chartAt ℂ p).symm z) ∈ (chartAt ℂ (f p)).source :=
    hsymm.eventually (hf_cont hsrc_nhds)
  filter_upwards [hsrc] with z hz
  simp [chartLocalAt, Function.comp_def, (chartAt ℂ (f p)).left_inv hz]

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

omit [IsManifold 𝓘(ℂ) ω X] [IsManifold 𝓘(ℂ) ω Y] in
/-- **Plan leaf 11 (NEW).** The local inverse is holomorphic. -/
theorem IsHolomorphicAt.localInverse_isHolomorphicAt
    {f : X → Y} {p : X} (hf : IsHolomorphicAt f p)
    (hderiv : deriv (chartLocalAt f p) (chartAt ℂ p p) ≠ 0) :
    IsHolomorphicAt (hf.localInverse hderiv) (f p) := by
  unfold IsHolomorphicAt chartLocalAt IsHolomorphicAt.localInverse
  let r : ℂ → ℂ :=
    hf.hasStrictDerivAt.localInverse (chartLocalAt f p)
      (deriv (chartLocalAt f p) (chartAt ℂ p p)) (chartAt ℂ p p) hderiv
  have hli_r :
      r (chartLocalAt f p (chartAt ℂ p p)) = chartAt ℂ p p := by
    dsimp [r]
    exact (HasStrictDerivAt.eventually_left_inverse
      (f := chartLocalAt f p)
      (f' := (deriv (chartLocalAt f p) (chartAt ℂ p p) : ℂ))
      (a := chartAt ℂ p p) (hf := hf.hasStrictDerivAt)
      (hf' := hderiv)).self_of_nhds
  have h_inv_apply :
      (chartAt ℂ p).symm
          (hf.hasStrictDerivAt.localInverse (chartLocalAt f p)
            (deriv (chartLocalAt f p) (chartAt ℂ p p)) (chartAt ℂ p p) hderiv
            (chartAt ℂ (f p) (f p))) = p := by
    change (chartAt ℂ p).symm (r (chartAt ℂ (f p) (f p))) = p
    have harg : chartAt ℂ (f p) (f p) = chartLocalAt f p (chartAt ℂ p p) := by
      simp [chartLocalAt]
    rw [harg, hli_r]
    exact (chartAt ℂ p).left_inv (mem_chart_source ℂ p)
  rw [h_inv_apply]
  have hr : AnalyticAt ℂ r (chartLocalAt f p (chartAt ℂ p p)) :=
    hf.analyticAt_localInverse hderiv
  have hfp :
      chartLocalAt f p (chartAt ℂ p p) = chartAt ℂ (f p) (f p) := by
    simp [chartLocalAt]
  rw [hfp] at hr
  refine hr.congr ?_
  have hsrc :
      ∀ᶠ z in 𝓝 (chartAt ℂ (f p) (f p)),
        z ∈ (chartAt ℂ (f p)).target :=
    chart_target_mem_nhds ℂ (f p)
  have hsrc_p :
      ∀ᶠ z in 𝓝 (chartAt ℂ (f p) (f p)),
        r z ∈ (chartAt ℂ p).target := by
    have hr_tendsto : Tendsto r (𝓝 (chartAt ℂ (f p) (f p))) (𝓝 (chartAt ℂ p p)) := by
      have hr_cont := hr.continuousAt
      have hli :
          r (chartAt ℂ (f p) (f p)) = chartAt ℂ p p := by
        rw [← hfp]
        exact hli_r
      simpa [ContinuousAt, hli] using hr_cont
    exact hr_tendsto.eventually (chart_target_mem_nhds ℂ p)
  filter_upwards [hsrc, hsrc_p] with z hzY hzX
  change r z =
    (chartAt ℂ p)
      ((chartAt ℂ p).symm
        (r ((chartAt ℂ (f p)) ((chartAt ℂ (f p)).symm z))))
  have hzYeq : (chartAt ℂ (f p)) ((chartAt ℂ (f p)).symm z) = z :=
    (chartAt ℂ (f p)).right_inv hzY
  rw [hzYeq]
  exact ((chartAt ℂ p).right_inv hzX).symm

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
    (hf_an : IsHolomorphicAt f_ p) (hf_cont : ContinuousAt f_ p)
    (he₁ : e₁ ∈ IsManifold.maximalAtlas 𝓘(ℂ) ω X) (hp₁ : p ∈ e₁.source)
    (he₂ : e₂ ∈ IsManifold.maximalAtlas 𝓘(ℂ) ω Y) (hp₂ : f_ p ∈ e₂.source) :
    analyticOrderNatAt (fun t => e₂ (f_ (e₁.symm t)) - e₂ (f_ p)) (e₁ p) =
    mapAnalyticOrderAt f_ p := by
  let z₀ := chartAt ℂ p p
  let y₀ := chartAt ℂ (f_ p) (f_ p)
  let F : ℂ → ℂ := chartLocalAt f_ p
  let G : ℂ → ℂ := fun z => e₂ (f_ ((chartAt ℂ p).symm z)) - e₂ (f_ p)
  let φ : ℂ → ℂ := chartAt ℂ p ∘ e₁.symm
  let β : ℂ → ℂ := e₂ ∘ (chartAt ℂ (f_ p)).symm

  have hφ_an : AnalyticAt ℂ φ (e₁ p) :=
    transition_analyticAt e₁ he₁ hp₁
  have hφ_der : deriv φ (e₁ p) ≠ 0 :=
    transition_deriv_ne_zero e₁ he₁ hp₁
  have hφ_at : φ (e₁ p) = z₀ := by
    simp [φ, z₀, Function.comp_apply, e₁.left_inv hp₁]
  have hpre_congr :
      (fun t => e₂ (f_ (e₁.symm t)) - e₂ (f_ p)) =ᶠ[𝓝 (e₁ p)] G ∘ φ := by
    have hmem : e₁.target ∩ e₁.symm ⁻¹' (chartAt ℂ p).source ∈ 𝓝 (e₁ p) :=
      target_inter_preimage_mem_nhds e₁ hp₁
    filter_upwards [hmem] with t ht
    simp [G, φ, Function.comp_def, (chartAt ℂ p).left_inv ht.2]
  have hpre :
      analyticOrderAt (fun t => e₂ (f_ (e₁.symm t)) - e₂ (f_ p)) (e₁ p) =
        analyticOrderAt G z₀ := by
    rw [analyticOrderAt_congr hpre_congr,
      analyticOrderAt_comp_of_deriv_ne_zero hφ_an hφ_der, hφ_at]

  have hF_at : F z₀ = y₀ := by
    simp [F, z₀, y₀, chartLocalAt, Function.comp_def,
      (chartAt ℂ p).left_inv (mem_chart_source ℂ p)]
  have hβ_an : AnalyticAt ℂ β y₀ := by
    simpa [β, y₀] using
      (analyticAt_transition_of_mem_maximalAtlas
        (IsManifold.chart_mem_maximalAtlas (f_ p)) he₂
        (mem_chart_source ℂ (f_ p)) hp₂)
  have hβ_der : deriv β y₀ ≠ 0 := by
    simpa [β, y₀] using
      chartAt_symm_transition_deriv_ne_zero e₂ he₂ hp₂
  have hβ_order :
      analyticOrderAt (fun y => β y - β y₀) y₀ = 1 :=
    hβ_an.analyticOrderAt_sub_eq_one_of_deriv_ne_zero hβ_der
  have hG_congr :
      G =ᶠ[𝓝 z₀] (fun z => β (F z) - β y₀) := by
    have hsymm :
        Tendsto (fun z => (chartAt ℂ p).symm z) (𝓝 z₀) (𝓝 p) := by
      have hcont := (chartAt ℂ p).continuousAt_symm
        ((chartAt ℂ p).map_source (mem_chart_source ℂ p))
      change Tendsto (fun z => (chartAt ℂ p).symm z) (𝓝 (chartAt ℂ p p))
        (𝓝 ((chartAt ℂ p).symm (chartAt ℂ p p))) at hcont
      simpa [z₀, (chartAt ℂ p).left_inv (mem_chart_source ℂ p)] using hcont
    have hsrc_nhds :
        (chartAt ℂ (f_ p)).source ∈ 𝓝 (f_ p) :=
      (chartAt ℂ (f_ p)).open_source.mem_nhds (mem_chart_source ℂ (f_ p))
    have hsrc :
        ∀ᶠ z in 𝓝 z₀,
          f_ ((chartAt ℂ p).symm z) ∈ (chartAt ℂ (f_ p)).source :=
      hsymm.eventually (hf_cont hsrc_nhds)
    filter_upwards [hsrc] with z hz
    simp [G, F, β, y₀, chartLocalAt, Function.comp_def,
      (chartAt ℂ (f_ p)).left_inv hz]
  have hpost :
      analyticOrderAt G z₀ = analyticOrderAt (fun z => F z - y₀) z₀ := by
    rw [analyticOrderAt_congr hG_congr]
    have hβ_sub_an : AnalyticAt ℂ (fun y => β y - β y₀) y₀ := by
      simpa using hβ_an.sub analyticAt_const
    have hF_an : AnalyticAt ℂ F z₀ := by
      simpa [F, z₀] using hf_an
    have hβ_sub_an_F : AnalyticAt ℂ (fun y => β y - β y₀) (F z₀) := by
      simpa [hF_at] using hβ_sub_an
    have hcomp :
        analyticOrderAt ((fun y => β y - β y₀) ∘ F) z₀ =
          analyticOrderAt (fun y => β y - β y₀) (F z₀) *
            analyticOrderAt (fun z => F z - F z₀) z₀ :=
      hβ_sub_an_F.analyticOrderAt_comp hF_an
    simpa [Function.comp_def, hF_at, hβ_order] using hcomp
  unfold mapAnalyticOrderAt analyticOrderNatAt
  simp
  exact congrArg ENat.toNat (hpre.trans hpost)

/-- Backwards-compatible name for the chart-independence theorem. -/
theorem mapAnalyticOrderAt_eq_of_mem_maximalAtlas
    {f_ : X → Y} (_hf : IsHolomorphic f_) {p : X}
    {e₁ : OpenPartialHomeomorph X ℂ}
    (he₁ : e₁ ∈ IsManifold.maximalAtlas 𝓘(ℂ) ω X) (hp₁ : p ∈ e₁.source)
    {e₂ : OpenPartialHomeomorph Y ℂ}
    (he₂ : e₂ ∈ IsManifold.maximalAtlas 𝓘(ℂ) ω Y) (hp₂ : f_ p ∈ e₂.source) :
    analyticOrderNatAt (fun t => e₂ (f_ (e₁.symm t)) - e₂ (f_ p)) (e₁ p) =
    mapAnalyticOrderAt f_ p :=
  mapAnalyticOrderAt_congr_of_maximalAtlas (_hf.holomorphicAt p)
    _hf.continuous.continuousAt he₁ hp₁ he₂ hp₂

end ChartIndependence

section Compatibility

/-- Chart-local analyticity supplied by manifold-level complex smoothness. -/
theorem IsHolomorphicAt.of_contMDiff
    [IsManifold 𝓘(ℂ) ω X] [IsManifold 𝓘(ℂ) ω Y]
    {f : X → Y} (hf : ContMDiff 𝓘(ℂ) 𝓘(ℂ) (⊤ : WithTop ℕ∞) f) (p : X) :
    IsHolomorphicAt f p := by
  unfold IsHolomorphicAt chartLocalAt
  have hcmd : ContMDiffAt 𝓘(ℂ) 𝓘(ℂ) (⊤ : WithTop ℕ∞) f p :=
    hf.contMDiffAt
  have hchart :=
    (contMDiffAt_iff_of_mem_source (I := 𝓘(ℂ)) (I' := 𝓘(ℂ))
      (x := p) (y := f p) (f := f) (n := (⊤ : WithTop ℕ∞))
      (mem_chart_source ℂ p) (mem_chart_source ℂ (f p))).mp hcmd
  have hcd : ContDiffAt ℂ (⊤ : WithTop ℕ∞)
      (chartAt ℂ (f p) ∘ f ∘ (chartAt ℂ p).symm) (chartAt ℂ p p) := by
    simpa [contDiffWithinAt_univ, ModelWithCorners.range_eq_target] using hchart.2
  exact hcd.analyticAt

/-- Local constancy of a holomorphic map on a preconnected source forces global constancy. -/
theorem IsHolomorphic.eq_const_of_eventuallyEq
    [PreconnectedSpace X] [T2Space Y]
    {f : X → Y} (_hf : IsHolomorphic f) {y₀ : Y} {x₁ : X}
    (_h_local : ∀ᶠ x in 𝓝 x₁, f x = y₀) :
    ∀ x, f x = y₀ := by
  let A : Set X := {x | ∀ᶠ z in 𝓝 x, f z = y₀}
  have hA_open : IsOpen A := by
    simpa [A] using (isOpen_setOf_eventually_nhds (X := X) (p := fun z => f z = y₀))
  have hA_sub : A ⊆ {x | f x = y₀} := by
    intro x hxA
    by_contra hne
    have hne' : ∀ᶠ z in 𝓝 x, f z ≠ y₀ :=
      _hf.continuous.continuousAt.eventually_ne hne
    rcases (hxA.and hne').exists with ⟨z, hz, hz_ne⟩
    exact hz_ne hz
  have hA_closed : IsClosed A := by
    rw [isClosed_iff_clusterPt]
    intro x hxcl
    by_cases hxA : x ∈ A
    · exact hxA
    have hfx : f x = y₀ := by
      by_contra hne
      have hne' : ∀ᶠ z in 𝓝 x, f z ≠ y₀ :=
        _hf.continuous.continuousAt.eventually_ne hne
      have hfreqA : ∃ᶠ z in 𝓝 x, z ∈ A :=
        clusterPt_principal_iff_frequently.mp hxcl
      rcases (hfreqA.and_eventually hne').exists with ⟨z, hzA, hz_ne⟩
      exact hz_ne (hA_sub hzA)
    let z₀ := chartAt ℂ x x
    let c₀ := chartAt ℂ (f x) (f x)
    have hconst_an : AnalyticAt ℂ (fun _ : ℂ => c₀) z₀ := analyticAt_const
    rcases (_hf.holomorphicAt x).eventually_eq_or_eventually_ne hconst_an with h_eq | h_ne
    · have hsrc : ∀ᶠ x' in 𝓝 x, x' ∈ (chartAt ℂ x).source :=
        (chartAt ℂ x).open_source.mem_nhds (mem_chart_source ℂ x)
      have hchart_tendsto :
          Tendsto (fun x' => chartAt ℂ x x') (𝓝 x) (𝓝 z₀) :=
        (chartAt ℂ x).continuousAt (mem_chart_source ℂ x)
      have hchart_eq :
          ∀ᶠ x' in 𝓝 x, chartLocalAt f x (chartAt ℂ x x') = c₀ :=
        hchart_tendsto.eventually h_eq
      have htgt : ∀ᶠ x' in 𝓝 x, f x' ∈ (chartAt ℂ (f x)).source :=
        _hf.continuous.continuousAt.preimage_mem_nhds
          ((chartAt ℂ (f x)).open_source.mem_nhds (mem_chart_source ℂ (f x)))
      filter_upwards [hsrc, hchart_eq, htgt] with x' hxsrc hxchart hxtgt
      have hchart : chartAt ℂ (f x) (f x') = chartAt ℂ (f x) (f x) := by
        simpa [chartLocalAt, Function.comp_def, z₀, c₀,
          (chartAt ℂ x).left_inv hxsrc] using hxchart
      have hfx' : f x' = f x :=
        (chartAt ℂ (f x)).injOn hxtgt (mem_chart_source ℂ (f x)) hchart
      exact hfx'.trans hfx
    · have hfreq_eq :
          ∃ᶠ z in 𝓝[≠] z₀, chartLocalAt f x z = c₀ := by
        rw [frequently_nhdsWithin_iff, frequently_nhds_iff]
        intro V hzV hVopen
        have hV_mem : V ∈ 𝓝 z₀ := hVopen.mem_nhds hzV
        have hpre_mem : (chartAt ℂ x ⁻¹' V) ∈ 𝓝 x :=
          ((chartAt ℂ x).continuousAt (mem_chart_source ℂ x)).preimage_mem_nhds hV_mem
        have hsrc_mem : (chartAt ℂ x).source ∈ 𝓝 x :=
          (chartAt ℂ x).open_source.mem_nhds (mem_chart_source ℂ x)
        have hU_mem : ((chartAt ℂ x).source ∩ chartAt ℂ x ⁻¹' V) ∈ 𝓝 x :=
          inter_mem hsrc_mem hpre_mem
        rcases (clusterPt_principal_iff.mp hxcl _ hU_mem) with ⟨u, huU, huA⟩
        have hux : u ≠ x := by
          intro h
          exact hxA (by simpa [h] using huA)
        have hfu : f u = y₀ := hA_sub huA
        have hfu_fx : f u = f x := hfu.trans hfx.symm
        refine ⟨chartAt ℂ x u, huU.2, ?_, ?_⟩
        · simp [chartLocalAt, Function.comp_def, c₀, hfu_fx,
            (chartAt ℂ x).left_inv huU.1]
        · intro hz
          exact hux ((chartAt ℂ x).injOn huU.1 (mem_chart_source ℂ x) hz)
      rcases (hfreq_eq.and_eventually h_ne).exists with ⟨z, hz_eq, hz_ne⟩
      exact False.elim (hz_ne hz_eq)
  have hA_univ : A = Set.univ :=
    (IsClopen.eq_univ ⟨hA_closed, hA_open⟩ ⟨x₁, _h_local⟩)
  intro x
  exact hA_sub (by simp [hA_univ, A])

/-- Finite fibres of a nonconstant holomorphic map on a compact source. -/
theorem isHolomorphic_finite_fiber
    [CompactSpace X] [PreconnectedSpace X] [T2Space Y]
    {f : X → Y} (_hf : IsHolomorphic f)
    (_hnonconst : ¬ ∃ y₀ : Y, ∀ x, f x = y₀) (y : Y) :
    (f ⁻¹' {y}).Finite := by
  have hfiber_discrete : IsDiscrete (f ⁻¹' {y}) := by
    rw [isDiscrete_iff_discreteTopology, discreteTopology_subtype_iff]
    intro x hx
    apply Filter.not_neBot.mp
    intro hne
    have hfreq_fiber_within :
        ∃ᶠ u in 𝓝[≠] x, u ∈ f ⁻¹' {y} := by
      exact (Filter.frequently_iff_neBot (l := 𝓝[≠] x)
        (p := fun u : X => u ∈ f ⁻¹' {y})).2 hne
    have hfreq_fiber :
        ∃ᶠ u in 𝓝 x, u ∈ f ⁻¹' {y} ∧ u ≠ x := by
      simpa using (frequently_nhdsWithin_iff.mp hfreq_fiber_within)
    let z₀ := chartAt ℂ x x
    let c₀ := chartAt ℂ (f x) (f x)
    have hfreq_chart :
        ∃ᶠ z in 𝓝[≠] z₀, chartLocalAt f x z = c₀ := by
      rw [frequently_nhdsWithin_iff, frequently_nhds_iff]
      intro V hzV hVopen
      have hV_mem : V ∈ 𝓝 z₀ := hVopen.mem_nhds hzV
      have hpre_mem : (chartAt ℂ x ⁻¹' V) ∈ 𝓝 x :=
        ((chartAt ℂ x).continuousAt (mem_chart_source ℂ x)).preimage_mem_nhds hV_mem
      have hsrc_mem : (chartAt ℂ x).source ∈ 𝓝 x :=
        (chartAt ℂ x).open_source.mem_nhds (mem_chart_source ℂ x)
      have hnear : ((chartAt ℂ x).source ∩ chartAt ℂ x ⁻¹' V) ∈ 𝓝 x :=
        inter_mem hsrc_mem hpre_mem
      have hfreq_near :
          ∃ᶠ u in 𝓝 x, (u ∈ f ⁻¹' {y} ∧ u ≠ x) ∧
            u ∈ (chartAt ℂ x).source ∩ chartAt ℂ x ⁻¹' V :=
        hfreq_fiber.and_eventually hnear
      rcases hfreq_near.exists with ⟨u, ⟨hu_fiber, hux⟩, ⟨hu_src, huV⟩⟩
      have hfu : f u = f x := by
        have hux_y : f u = y := by simpa using hu_fiber
        have hx_y : f x = y := by simpa using hx
        exact hux_y.trans hx_y.symm
      refine ⟨chartAt ℂ x u, huV, ?_, ?_⟩
      · simp [chartLocalAt, Function.comp_def, c₀, hfu,
          (chartAt ℂ x).left_inv hu_src]
      · intro hz
        exact hux ((chartAt ℂ x).injOn hu_src (mem_chart_source ℂ x) hz)
    have heq_chart : ∀ᶠ z in 𝓝 z₀, chartLocalAt f x z = c₀ :=
      ((_hf.holomorphicAt x).frequently_eq_iff_eventually_eq analyticAt_const).mp
        (by simpa using hfreq_chart)
    have hsrc : ∀ᶠ x' in 𝓝 x, x' ∈ (chartAt ℂ x).source :=
      (chartAt ℂ x).open_source.mem_nhds (mem_chart_source ℂ x)
    have hchart_tendsto :
        Tendsto (fun x' => chartAt ℂ x x') (𝓝 x) (𝓝 z₀) :=
      (chartAt ℂ x).continuousAt (mem_chart_source ℂ x)
    have hchart_eq :
        ∀ᶠ x' in 𝓝 x, chartLocalAt f x (chartAt ℂ x x') = c₀ :=
      hchart_tendsto.eventually heq_chart
    have htgt : ∀ᶠ x' in 𝓝 x, f x' ∈ (chartAt ℂ (f x)).source :=
      _hf.continuous.continuousAt.preimage_mem_nhds
        ((chartAt ℂ (f x)).open_source.mem_nhds (mem_chart_source ℂ (f x)))
    have hlocal : ∀ᶠ x' in 𝓝 x, f x' = f x := by
      filter_upwards [hsrc, hchart_eq, htgt] with x' hxsrc hxchart hxtgt
      have hchart : chartAt ℂ (f x) (f x') = chartAt ℂ (f x) (f x) := by
        simpa [chartLocalAt, Function.comp_def, z₀, c₀,
          (chartAt ℂ x).left_inv hxsrc] using hxchart
      exact (chartAt ℂ (f x)).injOn hxtgt (mem_chart_source ℂ (f x)) hchart
    exact _hnonconst ⟨f x, fun x' => _hf.eq_const_of_eventuallyEq hlocal x'⟩
  have h_closed : IsClosed (f ⁻¹' {y}) := isClosed_singleton.preimage _hf.continuous
  exact h_closed.isCompact.finite hfiber_discrete

/-- Pairwise-disjoint open neighborhoods of a finite subset in a Hausdorff space. -/
theorem Set.Finite.exists_pairwiseDisjoint_open_nhds
    {X : Type*} [TopologicalSpace X] [T2Space X]
    {s : Set X} (hs : s.Finite) :
    ∃ U : X → Set X,
      (∀ x ∈ s, IsOpen (U x) ∧ x ∈ U x) ∧
      Set.Pairwise s (fun x y => Disjoint (U x) (U y)) := by
  obtain ⟨U, hU⟩ := Set.Finite.t2_separation hs
  exact ⟨U, fun x hx => ⟨(hU.1 x).2, (hU.1 x).1⟩, hU.2⟩

/-- Properness on a compact source: nearby fibers lie in any open set
containing the reference fiber. -/
theorem eventually_fiber_subset_of_compact_T2
    {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    [CompactSpace X] [T2Space Y]
    {f : X → Y} (hf_cont : Continuous f) {y₀ : Y} {U : Set X}
    (hU_open : IsOpen U) (hU_fibre : f ⁻¹' {y₀} ⊆ U) :
    ∀ᶠ y in 𝓝 y₀, f ⁻¹' {y} ⊆ U := by
  have h_compact : IsCompact (f '' (Uᶜ)) := by
    exact IsCompact.image (isClosed_compl_iff.mpr hU_open |>.isCompact) hf_cont
  have h_ne : y₀ ∉ f '' (Uᶜ) := by
    rintro ⟨x, hxU, rfl⟩
    exact hxU (hU_fibre rfl)
  have h_nhds : (f '' (Uᶜ))ᶜ ∈ 𝓝 y₀ :=
    h_compact.isClosed.isOpen_compl.mem_nhds h_ne
  filter_upwards [h_nhds] with y hy x hx
  exact Classical.not_not.1 fun hxU => hy ⟨x, hxU, hx⟩

/-- Local constancy of a complex-smooth map on a preconnected source
forces global constancy.  This is the `ContMDiff` variant of
`IsHolomorphic.eq_const_of_eventuallyEq`, used while constructing the
full `IsHolomorphic` structure. -/
theorem eq_const_of_eventuallyEq_of_contMDiff
    [IsManifold 𝓘(ℂ) ω X] [IsManifold 𝓘(ℂ) ω Y]
    [PreconnectedSpace X] [T2Space Y]
    {f : X → Y} (hf : ContMDiff 𝓘(ℂ) 𝓘(ℂ) (⊤ : WithTop ℕ∞) f)
    {y₀ : Y} {x₁ : X} (h_local : ∀ᶠ x in 𝓝 x₁, f x = y₀) :
    ∀ x, f x = y₀ := by
  let A : Set X := {x | ∀ᶠ z in 𝓝 x, f z = y₀}
  have hA_open : IsOpen A := by
    simpa [A] using (isOpen_setOf_eventually_nhds (X := X) (p := fun z => f z = y₀))
  have hA_sub : A ⊆ {x | f x = y₀} := by
    intro x hxA
    by_contra hne
    have hne' : ∀ᶠ z in 𝓝 x, f z ≠ y₀ :=
      hf.continuous.continuousAt.eventually_ne hne
    rcases (hxA.and hne').exists with ⟨z, hz, hz_ne⟩
    exact hz_ne hz
  have hA_closed : IsClosed A := by
    rw [isClosed_iff_clusterPt]
    intro x hxcl
    by_cases hxA : x ∈ A
    · exact hxA
    have hfx : f x = y₀ := by
      by_contra hne
      have hne' : ∀ᶠ z in 𝓝 x, f z ≠ y₀ :=
        hf.continuous.continuousAt.eventually_ne hne
      have hfreqA : ∃ᶠ z in 𝓝 x, z ∈ A :=
        clusterPt_principal_iff_frequently.mp hxcl
      rcases (hfreqA.and_eventually hne').exists with ⟨z, hzA, hz_ne⟩
      exact hz_ne (hA_sub hzA)
    let z₀ := chartAt ℂ x x
    let c₀ := chartAt ℂ (f x) (f x)
    have hconst_an : AnalyticAt ℂ (fun _ : ℂ => c₀) z₀ := analyticAt_const
    rcases (IsHolomorphicAt.of_contMDiff hf x).eventually_eq_or_eventually_ne hconst_an with h_eq | h_ne
    · have hsrc : ∀ᶠ x' in 𝓝 x, x' ∈ (chartAt ℂ x).source :=
        (chartAt ℂ x).open_source.mem_nhds (mem_chart_source ℂ x)
      have hchart_tendsto :
          Tendsto (fun x' => chartAt ℂ x x') (𝓝 x) (𝓝 z₀) :=
        (chartAt ℂ x).continuousAt (mem_chart_source ℂ x)
      have hchart_eq :
          ∀ᶠ x' in 𝓝 x, chartLocalAt f x (chartAt ℂ x x') = c₀ :=
        hchart_tendsto.eventually h_eq
      have htgt : ∀ᶠ x' in 𝓝 x, f x' ∈ (chartAt ℂ (f x)).source :=
        hf.continuous.continuousAt.preimage_mem_nhds
          ((chartAt ℂ (f x)).open_source.mem_nhds (mem_chart_source ℂ (f x)))
      filter_upwards [hsrc, hchart_eq, htgt] with x' hxsrc hxchart hxtgt
      have hchart : chartAt ℂ (f x) (f x') = chartAt ℂ (f x) (f x) := by
        simpa [chartLocalAt, Function.comp_def, z₀, c₀,
          (chartAt ℂ x).left_inv hxsrc] using hxchart
      have hfx' : f x' = f x :=
        (chartAt ℂ (f x)).injOn hxtgt (mem_chart_source ℂ (f x)) hchart
      exact hfx'.trans hfx
    · have hfreq_eq :
          ∃ᶠ z in 𝓝[≠] z₀, chartLocalAt f x z = c₀ := by
        rw [frequently_nhdsWithin_iff, frequently_nhds_iff]
        intro V hzV hVopen
        have hV_mem : V ∈ 𝓝 z₀ := hVopen.mem_nhds hzV
        have hpre_mem : (chartAt ℂ x ⁻¹' V) ∈ 𝓝 x :=
          ((chartAt ℂ x).continuousAt (mem_chart_source ℂ x)).preimage_mem_nhds hV_mem
        have hsrc_mem : (chartAt ℂ x).source ∈ 𝓝 x :=
          (chartAt ℂ x).open_source.mem_nhds (mem_chart_source ℂ x)
        have hU_mem : ((chartAt ℂ x).source ∩ chartAt ℂ x ⁻¹' V) ∈ 𝓝 x :=
          inter_mem hsrc_mem hpre_mem
        rcases (clusterPt_principal_iff.mp hxcl _ hU_mem) with ⟨u, huU, huA⟩
        have hux : u ≠ x := by
          intro h
          exact hxA (by simpa [h] using huA)
        have hfu : f u = y₀ := hA_sub huA
        have hfu_fx : f u = f x := hfu.trans hfx.symm
        refine ⟨chartAt ℂ x u, huU.2, ?_, ?_⟩
        · simp [chartLocalAt, Function.comp_def, c₀, hfu_fx,
            (chartAt ℂ x).left_inv huU.1]
        · intro hz
          exact hux ((chartAt ℂ x).injOn huU.1 (mem_chart_source ℂ x) hz)
      rcases (hfreq_eq.and_eventually h_ne).exists with ⟨z, hz_eq, hz_ne⟩
      exact False.elim (hz_ne hz_eq)
  have hA_univ : A = Set.univ :=
    (IsClopen.eq_univ ⟨hA_closed, hA_open⟩ ⟨x₁, h_local⟩)
  intro x
  exact hA_sub (by simp [hA_univ, A])

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

/-- Positivity of the local analytic order for a nonconstant complex-smooth map,
without assuming an already completed `IsHolomorphic` structure. -/
theorem mapAnalyticOrderAt_pos_of_contMDiff
    [IsManifold 𝓘(ℂ) ω X] [IsManifold 𝓘(ℂ) ω Y]
    [PreconnectedSpace X] [T2Space Y]
    {f : X → Y} (hf : ContMDiff 𝓘(ℂ) 𝓘(ℂ) (⊤ : WithTop ℕ∞) f)
    (hnonconst : ¬ ∃ y₀ : Y, ∀ x, f x = y₀) (x : X) :
    0 < mapAnalyticOrderAt f x := by
  let z₀ := chartAt ℂ x x
  let F : ℂ → ℂ := fun z => chartLocalAt f x z - chartLocalAt f x z₀
  have hF_an : AnalyticAt ℂ F z₀ :=
    (IsHolomorphicAt.of_contMDiff hf x).sub analyticAt_const
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
      hf.continuous.continuousAt.preimage_mem_nhds
        ((chartAt ℂ (f x)).open_source.mem_nhds (mem_chart_source ℂ (f x)))
    have h_local : ∀ᶠ x' in 𝓝 x, f x' = f x := by
      filter_upwards [h_chart_eq, h_target] with x' hx' hfx'
      have hchart : chartAt ℂ (f x) (f x') = chartAt ℂ (f x) (f x) := by
        simpa [chartLocalAt, Function.comp_def, z₀,
          (chartAt ℂ x).left_inv hx'.1] using hx'.2
      exact (chartAt ℂ (f x)).injOn hfx' (mem_chart_source ℂ (f x)) hchart
    exact hnonconst ⟨f x, fun x' =>
      eq_const_of_eventuallyEq_of_contMDiff hf h_local x'⟩
  unfold mapAnalyticOrderAt analyticOrderNatAt
  change 0 < (analyticOrderAt F z₀).toNat
  exact Nat.pos_of_ne_zero fun hnat0 => by
    have hcast : (analyticOrderAt F z₀).toNat = analyticOrderAt F z₀ :=
      ENat.coe_toNat horder_ne_top
    have horder_zero : analyticOrderAt F z₀ = 0 := by
      rw [← hcast, hnat0]
      simp
    exact horder_ne_zero horder_zero

/-- Local `k`-fold ramification for a nonconstant complex-smooth map, with
the source neighborhood chosen inside a prescribed open neighborhood. -/
theorem local_kfold_ramified_of_contMDiff_within
    [IsManifold 𝓘(ℂ) ω X] [IsManifold 𝓘(ℂ) ω Y]
    {f : X → Y} (hf : ContMDiff 𝓘(ℂ) 𝓘(ℂ) (⊤ : WithTop ℕ∞) f)
    {x : X} {O : Set X} (hO_open : IsOpen O) (hxO : x ∈ O)
    {k : ℕ} (hk : 0 < k) (hram : mapAnalyticOrderAt f x = k) :
    ∃ U : Set X, IsOpen U ∧ x ∈ U ∧ U ⊆ O ∧
    ∃ V : Set Y, IsOpen V ∧ f x ∈ V ∧
    ∀ y ∈ V, y ≠ f x →
    ∃ s : Finset X, s.card = k ∧ ↑s ⊆ U ∧
      (∀ x' ∈ s, f x' = y ∧ mapAnalyticOrderAt f x' = 1) ∧
      (∀ x' ∈ U, f x' = y → x' ∈ s) := by
  classical
  let sx := chartAt ℂ x
  let sy := chartAt ℂ (f x)
  let z₀ := sx x
  let c₀ := sy (f x)
  let g : ℂ → ℂ := fun z => chartLocalAt f x z - c₀
  let N : Set ℂ := sx.target ∩ sx.symm ⁻¹' (O ∩ f ⁻¹' sy.source)
  have hN_open : IsOpen N := by
    exact sx.isOpen_inter_preimage_symm
      (hO_open.inter (hf.continuous.isOpen_preimage _ sy.open_source))
  have hz₀N : z₀ ∈ N := by
    refine ⟨sx.map_source (mem_chart_source ℂ x), ?_⟩
    simp [sx, sy, z₀, hxO]
  have hg : AnalyticAt ℂ g z₀ := by
    simpa [g, z₀, c₀] using
      (IsHolomorphicAt.of_contMDiff hf x).sub analyticAt_const
  have hg0 : g z₀ = 0 := by
    simp [g, z₀, c₀, sx, sy, chartLocalAt, Function.comp_def]
  have hord : analyticOrderNatAt g z₀ = k := by
    simpa [mapAnalyticOrderAt, g, z₀, c₀] using hram
  have hord_ne_top : analyticOrderAt g z₀ ≠ ⊤ := by
    intro htop
    have hnat : analyticOrderNatAt g z₀ = 0 := by
      simp [analyticOrderNatAt, htop]
    exact (Nat.ne_of_gt hk) (hord.symm.trans hnat)
  obtain ⟨Uc, hUc_open, hz₀Uc, hUcN, Vc, hVc_open, h0Vc, hlocal⟩ :=
    AnalyticLocalMapping.analytic_local_mapping_theorem
      g z₀ k hk hN_open hz₀N hg hg0 hord hord_ne_top
  let U : Set X := sx.source ∩ sx ⁻¹' Uc
  have hU_open : IsOpen U := sx.isOpen_inter_preimage hUc_open
  have hxU : x ∈ U := by
    exact ⟨mem_chart_source ℂ x, hz₀Uc⟩
  have hUO : U ⊆ O := by
    intro x' hx'
    have hxN : sx x' ∈ N := hUcN hx'.2
    simpa [N, sx.left_inv hx'.1] using hxN.2.1
  let Wc : Set ℂ := {z | z - c₀ ∈ Vc}
  have hWc_open : IsOpen Wc := by
    exact hVc_open.preimage (by fun_prop : Continuous fun z : ℂ => z - c₀)
  let V : Set Y := sy.source ∩ sy ⁻¹' Wc
  have hV_open : IsOpen V := sy.isOpen_inter_preimage hWc_open
  have hfxV : f x ∈ V := by
    refine ⟨mem_chart_source ℂ (f x), ?_⟩
    simpa [Wc, c₀] using h0Vc
  refine ⟨U, hU_open, hxU, hUO, V, hV_open, hfxV, ?_⟩
  intro y hyV hy_ne
  let w : ℂ := sy y - c₀
  have hwVc : w ∈ Vc := by
    exact hyV.2
  have hw_ne : w ≠ 0 := by
    intro hw0
    apply hy_ne
    have hchart : sy y = sy (f x) := by
      dsimp [w, c₀] at hw0
      exact sub_eq_zero.mp hw0
    exact sy.injOn hyV.1 (mem_chart_source ℂ (f x)) hchart
  obtain ⟨S, hS_card, hS_Uc, hS_roots, hS_all⟩ := hlocal w hwVc hw_ne
  let s : Finset X := S.image sx.symm
  refine ⟨s, ?_, ?_, ?_, ?_⟩
  · dsimp [s]
    refine (Finset.card_image_of_injOn ?_).trans hS_card
    intro z hz z' hz' hzz'
    have hzN : z ∈ N := hUcN (hS_Uc hz)
    have hz'N : z' ∈ N := hUcN (hS_Uc hz')
    have hz_target : z ∈ sx.target := hzN.1
    have hz'_target : z' ∈ sx.target := hz'N.1
    calc
      z = sx (sx.symm z) := (sx.right_inv hz_target).symm
      _ = sx (sx.symm z') := by rw [hzz']
      _ = z' := sx.right_inv hz'_target
  · intro x' hx'
    have hxfin : x' ∈ s := by simpa using hx'
    rcases Finset.mem_image.mp hxfin with ⟨z, hzS, rfl⟩
    have hzN : z ∈ N := hUcN (hS_Uc hzS)
    refine ⟨sx.target_subset_preimage_source hzN.1, ?_⟩
    have hright : sx (sx.symm z) = z := sx.right_inv hzN.1
    show sx (sx.symm z) ∈ Uc
    rw [hright]
    exact hS_Uc hzS
  · intro x' hx'
    have hxfin : x' ∈ s := by simpa using hx'
    rcases Finset.mem_image.mp hxfin with ⟨z, hzS, rfl⟩
    have hzN : z ∈ N := hUcN (hS_Uc hzS)
    have hxsrc : sx.symm z ∈ sx.source := sx.target_subset_preimage_source hzN.1
    have hfxsrc : f (sx.symm z) ∈ sy.source := hzN.2.2
    have hzroot := hS_roots z hzS
    have hfy : f (sx.symm z) = y := by
      have hchart : sy (f (sx.symm z)) = sy y := by
        have hgz : g z = w := hzroot.1
        dsimp [g, w, c₀, chartLocalAt, Function.comp_def] at hgz
        have := congrArg (fun q : ℂ => q + c₀) hgz
        simpa [sub_eq_add_neg, add_assoc, add_comm, add_left_comm, c₀] using this
      exact sy.injOn hfxsrc hyV.1 hchart
    refine ⟨hfy, ?_⟩
    have horder_chart :
        analyticOrderNatAt (fun t => sy (f (sx.symm t)) - sy (f (sx.symm z))) (sx (sx.symm z)) = 1 := by
      have hcongr :
          (fun t => sy (f (sx.symm t)) - sy (f (sx.symm z))) =ᶠ[𝓝 z]
            (fun t => g t - w) := by
        apply Filter.Eventually.of_forall
        intro t
        dsimp [g, w, c₀, chartLocalAt, Function.comp_def]
        rw [hfy]
        ring
      have hzorder := hzroot.2
      have hz_order_at_z :
          analyticOrderNatAt (fun t => sy (f (sx.symm t)) - sy (f (sx.symm z))) z = 1 := by
        change (analyticOrderAt (fun t => sy (f (sx.symm t)) - sy (f (sx.symm z))) z).toNat = 1
        rw [analyticOrderAt_congr hcongr]
        exact hzorder
      simpa [sx.right_inv hzN.1] using hz_order_at_z
    have hchartOrder :=
      mapAnalyticOrderAt_congr_of_maximalAtlas
        (IsHolomorphicAt.of_contMDiff hf (sx.symm z))
        (hf.continuous.continuousAt)
        (IsManifold.chart_mem_maximalAtlas x) hxsrc
        (IsManifold.chart_mem_maximalAtlas (f x)) (by simpa [hfy] using hyV.1)
    exact hchartOrder.symm.trans horder_chart
  · intro x' hx'U hfx'y
    have hxsrc : x' ∈ sx.source := hx'U.1
    have hzUc : sx x' ∈ Uc := hx'U.2
    have hgz : g (sx x') = w := by
      dsimp [g, w, c₀, chartLocalAt, Function.comp_def]
      rw [sx.left_inv hxsrc, hfx'y]
    have hmemS : sx x' ∈ S := hS_all (sx x') hzUc hgz
    dsimp [s]
    exact Finset.mem_image.mpr ⟨sx x', hmemS, sx.left_inv hxsrc⟩

/-- Local `k`-fold ramification for a nonconstant complex-smooth map, as a
standalone theorem for use in the weighted-fiber conservation proof. -/
theorem local_kfold_ramified_of_contMDiff
    [IsManifold 𝓘(ℂ) ω X] [IsManifold 𝓘(ℂ) ω Y]
    {f : X → Y} (hf : ContMDiff 𝓘(ℂ) 𝓘(ℂ) (⊤ : WithTop ℕ∞) f)
    {x : X} {k : ℕ} (hk : 0 < k) (hram : mapAnalyticOrderAt f x = k) :
    ∃ U : Set X, IsOpen U ∧ x ∈ U ∧
    ∃ V : Set Y, IsOpen V ∧ f x ∈ V ∧
    ∀ y ∈ V, y ≠ f x →
    ∃ s : Finset X, s.card = k ∧ ↑s ⊆ U ∧
      (∀ x' ∈ s, f x' = y ∧ mapAnalyticOrderAt f x' = 1) ∧
      (∀ x' ∈ U, f x' = y → x' ∈ s) := by
  obtain ⟨U, hUopen, hxU, _hUuniv, V, hVopen, hfxV, hV⟩ :=
    local_kfold_ramified_of_contMDiff_within hf isOpen_univ (Set.mem_univ x) hk hram
  exact ⟨U, hUopen, hxU, V, hVopen, hfxV, hV⟩

/-- The local witness returned by `local_kfold_ramified_of_contMDiff`
contributes exactly `k` to the weighted fiber sum because all its
points are unramified. -/
theorem local_kfold_witness_weighted_sum
    {f : X → Y} {s : Finset X} {k : ℕ}
    (hcard : s.card = k)
    (horder : ∀ x ∈ s, mapAnalyticOrderAt f x = 1) :
    s.sum (mapAnalyticOrderAt f) = k := by
  calc
    s.sum (mapAnalyticOrderAt f) = s.sum (fun _ => 1) := by
      exact Finset.sum_congr rfl horder
    _ = s.card := by simp
    _ = k := hcard

/-- Weighted sums over a finite disjoint union split into the sum of the
local weighted contributions. -/
theorem weighted_sum_biUnion
    {ι X : Type*} [DecidableEq X] {I : Finset ι} {t : ι → Finset X}
    {w : X → ℕ} {a : ι → ℕ}
    (hdisj : Set.PairwiseDisjoint (↑I) t)
    (hlocal : ∀ i ∈ I, (t i).sum w = a i) :
    (I.biUnion t).sum w = ∑ i ∈ I, a i := by
  classical
  rw [Finset.sum_biUnion hdisj]
  exact Finset.sum_congr rfl fun i hi => hlocal i hi

/-- If a finite set is exactly an explicitly constructed disjoint union,
its `toFinset` has the same weighted sum as that union. -/
theorem finite_toFinset_sum_eq_of_set_eq
    {X : Type*} {S : Set X} (hS : S.Finite) {u : Finset X}
    {w : X → ℕ} (hset : S = (u : Set X)) :
    hS.toFinset.sum w = u.sum w := by
  have hfin : hS.toFinset = u := by
    apply Finset.ext
    intro x
    rw [Set.Finite.mem_toFinset, hset]
    exact Iff.rfl
  rw [hfin]

/-- Smooth maps between complex manifolds are holomorphic in the project-local sense.

BLOCKED (sorry 1376, blueprint `lem:impl-meromorphic-lift`).
This is the constructor for `IsHolomorphic f` from a `ContMDiff` hypothesis,
which has four fields:

* `continuous` — discharged directly from `ContMDiff.continuous`.

* `holomorphicAt : ∀ p, IsHolomorphicAt f p` — requires turning a
  `ContMDiffAt 𝓘(ℂ) 𝓘(ℂ) (⊤ : WithTop ℕ∞)` hypothesis (which is `Cⁿ`
  at level `n = ω` over the complex model) into `AnalyticAt ℂ` for the
  chart-local representation `chartAt ℂ (f p) ∘ f ∘ (chartAt ℂ p).symm`.
  Pinned Mathlib `v4.28.0` does not provide a manifold-level analyticity
  predicate or a `ContMDiff → AnalyticAt` chart-local extraction lemma
  (no `MAnalyticAt`, no `analyticAt_iff_contMDiff_ω`), so this requires a
  new helper not present in this file.

* `local_kfold_ramified` — the manifold-level local mapping theorem: at a
  point with `mapAnalyticOrderAt f x = k > 0`, the map is locally a
  `k`-to-`1` branched cover with the central fibre as the unique ramified
  point. The CP¹-specific analog
  `JacobianChallenge.HolomorphicForms.liftToCp1_local_kfold_ramified_finite`
  in `Jacobian/HolomorphicForms/MeromorphicToCp1.lean` is itself still a
  `sorry`, and the chart-level prerequisite
  `JacobianChallenge.HolomorphicForms.kfold_fiber_of_conjugate_pow` in
  `Jacobian/HolomorphicForms/LocalMappingThm.lean` has not yet been lifted
  to the manifold setting via chart transport.

* `weightedFiberSum_eventually_eq` — local conservation of the weighted
  fibre count on compact, preconnected `X`. The CP¹-specific analog
  `JacobianChallenge.HolomorphicForms.liftToCp1_weightedFiberSum_eventually_eq_finite`
  is also still a `sorry`, and no generic manifold-level version exists.

The first two prerequisites (chart-local analyticity from `ContMDiff` at
`ω`, manifold-level local mapping theorem) and the fibre-count
conservation theorem must land before this sorry can be discharged
honestly; degenerate solutions would violate the anti-cheat clause
(`mapAnalyticOrderAt` would have to be tied to genuine analytic order). -/
theorem isHolomorphic_of_contMDiff
    [IsManifold 𝓘(ℂ) ω X] [IsManifold 𝓘(ℂ) ω Y]
    {f : X → Y} (_hf : ContMDiff 𝓘(ℂ) 𝓘(ℂ) (⊤ : WithTop ℕ∞) f) :
    IsHolomorphic f := by
  refine
    { continuous := _hf.continuous
      holomorphicAt := IsHolomorphicAt.of_contMDiff _hf
      local_kfold_ramified := ?_
      weightedFiberSum_eventually_eq := ?_ }
  · intro _iX _iY x k hk hram
    exact local_kfold_ramified_of_contMDiff _hf hk hram
  · -- Blocked: this is the global conservation of weighted fibre cardinality
    -- for a nonconstant holomorphic map on a compact connected Riemann
    -- surface. Existing project lemmas either already require
    -- `IsHolomorphic` or apply to separately constructed meromorphic sphere
    -- lifts, so using them here would be circular.
    sorry

end Compatibility

end JacobianChallenge.HolomorphicForms
