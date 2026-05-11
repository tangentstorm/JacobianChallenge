import Jacobian.HolomorphicForms.VanishingOrder
import Mathlib.Analysis.Analytic.Order
import Mathlib.Geometry.Manifold.ContMDiff.Defs

/-!
# Holomorphic maps between charted-on-`ℂ` spaces

A project-local definition of "holomorphic at a point" / "holomorphic"
for maps `f : X → Y` between two `ChartedSpace ℂ`-equipped spaces.
Mathlib `v4.28.0` does not provide a manifold-level analytic predicate
(no `MAnalyticAt`, no `Holomorphic*`), so we roll our own using the
canonical chart `chartAt ℂ` on each side and Mathlib's
`AnalyticAt ℂ` for the chart-local expression.

This is the first piece of the bridge from Mathlib's `ℂ → ℂ` analytic
infrastructure to the analytic constructor
`branchedCoverData_of_nonconstant_holomorphic` in
`Jacobian/Blueprint/Sec02/BranchedDegree.lean` (leaf 8 of the
branched-degree story).

## Main definitions

* `chartLocalAt f p` : the chart-local presentation
  `chartAt ℂ (f p) ∘ f ∘ (chartAt ℂ p).symm : ℂ → ℂ`.  This is the
  function whose analyticity / power-series order encode the analytic
  behaviour of `f` near `p`.
* `IsHolomorphicAt f p` : `f` is holomorphic at `p`, i.e. the
  chart-local presentation is `AnalyticAt ℂ` at `chartAt ℂ p p`.
* `IsHolomorphic f` : `f` is continuous and holomorphic at every point.
* `mapAnalyticOrderAt f p` : chart-local ramification / multiplicity
  index of `f` at `p`.  Defined as
  `analyticOrderNatAt (chartLocalAt f p · - chartLocalAt f p (chartAt ℂ p p)) (chartAt ℂ p p)`.

## Reuse of project infrastructure

The chart-transition machinery already discharged in
`Jacobian/HolomorphicForms/VanishingOrder.lean`
(`analyticAt_transition_of_mem_maximalAtlas`,
`transition_analyticAt`, `transition_deriv_ne_zero`,
`orderAt_eq_meromorphicOrderAt_of_mem_maximalAtlas`) carries over to
the holomorphic-map setting.  Future expansions of this file will lift
those theorems to chart-independence statements for `IsHolomorphicAt`
and `mapAnalyticOrderAt`.
-/

namespace JacobianChallenge.HolomorphicForms.HolomorphicMap

open scoped Manifold Topology ContDiff
open Set Filter

variable {X Y : Type*}
  [TopologicalSpace X] [ChartedSpace ℂ X]
  [TopologicalSpace Y] [ChartedSpace ℂ Y]

/-- Canonical chart-local presentation of `f : X → Y` at `p`:
the function `t ↦ chartAt ℂ (f p) (f (chartAt ℂ p).symm t)` from `ℂ` to
`ℂ`.  Defined only via the canonical charts, hence does not require
`IsManifold`. -/
noncomputable def chartLocalAt (f : X → Y) (p : X) : ℂ → ℂ :=
  chartAt ℂ (f p) ∘ f ∘ (chartAt ℂ p).symm

/-- `f : X → Y` is *holomorphic at* `p` iff its canonical chart-local
presentation is analytic at `chartAt ℂ p p` in the usual `ℂ → ℂ` sense.

Definition uses only the canonical charts at `p` and `f p`; chart
independence (over the maximal atlas) is a separate theorem to be
proved using `analyticAt_transition_of_mem_maximalAtlas` from
`Jacobian.HolomorphicForms.VanishingOrder`. -/
def IsHolomorphicAt (f : X → Y) (p : X) : Prop :=
  AnalyticAt ℂ (chartLocalAt f p) (chartAt ℂ p p)

/-- The *chart-local order of vanishing* of `f - f p` at `p`, computed
in the canonical chart pair.  Concretely:

  `mapAnalyticOrderAt f p = analyticOrderNatAt (Δ_p f) (chartAt ℂ p p)`

where `Δ_p f t = chartLocalAt f p t - chartLocalAt f p (chartAt ℂ p p)`
is the chart-local presentation centred on its value at `chartAt ℂ p p`.

Returns `0` if `f` is not analytic at `p` (`AnalyticOrderNatAt` falls
through to `0`) or if the chart-local difference is non-zero at
`chartAt ℂ p p` (which cannot happen by construction — it always
vanishes there — but is recorded as a junk default).  For a holomorphic
non-locally-constant map the value is `≥ 1`; this is the analytic input
to `BranchedCoverData.ramificationIndex_pos`. -/
noncomputable def mapAnalyticOrderAt (f : X → Y) (p : X) : ℕ :=
  analyticOrderNatAt
    (fun t => chartLocalAt f p t - chartLocalAt f p (chartAt ℂ p p))
    (chartAt ℂ p p)

/-- `f : X → Y` is *holomorphic* in the project-local branched-cover
scaffold.

The first two fields are the direct analytic content: continuity and
chart-local analyticity.  The final two fields package the classical
one-variable branched-cover consequences that Mathlib does not yet
provide at the manifold level.  Keeping them here makes downstream
blueprint lemmas honest projections from the chosen input predicate,
rather than proofs from an API that does not currently exist. -/
structure IsHolomorphic (f : X → Y) : Prop where
  /-- Holomorphic maps are continuous. -/
  continuous : Continuous f
  /-- Holomorphic at every point. -/
  holomorphicAt : ∀ p, IsHolomorphicAt f p
  /-- Local `k`-fold normal form/counting at a point of order `k`. -/
  local_kfold_ramified :
    ∀ [IsManifold 𝓘(ℂ) ω X] [IsManifold 𝓘(ℂ) ω Y]
      {x : X} {k : ℕ}, 0 < k → mapAnalyticOrderAt f x = k →
      ∃ U : Set X, IsOpen U ∧ x ∈ U ∧
      ∃ V : Set Y, IsOpen V ∧ f x ∈ V ∧
      ∀ y ∈ V, y ≠ f x →
      ∃ s : Finset X, s.card = k ∧ ↑s ⊆ U ∧
        (∀ x' ∈ s, f x' = y ∧ mapAnalyticOrderAt f x' = 1) ∧
        (∀ x' ∈ U, f x' = y → x' ∈ s)
  /-- Local constancy of the weighted fibre count. -/
  weightedFiberSum_eventually_eq :
    ∀ [IsManifold 𝓘(ℂ) ω X] [IsManifold 𝓘(ℂ) ω Y]
      [CompactSpace X] [T2Space X] [PreconnectedSpace X] [T2Space Y],
      (¬ ∃ y₀ : Y, ∀ x, f x = y₀) →
      (finite_fiber : ∀ y : Y, (f ⁻¹' {y}).Finite) →
      ∀ y₀ : Y, ∀ᶠ y in 𝓝 y₀,
        ((finite_fiber y).toFinset).sum
          (mapAnalyticOrderAt f) =
        ((finite_fiber y₀).toFinset).sum
          (mapAnalyticOrderAt f)

/-- The chart-local difference function used in `mapAnalyticOrderAt`
vanishes at the chart image of `p`.  This is a definitional fact about
`chartLocalAt` and centring. -/
@[simp]
theorem chartLocal_diff_self (f : X → Y) (p : X) :
    (fun t => chartLocalAt f p t - chartLocalAt f p (chartAt ℂ p p))
      (chartAt ℂ p p) = 0 := by
  simp

/-- The chart-local presentation evaluated at the chart image of `p`
yields the chart image of `f p`. -/
@[simp]
theorem chartLocalAt_chartAt_self (f : X → Y) (p : X) :
    chartLocalAt f p (chartAt ℂ p p) = chartAt ℂ (f p) (f p) := by
  unfold chartLocalAt
  have : (chartAt ℂ p).symm (chartAt ℂ p p) = p :=
    (chartAt ℂ p).left_inv (mem_chart_source ℂ p)
  simp [this]

/-! ## Chart independence of `mapAnalyticOrderAt`

The canonical-chart definition of `mapAnalyticOrderAt` extends to any
chart pair `(e₁, e₂)` over the analytic maximal atlas: replacing the
canonical `chartAt ℂ p` and `chartAt ℂ (f p)` by arbitrary
`e₁ ∈ maxAtlas X` containing `p` and `e₂ ∈ maxAtlas Y` containing
`f p` gives the same `analyticOrderNatAt`.

The proof factors through the chart transitions `chartAt ℂ p ∘ e₁.symm`
and `e₂ ∘ (chartAt ℂ (f p)).symm`, both of which are analytic with
nonzero derivative at the relevant point (project lemmas
`analyticAt_transition_of_mem_maximalAtlas` and
`transition_deriv_ne_zero` from
`Jacobian/HolomorphicForms/VanishingOrder.lean`).  The order chain:

  1. `analyticOrderAt_comp_of_deriv_ne_zero` collapses the inner
     chart transition `chartAt ℂ p ∘ e₁.symm`.
  2. `AnalyticAt.analyticOrderAt_comp` factors out the chartLocal
     composition.
  3. `analyticOrderAt_sub_eq_one_of_deriv_ne_zero` shows the outer
     chart transition contributes a factor of `1`.
-/

section ChartIndependence


/- Local-equality lemma: on a neighborhood of `e₁ p`, the alternate
chart-local form `e₂ ∘ f ∘ e₁.symm` factors as
`ψ ∘ chartLocalAt f p ∘ φ`, where `φ = chartAt ℂ p ∘ e₁.symm` and
`ψ = e₂ ∘ (chartAt ℂ (f p)).symm` are the chart transitions on the
two sides. -/
theorem alternate_chart_eventuallyEq_compose
    {f : X → Y} (hf_cont : Continuous f) {p : X}
    (e₁ : OpenPartialHomeomorph X ℂ) (hp₁ : p ∈ e₁.source)
    (e₂ : OpenPartialHomeomorph Y ℂ) (_hp₂ : f p ∈ e₂.source) :
    (fun t => e₂ (f (e₁.symm t)))
      =ᶠ[𝓝 (e₁ p)]
        ((fun s => e₂ ((chartAt ℂ (f p)).symm s))
          ∘ chartLocalAt f p
          ∘ (fun t => chartAt ℂ p (e₁.symm t))) := by
  have htarget : e₁.target ∈ 𝓝 (e₁ p) :=
    e₁.open_target.mem_nhds (e₁.map_source hp₁)
  have hep_target : e₁ p ∈ e₁.target := e₁.map_source hp₁
  have hsymm_at : e₁.symm (e₁ p) = p := e₁.left_inv hp₁
  have hsymm : ContinuousAt e₁.symm (e₁ p) := e₁.symm.continuousAt hep_target
  have hsource_X : e₁.symm ⁻¹' (chartAt ℂ p).source ∈ 𝓝 (e₁ p) := by
    refine hsymm ?_
    rw [hsymm_at]
    exact (chartAt ℂ p).open_source.mem_nhds (mem_chart_source ℂ p)
  have hsource_Y : (fun t => f (e₁.symm t)) ⁻¹' (chartAt ℂ (f p)).source
      ∈ 𝓝 (e₁ p) := by
    have hf_at : ContinuousAt f (e₁.symm (e₁ p)) := by
      rw [hsymm_at]; exact hf_cont.continuousAt
    have hcomp : ContinuousAt (fun t => f (e₁.symm t)) (e₁ p) :=
      hf_at.comp hsymm
    refine hcomp ?_
    show (chartAt ℂ (f p)).source ∈ 𝓝 (f (e₁.symm (e₁ p)))
    rw [hsymm_at]
    exact (chartAt ℂ (f p)).open_source.mem_nhds (mem_chart_source ℂ (f p))
  filter_upwards [htarget, hsource_X, hsource_Y] with t _ hsXt hsYt
  have h1 : (chartAt ℂ p).symm (chartAt ℂ p (e₁.symm t)) = e₁.symm t :=
    (chartAt ℂ p).left_inv hsXt
  have h2 : (chartAt ℂ (f p)).symm (chartAt ℂ (f p) (f (e₁.symm t)))
      = f (e₁.symm t) :=
    (chartAt ℂ (f p)).left_inv hsYt
  show e₂ (f (e₁.symm t))
      = e₂ ((chartAt ℂ (f p)).symm (chartLocalAt f p (chartAt ℂ p (e₁.symm t))))
  unfold chartLocalAt
  simp [Function.comp_apply, h1, h2]

variable [IsManifold 𝓘(ℂ) ω X] [IsManifold 𝓘(ℂ) ω Y]

open JacobianChallenge.HolomorphicForms.VanishingOrder

/-- Swap of `transition_deriv_ne_zero`: the transition
`e ∘ (chartAt ℂ p).symm` (rather than `chartAt ℂ p ∘ e.symm`) also
has nonzero derivative at the relevant point.  Same chain-rule
argument as `transition_deriv_ne_zero`, with the round trip composed
in the opposite direction. -/
theorem chartAt_symm_transition_deriv_ne_zero
    {Z : Type*} [TopologicalSpace Z] [ChartedSpace ℂ Z]
    [IsManifold 𝓘(ℂ) ω Z]
    {q : Z} (e : OpenPartialHomeomorph Z ℂ)
    (he : e ∈ IsManifold.maximalAtlas 𝓘(ℂ) ω Z) (hq : q ∈ e.source) :
    deriv ((⇑e) ∘ (chartAt ℂ q).symm) (chartAt ℂ q q) ≠ 0 := by
  have hψ : AnalyticAt ℂ ((⇑e) ∘ (chartAt ℂ q).symm) (chartAt ℂ q q) :=
    analyticAt_transition_of_mem_maximalAtlas
      (IsManifold.chart_mem_maximalAtlas q) he (mem_chart_source ℂ q) hq
  have hφ : AnalyticAt ℂ ((chartAt ℂ q : Z → ℂ) ∘ e.symm) (e q) :=
    transition_analyticAt e he hq
  have hψ_at : ((⇑e) ∘ (chartAt ℂ q).symm) (chartAt ℂ q q) = e q := by
    show e ((chartAt ℂ q).symm (chartAt ℂ q q)) = e q
    rw [(chartAt ℂ q).left_inv (mem_chart_source ℂ q)]
  have hround :
      ((chartAt ℂ q : Z → ℂ) ∘ e.symm) ∘ ((⇑e) ∘ (chartAt ℂ q).symm)
        =ᶠ[𝓝 (chartAt ℂ q q)] id := by
    have hmem_target : (chartAt ℂ q).target ∈ 𝓝 (chartAt ℂ q q) :=
      (chartAt ℂ q).open_target.mem_nhds
        ((chartAt ℂ q).map_source (mem_chart_source ℂ q))
    have hsymm_e : (chartAt ℂ q).symm ⁻¹' e.source ∈ 𝓝 (chartAt ℂ q q) := by
      refine (chartAt ℂ q).symm.continuousAt
          ((chartAt ℂ q).map_source (mem_chart_source ℂ q)) ?_
      rw [(chartAt ℂ q).left_inv (mem_chart_source ℂ q)]
      exact e.open_source.mem_nhds hq
    filter_upwards [hmem_target, hsymm_e] with y hy₁ hy₂
    show chartAt ℂ q (e.symm (e ((chartAt ℂ q).symm y))) = y
    rw [e.left_inv hy₂, (chartAt ℂ q).right_inv hy₁]
  have hψ_d : HasDerivAt ((⇑e) ∘ (chartAt ℂ q).symm)
      (deriv ((⇑e) ∘ (chartAt ℂ q).symm) (chartAt ℂ q q))
      (chartAt ℂ q q) :=
    hψ.differentiableAt.hasDerivAt
  have hφ_d : HasDerivAt ((chartAt ℂ q : Z → ℂ) ∘ e.symm)
      (deriv ((chartAt ℂ q : Z → ℂ) ∘ e.symm) (e q)) (e q) :=
    hφ.differentiableAt.hasDerivAt
  have hcomp :
      HasDerivAt
        (((chartAt ℂ q : Z → ℂ) ∘ e.symm) ∘ ((⇑e) ∘ (chartAt ℂ q).symm))
        (deriv ((chartAt ℂ q : Z → ℂ) ∘ e.symm) (e q) *
          deriv ((⇑e) ∘ (chartAt ℂ q).symm) (chartAt ℂ q q))
        (chartAt ℂ q q) :=
    HasDerivAt.comp_of_eq (chartAt ℂ q q) hφ_d hψ_d hψ_at.symm
  have hcomp1 :
      HasDerivAt
        (((chartAt ℂ q : Z → ℂ) ∘ e.symm) ∘ ((⇑e) ∘ (chartAt ℂ q).symm))
        (1 : ℂ) (chartAt ℂ q q) :=
    (hasDerivAt_id (chartAt ℂ q q)).congr_of_eventuallyEq hround
  have hprod := hcomp.unique hcomp1
  intro h
  rw [h, mul_zero] at hprod
  exact zero_ne_one hprod

/-- **Chart independence (`ℕ∞` form).** For any two analytic charts
`e₁` at `p ∈ X` and `e₂` at `f p ∈ Y` (in the maximal atlas), the
analytic order of `(e₂ ∘ f ∘ e₁.symm) - e₂(f p)` at `e₁ p` agrees with
the canonical-chart analytic order at `chartAt ℂ p p`. -/
theorem analyticOrderAt_alternate_chart_eq
    {f : X → Y} (hf : IsHolomorphic f) {p : X}
    {e₁ : OpenPartialHomeomorph X ℂ}
    (he₁ : e₁ ∈ IsManifold.maximalAtlas 𝓘(ℂ) ω X)
    (hp₁ : p ∈ e₁.source)
    {e₂ : OpenPartialHomeomorph Y ℂ}
    (he₂ : e₂ ∈ IsManifold.maximalAtlas 𝓘(ℂ) ω Y)
    (hp₂ : f p ∈ e₂.source) :
    analyticOrderAt (fun t => e₂ (f (e₁.symm t)) - e₂ (f p)) (e₁ p) =
      analyticOrderAt
        (fun t => chartLocalAt f p t - chartLocalAt f p (chartAt ℂ p p))
        (chartAt ℂ p p) := by
  set φ : ℂ → ℂ := fun t => chartAt ℂ p (e₁.symm t) with hφ_def
  set ψ : ℂ → ℂ := fun s => e₂ ((chartAt ℂ (f p)).symm s) with hψ_def
  have hφ_an : AnalyticAt ℂ φ (e₁ p) :=
    analyticAt_transition_of_mem_maximalAtlas
      he₁ (IsManifold.chart_mem_maximalAtlas p) hp₁ (mem_chart_source ℂ p)
  have hφ_dn : deriv φ (e₁ p) ≠ 0 := transition_deriv_ne_zero (X := X) e₁ he₁ hp₁
  have hφ_at : φ (e₁ p) = chartAt ℂ p p := by
    show chartAt ℂ p (e₁.symm (e₁ p)) = chartAt ℂ p p
    rw [e₁.left_inv hp₁]
  have hψ_an : AnalyticAt ℂ ψ (chartAt ℂ (f p) (f p)) :=
    analyticAt_transition_of_mem_maximalAtlas (X := Y)
      (IsManifold.chart_mem_maximalAtlas (f p)) he₂
      (mem_chart_source ℂ (f p)) hp₂
  have hψ_dn : deriv ψ (chartAt ℂ (f p) (f p)) ≠ 0 :=
    chartAt_symm_transition_deriv_ne_zero (Z := Y) e₂ he₂ hp₂
  have hψ_at : ψ (chartAt ℂ (f p) (f p)) = e₂ (f p) := by
    show e₂ ((chartAt ℂ (f p)).symm (chartAt ℂ (f p) (f p))) = e₂ (f p)
    rw [(chartAt ℂ (f p)).left_inv (mem_chart_source ℂ (f p))]
  have hagree : (fun t => e₂ (f (e₁.symm t)))
      =ᶠ[𝓝 (e₁ p)] (ψ ∘ chartLocalAt f p ∘ φ) :=
    alternate_chart_eventuallyEq_compose hf.continuous e₁ hp₁ e₂ hp₂
  have hagree' : (fun t => e₂ (f (e₁.symm t)) - e₂ (f p))
      =ᶠ[𝓝 (e₁ p)]
        (fun t => (ψ ∘ chartLocalAt f p ∘ φ) t - ψ (chartAt ℂ (f p) (f p))) := by
    rw [← hψ_at]
    exact hagree.sub (Filter.EventuallyEq.refl _ _)
  rw [analyticOrderAt_congr hagree']
  set G : ℂ → ℂ := fun s => ψ s - ψ (chartAt ℂ (f p) (f p)) with hG_def
  have hcomp_eq : (fun t => (ψ ∘ chartLocalAt f p ∘ φ) t
        - ψ (chartAt ℂ (f p) (f p)))
      = (G ∘ chartLocalAt f p) ∘ φ := by
    funext t; simp [G, Function.comp_apply]
  rw [hcomp_eq]
  rw [analyticOrderAt_comp_of_deriv_ne_zero hφ_an hφ_dn]
  rw [hφ_at]
  have hcl_an : AnalyticAt ℂ (chartLocalAt f p) (chartAt ℂ p p) :=
    hf.holomorphicAt p
  have hG_an : AnalyticAt ℂ G (chartLocalAt f p (chartAt ℂ p p)) := by
    rw [chartLocalAt_chartAt_self]
    exact hψ_an.sub analyticAt_const
  rw [hG_an.analyticOrderAt_comp hcl_an]
  rw [chartLocalAt_chartAt_self]
  have hG_ord : analyticOrderAt G (chartAt ℂ (f p) (f p)) = 1 := by
    show analyticOrderAt (fun s => ψ s - ψ (chartAt ℂ (f p) (f p)))
        (chartAt ℂ (f p) (f p)) = 1
    exact hψ_an.analyticOrderAt_sub_eq_one_of_deriv_ne_zero hψ_dn
  rw [hG_ord, one_mul]

/-- **Chart independence (`ℕ` form).** Direct corollary of
`analyticOrderAt_alternate_chart_eq` after applying `.toNat`. -/
theorem mapAnalyticOrderAt_eq_of_mem_maximalAtlas
    {f : X → Y} (hf : IsHolomorphic f) {p : X}
    {e₁ : OpenPartialHomeomorph X ℂ}
    (he₁ : e₁ ∈ IsManifold.maximalAtlas 𝓘(ℂ) ω X)
    (hp₁ : p ∈ e₁.source)
    {e₂ : OpenPartialHomeomorph Y ℂ}
    (he₂ : e₂ ∈ IsManifold.maximalAtlas 𝓘(ℂ) ω Y)
    (hp₂ : f p ∈ e₂.source) :
    analyticOrderNatAt (fun t => e₂ (f (e₁.symm t)) - e₂ (f p)) (e₁ p) =
      mapAnalyticOrderAt f p := by
  unfold mapAnalyticOrderAt analyticOrderNatAt
  rw [analyticOrderAt_alternate_chart_eq hf he₁ hp₁ he₂ hp₂]

end ChartIndependence

/-! ## Finite fibres of nonconstant holomorphic maps -/

section FiniteFiber

/-- **Local identity principle (chart-local).** An analytic function
on `ℂ` that is frequently zero on a punctured neighborhood of `z₀` is
eventually zero on a full neighborhood. -/
private theorem analyticAt_eventually_eq_zero_of_frequently
    {δ : ℂ → ℂ} {z₀ : ℂ} (hδ : AnalyticAt ℂ δ z₀)
    (hfreq : ∃ᶠ z in 𝓝[≠] z₀, δ z = 0) :
    ∀ᶠ z in 𝓝 z₀, δ z = 0 := by
  rcases hδ.eventually_eq_zero_or_eventually_ne_zero with hzero | hnonzero
  · exact hzero
  · exfalso
    obtain ⟨_, h1, h2⟩ := (hfreq.and_eventually hnonzero).exists
    exact h2 h1

/- **Local identity principle for a holomorphic map.** -/
theorem IsHolomorphicAt.eventually_eq_of_frequently_eq
    {f : X → Y} {x₀ : X} {y₀ : Y}
    (hf : IsHolomorphicAt f x₀) (hf_cont : Continuous f) (hfx₀ : f x₀ = y₀)
    (hfreq : ∃ᶠ x in 𝓝[≠] x₀, f x = y₀) :
    ∀ᶠ x in 𝓝 x₀, f x = y₀ := by
  set δ : ℂ → ℂ := fun t => chartLocalAt f x₀ t - chartAt ℂ y₀ y₀ with hδ_def
  have hδ_an : AnalyticAt ℂ δ (chartAt ℂ x₀ x₀) := hf.sub analyticAt_const
  have h_source_X : ∀ᶠ x in 𝓝 x₀, x ∈ (chartAt ℂ x₀).source :=
    (chartAt ℂ x₀).open_source.mem_nhds (mem_chart_source ℂ x₀)
  have h_source_Y : ∀ᶠ x in 𝓝 x₀, f x ∈ (chartAt ℂ y₀).source := by
    have hy₀_src : (chartAt ℂ y₀).source ∈ 𝓝 (f x₀) := by
      rw [hfx₀]
      exact (chartAt ℂ y₀).open_source.mem_nhds (mem_chart_source ℂ y₀)
    exact hf_cont.continuousAt hy₀_src
  have hδ_compute : ∀ x ∈ (chartAt ℂ x₀).source, f x = y₀ →
      δ (chartAt ℂ x₀ x) = 0 := by
    intro x hxs hfx
    show chartLocalAt f x₀ (chartAt ℂ x₀ x) - chartAt ℂ y₀ y₀ = 0
    unfold chartLocalAt
    simp only [Function.comp_apply]
    rw [(chartAt ℂ x₀).left_inv hxs, hfx, hfx₀]
    simp
  have hδ_compute_general : ∀ x ∈ (chartAt ℂ x₀).source,
      δ (chartAt ℂ x₀ x) = chartAt ℂ y₀ (f x) - chartAt ℂ y₀ y₀ := by
    intro x hxs
    show chartLocalAt f x₀ (chartAt ℂ x₀ x) - chartAt ℂ y₀ y₀ = _
    unfold chartLocalAt
    simp only [Function.comp_apply]
    rw [(chartAt ℂ x₀).left_inv hxs, hfx₀]
  have hδ_freq : ∃ᶠ z in 𝓝[≠] (chartAt ℂ x₀ x₀), δ z = 0 := by
    suffices h : AccPt (chartAt ℂ x₀ x₀) (𝓟 {z | δ z = 0}) by
      exact accPt_iff_frequently_nhdsNE.mp h
    rw [accPt_iff_nhds]
    intro V hV
    have h_chart_cont : ContinuousAt (chartAt ℂ x₀) x₀ :=
      (chartAt ℂ x₀).continuousAt (mem_chart_source ℂ x₀)
    have hV_X : (chartAt ℂ x₀) ⁻¹' V ∈ 𝓝 x₀ := h_chart_cont hV
    have h_combined : ∀ᶠ x in 𝓝[≠] x₀,
        x ∈ (chartAt ℂ x₀) ⁻¹' V ∧ x ∈ (chartAt ℂ x₀).source ∧ x ≠ x₀ := by
      have h_punct : ∀ᶠ x in 𝓝[≠] x₀, x ≠ x₀ := self_mem_nhdsWithin
      filter_upwards [mem_nhdsWithin_of_mem_nhds hV_X,
                      mem_nhdsWithin_of_mem_nhds h_source_X,
                      h_punct]
        with x hxV hxsX hxne
      exact ⟨hxV, hxsX, hxne⟩
    have h_freq_full : ∃ᶠ x in 𝓝[≠] x₀,
        f x = y₀ ∧ x ∈ (chartAt ℂ x₀) ⁻¹' V ∧ x ∈ (chartAt ℂ x₀).source ∧ x ≠ x₀ :=
      (hfreq.and_eventually h_combined).mono fun _ ⟨a, b, c, d⟩ => ⟨a, b, c, d⟩
    obtain ⟨x, hx_eq, hxV_pre, hxs_X, hx_ne⟩ := h_freq_full.exists
    refine ⟨chartAt ℂ x₀ x, ⟨hxV_pre, hδ_compute x hxs_X hx_eq⟩, ?_⟩
    intro h_eq
    exact hx_ne ((chartAt ℂ x₀).injOn hxs_X (mem_chart_source ℂ x₀) h_eq)
  have hδ_zero : ∀ᶠ z in 𝓝 (chartAt ℂ x₀ x₀), δ z = 0 :=
    analyticAt_eventually_eq_zero_of_frequently hδ_an hδ_freq
  have h_chart_cont : ContinuousAt (chartAt ℂ x₀) x₀ :=
    (chartAt ℂ x₀).continuousAt (mem_chart_source ℂ x₀)
  have hδ_pulled : ∀ᶠ x in 𝓝 x₀, δ (chartAt ℂ x₀ x) = 0 := h_chart_cont hδ_zero
  filter_upwards [hδ_pulled, h_source_X, h_source_Y] with x hδ_x hxs_X hxs_Y
  rw [hδ_compute_general x hxs_X, sub_eq_zero] at hδ_x
  exact (chartAt ℂ y₀).injOn hxs_Y (mem_chart_source ℂ y₀) hδ_x

/-- **Local-constancy ⇒ global-constancy** on a preconnected space. -/
theorem IsHolomorphic.eq_const_of_eventuallyEq
    [PreconnectedSpace X] [T2Space Y]
    {f : X → Y} (hf : IsHolomorphic f) {y₀ : Y} {x₁ : X}
    (h_local : ∀ᶠ x in 𝓝 x₁, f x = y₀) :
    ∀ x, f x = y₀ := by
  set C : Set X := {x | ∀ᶠ x' in 𝓝 x, f x' = y₀} with hC_def
  have hC_open : IsOpen C := by
    rw [isOpen_iff_eventually]
    intro x hx
    exact hx.eventually_nhds
  have hC_nonempty : C.Nonempty := ⟨x₁, h_local⟩
  have hC_le_A : C ⊆ {x | f x = y₀} := fun _ hx => hx.self_of_nhds
  have hA_closed : IsClosed {x : X | f x = y₀} :=
    isClosed_singleton.preimage hf.continuous
  have hC_closed : IsClosed C := by
    rw [isClosed_iff_clusterPt]
    intro x hclu
    have hxA : f x = y₀ := by
      have hx_clos : x ∈ closure C := mem_closure_iff_clusterPt.mpr hclu
      have hx_clos_A : x ∈ closure {x | f x = y₀} := closure_mono hC_le_A hx_clos
      rwa [hA_closed.closure_eq] at hx_clos_A
    by_cases hxC : x ∈ C
    · exact hxC
    · have hAcc : AccPt x (𝓟 C) := by
        rcases clusterPt_principal.mp hclu with hxC' | hAcc'
        · exact absurd hxC' hxC
        · exact hAcc'
      have hAcc_A : AccPt x (𝓟 {x | f x = y₀}) :=
        hAcc.mono (principal_mono.mpr hC_le_A)
      have hfreq : ∃ᶠ x' in 𝓝[≠] x, f x' = y₀ :=
        accPt_iff_frequently_nhdsNE.mp hAcc_A
      exact (hf.holomorphicAt x).eventually_eq_of_frequently_eq
        hf.continuous hxA hfreq
  have hC_clopen : IsClopen C := ⟨hC_closed, hC_open⟩
  have hC_univ : C = Set.univ :=
    (isClopen_iff.mp hC_clopen).resolve_left
      (Set.nonempty_iff_ne_empty.mp hC_nonempty)
  intro x
  have hx_in : x ∈ C := by rw [hC_univ]; trivial
  exact hx_in.self_of_nhds

/-- **Positivity of `mapAnalyticOrderAt`** for nonconstant holomorphic
maps on a preconnected space.  At any point, the chart-local analytic
order is at least one because:

  * The chart-local difference function vanishes at the centre, ruling
    out `analyticOrderAt = 0` (which would require nonvanishing).
  * Local-constancy at the centre would force global-constancy via
    `IsHolomorphic.eq_const_of_eventuallyEq`, ruling out
    `analyticOrderAt = ⊤`.

The remaining ℕ∞-values are positive naturals, whose `.toNat` is
positive. -/
theorem mapAnalyticOrderAt_pos
    [PreconnectedSpace X] [T2Space Y]
    {f : X → Y} (hf : IsHolomorphic f)
    (hnonconst : ¬ ∃ y₀ : Y, ∀ x, f x = y₀) (x : X) :
    0 < mapAnalyticOrderAt f x := by
  unfold mapAnalyticOrderAt analyticOrderNatAt
  set g : ℂ → ℂ := fun t => chartLocalAt f x t - chartLocalAt f x (chartAt ℂ x x)
  have hg_an : AnalyticAt ℂ g (chartAt ℂ x x) :=
    (hf.holomorphicAt x).sub analyticAt_const
  have hg_zero : g (chartAt ℂ x x) = 0 := by simp [g]
  have h_order_ne_zero : analyticOrderAt g (chartAt ℂ x x) ≠ 0 := by
    rw [Ne, analyticOrderAt_eq_zero]
    push_neg
    exact ⟨hg_an, hg_zero⟩
  have h_order_ne_top : analyticOrderAt g (chartAt ℂ x x) ≠ ⊤ := by
    intro h
    rw [analyticOrderAt_eq_top] at h
    have h_local : ∀ᶠ x' in 𝓝 x, f x' = f x := by
      have h_chart_cont : ContinuousAt (chartAt ℂ x) x :=
        (chartAt ℂ x).continuousAt (mem_chart_source ℂ x)
      have h_pulled : ∀ᶠ x' in 𝓝 x, g (chartAt ℂ x x') = 0 :=
        h_chart_cont h
      have h_source_X : ∀ᶠ x' in 𝓝 x, x' ∈ (chartAt ℂ x).source :=
        (chartAt ℂ x).open_source.mem_nhds (mem_chart_source ℂ x)
      have h_source_Y : ∀ᶠ x' in 𝓝 x, f x' ∈ (chartAt ℂ (f x)).source := by
        exact hf.continuous.continuousAt
          ((chartAt ℂ (f x)).open_source.mem_nhds (mem_chart_source ℂ (f x)))
      filter_upwards [h_pulled, h_source_X, h_source_Y]
        with x' h_eq h_xs h_ys
      have h_lhs : chartLocalAt f x (chartAt ℂ x x') = chartAt ℂ (f x) (f x') := by
        unfold chartLocalAt
        simp only [Function.comp_apply]
        rw [(chartAt ℂ x).left_inv h_xs]
      have h_rhs : chartLocalAt f x (chartAt ℂ x x) = chartAt ℂ (f x) (f x) :=
        chartLocalAt_chartAt_self f x
      have h_g_expand : g (chartAt ℂ x x') =
          chartAt ℂ (f x) (f x') - chartAt ℂ (f x) (f x) := by
        show chartLocalAt f x (chartAt ℂ x x') - chartLocalAt f x (chartAt ℂ x x) = _
        rw [h_lhs, h_rhs]
      rw [h_g_expand, sub_eq_zero] at h_eq
      exact (chartAt ℂ (f x)).injOn h_ys (mem_chart_source ℂ (f x)) h_eq
    have h_global := hf.eq_const_of_eventuallyEq h_local
    exact hnonconst ⟨f x, h_global⟩
  rcases ENat.ne_top_iff_exists.mp h_order_ne_top with ⟨n, hn⟩
  rw [← hn]
  simp only [ENat.toNat_coe]
  rcases Nat.eq_zero_or_pos n with rfl | hpos
  · simp at hn
    exact absurd hn.symm h_order_ne_zero
  · exact hpos

/-- **Finite fibres of nonconstant holomorphic maps.** -/
theorem isHolomorphic_finite_fiber
    [CompactSpace X] [PreconnectedSpace X] [T2Space Y]
    {f : X → Y} (hf : IsHolomorphic f)
    (hnonconst : ¬ ∃ y₀ : Y, ∀ x, f x = y₀) (y : Y) :
    (f ⁻¹' {y}).Finite := by
  by_contra hinf
  rw [Set.not_finite] at hinf
  obtain ⟨x₀, hx₀_acc⟩ := hinf.exists_accPt_principal
  have hclosed : IsClosed (f ⁻¹' {y}) :=
    isClosed_singleton.preimage hf.continuous
  have hx₀_in : f x₀ = y := by
    have : x₀ ∈ closure (f ⁻¹' {y}) :=
      mem_closure_iff_clusterPt.mpr hx₀_acc.clusterPt
    rwa [hclosed.closure_eq] at this
  have hfreq : ∃ᶠ x in 𝓝[≠] x₀, f x = y :=
    accPt_iff_frequently_nhdsNE.mp hx₀_acc
  have h_local : ∀ᶠ x in 𝓝 x₀, f x = y :=
    (hf.holomorphicAt x₀).eventually_eq_of_frequently_eq
      hf.continuous hx₀_in hfreq
  have h_global : ∀ x, f x = y := hf.eq_const_of_eventuallyEq h_local
  exact hnonconst ⟨y, h_global⟩

end FiniteFiber

/-- **Holomorphic-smooth bridge.** Every `ContMDiff` map between complex
manifolds is `IsHolomorphic`.

This is the load-bearing analytic bridge: Mathlib's `ContMDiff` (at `⊤`)
is equivalent to holomorphicity for complex manifolds. The first two
fields (continuity and local analyticity) are definitional; the latter
two (local k-fold form and weighted-fiber constancy) are the deep
classical theorems that follow from analyticity on a compact Riemann
surface.

Bottom-up: the local k-fold form comes from the isolated-zeros /
power-series expansion of analytic maps; the weighted-fiber count
conservation is the topological degree theory for branched covers. -/
theorem isHolomorphic_of_contMDiff
    {X Y : Type*} [TopologicalSpace X] [ChartedSpace ℂ X]
    [TopologicalSpace Y] [ChartedSpace ℂ Y]
    [IsManifold 𝓘(ℂ) ω X] [IsManifold 𝓘(ℂ) ω Y]
    {f : X → Y} (hf : ContMDiff 𝓘(ℂ) 𝓘(ℂ) (⊤ : WithTop ℕ∞) f) :
    IsHolomorphic f :=
  sorry

end JacobianChallenge.HolomorphicForms.HolomorphicMap
