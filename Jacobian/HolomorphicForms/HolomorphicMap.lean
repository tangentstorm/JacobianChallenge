import Jacobian.HolomorphicForms.VanishingOrder
import Mathlib.Analysis.Analytic.Order

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
`Jacobian/Blueprint/Sec02/BranchedDegree.lean` (the still-`sorry`-bearing
"leaf 8" of the branched-degree story).

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

/-- `f : X → Y` is *holomorphic* iff it is continuous and holomorphic
at every point.  Continuity is included so that consumers of the
predicate can talk about `f ⁻¹' {y}` and pull back open sets without
re-deriving continuity from chart-local analyticity. -/
structure IsHolomorphic (f : X → Y) : Prop where
  /-- Holomorphic maps are continuous. -/
  continuous : Continuous f
  /-- Holomorphic at every point. -/
  holomorphicAt : ∀ p, IsHolomorphicAt f p

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

/-- Local-equality lemma: on a neighborhood of `e₁ p`, the alternate
chart-local form `e₂ ∘ f ∘ e₁.symm` factors as
`ψ ∘ chartLocalAt f p ∘ φ`, where `φ = chartAt ℂ p ∘ e₁.symm` and
`ψ = e₂ ∘ (chartAt ℂ (f p)).symm` are the chart transitions on the
two sides. -/
theorem alternate_chart_eventuallyEq_compose
    {f : X → Y} (hf_cont : Continuous f) {p : X}
    (e₁ : OpenPartialHomeomorph X ℂ) (hp₁ : p ∈ e₁.source)
    (e₂ : OpenPartialHomeomorph Y ℂ) (hp₂ : f p ∈ e₂.source) :
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

end JacobianChallenge.HolomorphicForms.HolomorphicMap
