import Mathlib.Analysis.Meromorphic.Basic
import Mathlib.Analysis.Meromorphic.Order
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.FDeriv.Analytic
import Mathlib.Analysis.Complex.Basic
import Mathlib.Geometry.Manifold.IsManifold.Basic
import Mathlib.Geometry.Manifold.IsManifold.ExtChartAt

/-!
# Order of vanishing of a meromorphic germ at a point on a complex 1-manifold

This file formalizes blueprint leaf node `def:vanishing-order` from
`tex/sections/01-compact-riemann-surfaces.tex`:

> For a holomorphic chart `φ : U → ℂ` sending `p ↦ 0` and a meromorphic germ
> `f` at `p`, the order of vanishing `ord_p(f) ∈ ℤ ∪ {+∞}` is the order of
> the Laurent series of `f ∘ φ⁻¹` at `0`. The convention is `ord_p(0) = +∞`
> and `ord_p(f) < 0` for poles. The value is independent of the chart.

The construction uses Mathlib's `meromorphicOrderAt` for `ℂ → ℂ` functions,
pulled back through the canonical extended chart `extChartAt 𝓘(ℂ) p`.
Chart independence is the substantive content.

## Main definitions

* `MeromorphicAtX f p` : `f : X → ℂ` is meromorphic at `p` in the manifold
  sense, i.e. its pullback to ℂ via the canonical extended chart at `p` is
  meromorphic in the usual sense.
* `orderAt p f : WithTop ℤ` : the order of vanishing of `f` at `p`,
  computed in the canonical extended chart. Returns `0` (junk) if `f` is
  not meromorphic at `p`, and `⊤` if `f` vanishes locally near `p`.

## Main theorems

* `orderAt_eq_meromorphicOrderAt_of_mem_maximalAtlas` — chart
  independence: for any chart `e ∈ maximalAtlas 𝓘(ℂ) ω X` with
  `p ∈ e.source`, `orderAt p f` equals `meromorphicOrderAt (f ∘ e.symm)
  (e p)`.

## TOPDOWN refinement

The chart-independence theorem reduces to two sub-obligations about
the transition map `g := chartAt ℂ p ∘ e.symm`:

* `transition_analyticAt` — the transition is analytic at `e p`. Follows
  from the manifold typeclass: transitions in `IsManifold 𝓘(ℂ) ω X`
  are `C^ω`, which on the trivial model coincides with analyticity.
* `transition_deriv_ne_zero` — the transition's derivative at `e p` is
  nonzero. The symmetric transition is analytic too (apply the same
  lemma with chart roles swapped), and the round trip is the identity
  near `e p`; the chain rule gives the product of the two derivatives
  equal to `1`, so neither factor can vanish.

Both sub-obligations are now discharged in this file via the named
helper `analyticAt_transition_of_mem_maximalAtlas`.
-/

namespace JacobianChallenge.HolomorphicForms.VanishingOrder

open scoped Manifold Topology ContDiff
open Set Filter

variable {X : Type*} [TopologicalSpace X] [ChartedSpace ℂ X]

/-! ### Definitions

`MeromorphicAtX` and `orderAt` are introduced before the analytic-manifold
hypothesis is needed: their definitions only use the `ChartedSpace ℂ X`
structure and the canonical extended chart `extChartAt 𝓘(ℂ) p`. -/

/-- `f : X → ℂ` is meromorphic at `p ∈ X` (in the manifold sense) iff its
pullback `f ∘ (extChartAt 𝓘(ℂ) p).symm` is meromorphic at `extChartAt 𝓘(ℂ) p p`
in the usual `ℂ → ℂ` sense.

Wraps Mathlib's `MeromorphicAt`, which is only defined for `f : 𝕜 → E`. -/
def MeromorphicAtX (f : X → ℂ) (p : X) : Prop :=
  MeromorphicAt (f ∘ (extChartAt 𝓘(ℂ) p).symm) (extChartAt 𝓘(ℂ) p p)

/-- The order of vanishing of a meromorphic germ `f : X → ℂ` at `p ∈ X`.

Computed in the canonical extended chart at `p`. Returns:
* a finite integer `n ∈ ℤ` for a germ vanishing or pole-of-order `-n`,
* `⊤` if `f` vanishes on a punctured neighborhood of `p` (in particular
  for the zero germ),
* `0` (junk) if `f` is not meromorphic at `p`.

Chart independence is `orderAt_eq_meromorphicOrderAt_of_mem_maximalAtlas`. -/
noncomputable def orderAt (p : X) (f : X → ℂ) : WithTop ℤ :=
  meromorphicOrderAt (f ∘ (extChartAt 𝓘(ℂ) p).symm) (extChartAt 𝓘(ℂ) p p)

/-! ### Bridging `extChartAt` and `chartAt`

`extChartAt 𝓘(ℂ) p = (chartAt ℂ p).extend 𝓘(ℂ)`, which on the trivial
model `𝓘(ℂ) = id` coincides with `chartAt ℂ p` as a function. We
record the two pointwise identifications used in the chart-independence
proof. -/

/-- The canonical extended chart at `p` agrees with `chartAt ℂ p` as a
function. Follows from `extChartAt_coe` and `modelWithCornersSelf_coe`. -/
theorem extChartAt_eq_chartAt (p : X) :
    ⇑(extChartAt 𝓘(ℂ) p) = chartAt ℂ p := by
  funext x
  simp

/-- The canonical extended chart's inverse agrees with `(chartAt ℂ p).symm`
as a function. -/
theorem extChartAt_symm_eq_chartAt_symm (p : X) :
    ⇑(extChartAt 𝓘(ℂ) p).symm = (chartAt ℂ p).symm := by
  funext x
  simp

/-- The `extChartAt`-form of `orderAt` rewrites in terms of `chartAt`. -/
theorem orderAt_eq_chartAt (p : X) (f : X → ℂ) :
    orderAt p f =
      meromorphicOrderAt (f ∘ (chartAt ℂ p).symm) (chartAt ℂ p p) := by
  unfold orderAt
  rw [extChartAt_symm_eq_chartAt_symm, extChartAt_eq_chartAt]

/-! ### Punctured-neighborhood agreement of two chart pullbacks

For any chart `e` at `p` (containing `p` in its source), the pullback
`f ∘ e.symm` agrees, on a neighborhood of `e p`, with the composition
`(f ∘ (chartAt ℂ p).symm) ∘ (chartAt ℂ p ∘ e.symm)`. This is the
bookkeeping needed to apply `meromorphicOrderAt_congr` and
`meromorphicOrderAt_comp_of_deriv_ne_zero` together. -/

/-- On the open set where `e.symm` lands in `(chartAt ℂ p).source`,
`f ∘ e.symm` factors as `(f ∘ (chartAt ℂ p).symm) ∘ (chartAt ℂ p ∘ e.symm)`. -/
theorem comp_eqOn
    {p : X} (e : OpenPartialHomeomorph X ℂ) (f : X → ℂ) :
    EqOn (f ∘ e.symm)
      ((f ∘ (chartAt ℂ p).symm) ∘ (chartAt ℂ p ∘ e.symm))
      (e.target ∩ e.symm ⁻¹' (chartAt ℂ p).source) := by
  intro y hy
  obtain ⟨_, hy₂⟩ := hy
  have h := (chartAt ℂ p).left_inv hy₂
  simp [Function.comp, h]

/-- The set `e.target ∩ e.symm ⁻¹' (chartAt ℂ p).source` is a neighborhood
of `e p` whenever `p` lies in `e.source`. -/
theorem target_inter_preimage_mem_nhds
    {p : X} (e : OpenPartialHomeomorph X ℂ) (hp : p ∈ e.source) :
    e.target ∩ e.symm ⁻¹' (chartAt ℂ p).source ∈ 𝓝 (e p) := by
  refine Filter.inter_mem ?_ ?_
  · exact e.open_target.mem_nhds (e.map_source hp)
  · refine e.symm.continuousAt (e.map_source hp) ?_
    rw [e.left_inv hp]
    exact (chartAt ℂ p).open_source.mem_nhds (mem_chart_source ℂ p)

/-- **Punctured-neighborhood agreement.** The pullback `f ∘ e.symm`
agrees with the composite `(f ∘ (chartAt ℂ p).symm) ∘ (chartAt ℂ p ∘ e.symm)`
on a punctured neighborhood of `e p`. -/
theorem eventuallyEq_pullback
    {p : X} (e : OpenPartialHomeomorph X ℂ) (hp : p ∈ e.source)
    (f : X → ℂ) :
    (f ∘ e.symm) =ᶠ[𝓝[≠] (e p)]
      (f ∘ (chartAt ℂ p).symm) ∘ (chartAt ℂ p ∘ e.symm) := by
  have hmem : e.target ∩ e.symm ⁻¹' (chartAt ℂ p).source ∈ 𝓝 (e p) :=
    target_inter_preimage_mem_nhds e hp
  filter_upwards [Filter.mem_inf_of_left hmem] with y hy
  exact comp_eqOn e f hy

/-! ### Chart-independence

Below this point we assume `IsManifold 𝓘(ℂ) ω X` (analytic complex
1-manifold). The chart-independence theorem reduces to two sub-obligations
about the transition map `g := chartAt ℂ p ∘ e.symm`:

* `transition_analyticAt` — the transition is analytic at `e p`.
* `transition_deriv_ne_zero` — the transition has nonzero derivative at `e p`.

Both are discharged below via the named helper
`analyticAt_transition_of_mem_maximalAtlas` (compatibility +
`ContDiffAt.analyticAt`) and a chain-rule argument on the round trip. -/

set_option linter.unusedSectionVars false

variable [IsManifold 𝓘(ℂ) ω X]

/-- **Generalized analyticity of transitions.** For any two charts
`e₁, e₂ ∈ maximalAtlas 𝓘(ℂ) ω X` containing `p` in their sources, the
transition `e₂ ∘ e₁.symm` is analytic at `e₁ p`.

Proof: `compatible_of_mem_maximalAtlas` gives
`e₁.symm.trans e₂ ∈ contDiffGroupoid ω 𝓘(ℂ)`. Unfolding through
`mem_groupoid_of_pregroupoid` and `contDiffPregroupoid` (and simplifying
under the trivial model `𝓘(ℂ)`) gives `ContDiffOn ℂ ω (e₂ ∘ e₁.symm)`
on the open transition source. Restricting to a neighborhood of `e₁ p`
upgrades to `ContDiffAt`, then `ContDiffAt.analyticAt` finishes.

Note: the proof depends on the maximal-atlas membership but not on the
`IsManifold` typeclass directly; we keep the typeclass in scope anyway
for uniformity with the rest of the section. -/
theorem analyticAt_transition_of_mem_maximalAtlas
    {p : X} {e₁ e₂ : OpenPartialHomeomorph X ℂ}
    (he₁ : e₁ ∈ IsManifold.maximalAtlas 𝓘(ℂ) ω X)
    (he₂ : e₂ ∈ IsManifold.maximalAtlas 𝓘(ℂ) ω X)
    (hp₁ : p ∈ e₁.source) (hp₂ : p ∈ e₂.source) :
    AnalyticAt ℂ (e₂ ∘ e₁.symm) (e₁ p) := by
  -- Step 1: get groupoid membership of the transition.
  have hcompat := IsManifold.compatible_of_mem_maximalAtlas he₁ he₂
  rw [contDiffGroupoid, mem_groupoid_of_pregroupoid] at hcompat
  -- The forward (toFun) component of the pregroupoid property.
  have hcd := hcompat.1
  -- Step 2: simplify under the trivial model `𝓘(ℂ)`.
  -- `contDiffPregroupoid.property f s` is
  -- `ContDiffOn ℂ ω (𝓘(ℂ) ∘ f ∘ 𝓘(ℂ).symm) (𝓘(ℂ).symm ⁻¹' s ∩ range 𝓘(ℂ))`,
  -- which reduces to `ContDiffOn ℂ ω f s` since `𝓘(ℂ) = id` and
  -- `range 𝓘(ℂ) = univ`.
  simp only [contDiffPregroupoid, modelWithCornersSelf_coe,
    modelWithCornersSelf_coe_symm, Function.id_comp, Function.comp_id,
    range_id, preimage_id, inter_univ] at hcd
  -- Step 3: rewrite through `coe_trans` so the function becomes `e₂ ∘ e₁.symm`.
  have hcoe : ⇑(e₁.symm.trans e₂) = e₂ ∘ e₁.symm := by
    funext y; rfl
  rw [hcoe] at hcd
  -- Step 4: `e₁ p` is in the (open) transition source.
  have hep_target : e₁ p ∈ e₁.symm.source := by
    show e₁ p ∈ e₁.target
    exact e₁.map_source hp₁
  have hep_pre : e₁.symm (e₁ p) ∈ e₂.source := by
    rw [e₁.left_inv hp₁]; exact hp₂
  have hep_mem : e₁ p ∈ (e₁.symm.trans e₂).source := by
    rw [OpenPartialHomeomorph.trans_source]
    exact ⟨hep_target, hep_pre⟩
  -- Step 5: upgrade `ContDiffOn` at an interior point to `ContDiffAt`.
  have hopen : IsOpen (e₁.symm.trans e₂).source := (e₁.symm.trans e₂).open_source
  have hcdat : ContDiffAt ℂ ω (e₂ ∘ e₁.symm) (e₁ p) :=
    (hcd (e₁ p) hep_mem).contDiffAt (hopen.mem_nhds hep_mem)
  -- Step 6: `ContDiffAt 𝕜 ω → AnalyticAt 𝕜`.
  exact hcdat.analyticAt

/-- **Sub-obligation 1 (discharged).** The transition `chartAt ℂ p ∘ e.symm`
is analytic at `e p`. Specialization of
`analyticAt_transition_of_mem_maximalAtlas` to `e₂ = chartAt ℂ p`. -/
theorem transition_analyticAt
    {p : X} (e : OpenPartialHomeomorph X ℂ)
    (he : e ∈ IsManifold.maximalAtlas 𝓘(ℂ) ω X) (hp : p ∈ e.source) :
    AnalyticAt ℂ (chartAt ℂ p ∘ e.symm) (e p) :=
  analyticAt_transition_of_mem_maximalAtlas he
    (IsManifold.chart_mem_maximalAtlas p) hp (mem_chart_source ℂ p)

/-- **Sub-obligation 2 (discharged).** The transition `chartAt ℂ p ∘ e.symm`
has nonzero derivative at `e p`.

Proof: the symmetric transition `e ∘ (chartAt ℂ p).symm` is also analytic
(apply the generalized lemma with chart roles swapped). The two compose
to the identity on a neighborhood of `e p`. Differentiating via the chain
rule gives `(deriv g')(g(e p)) * (deriv g)(e p) = 1`, so neither factor
can be zero. -/
theorem transition_deriv_ne_zero
    {p : X} (e : OpenPartialHomeomorph X ℂ)
    (he : e ∈ IsManifold.maximalAtlas 𝓘(ℂ) ω X) (hp : p ∈ e.source) :
    deriv (chartAt ℂ p ∘ e.symm) (e p) ≠ 0 := by
  -- The forward and backward transitions, both analytic.
  have hg : AnalyticAt ℂ (chartAt ℂ p ∘ e.symm) (e p) :=
    transition_analyticAt e he hp
  have hgep : (chartAt ℂ p ∘ e.symm) (e p) = chartAt ℂ p p := by
    simp [Function.comp_apply, e.left_inv hp]
  have hg' : AnalyticAt ℂ (e ∘ (chartAt ℂ p).symm) (chartAt ℂ p p) :=
    analyticAt_transition_of_mem_maximalAtlas
      (IsManifold.chart_mem_maximalAtlas p) he (mem_chart_source ℂ p) hp
  -- Eventual identity of the round trip near `e p`.
  have hid : (e ∘ (chartAt ℂ p).symm) ∘ (chartAt ℂ p ∘ e.symm) =ᶠ[𝓝 (e p)] id := by
    have hmem : e.target ∩ e.symm ⁻¹' (chartAt ℂ p).source ∈ 𝓝 (e p) :=
      target_inter_preimage_mem_nhds e hp
    filter_upwards [hmem] with y hy
    obtain ⟨hy₁, hy₂⟩ := hy
    show e ((chartAt ℂ p).symm ((chartAt ℂ p) (e.symm y))) = y
    rw [(chartAt ℂ p).left_inv hy₂, e.right_inv hy₁]
  -- Chain rule: derivative of round trip = product of factor derivatives.
  have hg_d : HasDerivAt (chartAt ℂ p ∘ e.symm)
      (deriv (chartAt ℂ p ∘ e.symm) (e p)) (e p) :=
    hg.differentiableAt.hasDerivAt
  have hg'_d : HasDerivAt (e ∘ (chartAt ℂ p).symm)
      (deriv (e ∘ (chartAt ℂ p).symm) (chartAt ℂ p p)) (chartAt ℂ p p) :=
    hg'.differentiableAt.hasDerivAt
  -- `comp_of_eq` consumes the equality `chartAt ℂ p p = (chartAt ℂ p ∘ e.symm) (e p)`,
  -- avoiding higher-order unification on the third HasDerivAt argument.
  -- Note: the lemma takes `x` (here `e p`) as an explicit positional argument,
  -- per the section variable convention in `Mathlib/Analysis/Calculus/Deriv/Comp.lean`.
  have hcomp : HasDerivAt ((e ∘ (chartAt ℂ p).symm) ∘ (chartAt ℂ p ∘ e.symm))
      (deriv (e ∘ (chartAt ℂ p).symm) (chartAt ℂ p p) *
        deriv (chartAt ℂ p ∘ e.symm) (e p)) (e p) :=
    HasDerivAt.comp_of_eq (e p) hg'_d hg_d hgep.symm
  -- The round trip is eventually `id`, so its derivative is `1`.
  have hcomp1 : HasDerivAt ((e ∘ (chartAt ℂ p).symm) ∘ (chartAt ℂ p ∘ e.symm))
      (1 : ℂ) (e p) :=
    (hasDerivAt_id (e p)).congr_of_eventuallyEq hid
  -- Uniqueness of the derivative.
  have hprod :
      deriv (e ∘ (chartAt ℂ p).symm) (chartAt ℂ p p) *
        deriv (chartAt ℂ p ∘ e.symm) (e p) = 1 :=
    hcomp.unique hcomp1
  -- Conclude.
  intro h
  rw [h, mul_zero] at hprod
  exact zero_ne_one hprod

/-! ### Main chart-independence theorem -/

/-- **Chart independence (canonical to arbitrary).** For any chart
`e ∈ maximalAtlas 𝓘(ℂ) ω X` with `p ∈ e.source`,
`orderAt p f = meromorphicOrderAt (f ∘ e.symm) (e p)`.

The proof composes:
1. `orderAt_eq_chartAt` rewrites the LHS through the canonical chart.
2. `eventuallyEq_pullback` and `meromorphicOrderAt_congr` rewrite
   `f ∘ e.symm` as the composite via the transition map.
3. `meromorphicOrderAt_comp_of_deriv_ne_zero`
   (`Mathlib.Analysis.Meromorphic.Order`, line 754), fed by
   `transition_analyticAt` and `transition_deriv_ne_zero`, evaluates the
   composite's order at the transition's image.
4. The transition sends `e p ↦ chartAt ℂ p p` (since `e.symm (e p) = p`),
   closing the chain. -/
theorem orderAt_eq_meromorphicOrderAt_of_mem_maximalAtlas
    {p : X} (f : X → ℂ) (e : OpenPartialHomeomorph X ℂ)
    (he : e ∈ IsManifold.maximalAtlas 𝓘(ℂ) ω X) (hp : p ∈ e.source) :
    orderAt p f = meromorphicOrderAt (f ∘ e.symm) (e p) := by
  -- Step 1: rewrite LHS through canonical chart.
  rw [orderAt_eq_chartAt]
  -- Step 2: rewrite `f ∘ e.symm` as the composite via the transition `g`.
  have hcongr : (f ∘ e.symm) =ᶠ[𝓝[≠] (e p)]
      (f ∘ (chartAt ℂ p).symm) ∘ (chartAt ℂ p ∘ e.symm) :=
    eventuallyEq_pullback e hp f
  rw [meromorphicOrderAt_congr hcongr]
  -- Step 3: apply `meromorphicOrderAt_comp_of_deriv_ne_zero` to the
  -- transition `g := chartAt ℂ p ∘ e.symm`.
  have hg_an : AnalyticAt ℂ (chartAt ℂ p ∘ e.symm) (e p) :=
    transition_analyticAt e he hp
  have hg_der : deriv (chartAt ℂ p ∘ e.symm) (e p) ≠ 0 :=
    transition_deriv_ne_zero e he hp
  rw [meromorphicOrderAt_comp_of_deriv_ne_zero hg_an hg_der]
  -- Step 4: identify `(chartAt ℂ p ∘ e.symm) (e p) = chartAt ℂ p p`.
  have hep : (chartAt ℂ p ∘ e.symm) (e p) = chartAt ℂ p p := by
    simp [Function.comp_apply, e.left_inv hp]
  rw [hep]

/-! ### Manifold meromorphy ⇒ chart-pullback meromorphy

If `f : X → ℂ` is meromorphic at every point of `X` (in the manifold sense
encoded by `MeromorphicAtX`), then for every base point `p : X`, the
chart pullback `f ∘ (chartAt ℂ p).symm` is meromorphic on the entire
chart target `(chartAt ℂ p).target`.

The proof at a point `w ∈ (chartAt ℂ p).target` factorises through the
chart at `q := (chartAt ℂ p).symm w`: the transition
`chartAt ℂ q ∘ (chartAt ℂ p).symm` is analytic at `w` with nonzero
derivative (the existing transition-analyticity infrastructure), so
`meromorphicAt_comp_iff_of_deriv_ne_zero` lifts manifold-level meromorphy
at `q` to chart-target-level meromorphy at `w`.
-/

/-- **Chart pullback is meromorphic at every target point.**

Given pointwise manifold meromorphy of `f`, the chart pullback through
`chartAt ℂ p` is `MeromorphicAt` at every `w ∈ (chartAt ℂ p).target`. -/
theorem meromorphicAt_chart_pullback_of_meromorphicAtX
    {f : X → ℂ} (hf : ∀ q : X, MeromorphicAtX f q) (p : X)
    {w : ℂ} (hw : w ∈ (chartAt ℂ p).target) :
    MeromorphicAt (f ∘ (chartAt ℂ p).symm) w := by
  set q : X := (chartAt ℂ p).symm w with hq_def
  have hq_source : q ∈ (chartAt ℂ p).source := (chartAt ℂ p).map_target hw
  have hpq : (chartAt ℂ p) q = w := (chartAt ℂ p).right_inv hw
  -- Membership of charts in the maximal atlas.
  have hp_mem : (chartAt ℂ p) ∈ IsManifold.maximalAtlas 𝓘(ℂ) ω X :=
    IsManifold.chart_mem_maximalAtlas p
  have hq_mem : (chartAt ℂ q) ∈ IsManifold.maximalAtlas 𝓘(ℂ) ω X :=
    IsManifold.chart_mem_maximalAtlas q
  have hq_q_source : q ∈ (chartAt ℂ q).source := mem_chart_source ℂ q
  -- The transition `chartAt ℂ q ∘ (chartAt ℂ p).symm` is analytic at `w`.
  have h_an : AnalyticAt ℂ ((chartAt ℂ q) ∘ (chartAt ℂ p).symm) w := by
    rw [show w = (chartAt ℂ p) q from hpq.symm]
    exact analyticAt_transition_of_mem_maximalAtlas hp_mem hq_mem hq_source hq_q_source
  -- Its derivative at `w` is nonzero.
  have h_der : deriv ((chartAt ℂ q) ∘ (chartAt ℂ p).symm) w ≠ 0 := by
    rw [show w = (chartAt ℂ p) q from hpq.symm]
    exact transition_deriv_ne_zero (chartAt ℂ p) hp_mem hq_source
  -- Manifold meromorphy at `q` translates to `MeromorphicAt (f ∘ chartAt ℂ q .symm)`
  -- at `chartAt ℂ q q`.
  have hfq : MeromorphicAt (f ∘ (chartAt ℂ q).symm) ((chartAt ℂ q) q) := by
    have h := hf q
    unfold MeromorphicAtX at h
    rwa [extChartAt_symm_eq_chartAt_symm, extChartAt_eq_chartAt] at h
  -- Lift to meromorphy of the composite at `w`.
  have hcomp : MeromorphicAt
      ((f ∘ (chartAt ℂ q).symm) ∘ ((chartAt ℂ q) ∘ (chartAt ℂ p).symm)) w := by
    rw [meromorphicAt_comp_iff_of_deriv_ne_zero h_an h_der]
    have heval : ((chartAt ℂ q) ∘ (chartAt ℂ p).symm) w = (chartAt ℂ q) q := by
      simp [Function.comp_apply, hq_def]
    rw [heval]; exact hfq
  -- The composite agrees with `f ∘ (chartAt ℂ p).symm` on a punctured nbhd of `w`.
  -- Use `eventuallyEq_pullback` with role-bookkeeping (outer chart at `q`, `e := chartAt ℂ p`).
  have heq : (f ∘ (chartAt ℂ p).symm) =ᶠ[𝓝[≠] w]
      (f ∘ (chartAt ℂ q).symm) ∘ ((chartAt ℂ q) ∘ (chartAt ℂ p).symm) := by
    have := eventuallyEq_pullback (p := q) (chartAt ℂ p) hq_source f
    rwa [hpq] at this
  exact hcomp.congr heq.symm

/-- **Chart pullback is meromorphic on the chart target.**

Packages `meromorphicAt_chart_pullback_of_meromorphicAtX` as a
`MeromorphicOn` statement. -/
theorem meromorphicOn_chart_pullback_of_meromorphicAtX
    {f : X → ℂ} (hf : ∀ q : X, MeromorphicAtX f q) (p : X) :
    MeromorphicOn (f ∘ (chartAt ℂ p).symm) (chartAt ℂ p).target :=
  fun _w hw ↦ meromorphicAt_chart_pullback_of_meromorphicAtX hf p hw

/-- **Chart-independence (two arbitrary atlas charts).** For two charts
`e₁, e₂ ∈ maximalAtlas 𝓘(ℂ) ω X` both containing `p` in their sources,
the meromorphic-order pullbacks agree. -/
theorem meromorphicOrderAt_pullback_eq
    {p : X} (f : X → ℂ)
    {e₁ e₂ : OpenPartialHomeomorph X ℂ}
    (he₁ : e₁ ∈ IsManifold.maximalAtlas 𝓘(ℂ) ω X) (hp₁ : p ∈ e₁.source)
    (he₂ : e₂ ∈ IsManifold.maximalAtlas 𝓘(ℂ) ω X) (hp₂ : p ∈ e₂.source) :
    meromorphicOrderAt (f ∘ e₁.symm) (e₁ p) =
      meromorphicOrderAt (f ∘ e₂.symm) (e₂ p) := by
  rw [← orderAt_eq_meromorphicOrderAt_of_mem_maximalAtlas f e₁ he₁ hp₁,
      ← orderAt_eq_meromorphicOrderAt_of_mem_maximalAtlas f e₂ he₂ hp₂]

end JacobianChallenge.HolomorphicForms.VanishingOrder
