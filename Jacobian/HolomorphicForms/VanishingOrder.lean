import Mathlib.Analysis.Meromorphic.Basic
import Mathlib.Analysis.Meromorphic.Order
import Mathlib.Analysis.Calculus.ContDiff.Defs
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

* `transition_analyticAt` — the transition is analytic at `e p`. This
  follows from the manifold typeclass: transitions in `IsManifold 𝓘(ℂ) ω X`
  are `C^ω`, which on the trivial model coincides with analyticity.
* `transition_deriv_ne_zero` — the transition's derivative at `e p` is
  nonzero. This is the complex inverse function theorem applied to the
  fact that the transition has a holomorphic inverse (the symmetric
  transition is also `C^ω`).

Both sub-obligations are stated as named theorems with `sorry` bodies in
this file; downstream sessions can discharge them independently.
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

Both are stated with `sorry` bodies; the assembly applying
`meromorphicOrderAt_comp_of_deriv_ne_zero` is fully discharged. -/

variable [IsManifold 𝓘(ℂ) ω X]

/-- **Sub-obligation 1.** The transition map between two holomorphic
charts in the analytic atlas is analytic at the relevant point.

Concretely: for any `e ∈ maximalAtlas 𝓘(ℂ) ω X` with `p ∈ e.source`,
the composite `chartAt ℂ p ∘ e.symm` is analytic at `e p`.

Proof sketch: `compatible_of_mem_maximalAtlas` gives
`e.symm.trans (chartAt ℂ p) ∈ contDiffGroupoid ω 𝓘(ℂ)`. Unfolding
`mem_groupoid_of_pregroupoid` yields
`ContDiffOn ℂ ω (chartAt ℂ p ∘ e.symm) ((e.symm.trans (chartAt ℂ p)).source)`
(after eliminating `𝓘(ℂ)` via `modelWithCornersSelf_coe`). The point
`e p` is in this open source, so `ContDiffOn` upgrades to `ContDiffAt`
at `e p`, and `ContDiffAt.analyticAt` finishes.

Left as a sorry'd sub-obligation; the bookkeeping involves several
unfolds of `contDiffGroupoid`, `contDiffPregroupoid`, and the source
of `e.symm.trans`. -/
theorem transition_analyticAt
    {p : X} (e : OpenPartialHomeomorph X ℂ)
    (he : e ∈ IsManifold.maximalAtlas 𝓘(ℂ) ω X) (hp : p ∈ e.source) :
    AnalyticAt ℂ (chartAt ℂ p ∘ e.symm) (e p) := by
  sorry

/-- **Sub-obligation 2.** The transition map between two holomorphic
charts in the analytic atlas has nonzero derivative.

Concretely: for any `e ∈ maximalAtlas 𝓘(ℂ) ω X` with `p ∈ e.source`,
`deriv (chartAt ℂ p ∘ e.symm) (e p) ≠ 0`.

Proof sketch: the symmetric transition `e ∘ (chartAt ℂ p).symm` is also
analytic at `chartAt ℂ p p` (apply `transition_analyticAt` with the roles
of `e` and `chartAt ℂ p` swapped). Since the two are local inverses near
`e p`, the chain rule applied to `id = e.symm ∘ e` (after composing with
`chartAt ℂ p` on both sides) gives that the product of their derivatives
at corresponding points equals `1`, hence each derivative is nonzero.

This is the only step in the construction without a single off-the-shelf
Mathlib lemma; it reduces to the complex inverse function theorem
(`Mathlib.Analysis.Calculus.InverseFunctionTheorem`) plus chain-rule
algebra on `deriv`. Estimated 30–50 LOC when discharged. Left as a
sorry'd sub-obligation. -/
theorem transition_deriv_ne_zero
    {p : X} (e : OpenPartialHomeomorph X ℂ)
    (he : e ∈ IsManifold.maximalAtlas 𝓘(ℂ) ω X) (hp : p ∈ e.source) :
    deriv (chartAt ℂ p ∘ e.symm) (e p) ≠ 0 := by
  sorry

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
