import Jacobian.Blueprint.Sec01.VanishingOrder
import Mathlib.Topology.ClusterPt
import Mathlib.Topology.DiscreteSubset
import Mathlib.Analysis.Meromorphic.IsolatedZeros
import Mathlib.Analysis.Meromorphic.Order

/-! Blueprint: `lem:divisor-discrete` in
`tex/sections/01-compact-riemann-surfaces.tex`.

For a nonzero meromorphic function `f` on a compact Riemann surface `X`,
the set `{p ∈ X : ord_p(f) ≠ 0}` has no accumulation point. -/

namespace JacobianChallenge.Blueprint

open scoped Manifold ContDiff Topology
open Filter Set
open JacobianChallenge.HolomorphicForms.VanishingOrder

/-- **Discreteness of the divisor support.**

For a meromorphic function `f` on a complex 1-manifold `X` whose vanishing
order is finite at every point (the manifold-level encoding of "`f` is
nonzero"), the set of points with nonzero vanishing order has no
accumulation point.

The hypotheses encode the blueprint phrase "nonzero meromorphic function"
pointwise:

* `hf_mero : ∀ q, MeromorphicAtX f q` — `f` is meromorphic at every point
  of `X`. Without this, the conclusion is meaningless (the `vanishingOrder`
  is `0` junk-default outside meromorphy).
* `hf_finite : ∀ q, vanishingOrder X q f ≠ ⊤` — `f` is not locally
  identically zero anywhere. Without this, the disjoint counterexample
  `X = ℂ ⊔ ℂ, f = 0 ⊔ 1` makes the statement false (the zero copy has
  `meromorphicOrderAt = ⊤` everywhere and accumulates with itself).
  On a connected Riemann surface, this hypothesis follows from the
  existential form `∃ q, vanishingOrder X q f ≠ ⊤` via the identity
  principle (`isClopen_setOf_meromorphicOrderAt_eq_top` plus
  `[ConnectedSpace X]`); that propagation is left to a separate lemma
  to keep this leaf statement chart-local.

Proof: pick `p`, work in the chart at `p`. The pullback
`f ∘ (chartAt ℂ p).symm` is meromorphic on the entire chart target via
`meromorphicOn_chart_pullback_of_meromorphicAtX`. Mathlib's
`MeromorphicOn.codiscrete_setOf_meromorphicOrderAt_eq_zero_or_top`
provides a punctured chart-target neighborhood of `chartAt ℂ p p` on
which the meromorphic order is `0` or `⊤`. The `⊤` disjunct is excluded
by `hf_finite` (transferred via chart-independence). Pulling back through
`chartAt ℂ p` gives a punctured `X`-neighborhood of `p` on which
`vanishingOrder X · f = 0`. -/
theorem divisor_discrete
    (X : Type*) [TopologicalSpace X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X]
    (f : X → ℂ)
    (hf_mero : ∀ q : X, MeromorphicAtX f q)
    (hf_finite : ∀ q : X, vanishingOrder X q f ≠ ⊤) :
    ∀ p : X, ¬ AccPt p (Filter.principal {q : X | vanishingOrder X q f ≠ 0}) := by
  intro p
  -- Reformulate as filter membership: `{q | order q f = 0} ∈ 𝓝[≠] p`.
  rw [accPt_iff_frequently_nhdsNE, Filter.not_frequently]
  set chart_p := chartAt ℂ p with hchart_p_def
  have hp_atlas : chart_p ∈ IsManifold.maximalAtlas 𝓘(ℂ) ω X :=
    IsManifold.chart_mem_maximalAtlas p
  have hp_source : p ∈ chart_p.source := mem_chart_source ℂ p
  have hp_target : (chart_p) p ∈ chart_p.target := chart_p.map_source hp_source
  have hMer : MeromorphicOn (f ∘ chart_p.symm) chart_p.target :=
    meromorphicOn_chart_pullback_of_meromorphicAtX hf_mero p
  -- Codiscrete fact: `{u | order = 0 ∨ ⊤}` (subtype) ∈ codiscrete chart_p.target.
  -- Translate to ambient `codiscreteWithin chart_p.target` and apply at `chart_p p`.
  have hcod := mem_codiscrete_subtype_iff_mem_codiscreteWithin.1
    hMer.codiscrete_setOf_meromorphicOrderAt_eq_zero_or_top
  rw [mem_codiscreteWithin_iff_forall_mem_nhdsNE] at hcod
  have h_at := hcod (chart_p p) hp_target
  -- Extract an open `W` ⊆ ℂ with `chart_p p ∈ W` and the codiscrete inclusion
  -- on `W ∩ {chart_p p}ᶜ`.
  rw [mem_nhdsWithin] at h_at
  obtain ⟨W, hW_open, hW_mem, hW_sub⟩ := h_at
  -- Show `{q | vanishingOrder X q f = 0} ∈ 𝓝[≠] p`.
  have hgood : {q : X | vanishingOrder X q f = 0} ∈ 𝓝[≠] p := by
    rw [mem_nhdsWithin]
    refine ⟨chart_p.source ∩ chart_p ⁻¹' W,
            chart_p.isOpen_inter_preimage hW_open,
            ⟨hp_source, hW_mem⟩, ?_⟩
    rintro q ⟨⟨hq_src, hq_W⟩, hq_ne_p⟩
    -- `hq_ne_p : q ∈ ({p} : Set X)ᶜ`, i.e., `q ≠ p`.
    have hq_ne : q ≠ p := hq_ne_p
    have hcq_target : chart_p q ∈ chart_p.target := chart_p.map_source hq_src
    have hcq_ne : chart_p q ≠ chart_p p := by
      intro hcq_eq
      apply hq_ne
      have h₁ := chart_p.left_inv hq_src
      have h₂ := chart_p.left_inv hp_source
      rw [hcq_eq] at h₁
      exact h₁.symm.trans h₂
    have h_in := hW_sub ⟨hq_W, hcq_ne⟩
    rcases h_in with h_image | h_compl
    · obtain ⟨u, hu_prop, hu_val⟩ := h_image
      simp only [Set.mem_setOf_eq] at hu_prop
      rw [hu_val] at hu_prop
      have hchart_indep :
          orderAt q f = meromorphicOrderAt (f ∘ chart_p.symm) (chart_p q) :=
        orderAt_eq_meromorphicOrderAt_of_mem_maximalAtlas
          (p := q) f chart_p hp_atlas hq_src
      have h_van_eq : vanishingOrder X q f =
          meromorphicOrderAt (f ∘ chart_p.symm) (chart_p q) := hchart_indep
      rcases hu_prop with hu0 | huT
      · show vanishingOrder X q f = 0
        rw [h_van_eq, hu0]
      · exact absurd (h_van_eq.trans huT) (hf_finite q)
    · exact absurd hcq_target h_compl
  -- Conclude: `{q | order q f = 0} ⊆ {q | ¬ order q f ≠ 0}`.
  filter_upwards [hgood] with q hq using fun h_ne => h_ne hq

end JacobianChallenge.Blueprint
