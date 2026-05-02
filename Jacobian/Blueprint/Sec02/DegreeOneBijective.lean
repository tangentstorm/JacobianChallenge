import Jacobian.Blueprint.Sec02.BranchedDegree

/-! # Blueprint: `thm:degree-one-bijective`

Section 2 of `tex/sections/02-holomorphic-forms-and-genus.tex`.

A degree-one holomorphic map between compact connected Riemann
surfaces is bijective: degree one forces every fibre to have a single
sheet (injectivity), and the same singleton fibre witness gives
surjectivity.

The analytic hypothesis "non-constant holomorphic between compact
connected Riemann surfaces" is absorbed into the existence of a
`BranchedCoverData X Y f`; the analytic constructor producing such
data from the holomorphic input is the still-open
`branchedCoverData_of_nonconstant_holomorphic` (leaf 8 in
`Jacobian/Blueprint/Sec02/BranchedDegree.lean`).  Once that lands, the
hypothesis here is fed by the constructor and this theorem becomes a
direct consequence of the combinatorial leaf 7. -/

namespace JacobianChallenge.Blueprint

/-- **`thm:degree-one-bijective`.** A degree-one branched cover is
bijective.  Surjectivity comes from the singleton fibre over any
target point; injectivity follows because two distinct preimages of
the same point would each contribute a positive summand to a weighted
fibre sum already equal to one. -/
theorem degree_one_bijective
    {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    {f : X → Y} [Nonempty Y] (h : BranchedCoverData X Y f)
    (hdeg : branchedDegree h = 1) :
    Function.Bijective f := by
  refine ⟨?_, ?_⟩
  · intro x₁ x₂ heq
    obtain ⟨x, hxs, _⟩ := branchedDegree_one_fiber_singleton h (f x₁) hdeg
    have hx₁ : x₁ = x := by
      have hmem : x₁ ∈ (h.finite_fiber (f x₁)).toFinset := by
        rw [Set.Finite.mem_toFinset]; rfl
      rw [hxs, Finset.mem_singleton] at hmem
      exact hmem
    have hx₂ : x₂ = x := by
      have hmem : x₂ ∈ (h.finite_fiber (f x₁)).toFinset := by
        rw [Set.Finite.mem_toFinset]; exact heq.symm
      rw [hxs, Finset.mem_singleton] at hmem
      exact hmem
    rw [hx₁, hx₂]
  · intro y
    obtain ⟨x, hxs, _⟩ := branchedDegree_one_fiber_singleton h y hdeg
    have hmem : x ∈ (h.finite_fiber y).toFinset := by
      rw [hxs]; exact Finset.mem_singleton_self x
    rw [Set.Finite.mem_toFinset] at hmem
    exact ⟨x, hmem⟩

end JacobianChallenge.Blueprint
