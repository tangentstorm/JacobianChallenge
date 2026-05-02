import Jacobian.Blueprint.Sec02.BranchedDegree

/-! # Blueprint stub: `lem:degree-one-no-ramification`

Section 2 of `tex/sections/02-holomorphic-forms-and-genus.tex`.

A degree-one branched cover is unramified everywhere: at every source
point the ramification index is `1`. Combinatorial heart of the
degree-one ⇒ bijective ⇒ biholomorphism chain.

This stub records the statement using the existing `BranchedCoverData`
API (`Jacobian/Blueprint/Sec02/BranchedDegree.lean`). The proof is the
companion to leaf 7 `branchedDegree_one_fiber_unique`:
weighted-fibre-sum equal to `1` over a finite fibre with
positive-integer summands forces every summand to be `1` (so every
fibre has a single element, and its ramification index is `1`). -/

namespace JacobianChallenge.Blueprint

/-- **MEDIUM.** A degree-one branched cover is unramified at every
source point.

PROOF SKETCH (sorry pending the analytic frontier / structural axiom
on `weightedFiberCard`): for any `x : X`, set `y := f x` and rewrite
`branchedDegree h` via `branchedDegree_eq_weightedFiberCard h y`; the
weighted-fibre sum at `y` equals `1`, the summand
`h.ramificationIndex x` is positive (`h.ramificationIndex_pos x`), and
all summands are positive — so the sum-equals-one forces every
summand (in particular at `x`) to be `1`. -/
theorem degree_one_no_ramification
    {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    {f : X → Y} [Nonempty Y] (h : BranchedCoverData X Y f)
    (_hdeg : branchedDegree h = 1) :
    ∀ x : X, h.ramificationIndex x = 1 := by
  intro x
  have h_one := branchedDegree_one_fiber_singleton h (f x) _hdeg
  obtain ⟨x', hxs, hrx'⟩ := h_one
  have hx_mem : x ∈ (h.finite_fiber (f x)).toFinset := by
    rw [Set.Finite.mem_toFinset]; rfl
  rw [hxs, Finset.mem_singleton] at hx_mem
  rw [hx_mem]
  exact hrx'

end JacobianChallenge.Blueprint
