import Jacobian.Blueprint.Sec02.BranchedDegree

/-! # Blueprint stub: `lem:branch-locus-finite`

Section 2 of `tex/sections/02-holomorphic-forms-and-genus.tex`.

The branch locus of a holomorphic map between compact Riemann
surfaces is finite: the set of points where the ramification index
exceeds `1` accumulates nowhere (analytic isolated-zeros applied to
the chart-pulled derivative), so by compactness it is finite.

This stub records the **statement only** (sorry-bearing). The
hypothesis is encoded through `BranchedCoverData` (sibling stub in
`Sec02/BranchedDegree.lean`); the conclusion is a `Set.Finite` claim
on the ramified points in the source `X`. The branch locus *in `Y`*
is the image of this set under `f`, which is then finite as the image
of a finite set.

The proof requires the analytic isolated-zeros theorem (the
ramification-index function is locally constant equal to `1` away
from a discrete set), which is the "single biggest analytic gap"
flagged in `Jacobian/Blueprint/Sec02/BranchedDegree.lean` (leaf 8). -/

namespace JacobianChallenge.Blueprint

/-- The set of ramified points of a `BranchedCoverData` on a compact
source is finite.

PROOF SKETCH (sorry pending the analytic frontier): the chart-pulled
derivative `(ψ ∘ f ∘ φ⁻¹)'` of a nonconstant holomorphic map vanishes
on a discrete subset of each chart (analytic isolated-zeros), so the
ramified set is closed-discrete in `X`; closed-discrete + compact
implies finite. -/
theorem branch_locus_finite
    {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    [CompactSpace X]
    {f : X → Y} (h : BranchedCoverData X Y f) :
    {x : X | h.ramificationIndex x ≠ 1}.Finite := by
  sorry

/-- The branch locus *in the target* — the image under `f` of the
ramified points — is finite, as the image of a finite set. -/
theorem branch_locus_finite_image
    {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    [CompactSpace X]
    {f : X → Y} (h : BranchedCoverData X Y f) :
    (f '' {x : X | h.ramificationIndex x ≠ 1}).Finite :=
  (branch_locus_finite h).image f

end JacobianChallenge.Blueprint
