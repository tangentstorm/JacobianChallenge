import Jacobian.Blueprint.Sec02.BranchedDegree
import Jacobian.HolomorphicForms.CotangentBundle

/-! # Blueprint stub: `thm:local-biholo-unramified`

Section 2 of `tex/sections/02-holomorphic-forms-and-genus.tex`.

A holomorphic map between complex 1-manifolds is a *local
biholomorphism* at every unramified point. The classical proof uses
the inverse function theorem applied to the chart-pulled function
`ψ ∘ f ∘ φ⁻¹ : ℂ → ℂ`: the holomorphic Jacobian at the chart image
of an unramified point is nonzero, so by `HasFDerivAt.localHomeomorph`
(Mathlib) the chart-pulled function is locally a homeomorphism, and
holomorphicity of the inverse follows from the Cauchy-Riemann
equations.

This stub records the **statement only** (sorry-bearing, as MEDIUM
classification allows). It packages the unramified hypothesis through
`BranchedCoverData` (sibling stub, leaf 1 / leaf 2 of
`def:branched-degree`) so the existing branched-degree chain plugs in
without further plumbing. The conclusion is the abstract
"there exist open neighbourhoods `U ∋ x` and `V ∋ f x` with `f`
restricting to a bijection `U → V`"; the upgrade to a full
biholomorphism (continuity of the inverse + holomorphicity) is a
follow-up node once `PartialHomeomorph`/biholomorphism API stabilises
in the project. -/

namespace JacobianChallenge.Blueprint

open scoped Manifold

/-- A holomorphic map between complex 1-manifolds is locally a
homeomorphism around every unramified point: there exist open
neighbourhoods `U ∋ x` and `V ∋ f x` such that `f` restricts to a
bijection `U → V`.

The unramified hypothesis is encoded as `h.ramificationIndex x = 1`
relative to a packaged `BranchedCoverData` (sibling stub in
`Sec02/BranchedDegree.lean`). The sorry is the inverse-function-
theorem-on-charts argument; once the project's biholomorphism API
lands the conclusion can be strengthened to a full `PartialHomeomorph`
with holomorphic inverse. -/
theorem local_biholo_unramified
    (X Y : Type*) [TopologicalSpace X] [TopologicalSpace Y]
    [ChartedSpace ℂ X] [ChartedSpace ℂ Y]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) Y]
    {f : X → Y} (h : BranchedCoverData X Y f)
    (x : X) (_hunram : h.ramificationIndex x = 1) :
    ∃ U : Set X, ∃ V : Set Y,
      IsOpen U ∧ IsOpen V ∧ x ∈ U ∧ f x ∈ V ∧ Set.BijOn f U V := by
  sorry

end JacobianChallenge.Blueprint
