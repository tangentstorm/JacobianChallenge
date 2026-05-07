import Jacobian.HolomorphicForms.BranchedCover

/-!
# Blueprint compatibility shim for `def:branched-degree`

The proof-bearing declarations have been promoted to
`Jacobian.HolomorphicForms.BranchedCover`.  This file remains as a blueprint
entry point so older blueprint scaffolds can keep importing the section name
without making production code depend on `Jacobian.Blueprint`.
-/

namespace JacobianChallenge.Blueprint

export JacobianChallenge.HolomorphicForms
  (ramificationIndexStub
   BranchedCoverData
   branchedDegree
   branchedDegree_eq_weightedFiberCard
   branchedDegree_pos
   branchedDegree_eq_card_toFinset_of_unramified_fiber
   branchedDegree_one_fiber_singleton
   branchedDegree_one_fiber_unique)

namespace BranchedCoverData

/-- Compatibility alias for the promoted derived weighted fibre count. -/
noncomputable abbrev weightedFiberCard
    {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    {f : X → Y} (h : BranchedCoverData X Y f) (y : Y) : ℕ :=
  JacobianChallenge.HolomorphicForms.BranchedCoverData.weightedFiberCard h y

/-- Compatibility alias for the promoted constancy theorem. -/
theorem weightedFiberCard_const
    {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    {f : X → Y} (h : BranchedCoverData X Y f) (y₁ y₂ : Y) :
    h.weightedFiberCard y₁ = h.weightedFiberCard y₂ :=
  JacobianChallenge.HolomorphicForms.BranchedCoverData.weightedFiberCard_const h y₁ y₂

end BranchedCoverData

end JacobianChallenge.Blueprint
