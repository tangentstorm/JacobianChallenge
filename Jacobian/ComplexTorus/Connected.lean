import Mathlib.Analysis.Normed.Module.Convex
import Mathlib.Topology.Algebra.Group.Quotient
import Jacobian.ComplexTorus.Defs

/-!
# Connectedness of the complex-torus quotient

Queue B sibling of `Jacobian/ComplexTorus/Basic.lean`.

A normed `ℂ`-space is connected (in fact path-connected via convex
combinations through `0`); the quotient by any closed subgroup is the
continuous image of a connected space under a surjection, hence connected.
-/

namespace JacobianChallenge.ComplexTorus

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V]
  (Λ : FullComplexLattice V)

/-- The complex-torus quotient is connected. -/
instance connectedSpace_quotient : ConnectedSpace (quotient V Λ) :=
  (mk_surjective V Λ).connectedSpace QuotientAddGroup.continuous_mk

end JacobianChallenge.ComplexTorus
