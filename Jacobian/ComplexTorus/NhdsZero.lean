import Mathlib.Topology.Algebra.Group.Quotient
import Jacobian.WorkPackets.StatementBank

/-!
# Neighborhood basis at zero in a complex-lattice quotient

This file is a Queue B sibling of `Jacobian/ComplexTorus/Basic.lean`.

The single bounded packet: the filter `𝓝 0` on the torus quotient is the
push-forward of `𝓝 0` on the ambient vector space along the quotient map.
This is just the topological-quotient nhds equation specialised to `0`.
-/

namespace JacobianChallenge.ComplexTorus

open Filter Topology

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V]
  (Λ : FullComplexLattice V)

/-- Neighborhoods of `0` in the torus quotient are pushed forward from
neighborhoods of `0` in `V`. -/
lemma nhds_zero_eq :
    𝓝 (0 : quotient V Λ) = Filter.map (mk V Λ) (𝓝 (0 : V)) := by
  sorry

end JacobianChallenge.ComplexTorus
