import Mathlib.Topology.Algebra.Group.Quotient
import Jacobian.WorkPackets.StatementBank

/-!
# Neighborhoods at an arbitrary point of the complex-torus quotient

Queue B sibling of `Jacobian/ComplexTorus/Basic.lean`.

`NhdsZero.lean` already covers the special case `mk V Λ 0`. This file
generalises to any point `mk V Λ v`.
-/

namespace JacobianChallenge.ComplexTorus

open Filter Topology

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V]
  (Λ : FullComplexLattice V)

/-- Neighborhoods of any point in the complex-torus quotient are pushed
forward from neighborhoods of a representative in `V`. -/
lemma nhds_mk_eq (v : V) :
    𝓝 (mk V Λ v) = Filter.map (mk V Λ) (𝓝 v) :=
  QuotientAddGroup.nhds_eq Λ.subgroup v

end JacobianChallenge.ComplexTorus
