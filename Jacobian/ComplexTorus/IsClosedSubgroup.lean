import Mathlib.Topology.Algebra.Group.Quotient
import Jacobian.WorkPackets.StatementBank

/-!
# Closedness of the lattice gives `T2` on the quotient

This file is a Queue B sibling of `Jacobian/ComplexTorus/Basic.lean`.

The single bounded packet: when `Λ.subgroup` is a closed subgroup of a
topological additive group `V`, the quotient `V ⧸ Λ.subgroup` is `T2`
without needing to read this off the `FullComplexLattice` field. This
lets us re-derive `Λ.quotient_t2` from `Λ.isClosed` alone.

The intent is to eventually replace the `quotient_t2` field of
`FullComplexLattice` with this derived instance, but for now we only need
a stand-alone lemma.
-/

namespace JacobianChallenge.ComplexTorus

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V]
  (Λ : FullComplexLattice V)

/-- A closed lattice gives a `T2` quotient. -/
lemma t2Space_quotient_of_isClosed
    (h : IsClosed (Λ.subgroup : Set V)) :
    T2Space (quotient V Λ) := by
  sorry

end JacobianChallenge.ComplexTorus
