import Mathlib.Topology.Algebra.Group.Quotient
import Jacobian.WorkPackets.StatementBank

/-!
# Bundled additive monoid hom for the quotient projection

Queue B sibling of `Jacobian/ComplexTorus/Basic.lean`.

The quotient projection is intrinsically a group homomorphism. This file
re-exposes Mathlib's `QuotientAddGroup.mk'` under our local naming so other
files can use `mkHom` without reaching into the Mathlib namespace.
-/

namespace JacobianChallenge.ComplexTorus

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V]
  (Λ : FullComplexLattice V)

/-- The quotient projection as an additive group homomorphism. -/
def mkHom : V →+ quotient V Λ := by
  sorry

/-- `mkHom` agrees with `mk` on representatives. -/
@[simp] lemma mkHom_apply (v : V) : mkHom Λ v = mk V Λ v := by
  sorry

end JacobianChallenge.ComplexTorus
