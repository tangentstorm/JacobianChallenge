import Mathlib.Topology.Algebra.Group.Quotient
import Jacobian.ComplexTorus.Defs

/-!
# Negation on the complex-torus quotient

Queue B sibling of `Jacobian/ComplexTorus/Basic.lean`.

Two bounded packets: `mk_neg` (a quotient simp lemma) and the continuity of
negation on `quotient V Λ`.
-/

namespace JacobianChallenge.ComplexTorus

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V]
  (Λ : FullComplexLattice V)

/-- The quotient projection commutes with negation. -/
@[simp] lemma mk_neg (v : V) : mk V Λ (-v) = -mk V Λ v := rfl

/-- Negation on the complex-torus quotient is continuous. -/
lemma continuous_neg : Continuous (Neg.neg : quotient V Λ → quotient V Λ) :=
  ContinuousNeg.continuous_neg

end JacobianChallenge.ComplexTorus
