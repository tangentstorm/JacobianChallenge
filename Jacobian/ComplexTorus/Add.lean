import Mathlib.Topology.Algebra.Group.Quotient
import Jacobian.WorkPackets.StatementBank

/-!
# Addition on the complex-torus quotient

Queue B sibling of `Jacobian/ComplexTorus/Basic.lean`.

Two bounded packets: `mk_add` (a quotient simp lemma) and the continuity of
binary addition on `quotient V Λ`.
-/

namespace JacobianChallenge.ComplexTorus

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V]
  (Λ : FullComplexLattice V)

/-- The quotient projection commutes with addition. -/
@[simp] lemma mk_add (v w : V) :
    mk V Λ (v + w) = mk V Λ v + mk V Λ w := by
  sorry

/-- Addition on the complex-torus quotient is continuous. -/
lemma continuous_add :
    Continuous (fun p : quotient V Λ × quotient V Λ => p.1 + p.2) := by
  sorry

end JacobianChallenge.ComplexTorus
