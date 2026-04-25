import Mathlib.Topology.Algebra.Group.Quotient
import Jacobian.WorkPackets.StatementBank

/-!
# Range and full-image lemmas for the quotient projection

Queue B sibling of `Jacobian/ComplexTorus/Basic.lean`.
-/

namespace JacobianChallenge.ComplexTorus

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V]
  (Λ : FullComplexLattice V)

/-- The range of the quotient projection is everything. -/
@[simp] lemma range_mk : Set.range (mk V Λ) = Set.univ :=
  (mk_surjective V Λ).range_eq

/-- The image of the universal set under `mk` is the universal set. -/
@[simp] lemma mk_image_univ : mk V Λ '' Set.univ = Set.univ :=
  Set.image_univ_of_surjective (mk_surjective V Λ)

end JacobianChallenge.ComplexTorus
