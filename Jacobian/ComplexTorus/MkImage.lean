import Mathlib.Topology.Algebra.Group.Quotient
import Jacobian.WorkPackets.StatementBank

/-!
# Image lemmas for the quotient projection

Queue B sibling of `Jacobian/ComplexTorus/Basic.lean`.
-/

namespace JacobianChallenge.ComplexTorus

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V]
  (Λ : FullComplexLattice V)

/-- The continuous quotient projection sends compact sets to compact sets. -/
lemma mk_image_isCompact {K : Set V} (hK : IsCompact K) :
    IsCompact (mk V Λ '' K) :=
  hK.image continuous_quotient_mk'

/-- The quotient projection sends open sets to open sets (it is an open map). -/
lemma mk_image_isOpen {U : Set V} (hU : IsOpen U) :
    IsOpen (mk V Λ '' U) :=
  QuotientAddGroup.isOpenMap_coe U hU

end JacobianChallenge.ComplexTorus
