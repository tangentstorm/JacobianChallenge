import Mathlib.Topology.Algebra.Group.Quotient
import Jacobian.ComplexTorus.Defs

/-!
# Preimage lemmas for the quotient projection

Queue B sibling of `Jacobian/ComplexTorus/Basic.lean`.
-/

namespace JacobianChallenge.ComplexTorus

variable {V : Type*} [NormedAddCommGroup V]
  (Λ : FullComplexLattice V)

/-- The preimage of an open set under `mk` is open (mk is continuous). -/
lemma mk_preimage_isOpen {U : Set (quotient V Λ)} (hU : IsOpen U) :
    IsOpen (mk V Λ ⁻¹' U) :=
  hU.preimage continuous_quotient_mk'

/-- The preimage of a closed set under `mk` is closed (mk is continuous). -/
lemma mk_preimage_isClosed {C : Set (quotient V Λ)} (hC : IsClosed C) :
    IsClosed (mk V Λ ⁻¹' C) :=
  hC.preimage continuous_quotient_mk'

end JacobianChallenge.ComplexTorus
