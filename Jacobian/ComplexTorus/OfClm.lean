import Mathlib.Topology.Algebra.Group.Quotient
import Jacobian.WorkPackets.StatementBank
import Jacobian.ComplexTorus.Basic

/-!
# Quotient map induced by a continuous linear map

Queue B sibling of `Jacobian/ComplexTorus/Basic.lean`.

A continuous linear map `V →L[ℂ] W` that maps `Λ.subgroup` into `Γ.subgroup`
gives a continuous additive homomorphism between the two complex tori.
This bundles the algebraic descent (already in the statement bank) with
continuity.
-/

namespace JacobianChallenge.ComplexTorus

variable {V W : Type*} [NormedAddCommGroup V] [NormedAddCommGroup W]
  [NormedSpace ℂ V] [NormedSpace ℂ W]
  {Λ : FullComplexLattice V} {Γ : FullComplexLattice W}

/-- A continuous linear map descends to a continuous additive homomorphism
between complex tori, given that it preserves the lattices. -/
def mapClm (f : V →L[ℂ] W)
    (hf : ∀ v ∈ Λ.subgroup, f v ∈ Γ.subgroup) :
    quotient V Λ →+ quotient W Γ :=
  map Λ Γ f.toAddMonoidHom hf

/-- The quotient map induced by a continuous linear map is continuous. -/
lemma mapClm_continuous (f : V →L[ℂ] W)
    (hf : ∀ v ∈ Λ.subgroup, f v ∈ Γ.subgroup) :
    Continuous (mapClm f hf) :=
  map_continuous f.continuous hf

end JacobianChallenge.ComplexTorus
