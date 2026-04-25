import Mathlib.Topology.Algebra.Group.Quotient
import Jacobian.WorkPackets.StatementBank
import Jacobian.ComplexTorus.OfClm

/-!
# Injectivity criterion for the continuous-linear quotient map

Queue B sibling of `Jacobian/ComplexTorus/Basic.lean`.

Wraps the additive `map_injective_of_preimage_subset` for the
continuous-linear-map version `mapClm`.
-/

namespace JacobianChallenge.ComplexTorus

variable {V W : Type*} [NormedAddCommGroup V] [NormedAddCommGroup W]
  [NormedSpace ℂ V] [NormedSpace ℂ W]
  {Λ : FullComplexLattice V} {Γ : FullComplexLattice W}

/-- If `f⁻¹(Γ.subgroup) ⊆ Λ.subgroup`, the continuous-linear-induced
quotient map is injective. -/
lemma mapClm_injective_of_preimage_subset (f : V →L[ℂ] W)
    (hf : ∀ v ∈ Λ.subgroup, f v ∈ Γ.subgroup)
    (hker : ∀ v : V, f v ∈ Γ.subgroup → v ∈ Λ.subgroup) :
    Function.Injective (mapClm f hf) := by
  sorry

end JacobianChallenge.ComplexTorus
