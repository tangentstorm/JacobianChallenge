import Mathlib.Topology.Algebra.Group.Quotient
import Jacobian.WorkPackets.StatementBank

/-!
# Injectivity criterion for the induced quotient map

Queue B sibling of `Jacobian/ComplexTorus/Basic.lean`.

The single bounded packet: when the preimage of `Γ.subgroup` under `f` is
exactly `Λ.subgroup`, the induced map `map Λ Γ f hf` is injective.
-/

namespace JacobianChallenge.ComplexTorus

variable {V W : Type*} [NormedAddCommGroup V] [NormedAddCommGroup W]
  [NormedSpace ℂ V] [NormedSpace ℂ W]
  {Λ : FullComplexLattice V} {Γ : FullComplexLattice W}

/-- If `f⁻¹(Γ.subgroup) ⊆ Λ.subgroup`, the induced quotient map is injective. -/
lemma map_injective_of_preimage_subset {f : V →+ W}
    (hf : ∀ v ∈ Λ.subgroup, f v ∈ Γ.subgroup)
    (hker : ∀ v : V, f v ∈ Γ.subgroup → v ∈ Λ.subgroup) :
    Function.Injective (map Λ Γ f hf) := by
  sorry

end JacobianChallenge.ComplexTorus
