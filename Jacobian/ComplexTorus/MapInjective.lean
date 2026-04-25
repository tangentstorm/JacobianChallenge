import Mathlib.Topology.Algebra.Group.Quotient
import Jacobian.WorkPackets.StatementBank
import Jacobian.ComplexTorus.Mk

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
  intro q₁ q₂ h
  obtain ⟨v₁, rfl⟩ := mk_surjective V Λ q₁
  obtain ⟨v₂, rfl⟩ := mk_surjective V Λ q₂
  rw [map_mk, map_mk, mk_eq_iff] at h
  rw [mk_eq_iff]
  apply hker
  rw [f.map_add, f.map_neg]
  exact h

end JacobianChallenge.ComplexTorus
