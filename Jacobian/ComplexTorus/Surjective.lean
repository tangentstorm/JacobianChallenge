import Mathlib.Topology.Algebra.Group.Quotient
import Jacobian.ComplexTorus.Defs

/-!
# Surjectivity of the induced quotient map

This file is a Queue B sibling of `Jacobian/ComplexTorus/Basic.lean`.

The single bounded packet here is: a surjective homomorphism `f : V →+ W`
descends to a surjective homomorphism between the corresponding quotient
tori, regardless of which lattices we choose, as long as the lattice
condition holds.
-/

namespace JacobianChallenge.ComplexTorus

variable {V W : Type*} [NormedAddCommGroup V] [NormedAddCommGroup W]
  {Λ : FullComplexLattice V} {Γ : FullComplexLattice W}

/-- If `f : V →+ W` is surjective and lattice-preserving, the induced quotient
homomorphism is surjective. -/
lemma map_surjective [NormedSpace ℂ V] [NormedSpace ℂ W]
    {f : V →+ W} (hf_surj : Function.Surjective f)
    (hf : ∀ v ∈ Λ.subgroup, f v ∈ Γ.subgroup) :
    Function.Surjective (map Λ Γ f hf) := by
  intro q
  obtain ⟨w, hw⟩ := mk_surjective W Γ q
  obtain ⟨v, hv⟩ := hf_surj w
  exact ⟨mk V Λ v, by rw [map_mk, hv, hw]⟩

end JacobianChallenge.ComplexTorus
