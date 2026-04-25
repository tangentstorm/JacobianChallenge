import Mathlib.Topology.Algebra.Group.Quotient
import Jacobian.ComplexTorus.Defs

/-!
# Helper lemmas for the induced quotient map

This file is a Queue B sibling of `Jacobian/ComplexTorus/Basic.lean`. It
collects bounded simp-style lemmas about
`map Λ Γ f hf : V ⧸ Λ.subgroup →+ W ⧸ Γ.subgroup`,
the descent of a lattice-preserving additive homomorphism. Keep the proofs
short and direct.
-/

namespace JacobianChallenge.ComplexTorus

variable {V W : Type*} [NormedAddCommGroup V] [NormedAddCommGroup W]
  [NormedSpace ℂ V] [NormedSpace ℂ W]
  {Λ : FullComplexLattice V} {Γ : FullComplexLattice W}

/-- The induced map sends the zero class to the zero class. -/
@[simp] lemma map_zero (f : V →+ W)
    (hf : ∀ v ∈ Λ.subgroup, f v ∈ Γ.subgroup) :
    map Λ Γ f hf 0 = 0 :=
  (map Λ Γ f hf).map_zero

/-- The induced map distributes over addition of representatives via `mk`. -/
lemma map_mk_add (f : V →+ W)
    (hf : ∀ v ∈ Λ.subgroup, f v ∈ Γ.subgroup) (v w : V) :
    map Λ Γ f hf (mk V Λ (v + w)) =
      map Λ Γ f hf (mk V Λ v) + map Λ Γ f hf (mk V Λ w) := by
  simp only [map_mk]
  rw [f.map_add]
  rfl

end JacobianChallenge.ComplexTorus
