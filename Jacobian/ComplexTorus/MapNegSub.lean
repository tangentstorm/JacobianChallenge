import Mathlib.Topology.Algebra.Group.Quotient
import Jacobian.ComplexTorus.Defs

/-!
# Negation and subtraction lemmas for the induced quotient map

Queue B sibling of `Jacobian/ComplexTorus/Basic.lean`.

These are direct consequences of `map Λ Γ f hf` being an additive group
homomorphism; they're stated separately for convenient `simp` lookup.
-/

namespace JacobianChallenge.ComplexTorus

variable {V W : Type*} [NormedAddCommGroup V] [NormedAddCommGroup W]
  [NormedSpace ℂ V] [NormedSpace ℂ W]
  {Λ : FullComplexLattice V} {Γ : FullComplexLattice W}

/-- The induced quotient map commutes with negation. -/
@[simp] lemma map_neg (f : V →+ W)
    (hf : ∀ v ∈ Λ.subgroup, f v ∈ Γ.subgroup) (q : quotient V Λ) :
    map Λ Γ f hf (-q) = -(map Λ Γ f hf q) :=
  (map Λ Γ f hf).map_neg q

/-- The induced quotient map commutes with subtraction. -/
@[simp] lemma map_sub (f : V →+ W)
    (hf : ∀ v ∈ Λ.subgroup, f v ∈ Γ.subgroup) (q p : quotient V Λ) :
    map Λ Γ f hf (q - p) = map Λ Γ f hf q - map Λ Γ f hf p :=
  (map Λ Γ f hf).map_sub q p

end JacobianChallenge.ComplexTorus
