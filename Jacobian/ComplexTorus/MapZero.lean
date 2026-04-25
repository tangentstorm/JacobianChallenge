import Mathlib.Topology.Algebra.Group.Quotient
import Jacobian.WorkPackets.StatementBank
import Jacobian.ComplexTorus.OfClm

/-!
# The zero continuous-linear map descends to the zero quotient map

Queue B sibling of `Jacobian/ComplexTorus/Basic.lean`.

A trivial corner case: `mapClm` of the zero continuous linear map is
the constant-zero quotient map.
-/

namespace JacobianChallenge.ComplexTorus

variable {V W : Type*} [NormedAddCommGroup V] [NormedAddCommGroup W]
  [NormedSpace ℂ V] [NormedSpace ℂ W]
  {Λ : FullComplexLattice V} {Γ : FullComplexLattice W}

/-- Hypothesis that the zero continuous-linear map preserves any pair of
lattices (it sends everything to 0, which is in any subgroup). -/
lemma zero_preserves_lattices :
    ∀ v ∈ Λ.subgroup, (0 : V →L[ℂ] W) v ∈ Γ.subgroup := by
  sorry

/-- The zero continuous-linear map descends to the zero quotient map. -/
@[simp] lemma mapClm_zero :
    mapClm (0 : V →L[ℂ] W) (zero_preserves_lattices (Λ := Λ) (Γ := Γ)) = 0 := by
  sorry

end JacobianChallenge.ComplexTorus
