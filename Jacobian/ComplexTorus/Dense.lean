import Mathlib.Topology.Algebra.Group.Quotient
import Jacobian.WorkPackets.StatementBank

/-!
# Density on the complex-torus quotient

Queue B sibling of `Jacobian/ComplexTorus/Basic.lean`.

The image of a dense set under `mk` is dense exactly when the set is
dense modulo the lattice. This is a useful descriptor for density of
periodic patterns inside the torus.
-/

namespace JacobianChallenge.ComplexTorus

open scoped Pointwise

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V]
  (Λ : FullComplexLattice V)

/-- A subset of `V` projects to a dense subset of the torus iff it is
dense modulo the lattice. -/
lemma dense_mk_image_iff (s : Set V) :
    Dense (mk V Λ '' s) ↔ Dense (s + (Λ.subgroup : Set V)) := by
  sorry

/-- Equivalently: the preimage of a dense set in the torus is dense. -/
lemma dense_preimage_mk_iff (s : Set (quotient V Λ)) :
    Dense (mk V Λ ⁻¹' s) ↔ Dense s := by
  sorry

end JacobianChallenge.ComplexTorus
