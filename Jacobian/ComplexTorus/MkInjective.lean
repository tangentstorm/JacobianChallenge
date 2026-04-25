import Mathlib.Topology.Algebra.Group.Quotient
import Jacobian.WorkPackets.StatementBank

/-!
# Injectivity of the quotient projection

Queue B sibling of `Jacobian/ComplexTorus/Basic.lean`.

The quotient projection `mk V Λ` is injective exactly when the lattice
is trivial. This is a useful corner case that future code may need.
-/

namespace JacobianChallenge.ComplexTorus

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V]
  (Λ : FullComplexLattice V)

/-- `mk V Λ` is injective iff the lattice is the trivial subgroup. -/
lemma mk_injective_iff_subgroup_eq_bot :
    Function.Injective (mk V Λ) ↔ Λ.subgroup = ⊥ := by
  sorry

end JacobianChallenge.ComplexTorus
