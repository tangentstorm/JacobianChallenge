import Mathlib.Topology.Algebra.Group.Quotient
import Jacobian.ComplexTorus.Defs

/-!
# Injectivity of the quotient projection

Queue B sibling of `Jacobian/ComplexTorus/Basic.lean`.

The quotient projection `mk V Λ` is injective exactly when the lattice
is trivial. This is a useful corner case that future code may need.
-/

namespace JacobianChallenge.ComplexTorus

variable {V : Type*} [NormedAddCommGroup V]
  (Λ : FullComplexLattice V)

/-- `mk V Λ` is injective iff the lattice is the trivial subgroup. -/
lemma mk_injective_iff_subgroup_eq_bot :
    Function.Injective (mk V Λ) ↔ Λ.subgroup = ⊥ := by
  constructor
  · intro h
    ext x
    simp only [AddSubgroup.mem_bot]
    constructor
    · intro hx
      have : (QuotientAddGroup.mk x : V ⧸ Λ.subgroup) = QuotientAddGroup.mk 0 :=
        QuotientAddGroup.eq.mpr (by simp [hx])
      exact h this
    · intro hx
      rw [hx]
      exact Λ.subgroup.zero_mem
  · intro h x y hxy
    have hmem : -x + y ∈ Λ.subgroup := QuotientAddGroup.eq.mp hxy
    rw [h] at hmem
    rw [AddSubgroup.mem_bot, neg_add_eq_zero] at hmem
    exact hmem

end JacobianChallenge.ComplexTorus
