import Mathlib.Topology.Algebra.Group.Quotient
import Jacobian.ComplexTorus.Defs

/-! # Bounded helper lemmas for the quotient projection -/

namespace JacobianChallenge.ComplexTorus

variable {V : Type*} [NormedAddCommGroup V]
  (Λ : FullComplexLattice V)

/-- The quotient projection sends `0` to `0`. -/
@[simp] lemma mk_zero : mk V Λ 0 = 0 := rfl

/--
Two representatives map to the same class iff their difference lies in
the lattice.
-/
lemma mk_eq_iff {v w : V} :
    mk V Λ v = mk V Λ w ↔ -v + w ∈ Λ.subgroup :=
  QuotientAddGroup.eq

/-- A representative is in the kernel of `mk` iff it lies in the lattice. -/
lemma mk_eq_zero_iff {v : V} :
    mk V Λ v = 0 ↔ v ∈ Λ.subgroup := by
  rw [show (0 : quotient V Λ) = mk V Λ 0 from rfl, mk_eq_iff, add_zero,
    Λ.subgroup.neg_mem_iff]

end JacobianChallenge.ComplexTorus
