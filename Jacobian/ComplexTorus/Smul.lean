import Mathlib.Topology.Algebra.Group.Quotient
import Jacobian.ComplexTorus.Defs

/-!
# Integer scalar action on the complex-torus quotient

Queue B sibling of `Jacobian/ComplexTorus/Basic.lean`.

The single bounded packet: integer scalar multiplication descends to the
quotient compatibly with the quotient projection.
-/

namespace JacobianChallenge.ComplexTorus

variable {V : Type*} [NormedAddCommGroup V]
  (Λ : FullComplexLattice V)

/-- The quotient projection commutes with integer scalar multiplication. -/
@[simp] lemma mk_zsmul (n : ℤ) (v : V) :
    mk V Λ (n • v) = n • mk V Λ v :=
  map_zsmul (QuotientAddGroup.mk' Λ.subgroup) n v

/-- The quotient projection commutes with natural-number scalar
multiplication. -/
@[simp] lemma mk_nsmul (n : ℕ) (v : V) :
    mk V Λ (n • v) = n • mk V Λ v :=
  map_nsmul (QuotientAddGroup.mk' Λ.subgroup) n v

end JacobianChallenge.ComplexTorus
