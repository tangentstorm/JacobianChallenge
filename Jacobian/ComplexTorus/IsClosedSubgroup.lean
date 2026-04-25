import Mathlib.Topology.Algebra.Group.Quotient
import Jacobian.ComplexTorus.Defs

/-!
# Closedness of the lattice gives `T2` on the quotient

This file is a Queue B sibling of `Jacobian/ComplexTorus/Basic.lean`.

When `Λ.subgroup` is a closed subgroup of a topological additive group
`V`, the quotient `V ⧸ Λ.subgroup` is `T2`. After the
`FullComplexLattice` refactor that dropped the `quotient_t2` field,
this is the load-bearing derivation: the structure-level
`quotient_t2Space` instance in `StatementBank.lean` is exactly the
proof below packaged with `Λ.isClosed` plugged in.
-/

namespace JacobianChallenge.ComplexTorus

/-- An abstract closed-subgroup version: if `N : AddSubgroup V` is closed,
the quotient `V ⧸ N` is `T2`. This is the genuinely load-bearing fact
behind the structure-level `quotient_t2Space` instance in
`StatementBank.lean` — that instance just plugs in `Λ.isClosed` and
invokes Mathlib's `QuotientGroup.instT1Space`. -/
lemma t2Space_quotient_of_isClosed_subgroup
    {V : Type*} [NormedAddCommGroup V] {N : AddSubgroup V}
    (h : IsClosed (N : Set V)) :
    T2Space (V ⧸ N) := by
  haveI : IsClosed (N : Set V) := h
  exact inferInstance

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V]
  (Λ : FullComplexLattice V)

/-- The complex-torus quotient is `T2`. Wrapper around
`t2Space_quotient_of_isClosed_subgroup` plugging in `Λ.isClosed`. -/
lemma t2Space_quotient_of_isClosed
    (h : IsClosed (Λ.subgroup : Set V)) :
    T2Space (quotient V Λ) :=
  t2Space_quotient_of_isClosed_subgroup h

end JacobianChallenge.ComplexTorus
