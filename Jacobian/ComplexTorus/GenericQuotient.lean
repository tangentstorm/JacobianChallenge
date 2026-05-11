import Mathlib.Topology.Algebra.Group.Quotient

/-!
# Generic `AddSubgroup`-quotient lemmas, independent of `FullComplexLattice`

Queue B sibling. The lemmas here intentionally avoid `FullComplexLattice`
so they can be reused in other settings (and so the `FullComplexLattice`
wrappers stay thin). Each lemma is a small wrapper around an existing
Mathlib fact, but having them named locally lets the rest of the project
refer to them by short, layer-specific names.
-/

namespace JacobianChallenge.ComplexTorus

open Filter Topology

variable {G : Type*} [AddCommGroup G] (N : AddSubgroup G)

/-- The quotient projection `G → G ⧸ N` is surjective. -/
lemma mk_surjective' :
    Function.Surjective (QuotientAddGroup.mk : G → G ⧸ N) :=
  QuotientAddGroup.mk_surjective

/-- `mk x = mk y` iff `-x + y ∈ N`. -/
lemma mk_eq_iff' {x y : G} :
    (QuotientAddGroup.mk x : G ⧸ N) = QuotientAddGroup.mk y ↔ -x + y ∈ N :=
  QuotientAddGroup.eq

variable [TopologicalSpace G]

/-- The quotient projection `G → G ⧸ N` is continuous. -/
lemma continuous_mk' : Continuous (QuotientAddGroup.mk : G → G ⧸ N) :=
  continuous_quotient_mk'

variable [IsTopologicalAddGroup G]

/-- The quotient projection `G → G ⧸ N` is an open quotient map. -/
lemma isOpenQuotientMap_mk' :
    IsOpenQuotientMap (QuotientAddGroup.mk : G → G ⧸ N) :=
  QuotientAddGroup.isOpenQuotientMap_mk

end JacobianChallenge.ComplexTorus
