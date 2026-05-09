import Mathlib.Topology.Algebra.Group.Quotient
import Mathlib.Topology.Defs.Induced
import Jacobian.ComplexTorus.Defs

set_option linter.unusedSectionVars false

/-!
# Topological API for full complex lattice quotients

This file is the first narrow Queue B target. It collects bounded, file-scoped
lemmas about the quotient projection `mk : V → V ⧸ Λ.subgroup` for a
`FullComplexLattice Λ`, building on the algebraic API in
`Jacobian/ComplexTorus/Defs.lean`.
-/

namespace JacobianChallenge.ComplexTorus

variable {V W : Type*} [NormedAddCommGroup V] [NormedAddCommGroup W]
  [NormedSpace ℂ V] [NormedSpace ℂ W]
  (Λ : FullComplexLattice V) (Γ : FullComplexLattice W)

omit [NormedSpace ℂ V] [NormedAddCommGroup W] [NormedSpace ℂ W] in
/-- The quotient projection is continuous. -/
lemma mk_continuous : Continuous (mk V Λ) :=
  QuotientAddGroup.continuous_mk

omit [NormedSpace ℂ V] [NormedAddCommGroup W] [NormedSpace ℂ W] in
/-- The quotient projection is an open quotient map. -/
lemma mk_isOpenQuotientMap : IsOpenQuotientMap (mk V Λ) :=
  QuotientAddGroup.isOpenQuotientMap_mk

omit [NormedSpace ℂ V] [NormedAddCommGroup W] [NormedSpace ℂ W] in
/-- The quotient projection is an open map. -/
lemma mk_isOpenMap : IsOpenMap (mk V Λ) :=
  QuotientAddGroup.isOpenMap_coe

/-! ### Continuity of the induced quotient map

A continuous additive homomorphism `f : V →+ W` that preserves the chosen
lattices descends to a continuous additive homomorphism between the quotient
tori. The continuity is the first new bounded packet on top of the algebraic
`map` that the statement bank already provides.
-/

variable {Λ Γ}

omit [NormedSpace ℂ V] [NormedSpace ℂ W] in
/-- The induced map between two complex tori is continuous when the underlying
group homomorphism is continuous and lattice-preserving. -/
lemma map_continuous {f : V →+ W} (hf_cont : Continuous f)
    (hf : ∀ v ∈ Λ.subgroup, f v ∈ Γ.subgroup) :
    Continuous (map Λ Γ f hf) :=
  (mk_isOpenQuotientMap Λ).isQuotientMap.continuous_iff.mpr
    ((mk_continuous Γ).comp hf_cont)

end JacobianChallenge.ComplexTorus
