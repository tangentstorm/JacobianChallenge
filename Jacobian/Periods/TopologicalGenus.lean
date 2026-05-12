/-
Copyright (c) 2025 Jacobian Challenge contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Jacobian.Periods.IntegralOneCycle
import Jacobian.Periods.PrismChainHomotopy
import Mathlib.Algebra.Category.ModuleCat.Colimits
import Mathlib.Algebra.Category.ModuleCat.Abelian
import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.AlgebraicTopology.SingularHomology.Basic
import Mathlib.Algebra.Homology.Homotopy
import Mathlib.Topology.Category.TopCat.Basic
import Mathlib.Topology.Homotopy.Contractible
import Mathlib.Topology.Homotopy.Equiv

/-!
# Topological genus via singular homology

We define the **topological genus** of a compact connected topological space `M`
as half the ℤ-rank of its first singular homology group H₁(M; ℤ).

For a compact connected oriented 2-manifold (surface of genus g), this equals g.
For non-orientable or non-compact spaces the value is meaningless,
but the definition is still well-typed.

## Main definitions

* `JacobianChallenge.Periods.singularH1` — the first singular homology H₁(M; ℤ)
  as a type carrying `AddCommGroup` and `Module ℤ` instances. By design
  this is just `IntegralOneCycle M` re-exposed as a `Type` so the canonical
  `topologicalGenus` here unifies definitionally with the duplicate
  declaration in `Jacobian.Periods.PeriodFunctional`.
* `JacobianChallenge.Periods.topologicalGenus` — `Module.finrank ℤ H₁(M; ℤ) / 2`.
-/

noncomputable section

namespace JacobianChallenge.Periods

open AlgebraicTopology CategoryTheory HomologicalComplex

/-- The first singular homology of `M` with ℤ-coefficients, viewed as a
ℤ-module type. Defined as the coercion of `IntegralOneCycle M` (a
`ModuleCat ℤ` object) to its underlying `Type` — this makes
`singularH1 M = IntegralOneCycle M` reducible by `abbrev`, so the two
parallel `topologicalGenus` formulations across the project unify
definitionally. -/
abbrev singularH1 (M : Type) [TopologicalSpace M] : Type :=
  IntegralOneCycle M

instance singularH1.addCommGroup (M : Type) [TopologicalSpace M] :
    AddCommGroup (singularH1 M) :=
  ModuleCat.isAddCommGroup _

instance singularH1.module (M : Type) [TopologicalSpace M] :
    Module ℤ (singularH1 M) :=
  ModuleCat.isModule _

/-- The induced ℤ-linear map `singularH1 X →ₗ[ℤ] singularH1 Y` from a
continuous map `f : X → Y`, defined as the degree-1 homology component
of the singular chain complex functor applied to `f`. -/
noncomputable def singularH1_inducedLinearMap
    {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
    (f : C(X, Y)) : singularH1 X →ₗ[ℤ] singularH1 Y :=
  (((AlgebraicTopology.singularHomologyFunctor (ModuleCat ℤ) 1).obj
      (ModuleCat.of ℤ ℤ)).map (TopCat.ofHom f)).hom

/-- Identity functoriality of `singularH1_inducedLinearMap`. -/
theorem singularH1_inducedLinearMap_id (X : Type) [TopologicalSpace X] :
    singularH1_inducedLinearMap (X := X) (Y := X) (ContinuousMap.id X) =
      LinearMap.id := by
  simp [singularH1_inducedLinearMap, TopCat.ofHom_id, ModuleCat.hom_id]

/-- Composition functoriality of `singularH1_inducedLinearMap`. -/
theorem singularH1_inducedLinearMap_comp
    {X Y Z : Type} [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z]
    (f : C(X, Y)) (g : C(Y, Z)) :
    singularH1_inducedLinearMap (g.comp f) =
      (singularH1_inducedLinearMap g).comp (singularH1_inducedLinearMap f) := by
  simp [singularH1_inducedLinearMap, TopCat.ofHom_comp, ModuleCat.hom_comp]

/-- **Stage A leaf (prism construction).** Homotopy invariance of
`singularH1_inducedLinearMap`: homotopic maps induce equal `H₁`-maps. -/
theorem singularH1_inducedLinearMap_eq_of_homotopic
    {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
    {f g : C(X, Y)} (H : ContinuousMap.Homotopy f g) :
    singularH1_inducedLinearMap f = singularH1_inducedLinearMap g := by
  simp only [singularH1_inducedLinearMap]
  suffices h : Homotopy
      (((AlgebraicTopology.singularChainComplexFunctor (ModuleCat ℤ)).obj
          (ModuleCat.of ℤ ℤ)).map (TopCat.ofHom f))
      (((AlgebraicTopology.singularChainComplexFunctor (ModuleCat ℤ)).obj
          (ModuleCat.of ℤ ℤ)).map (TopCat.ofHom g)) by
    exact congrArg ModuleCat.Hom.hom (h.homologyMap_eq 1)
  exact (prism_chainHomotopy_exists H).some

/-- Topological genus of a compact connected 2-manifold, defined as
half the ℤ-rank of singular H₁. The definition is `noncomputable`
and is intended for compact connected oriented 2-manifolds; for
non-orientable or non-compact spaces the value is meaningless. -/
noncomputable def topologicalGenus
    (M : Type) [TopologicalSpace M] [CompactSpace M] [ConnectedSpace M] :
    ℕ :=
  Module.finrank ℤ (singularH1 M) / 2

private instance unit_totallyDisconnected : TotallyDisconnectedSpace Unit :=
  ⟨fun _ _ _ => Set.subsingleton_of_subsingleton⟩

theorem singularH1_unit_subsingleton : Subsingleton (singularH1 Unit) :=
  ModuleCat.subsingleton_of_isZero <|
    AlgebraicTopology.isZero_singularHomologyFunctor_of_totallyDisconnectedSpace
      (ModuleCat ℤ) 1 (ModuleCat.of ℤ ℤ) (TopCat.of Unit) one_ne_zero

/-- **Stage A leaf (homotopy invariance, ℤ-linear iso form).** A homotopy
equivalence `X ≃ₕ Y` induces a ℤ-linear isomorphism `singularH1 X ≃ₗ[ℤ] singularH1 Y`. -/
theorem singularH1_iso_of_homotopyEquiv {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
    (h : ContinuousMap.HomotopyEquiv X Y) :
    Nonempty (singularH1 X ≃ₗ[ℤ] singularH1 Y) := by
  refine ⟨LinearEquiv.ofLinear (singularH1_inducedLinearMap h.toFun)
    (singularH1_inducedLinearMap h.invFun) ?_ ?_⟩
  · -- f ∘ g = id
    obtain ⟨H_r⟩ := h.right_inv
    have h1 := singularH1_inducedLinearMap_comp h.invFun h.toFun
    have h2 := singularH1_inducedLinearMap_eq_of_homotopic H_r
    have h3 := singularH1_inducedLinearMap_id Y
    ext y
    change ((singularH1_inducedLinearMap h.toFun).comp (singularH1_inducedLinearMap h.invFun)) y = y
    rw [← h1, h2, h3]
    rfl
  · -- g ∘ f = id
    obtain ⟨H_l⟩ := h.left_inv
    have h1 := singularH1_inducedLinearMap_comp h.toFun h.invFun
    have h2 := singularH1_inducedLinearMap_eq_of_homotopic H_l
    have h3 := singularH1_inducedLinearMap_id X
    ext x
    change ((singularH1_inducedLinearMap h.invFun).comp (singularH1_inducedLinearMap h.toFun)) x = x
    rw [← h1, h2, h3]
    rfl

theorem singularH1_subsingleton_of_homotopyEquivUnit {X : Type} [TopologicalSpace X]
    (h : ContinuousMap.HomotopyEquiv X Unit) :
    Subsingleton (singularH1 X) := by
  obtain ⟨e⟩ := singularH1_iso_of_homotopyEquiv h
  haveI := singularH1_unit_subsingleton
  exact e.toEquiv.subsingleton

theorem singularH1_subsingleton_of_contractibleSpace {X : Type} [TopologicalSpace X] [ContractibleSpace X] :
    Subsingleton (singularH1 X) := by
  obtain ⟨h⟩ := ContractibleSpace.hequiv_unit X
  exact singularH1_subsingleton_of_homotopyEquivUnit h

end JacobianChallenge.Periods

end
