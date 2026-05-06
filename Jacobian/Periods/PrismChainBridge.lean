/-
Copyright (c) 2026 Jacobian Challenge contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.AlgebraicTopology.SingularHomology.Basic
import Mathlib.AlgebraicTopology.SingularSet
import Mathlib.AlgebraicTopology.TopologicalSimplex
import Mathlib.Algebra.Category.ModuleCat.Basic
import Mathlib.Algebra.Category.ModuleCat.Colimits
import Mathlib.Algebra.Category.ModuleCat.Abelian
import Mathlib.CategoryTheory.Limits.Shapes.Products
import Mathlib.Topology.Category.TopCat.Basic

/-!
# Bridge: singular n-simplex set ↔ continuous map type

This file packages the equivalence between Mathlib's category-theoretic
representation of the n-th level of `TopCat.toSSet.obj X` and the
concrete type `C(stdSimplex ℝ (Fin (n+1)), X)` of continuous maps from
the topological standard `n`-simplex.

Two perspectives of the same set:
* Mathlib: `(TopCat.toSSet.obj X).obj (op ⦋n⦌)` —
  Yoneda-restricted ULift hom-set;
* Geometric: `C(stdSimplex ℝ (Fin (n+1)), X)` — continuous maps.

The Mathlib equivalence `TopCat.toSSetObjEquiv` mediates these. We
re-expose it here at the universe / index choices we use throughout
(`Type 0`, `n : ℕ`).

## Bottom-up role

This is **Phase 1** of the prism-chain-homotopy plan
(see `Jacobian/Periods/PrismChainHomotopy.lean`). It provides the
universe/equiv plumbing needed to:
* identify a generator of the chain group `((sChain).obj X).X n`
  with a singular `n`-simplex `σ : C(stdSimplex ℝ (Fin (n+1)), X)`,
* define maps out of the chain group via `Limits.Sigma.desc`.
-/

noncomputable section

namespace JacobianChallenge.Periods

open CategoryTheory Limits AlgebraicTopology

/-- A *singular `n`-simplex* in `X`: a continuous map from the standard
topological `n`-simplex `stdSimplex ℝ (Fin (n+1))` to `X`. -/
abbrev SingSimplex (n : ℕ) (X : Type) [TopologicalSpace X] : Type :=
  C(stdSimplex ℝ (Fin (n + 1)), X)

/-- The categorical type of `n`-simplices in the singular simplicial set
of `X`, as it appears in Mathlib's `TopCat.toSSet`. Equivalent to
`SingSimplex n X` via `TopCat.toSSetObjEquiv`. -/
abbrev SingSimplexCat (n : ℕ) (X : Type) [TopologicalSpace X] : Type :=
  (TopCat.toSSet.obj (TopCat.of X)).obj (Opposite.op (SimplexCategory.mk n))

/-- The bridging equivalence: Mathlib's categorical singular `n`-simplex
set is equivalent to the concrete continuous-map type. -/
noncomputable def singSimplexEquiv (n : ℕ) (X : Type) [TopologicalSpace X] :
    SingSimplexCat n X ≃ SingSimplex n X :=
  TopCat.toSSetObjEquiv (TopCat.of X) (Opposite.op (SimplexCategory.mk n))

/-! ### Chain-level identifications

The level-`n` object of the singular chain complex
`((singularChainComplexFunctor (ModuleCat ℤ)).obj (ModuleCat.of ℤ ℤ)).obj
(TopCat.of X)` is *definitionally* the coproduct of `ModuleCat.of ℤ ℤ`
indexed by `SingSimplexCat n X`. We expose this fact and provide a
"basis morphism" API: each categorical simplex generator induces a
morphism from `ModuleCat.of ℤ ℤ` into the chain group. -/

/-- Abbreviation for the level-`n` chain group of `X`. -/
abbrev singChain (n : ℕ) (X : Type) [TopologicalSpace X] : ModuleCat ℤ :=
  (((singularChainComplexFunctor (ModuleCat ℤ)).obj (ModuleCat.of ℤ ℤ)).obj
      (TopCat.of X)).X n

/-- The chain group is *definitionally* the coproduct of `ℤ` indexed by
the categorical singular `n`-simplex set. This is the core bridge
exposing the structure for `Sigma.desc` constructions. -/
theorem singChain_eq_coproduct (n : ℕ) (X : Type) [TopologicalSpace X] :
    singChain n X = (∐ fun _ : SingSimplexCat n X => ModuleCat.of ℤ ℤ) :=
  rfl

/-- The basis morphism: each categorical singular `n`-simplex `σ`
induces a morphism `ModuleCat.of ℤ ℤ ⟶ singChain n X`
(the `Sigma.ι` inclusion at index `σ`). -/
noncomputable def singChain_basisCat {n : ℕ} {X : Type} [TopologicalSpace X]
    (σ : SingSimplexCat n X) : ModuleCat.of ℤ ℤ ⟶ singChain n X :=
  Sigma.ι (fun _ : SingSimplexCat n X => ModuleCat.of ℤ ℤ) σ

/-- Geometric basis morphism: each *concrete* singular `n`-simplex
(continuous map) `s : C(stdSimplex ℝ (Fin (n+1)), X)` induces a basis
morphism into the chain group, by passing through `singSimplexEquiv`. -/
noncomputable def singChain_basis {n : ℕ} {X : Type} [TopologicalSpace X]
    (s : SingSimplex n X) : ModuleCat.of ℤ ℤ ⟶ singChain n X :=
  singChain_basisCat ((singSimplexEquiv n X).symm s)

/-- Universal property: a morphism out of `singChain n X` in
`ModuleCat ℤ` is determined by its values on the basis morphisms,
indexed by categorical simplices.

This is the categorical-to-coproduct dual: define a morphism
out of `∐ ι R` by giving a morphism `R ⟶ Y` for each index. -/
noncomputable def singChain_descCat {n : ℕ} {X : Type} [TopologicalSpace X]
    {Y : ModuleCat ℤ} (φ : SingSimplexCat n X → (ModuleCat.of ℤ ℤ ⟶ Y)) :
    singChain n X ⟶ Y :=
  Sigma.desc φ

/-- Geometric `Sigma.desc`: define a morphism out of `singChain n X` by
giving a morphism `ModuleCat.of ℤ ℤ ⟶ Y` for each *concrete* simplex
`s : C(stdSimplex ℝ (Fin (n+1)), X)`. -/
noncomputable def singChain_desc {n : ℕ} {X : Type} [TopologicalSpace X]
    {Y : ModuleCat ℤ} (φ : SingSimplex n X → (ModuleCat.of ℤ ℤ ⟶ Y)) :
    singChain n X ⟶ Y :=
  singChain_descCat (fun σ => φ ((singSimplexEquiv n X) σ))

/-- Universal property of `Sigma.desc` on a basis morphism (categorical
form): `singChain_descCat φ ∘ singChain_basisCat σ = φ σ`. -/
@[simp]
theorem singChain_descCat_basisCat {n : ℕ} {X : Type} [TopologicalSpace X]
    {Y : ModuleCat ℤ} (φ : SingSimplexCat n X → (ModuleCat.of ℤ ℤ ⟶ Y))
    (σ : SingSimplexCat n X) :
    singChain_basisCat σ ≫ singChain_descCat φ = φ σ :=
  Sigma.ι_desc _ _

/-- Universal property on a basis morphism (geometric form):
`singChain_desc φ ∘ singChain_basis s = φ s`. -/
@[simp]
theorem singChain_desc_basis {n : ℕ} {X : Type} [TopologicalSpace X]
    {Y : ModuleCat ℤ} (φ : SingSimplex n X → (ModuleCat.of ℤ ℤ ⟶ Y))
    (s : SingSimplex n X) :
    singChain_basis s ≫ singChain_desc φ = φ s := by
  simp only [singChain_desc, singChain_basis, singChain_descCat_basisCat,
    Equiv.apply_symm_apply]

end JacobianChallenge.Periods

end
