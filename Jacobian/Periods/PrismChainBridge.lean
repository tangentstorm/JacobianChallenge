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

/-- Extensionality: two morphisms out of a singular chain group are
equal iff they agree on all categorical basis elements. -/
theorem singChain_hom_extCat {n : ℕ} {X : Type} [TopologicalSpace X]
    {Y : ModuleCat ℤ} (g₁ g₂ : singChain n X ⟶ Y)
    (h : ∀ σ : SingSimplexCat n X,
      singChain_basisCat σ ≫ g₁ = singChain_basisCat σ ≫ g₂) :
    g₁ = g₂ :=
  Sigma.hom_ext g₁ g₂ h

/-- Extensionality: two morphisms out of a singular chain group are
equal iff they agree on all geometric basis elements. -/
theorem singChain_hom_ext {n : ℕ} {X : Type} [TopologicalSpace X]
    {Y : ModuleCat ℤ} (g₁ g₂ : singChain n X ⟶ Y)
    (h : ∀ s : SingSimplex n X,
      singChain_basis s ≫ g₁ = singChain_basis s ≫ g₂) :
    g₁ = g₂ := by
  apply singChain_hom_extCat
  intro σ
  have := h ((singSimplexEquiv n X) σ)
  unfold singChain_basis at this
  rw [Equiv.symm_apply_apply] at this
  exact this

/-! ### Chain map on basis (Phase 2)

The functorial chain map `((sChain).obj R).map (TopCat.ofHom f)` at
degree `n` sends the basis element at `σ : SingSimplexCat n X` to the
basis element at `(toSSet.map (ofHom f)).app _ σ`. This is the
categorical functoriality of the chain functor; via the equiv, the
"pushed simplex" corresponds to the geometric `f.comp s`. -/

/-- The chain map at degree `n` sends a categorical basis to the
categorical basis at the pushed simplex. -/
theorem singChain_map_basisCat {X Y : Type} [TopologicalSpace X]
    [TopologicalSpace Y] (f : C(X, Y)) (n : ℕ) (σ : SingSimplexCat n X) :
    singChain_basisCat σ ≫
        (((singularChainComplexFunctor (ModuleCat ℤ)).obj
            (ModuleCat.of ℤ ℤ)).map (TopCat.ofHom f)).f n =
      singChain_basisCat ((TopCat.toSSet.map (TopCat.ofHom f)).app _ σ) := by
  simp [singChain_basisCat, singularChainComplexFunctor,
    SSet.singularChainComplexFunctor]

/-- The action of `TopCat.toSSet.map f` on the categorical simplex
matches `f.comp s` on the geometric side, via `singSimplexEquiv`. -/
theorem singSimplexEquiv_toSSet_map {X Y : Type} [TopologicalSpace X]
    [TopologicalSpace Y] (f : C(X, Y)) (n : ℕ) (σ : SingSimplexCat n X) :
    (singSimplexEquiv n Y) ((TopCat.toSSet.map (TopCat.ofHom f)).app _ σ) =
      f.comp ((singSimplexEquiv n X) σ) := by
  -- This follows from the definition of TopCat.toSSet via restrictedULiftYoneda
  -- and TopCat.toSSetObjEquiv.  We unfold both sides and use that the
  -- restricted ULift Yoneda action is just composition.
  rfl

/-- The chain map at degree `n` on a geometric basis: pushing `s` by
`f.comp s`. This is the key Phase 2 lemma needed for the boundary
identity. -/
theorem singChain_map_basis {X Y : Type} [TopologicalSpace X]
    [TopologicalSpace Y] (f : C(X, Y)) (n : ℕ) (s : SingSimplex n X) :
    singChain_basis s ≫
        (((singularChainComplexFunctor (ModuleCat ℤ)).obj
            (ModuleCat.of ℤ ℤ)).map (TopCat.ofHom f)).f n =
      singChain_basis (f.comp s) := by
  unfold singChain_basis
  rw [singChain_map_basisCat]
  -- Goal: singChain_basisCat (toSSet.map f σ) = singChain_basisCat (equiv.symm (f.comp s))
  -- where σ = equiv.symm s.  By singSimplexEquiv_toSSet_map, equiv (toSSet.map f σ) = f.comp (equiv σ)
  -- and equiv σ = s, so equiv (toSSet.map f σ) = f.comp s, hence
  -- toSSet.map f σ = equiv.symm (f.comp s).
  have h := singSimplexEquiv_toSSet_map f n ((singSimplexEquiv n X).symm s)
  rw [Equiv.apply_symm_apply] at h
  rw [show (TopCat.toSSet.map (TopCat.ofHom f)).app
        (Opposite.op (SimplexCategory.mk n)) ((singSimplexEquiv n X).symm s)
      = (singSimplexEquiv n Y).symm (f.comp s) by
      apply (singSimplexEquiv n Y).injective
      rw [Equiv.apply_symm_apply]; exact h]

/-! ### Chain differential on basis (Phase 2 main lemma)

The chain differential `d : C_{n+1}(X) ⟶ C_n(X)` of the singular chain
complex acts on a basis element `[s]` by the alternating sum of face
inclusions:
  `d [s] = Σ_{j : Fin (n+2)} (-1)^j • [s ∘ δ_j]`
where `δ_j` is the topological face inclusion. This is the key Phase 2
lemma needed for the boundary identity in the prism construction.
-/

/-- Chain differential on a categorical basis element: alternating sum
of face inclusions, in categorical (`SimplexCategory.δ`) form. -/
theorem singChain_d_basisCat {X : Type} [TopologicalSpace X] (n : ℕ)
    (σ : SingSimplexCat (n + 1) X) :
    singChain_basisCat σ ≫
        (((singularChainComplexFunctor (ModuleCat ℤ)).obj
            (ModuleCat.of ℤ ℤ)).obj (TopCat.of X)).d (n + 1) n =
      ∑ j : Fin (n + 2), ((-1 : ℤ) ^ j.val) •
        singChain_basisCat
          ((TopCat.toSSet.obj (TopCat.of X)).map (SimplexCategory.δ j).op σ) := by
  simp [singChain_basisCat, singularChainComplexFunctor,
    SSet.singularChainComplexFunctor, AlternatingFaceMapComplex.objD,
    SimplicialObject.δ, Preadditive.comp_sum, Sigma.ι_comp_map']

/-- The geometric face inclusion `Δⁿ → Δⁿ⁺¹` corresponding to dropping
the `j`-th vertex: pulled back from `SimplexCategory.δ j` via
`stdSimplex.map (Fin.succAbove j)`.

This is exactly `stdSimplex.map (Fin.succAbove j)` (up to ULift, which
is identity at universe 0 in our setting). -/
noncomputable def stdSimplexFaceInclusion (n : ℕ) (j : Fin (n + 2)) :
    C(stdSimplex ℝ (Fin (n + 1)), stdSimplex ℝ (Fin (n + 2))) :=
  ⟨stdSimplex.map (Fin.succAbove j), stdSimplex.continuous_map _⟩

/-- The simplicial face action on a categorical simplex `σ` corresponds,
via `singSimplexEquiv`, to geometric precomposition with the face
inclusion `stdSimplexFaceInclusion`. -/
theorem singSimplexEquiv_face {X : Type} [TopologicalSpace X] (n : ℕ)
    (j : Fin (n + 2)) (σ : SingSimplexCat (n + 1) X) :
    (singSimplexEquiv n X)
        ((TopCat.toSSet.obj (TopCat.of X)).map (SimplexCategory.δ j).op σ) =
      ((singSimplexEquiv (n + 1) X) σ).comp (stdSimplexFaceInclusion n j) := by
  -- The geometric simplex of σ via singSimplexEquiv comes from
  -- ULift-stripping the underlying continuous map.
  -- The simplicial face action precomposes with toTop.map (δ j),
  -- which on stdSimplex is stdSimplex.map (Fin.succAbove j) up to ULift.
  rfl

/-- Geometric form: the chain differential on a geometric basis element
is the alternating sum of basis elements at face precompositions. -/
theorem singChain_d_basis {X : Type} [TopologicalSpace X] (n : ℕ)
    (s : SingSimplex (n + 1) X) :
    singChain_basis s ≫
        (((singularChainComplexFunctor (ModuleCat ℤ)).obj
            (ModuleCat.of ℤ ℤ)).obj (TopCat.of X)).d (n + 1) n =
      ∑ j : Fin (n + 2), ((-1 : ℤ) ^ j.val) •
        singChain_basis (s.comp (stdSimplexFaceInclusion n j)) := by
  -- Reduce to categorical form, then use the fact that toSSet's face action
  -- corresponds to geometric face-precomposition under singSimplexEquiv.
  have key : ∀ j : Fin (n + 2),
      (TopCat.toSSet.obj (TopCat.of X)).map (SimplexCategory.δ j).op
          ((singSimplexEquiv (n + 1) X).symm s)
        = (singSimplexEquiv n X).symm (s.comp (stdSimplexFaceInclusion n j)) := by
    intro j
    apply (singSimplexEquiv n X).injective
    rw [Equiv.apply_symm_apply, singSimplexEquiv_face, Equiv.apply_symm_apply]
  unfold singChain_basis
  rw [singChain_d_basisCat]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  rw [key]

end JacobianChallenge.Periods

end
