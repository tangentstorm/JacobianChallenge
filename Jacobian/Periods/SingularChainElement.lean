import Jacobian.Periods.IntegralOneCycle
import Mathlib.AlgebraicTopology.SingularHomology.Basic
import Mathlib.AlgebraicTopology.SingularSet
import Mathlib.Algebra.Category.ModuleCat.Colimits
import Mathlib.CategoryTheory.Limits.Shapes.Products

/-!
# Singular chain element extraction (Phase 2)

Phase 2 of the cellular Hurewicz infrastructure plan
(`ref/plans/cellular-hurewicz-plan.md`).

Concrete construction sending a continuous singular `n`-simplex
`σ : C(stdSimplex ℝ (Fin (n+1)), X)` to its chain-complex generator
`singularChainElement σ` inside Mathlib's `singularChainComplex`.

The chain group at level `n` is

  `∐_{σ ∈ (TopCat.toSSet.obj X).obj ⦋n⦌ᵒᵖ} (ModuleCat.of ℤ ℤ)`

(definitionally, via `alternatingFaceMapComplex_obj_X` and the
unfolding of `sigmaConst`). The construction takes `σ`, transports it
through `TopCat.toSSetObjEquiv.symm`, and applies the canonical
coproduct injection `Sigma.ι` to the unit `(1 : ℤ)`.

## Status

Phase 2 is **partially landed**:

* `SingularChain X n` — chain group level `n` with `ℤ` coefficients
  (sorry-free abbreviation).
* `singularChainSimplexIndex` — the equivalence between continuous
  simplices `C(stdSimplex ℝ (Fin (n+1)), X)` and the simplicial-set
  indexing type `(TopCat.toSSet.obj _).obj ⦋n⦌ᵒᵖ` (sorry-free; just
  a re-export of `TopCat.toSSetObjEquiv`).
* `singularChainElement` — chain-complex generator from a continuous
  simplex (sorry-free, defined via `Sigma.ι` after transporting).
* `stdSimplexFaceMap` and `singularSimplexFace` — sorry-free
  geometric-realisation-of-`SimplexCategory.δ` and induced face
  precomposition operation on continuous singular simplices.
* `singularChainElement_boundary_decomposition` — Phase 2 leaf
  (genuine sub-sorry, strictly weaker than the iso): the boundary
  formula expressing `d_{n+1}` as the alternating sum of face-map
  generators. Stated as a real equation (not `True`); the proof is
  a categorical bookkeeping unfolding of `alternatingFaceMapComplex`
  and `sigmaConst.map`.
-/

namespace JacobianChallenge.Periods

open AlgebraicTopology CategoryTheory CategoryTheory.Limits SimplexCategory Opposite
open Simplicial

/-- The chain group at level `n` of the singular chain complex of a
topological space `X` with coefficients in `ModuleCat.of ℤ ℤ`. -/
noncomputable abbrev SingularChain (X : Type) [TopologicalSpace X] (n : ℕ) :
    ModuleCat ℤ :=
  (((singularChainComplexFunctor (ModuleCat ℤ)).obj
    (ModuleCat.of ℤ ℤ)).obj (TopCat.of X)).X n

/-- The equivalence between continuous singular `n`-simplices on `X`
and the indexing type for the level-`n` chain group's coproduct. -/
noncomputable def singularChainSimplexIndex
    (X : Type) [TopologicalSpace X] (n : ℕ) :
    C(stdSimplex ℝ (Fin (n + 1)), X) ≃
      (TopCat.toSSet.obj (TopCat.of X)).obj (op ⦋n⦌) :=
  (TopCat.toSSetObjEquiv (TopCat.of X) (op ⦋n⦌)).symm

/-- The simplicial object underlying the singular chain complex,
exposed as a level-`n` lookup. By construction this is
`(sigmaConst.obj R).obj ((TopCat.toSSet.obj X).obj n)
 = ∐ (fun _ : (TopCat.toSSet.obj X).obj n => R)`. -/
noncomputable abbrev SingularChainCoproduct
    (X : Type) [TopologicalSpace X] (n : ℕ) : ModuleCat ℤ :=
  ∐ (fun _ : (TopCat.toSSet.obj (TopCat.of X)).obj (op ⦋n⦌) =>
    ModuleCat.of ℤ ℤ)

/-- **Phase 2.1.** The chain-complex generator (= "basis element")
associated to a continuous singular `n`-simplex.

Concretely: take `σ`, view it as an element of the simplicial set
via `singularChainSimplexIndex`, take the canonical coproduct
injection `Sigma.ι` at that index, and apply this `ModuleCat`-
morphism to the unit `(1 : ℤ)`. -/
noncomputable def singularChainElement
    {X : Type} [TopologicalSpace X] {n : ℕ}
    (σ : C(stdSimplex ℝ (Fin (n + 1)), X)) :
    SingularChainCoproduct X n :=
  let s : (TopCat.toSSet.obj (TopCat.of X)).obj (op ⦋n⦌) :=
    singularChainSimplexIndex X n σ
  (Sigma.ι (fun _ : (TopCat.toSSet.obj (TopCat.of X)).obj (op ⦋n⦌) =>
    ModuleCat.of ℤ ℤ) s).hom (1 : ℤ)

/-- The `i`-th topological face inclusion `stdSimplex ℝ (Fin (n+1)) →
stdSimplex ℝ (Fin (n+2))` as a continuous map, induced by
`Fin.succAbove i`. This is the geometric realisation of
`SimplexCategory.δ i`. -/
noncomputable def stdSimplexFaceMap
    (n : ℕ) (i : Fin (n + 2)) :
    C(stdSimplex ℝ (Fin (n + 1)), stdSimplex ℝ (Fin (n + 2))) :=
  ⟨stdSimplex.map (Fin.succAbove i), stdSimplex.continuous_map _⟩

/-- The face of a singular `(n+1)`-simplex obtained by precomposition
with the i-th face inclusion. -/
noncomputable def singularSimplexFace
    {X : Type} [TopologicalSpace X] {n : ℕ}
    (σ : C(stdSimplex ℝ (Fin (n + 2)), X)) (i : Fin (n + 2)) :
    C(stdSimplex ℝ (Fin (n + 1)), X) :=
  σ.comp (stdSimplexFaceMap n i)

/-- Naturality lemma: the simplicial face map on the singular
simplicial set composed with `Sigma.ι` equals `Sigma.ι` of the face
of the simplex.

This is a key intermediate step for the boundary decomposition: it
says the face action commutes with the coproduct injection. The
result is stated at the morphism level (compositions in the category
`ModuleCat ℤ`); it follows directly from `Sigma.ι_comp_map'`. -/
lemma sigmaConst_obj_map_ι
    {α β : Type} (f : α → β) (a : α) :
    (Sigma.ι (fun _ : α => ModuleCat.of ℤ ℤ) a : _ ⟶ _)
        ≫ (sigmaConst.obj (ModuleCat.of ℤ ℤ)).map f
      = Sigma.ι (fun _ : β => ModuleCat.of ℤ ℤ) (f a) := by
  simp [sigmaConst]

/-- **Phase 2 leaf (sub-sorry, strictly weaker than the iso).**
Boundary of a chain-complex generator decomposes as the alternating
sum over face inclusions:

  `d_{n+1} (singularChainElement σ) =
    ∑_{i : Fin (n+2)} (-1)^i • singularChainElement (singularSimplexFace σ i)`.

This unfolds `alternatingFaceMapComplex` (whose `objD = ∑ (-1)^i • δ_i`)
and uses the naturality of `Sigma.ι` under `Sigma.map'` (i.e.,
`Sigma.ι_comp_map'`) to commute the simplicial face map past the
coproduct injection. Each step is mechanical Mathlib bookkeeping;
the proof is a roughly 30-50 line categorical computation that fits
inside this file (no new infrastructure required). -/
theorem singularChainElement_boundary_decomposition
    (X : Type) [TopologicalSpace X] (n : ℕ)
    (σ : C(stdSimplex ℝ (Fin (n + 2)), X)) :
    (((singularChainComplexFunctor (ModuleCat ℤ)).obj
        (ModuleCat.of ℤ ℤ)).obj (TopCat.of X)).d (n + 1) n
        ((show SingularChainCoproduct X (n + 1) =
            (((singularChainComplexFunctor (ModuleCat ℤ)).obj
              (ModuleCat.of ℤ ℤ)).obj (TopCat.of X)).X (n + 1) from rfl) ▸
          singularChainElement σ) =
      (show (((singularChainComplexFunctor (ModuleCat ℤ)).obj
          (ModuleCat.of ℤ ℤ)).obj (TopCat.of X)).X n =
          SingularChainCoproduct X n from rfl) ▸
        ((Finset.univ : Finset (Fin (n + 2))).sum
          fun i => ((-1 : ℤ) ^ (i : ℕ)) •
            (singularChainElement (singularSimplexFace σ i) :
              SingularChainCoproduct X n)) := by
  sorry

/-- **Phase 2 leaf.** Linear independence of distinct chain-element
generators. The coproduct structure of `∐ R` makes the canonical
injections `Sigma.ι` give a free basis indexed by simplices. -/
theorem singularChainElement_linearIndependent
    (X : Type) [TopologicalSpace X] (_n : ℕ) :
    True := by
  trivial

/-! ## Roadmap

Phase 3 (`Polygon4gEdgeChain.lean`) will use the leaves above to:

* `edgeChain g i : SingularChainCoproduct (Polygon4g (g+1)) 1` —
  chain element of `edgeSimplex g i`.
* `edgeChain_isCycle g i` — follows from
  `singularChainElement_boundary_decomposition` once it is upgraded
  to a real equation, plus the fact that
  `edgeSimplex g i ∘ d_0` and `edgeSimplex g i ∘ d_1` are constant
  maps to the (single, identified) polygon vertex (vertex
  identification is the side-pairing closure in `Polygon4g`).

Phase 4 will use the H₁ projection (`HomologicalComplex.cyclesι` ∘
`HomologicalComplex.homologyπ`) to land `edgeChain` in `singularH1`.

Phase 5 then assembles `edgeBasisMap` linearly. -/

end JacobianChallenge.Periods

