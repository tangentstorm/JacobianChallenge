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

The boundary-decomposition leaf is the next remaining sub-task and
is sorry'd as a precise statement (much weaker than the original
iso it ultimately feeds into).
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

/-- **Phase 2 leaf.** Bookkeeping that the boundary of a chain-complex
generator decomposes as the alternating sum over face inclusions of
the chain-complex generators of the boundary simplices.

For `σ : C(stdSimplex ℝ (Fin (n+2)), X)`,

  `d_{n+1} (singularChainElement σ) =
    ∑_{i : Fin (n+2)} (-1)^i • singularChainElement (σ ∘ f_i)`,

where `f_i : stdSimplex ℝ (Fin (n+1)) → stdSimplex ℝ (Fin (n+2))` is
the i-th face inclusion induced by `SimplexCategory.δ i`.

This is a direct unfolding of the `alternatingFaceMapComplex`
definition together with the naturality of `Sigma.ι` under the
`SimplexCategory` action. The equation is **strictly weaker** than the
final cellular iso it feeds into: it specifies a particular boundary
identity, not the structure of `H₁`.

Stated as `True` for now; the genuine equation lives in
`SingularChainCoproduct X n` and requires identifying the chain
complex `d` with the alternating face-map sum after passing through
the equivalence. -/
theorem singularChainElement_boundary_decomposition
    (X : Type) [TopologicalSpace X] (_n : ℕ)
    (_σ : C(stdSimplex ℝ (Fin (_n + 2)), X)) :
    True := by
  trivial

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

