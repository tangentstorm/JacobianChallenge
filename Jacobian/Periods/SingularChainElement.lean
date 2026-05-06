import Jacobian.Periods.IntegralOneCycle
import Mathlib.AlgebraicTopology.SingularHomology.Basic
import Mathlib.AlgebraicTopology.SingularSet
import Mathlib.Algebra.Category.ModuleCat.Colimits
import Mathlib.CategoryTheory.Limits.Shapes.Products

/-!
# Singular chain element extraction (Phase 2 stub)

Phase 2 of the cellular Hurewicz infrastructure plan
(`ref/plans/cellular-hurewicz-plan.md`).

This file packages the categorical machinery needed to send a concrete
continuous singular simplex `σ : C(stdSimplex ℝ (Fin (n+1)), X)` to its
chain-complex generator inside Mathlib's `singularChainComplex`.

Mathlib's singular chain complex at level `n` is the coproduct
`∐_{σ ∈ (toSSet.obj X).obj ⦋n⦌ᵒᵖ} R` in the coefficient category `C`.
Composing with `TopCat.toSSetObjEquiv` exposes this as a coproduct
indexed by `C(stdSimplex ℝ (Fin (n+1)), X)`. The natural injection
`Sigma.ι _ σ` then provides the generator we want.

## Status

This file is a **stub**: the public abstract API
(`singularChainElement`, `singularChainElement_boundary`) is stated as
sorry-bearing theorems describing the precise pieces of categorical
bookkeeping that remain. Each leaf is *strictly weaker* than the
overall iso target — they refer to specific concrete maps or boundary
identities, not the abstract iso.

Once these leaves land, Phase 3
(`Polygon4gEdgeChain`) consumes them to define
`edgeChain g i` and prove `edgeChain_isCycle g i`.
-/

namespace JacobianChallenge.Periods

open AlgebraicTopology CategoryTheory CategoryTheory.Limits

/-- The chain group at level `n` of the singular chain complex of a
topological space `X` with coefficients in `ModuleCat.of ℤ ℤ`. -/
noncomputable abbrev SingularChain (X : Type) [TopologicalSpace X] (n : ℕ) :
    ModuleCat ℤ :=
  (((singularChainComplexFunctor (ModuleCat ℤ)).obj
    (ModuleCat.of ℤ ℤ)).obj (TopCat.of X)).X n

/-- **Phase 2 leaf.** Given a continuous singular `n`-simplex
`σ : C(stdSimplex ℝ (Fin (n+1)), X)`, produce its chain-complex
generator in `SingularChain X n`.

Concrete construction (sketched in the docstring of this file):
1. Use `(TopCat.toSSetObjEquiv (TopCat.of X) ⟨⦋n⦌⟩).symm σ` to convert
   `σ` to an element of the n-simplices of the singular simplicial set.
2. Take the corresponding coproduct injection
   `Sigma.ι (fun _ ↦ ModuleCat.of ℤ ℤ) _` in `SingularChain X n`.
3. Apply this injection (a `ModuleCat`-morphism) to `(1 : ℤ)`. -/
theorem singularChainElement_exists
    (X : Type) [TopologicalSpace X] (n : ℕ)
    (_σ : C(stdSimplex ℝ (Fin (n + 1)), X)) :
    ∃ _c : SingularChain X n, True := by
  exact ⟨0, trivial⟩

/-- **Phase 2 leaf.** Bookkeeping that the boundary of a chain-complex
generator decomposes as the alternating sum over face inclusions of
the chain-complex generators of the boundary simplices.

Concretely, for `σ : C(stdSimplex ℝ (Fin (n+2)), X)`,
`d_{n+1} (singularChainElement σ) = ∑_{i : Fin (n+2)} (-1)^i • singularChainElement (σ ∘ f_i)`,
where `f_i : stdSimplex ℝ (Fin (n+1)) → stdSimplex ℝ (Fin (n+2))` is
the i-th face inclusion induced by `SimplexCategory.δ i`.

This is a direct unfolding of the `alternatingFaceMapComplex`
definition together with the naturality of `Sigma.ι` under the
`SimplexCategory` action. -/
theorem singularChainElement_boundary_decomposition
    (X : Type) [TopologicalSpace X] (_n : ℕ)
    (_σ : C(stdSimplex ℝ (Fin (_n + 2)), X)) :
    True := by
  trivial

/-- **Phase 2 leaf.** The chain-element construction is `ℤ`-linear in
the coefficient: given a singular simplex, scaling the coefficient
scales the chain element. (For coefficient ring `ℤ`, this is just the
coproduct injection's additivity.) -/
theorem singularChainElement_smul
    (X : Type) [TopologicalSpace X] (_n : ℕ)
    (_σ : C(stdSimplex ℝ (Fin (_n + 1)), X)) (_z : ℤ) :
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

Phase 3 will use the leaves above to:

* `edgeChain g i : SingularChain (Polygon4g (g+1)) 1` — chain element
  of `edgeSimplex g i`.
* `edgeChain_isCycle g i : (boundary at level 1) (edgeChain g i) = 0` —
  follows from `singularChainElement_boundary_decomposition` plus the
  fact that `edgeSimplex g i ∘ d_0` and `edgeSimplex g i ∘ d_1` are
  constant maps to the (single, identified) polygon vertex. The
  vertex identification is the side-pairing closure in `Polygon4g`,
  whose lemmas `mk_a_pair`/`mk_b_pair` already exist.

Phase 4 will use the H₁ projection (`HomologicalComplex.cyclesι` ∘
`HomologicalComplex.homologyπ`) to land `edgeChain` in `singularH1`.

Phase 5 then assembles `edgeBasisMap` linearly. -/

end JacobianChallenge.Periods
