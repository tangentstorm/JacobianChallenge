/-
Copyright (c) 2026 Jacobian Challenge contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.AlgebraicTopology.SingularHomology.Basic
import Mathlib.Algebra.Homology.Homotopy
import Mathlib.Topology.Homotopy.Basic
import Mathlib.Algebra.Category.ModuleCat.Basic
import Mathlib.Algebra.Category.ModuleCat.Colimits
import Mathlib.Algebra.Category.ModuleCat.Abelian
import Mathlib.Topology.Category.TopCat.Basic
import Jacobian.Periods.PrismConstruction
import Jacobian.Periods.PrismChainBridge

/-!
# Chain-level prism homotopy

This file builds the chain-level prism operator `P_n : C_n(X) ⟶ C_{n+1}(Y)`
from a homotopy `H : f ≃ g` and assembles it into a
`HomologicalComplex.Homotopy` between the singular chain complex maps
`(sChain.map f)` and `(sChain.map g)`. This is the *categorical* layer
of the prism construction (Hatcher §2.1, Lemma 2.10); the geometric
pieces — `prismSimplex`, `prismSimplex_top_face`,
`prismSimplex_bottom_face`, `prismSimplex_diagonal_face` — live in
`Jacobian/Periods/PrismConstruction.lean`. The Mathlib categorical
plumbing (universe / ULift / `Sigma.desc`) is in
`Jacobian/Periods/PrismChainBridge.lean`.

## Structure

* `prismChain_op n H` — the chain-level prism operator at degree `n`,
  defined on a generator `σ : SingSimplex n X` by
  `Σ_{i : Fin (n+1)} (-1)^i • [prismSimplex n i H σ]`.
* `prismChain_hom H i j` — the `Homotopy.hom` field: `prismChain_op i H`
  when `j = i+1`, otherwise `0`.
* `prismChain_hom_zero H` — proves the `Homotopy.zero` field.
* `prism_chainHomotopy_comm` — the `Homotopy.comm` field (the boundary
  identity `∂P + P∂ = g_* − f_*`). **This is the residual sorry.**
* `prismChainHomotopy H` — assembled `Homotopy`.
* `prism_chainHomotopy_exists` — `Nonempty (Homotopy ...)` via the above.
-/

noncomputable section

namespace JacobianChallenge.Periods

open AlgebraicTopology CategoryTheory Limits HomologicalComplex

/-! ### The chain-level prism operator

Given a homotopy `H : f ≃ g` between continuous maps `f, g : X → Y`,
the prism operator `P_n : C_n(X) ⟶ C_{n+1}(Y)` is defined on a basis
element corresponding to a singular `n`-simplex
`s : C(stdSimplex ℝ (Fin (n+1)), X)` by

  `P_n s := Σ_{i : Fin (n+1)} (-1)^i.val • [prismSimplex n i H s]`

where `[·]` is the basis morphism in the chain group (cf.
`singChain_basis` in the bridge file). -/

/-- The chain-level contribution at a single staircase index `i`:
the basis morphism of the prism simplex with sign `(-1)^i.val`. -/
noncomputable def prismChain_summand
    {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
    {f g : C(X, Y)} (H : ContinuousMap.Homotopy f g) (n : ℕ)
    (i : Fin (n + 1)) (s : SingSimplex n X) :
    ModuleCat.of ℤ ℤ ⟶ singChain (n + 1) Y :=
  ((-1 : ℤ) ^ i.val) • singChain_basis (prismSimplex n i H s)

/-- The chain-level prism operator at degree `n`, on a single
generator: the alternating sum over staircase indices
`i : Fin (n + 1)` of basis morphisms of `prismSimplex n i H s`. -/
noncomputable def prismChain_op_atSimplex
    {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
    {f g : C(X, Y)} (H : ContinuousMap.Homotopy f g) (n : ℕ)
    (s : SingSimplex n X) :
    ModuleCat.of ℤ ℤ ⟶ singChain (n + 1) Y :=
  ∑ i : Fin (n + 1), prismChain_summand H n i s

/-- The chain-level prism operator at degree `n`:
`P_n : C_n(X) ⟶ C_{n+1}(Y)`. -/
noncomputable def prismChain_op
    {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
    {f g : C(X, Y)} (H : ContinuousMap.Homotopy f g) (n : ℕ) :
    singChain n X ⟶ singChain (n + 1) Y :=
  singChain_desc (prismChain_op_atSimplex H n)

/-- Universal property: the prism operator on a basis element. -/
@[simp]
theorem prismChain_op_basis
    {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
    {f g : C(X, Y)} (H : ContinuousMap.Homotopy f g) (n : ℕ)
    (s : SingSimplex n X) :
    singChain_basis s ≫ prismChain_op H n =
      ∑ i : Fin (n + 1), prismChain_summand H n i s := by
  unfold prismChain_op
  rw [singChain_desc_basis]
  rfl

/-! ### The `Homotopy.hom` field, with case split on `j = i + 1`

`HomologicalComplex.Homotopy` requires `hom : ∀ i j, C.X i ⟶ D.X j` for
all pairs `(i, j)`, with `hom i j = 0` for `(i, j)` outside the
"chain shape" relation. For `ChainComplex C ℕ` (shape `down ℕ`), the
relation is `j + 1 = i`, so `hom i j` is non-zero only when `j = i + 1`,
where it equals our prism operator at degree `i`. -/

/-- The `Homotopy.hom` field: the chain prism operator at degree `i`
when `j = i + 1`, and zero otherwise. -/
noncomputable def prismChain_hom
    {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
    {f g : C(X, Y)} (H : ContinuousMap.Homotopy f g) (i j : ℕ) :
    singChain i X ⟶ singChain j Y := by
  by_cases h : j = i + 1
  · exact h ▸ prismChain_op H i
  · exact 0

/-- The `Homotopy.zero` field: when `j ≠ i + 1` (i.e., the chain-shape
relation `c.Rel j i` fails), the `prismChain_hom` is zero by
construction. For `ComplexShape.down ℕ`, `Rel j i` holds iff `i + 1 = j`. -/
theorem prismChain_hom_zero
    {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
    {f g : C(X, Y)} (H : ContinuousMap.Homotopy f g)
    (i j : ℕ) (hij : ¬ (ComplexShape.down ℕ).Rel j i) :
    prismChain_hom H i j = 0 := by
  unfold prismChain_hom
  rw [dif_neg]
  intro hji
  apply hij
  -- (ComplexShape.down ℕ).Rel j i ↔ i + 1 = j (since down is shift by 1)
  simp only [ComplexShape.down_Rel]
  omega

/-! ### The boundary identity (residual sorry)

The chain-homotopy condition: for each `i : ℕ`,
`(sChain.map f).f i = dNext i (prismChain_hom H) + prevD i (prismChain_hom H) + (sChain.map g).f i`.

This is the categorical packaging of the prism boundary equation
`∂P + P∂ = g_* − f_*`. The combinatorial verification depends on:
* `prismSimplex_top_face`     — face 0 of `P_0` = `g ∘ s`
* `prismSimplex_bottom_face`  — face `n+1` of `P_n` = `f ∘ s`
* `prismSimplex_diagonal_face`— pairwise cancellation between adjacent
                                 staircase simplices
* `prismSimplex_side_face`    — *side-face identity*, **still missing**
                                 in `PrismConstruction.lean`. -/

/-- The `Homotopy.comm` field — the boundary identity. **Residual sorry.**

This is the chain-level expression of the prism boundary equation
`∂P + P∂ = g_* − f_*`. To discharge:

1. Reduce to a per-basis-element equation by composing with
   `singChain_basis s` for arbitrary `s : SingSimplex i X`.
2. Unfold `dNext i (prismChain_hom H)` using `dNext_eq` with
   `c.Rel i (i+1)` — gives `d_X (i+1) i ≫ prismChain_op H i`.
3. Unfold `prevD i (prismChain_hom H)` using `prevD_eq` — gives
   `prismChain_op H (i-1) ≫ d_Y i (i-1)` (or zero at `i = 0`).
4. Unfold the chain differential `d` to alternating sum of face maps
   on the basis (the key `singChain_d_basis` lemma — Phase 2 of the
   plan, **TODO**).
5. Apply `prismSimplex_top_face`, `_bottom_face`, `_diagonal_face`,
   `_side_face` (the last is missing — Phase 4 of the plan).
6. Reassemble using `Finset.sum` rewrites; the alternating signs
   produce the desired cancellations.

This is a substantial calculation; see Hatcher pp. 112–113. -/
theorem prismChain_hom_comm
    {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
    {f g : C(X, Y)} (H : ContinuousMap.Homotopy f g) (i : ℕ) :
    (((singularChainComplexFunctor (ModuleCat ℤ)).obj
        (ModuleCat.of ℤ ℤ)).map (TopCat.ofHom f)).f i =
      dNext i (prismChain_hom H) + prevD i (prismChain_hom H) +
      (((singularChainComplexFunctor (ModuleCat ℤ)).obj
        (ModuleCat.of ℤ ℤ)).map (TopCat.ofHom g)).f i := by
  sorry

/-! ### Assembly into a `Homotopy` -/

/-- The chain-level prism homotopy, assembled from the prism operator,
the zero condition, and the boundary identity. -/
noncomputable def prismChainHomotopy
    {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
    {f g : C(X, Y)} (H : ContinuousMap.Homotopy f g) :
    Homotopy
      (((singularChainComplexFunctor (ModuleCat ℤ)).obj
          (ModuleCat.of ℤ ℤ)).map (TopCat.ofHom f))
      (((singularChainComplexFunctor (ModuleCat ℤ)).obj
          (ModuleCat.of ℤ ℤ)).map (TopCat.ofHom g)) where
  hom := prismChain_hom H
  zero := prismChain_hom_zero H
  comm := prismChain_hom_comm H

/-- **Chain-level prism homotopy, existence form.** Given a homotopy
`H : f ≃ g` between continuous maps `f, g : X → Y`, the singular chain
complex functor (with ℤ-coefficients) sends `f` and `g` to chain maps
that are homotopic via the prism construction.

Sorry-free assembly via `prismChainHomotopy` (the data form). The
residual sorry is now in `prismChain_hom_comm` (the boundary identity),
not at the assembly level. -/
theorem prism_chainHomotopy_exists
    {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
    {f g : C(X, Y)} (H : ContinuousMap.Homotopy f g) :
    Nonempty (Homotopy
      (((AlgebraicTopology.singularChainComplexFunctor (ModuleCat ℤ)).obj
          (ModuleCat.of ℤ ℤ)).map (TopCat.ofHom f))
      (((AlgebraicTopology.singularChainComplexFunctor (ModuleCat ℤ)).obj
          (ModuleCat.of ℤ ℤ)).map (TopCat.ofHom g))) :=
  ⟨prismChainHomotopy H⟩

end JacobianChallenge.Periods

end
