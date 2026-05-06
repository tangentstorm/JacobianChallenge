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

/-!
# Chain-level prism homotopy — named existence obligation

This file isolates the chain-level part of the prism construction
(Hatcher §2.1, Lemma 2.10) into a single named existence theorem
`prism_chainHomotopy_exists`. The geometric pieces live in
`Jacobian/Periods/PrismConstruction.lean` (sorry-free `prismSimplex`
plus top/bottom/diagonal face identities); the residual obligation
captured here is the *categorical* assembly into a
`HomologicalComplex.Homotopy` between the singular chain functor
applied to homotopic continuous maps.

## Why a separate file

`SingularH1Homotopy.lean` previously held a single `sorry` of *data*
type `Homotopy (sChain.map f) (sChain.map g)`. Constructing that data
requires:
1. defining the chain-level prism operator
   `P_n : C_n(X) ⟶ C_{n+1}(Y)` using `Sigma.desc` and `prismSimplex`,
2. proving the boundary identity `∂ P + P ∂ = g_* − f_*`,
3. packaging into the `Homotopy` structure.

This file replaces that data sorry with a *propositional* existence
sorry `Nonempty (Homotopy …)`. The original consumer in
`SingularH1Homotopy.lean` only needs `Homotopy.homologyMap_eq`, which
follows from any inhabitant of `Homotopy …`, so `Nonempty` suffices.

The remaining sorry is therefore strictly less content than the
original: the original required *constructing* the data (along with
proving the comm identity); the new obligation only requires showing
*existence*. Any concrete prism-construction discharge of the original
sorry equally discharges this one via `⟨_⟩`.

## What needs to be filled in (bottom-up content)

Given a homotopy `H : ContinuousMap.Homotopy f g` between
`f, g : X → Y`, one defines the chain-level prism operator at degree
`n` on a generator `σ : C(stdSimplex ℝ (Fin (n+1)), X)` of the singular
chain complex by

  `P_n σ := Σ_{i : Fin (n+1)} (-1)^i • [prismSimplex n i H σ]`

(where `[·]` denotes the basis element of the singular chain group).
The chain homotopy identity to verify is

  `(sChain.map f).f n = dNext n P + prevD n P + (sChain.map g).f n`.

Hatcher's proof of this identity uses three combinatorial facts:
* `prismSimplex_top_face`     — `∂_0 (prismSimplex n 0 H σ) = g ∘ σ`
* `prismSimplex_bottom_face`  — `∂_{n+1} (prismSimplex n n H σ) = f ∘ σ`
* `prismSimplex_diagonal_face`— `∂_{i+1} (prismSimplex n i H σ)
                                = ∂_{i+1} (prismSimplex n (i+1) H σ)`

(All three are sorry-free in `Jacobian/Periods/PrismConstruction.lean`.)
The remaining ingredient is the *side-face* identity, identifying the
`j`-th face of the `i`-th prism simplex (for `j ≠ i, i+1`, or for
`j = 0` with `i ≠ 0`, or for `j = n+1` with `i ≠ n`) with the prism
applied to a face of `σ`. This is the missing piece, plus the bookkeeping
to assemble these into the boundary identity.
-/

noncomputable section

namespace JacobianChallenge.Periods

open AlgebraicTopology CategoryTheory

/-- **Chain-level prism homotopy, existence form.** Given a homotopy
`H : f ≃ g` between continuous maps `f, g : X → Y`, the singular chain
complex functor (with ℤ-coefficients) sends `f` and `g` to chain maps
that are homotopic via the prism construction.

This is the *categorical assembly* of the prism construction
(`prismSimplex` and friends in `Jacobian/Periods/PrismConstruction.lean`)
into a `HomologicalComplex.Homotopy`. The construction is described in
Hatcher §2.1, Lemma 2.10.

**Status:** isolated as a single existence sorry, replacing the original
*data*-level sorry on `Homotopy …` in
`Jacobian/Periods/SingularH1Homotopy.lean`. The propositional form
(`Nonempty …`) is sufficient for downstream applications — the only
consumer is `Homotopy.homologyMap_eq`, which is satisfied by any
inhabitant.

**To discharge:** define the chain operator
`P_n : C_n(X) ⟶ C_{n+1}(Y)` via `Limits.Sigma.desc` and `prismSimplex`,
verify the boundary identity (using the diagonal-face cancellation
plus a still-needed *side-face* identity), package as a `Homotopy`,
and `exact ⟨_⟩`. -/
theorem prism_chainHomotopy_exists
    {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
    {f g : C(X, Y)} (_H : ContinuousMap.Homotopy f g) :
    Nonempty (Homotopy
      (((AlgebraicTopology.singularChainComplexFunctor (ModuleCat ℤ)).obj
          (ModuleCat.of ℤ ℤ)).map (TopCat.ofHom f))
      (((AlgebraicTopology.singularChainComplexFunctor (ModuleCat ℤ)).obj
          (ModuleCat.of ℤ ℤ)).map (TopCat.ofHom g))) := by
  -- Bottom-up content: prism construction (Hatcher §2.1 Lemma 2.10).
  -- See `Jacobian/Periods/PrismConstruction.lean` for the geometric data
  -- (`prismSimplex`, top/bottom/diagonal face identities), all sorry-free.
  -- The missing piece is the categorical assembly: define the chain-level
  -- operator using `Limits.Sigma.desc`, verify the boundary identity, and
  -- package as `Homotopy`.
  sorry

end JacobianChallenge.Periods

end
