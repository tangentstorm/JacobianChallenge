/-
Copyright (c) 2026 Jacobian Challenge contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.AlgebraicTopology.SingularHomology.Basic
import Mathlib.Algebra.Category.ModuleCat.Basic
import Jacobian.Periods.PrismConstruction
import Jacobian.Periods.PrismChainBridge

/-!
# Combinatorial identity for the chain-level prism boundary

This file isolates the residual sorry of
`prismChain_succ_combinatorial_identity` (in
`Jacobian/Periods/PrismChainHomotopy.lean`) and decomposes it into
five smaller, individually-named obligations.

## The identity

For a homotopy `H : f ≃ g`, a degree-`(i' + 1)` simplex
`s : SingSimplex (i' + 1) X`, and the chain prism operator at degree
`i' + 1`, the boundary identity reduces to the equation

```
∑_{l ∈ Fin(i'+2), j ∈ Fin(i'+3)} (-1)^(l + 1 + j) • basis(P_l ∘ δ_j)
  = -basis(g ∘ s) + basis(f ∘ s)
    - ∑_{j' ∈ Fin(i'+2), l' ∈ Fin(i'+1)}
        (-1)^(j' + l' + 1) • basis(P'_l' ∘ (s ∘ δ_j'))
```

where `P_l = prismSimplex (i'+1) l H s` is the staircase
`(i'+2)`-simplex and `P'_l' = prismSimplex i' l' H _` is the staircase
`(i'+1)`-simplex over a face of `s`.

## Strategy: partition the LHS index set

Partition the `(i'+2) × (i'+3)`-element LHS index set into five
disjoint regions:

* **Top** `(0, 0)` — face 0 of `P_0`. By
  `prismSimplex_top_face`, equals `g ∘ s`. Contributes
  `(-1)^(0+1+0) • basis(g ∘ s) = -basis(g ∘ s)`.
* **Bottom** `(i'+1, i'+2)` — face `(i'+2)` of `P_{i'+1}`. By
  `prismSimplex_bottom_face`, equals `f ∘ s`. Contributes
  `(-1)^((i'+1)+1+(i'+2)) • basis(f ∘ s) = +basis(f ∘ s)`.
* **Diagonal upper** `(l, l+1)` for `l ∈ Fin(i'+1)` — face `(l+1)` of
  `P_l`. The sign is `(-1)^(2l+2) = +1`.
* **Diagonal lower** `(l+1, l+1)` for `l ∈ Fin(i'+1)` — face `(l+1)`
  of `P_{l+1}`. The sign is `(-1)^(2l+3) = -1`. By
  `prismSimplex_diagonal_face`, the simplex equals the diagonal-upper
  case, so the two cancel pairwise.
* **Lower side** `(l, j)` with `j.val < l.val` — face `j` of `P_l`.
  By `prismSimplex_side_face_lower`, equals
  `prismSimplex i' (l-1) H (s ∘ δ_j)`.
* **Upper side** `(l, j)` with `l.val + 1 < j.val` — face `j` of `P_l`.
  By `prismSimplex_side_face_upper`, equals
  `prismSimplex i' l H (s ∘ δ_{j-1})`.

The lower-side and upper-side contributions, taken together,
re-index to exactly the negative of the dNext expansion.

## Status

* `prismChain_topContribution` — top-face contribution (sorry, ≤ 30 LOC).
* `prismChain_bottomContribution` — bottom-face contribution
  (sorry, ≤ 30 LOC).
* `prismChain_diagonalCancellation` — the two diagonal sums cancel
  (sorry, ≤ 60 LOC; uses `prismSimplex_diagonal_face`).
* `prismChain_lowerSideReindex` — lower-side sum re-indexes to
  `-(j' ≤ l')` part of `dNext_sum` (sorry, ≤ 100 LOC; uses
  `prismSimplex_side_face_lower` and a `Finset.sum_bij`).
* `prismChain_upperSideReindex` — upper-side sum re-indexes to
  `-(j' > l')` part of `dNext_sum` (sorry, ≤ 100 LOC; uses
  `prismSimplex_side_face_upper` and a `Finset.sum_bij`).
* `prismChain_LHS_eq_partition` — assembly via
  `Finset.sum_disjUnion` (sorry, ≤ 80 LOC of partition
  bookkeeping).

The goal is for each named obligation to be at most ~100 LOC; the
total budget remains ~300 LOC, but distributed across five focused
proofs rather than one monolith.
-/

noncomputable section

namespace JacobianChallenge.Periods

open AlgebraicTopology CategoryTheory Limits HomologicalComplex

/-! ### Index helpers for the partition. -/

/-- The Cartesian product index set of the LHS double sum:
`Fin (i' + 2) × Fin (i' + 3)`. -/
abbrev prismIndex (i' : ℕ) : Type := Fin (i' + 2) × Fin (i' + 3)

/-- Top index `(0, 0)`. -/
def prismIndex.top (i' : ℕ) : prismIndex i' :=
  (⟨0, by omega⟩, ⟨0, by omega⟩)

/-- Bottom index `(i' + 1, i' + 2)`. -/
def prismIndex.bot (i' : ℕ) : prismIndex i' :=
  (⟨i' + 1, by omega⟩, ⟨i' + 2, by omega⟩)

/-- Diagonal upper index `(l, l + 1)` for `l : Fin (i' + 1)`. -/
def prismIndex.diagUpper (i' : ℕ) (l : Fin (i' + 1)) : prismIndex i' :=
  (⟨l.val, by have := l.isLt; omega⟩, ⟨l.val + 1, by have := l.isLt; omega⟩)

/-- Diagonal lower index `(l + 1, l + 1)` for `l : Fin (i' + 1)`. -/
def prismIndex.diagLower (i' : ℕ) (l : Fin (i' + 1)) : prismIndex i' :=
  (⟨l.val + 1, by have := l.isLt; omega⟩, ⟨l.val + 1, by have := l.isLt; omega⟩)

/-! ### The summand definitions

These two helpers extract the building block of each side of the
combinatorial identity. They are stated as morphisms in `ModuleCat ℤ`
to match the morphism shape of `singChain_basis` and the existing
`prismChain_summand` in `PrismChainHomotopy.lean`. -/

/-- The summand of the LHS double sum at index `(l, j)`, equal to
`(-1)^(l + 1 + j) • basis((prismSimplex (i'+1) l H s) ∘ δ_j)`. -/
def prismChain_LHS_summand
    {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
    {f g : C(X, Y)} (H : ContinuousMap.Homotopy f g) (i' : ℕ)
    (s : SingSimplex (i' + 1) X) (lj : prismIndex i') :
    ModuleCat.of ℤ ℤ ⟶ singChain (i' + 1) Y :=
  ((-1 : ℤ) ^ (lj.1.val + 1 + lj.2.val)) • singChain_basis
    ((prismSimplex (i' + 1) lj.1 H s).comp (stdSimplexFaceInclusion (i' + 1) lj.2))

/-- The summand of the dNext expansion at index `(j', l')`, equal to
`(-1)^(j' + l' + 1) • basis(prismSimplex i' l' H (s ∘ δ_j'))`. -/
def prismChain_dNext_summand
    {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
    {f g : C(X, Y)} (H : ContinuousMap.Homotopy f g) (i' : ℕ)
    (s : SingSimplex (i' + 1) X)
    (j' : Fin (i' + 2)) (l' : Fin (i' + 1)) :
    ModuleCat.of ℤ ℤ ⟶ singChain (i' + 1) Y :=
  ((-1 : ℤ) ^ (j'.val + l'.val + 1)) • singChain_basis
    (prismSimplex i' l' H (s.comp (stdSimplexFaceInclusion i' j')))

/-! ### The five named contributions

Each contribution computes the partial sum of the LHS over one
region of the partition. -/

/-- **Top contribution.** The summand at `(0, 0)` equals
`-basis(g ∘ s)`.

Proof sketch (≤ 30 LOC):
* `prismIndex.top` unfolds to `(⟨0, _⟩, ⟨0, _⟩)`.
* `(-1)^(0 + 1 + 0) = -1`.
* The composition `(prismSimplex (i'+1) ⟨0, _⟩ H s).comp (stdSimplexFaceInclusion (i'+1) ⟨0, _⟩)`
  evaluates pointwise to `g (s p)` by `prismSimplex_top_face`.
* `singChain_basis` of the result equals `singChain_basis (g.comp s)`.
-/
theorem prismChain_topContribution
    {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
    {f g : C(X, Y)} (H : ContinuousMap.Homotopy f g) (i' : ℕ)
    (s : SingSimplex (i' + 1) X) :
    prismChain_LHS_summand H i' s (prismIndex.top i') =
      -singChain_basis (g.comp s) := by
  unfold prismChain_LHS_summand prismIndex.top
  -- Sign: (-1)^(0 + 1 + 0) = -1.
  -- Simplex: prismSimplex (i'+1) ⟨0, _⟩ H s ∘ δ_⟨0, _⟩ = g ∘ s by
  -- prismSimplex_top_face.
  have hsimp : (prismSimplex (i' + 1) ⟨0, by omega⟩ H s).comp
        (stdSimplexFaceInclusion (i' + 1) ⟨0, by omega⟩) = g.comp s := by
    ext p
    -- prismSimplex_top_face : prismSimplex n ⟨0, _⟩ H s (δ₀ p) = g (s p)
    -- Here n = i' + 1.
    exact prismSimplex_top_face (n := i' + 1) H s p
  rw [hsimp]
  -- Goal: (-1 : ℤ)^(0 + 1 + 0) • singChain_basis (g.comp s) = -singChain_basis (g.comp s)
  show ((-1 : ℤ) ^ (1 : ℕ)) • singChain_basis (g.comp s) = -singChain_basis (g.comp s)
  rw [pow_one, neg_one_zsmul]

/-- **Bottom contribution.** The summand at `(i'+1, i'+2)` equals
`+basis(f ∘ s)`.

Proof sketch (≤ 30 LOC):
* `prismIndex.bot` unfolds to `(⟨i'+1, _⟩, ⟨i'+2, _⟩)`.
* `(-1)^((i'+1) + 1 + (i'+2)) = (-1)^(2*i' + 4) = 1`.
* The composition equals `f.comp s` pointwise by
  `prismSimplex_bottom_face` (after rewriting the face index
  `⟨i'+2, _⟩ = Fin.last (i' + 2)`).
-/
theorem prismChain_bottomContribution
    {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
    {f g : C(X, Y)} (H : ContinuousMap.Homotopy f g) (i' : ℕ)
    (s : SingSimplex (i' + 1) X) :
    prismChain_LHS_summand H i' s (prismIndex.bot i') =
      singChain_basis (f.comp s) := by
  unfold prismChain_LHS_summand prismIndex.bot
  -- Simplex equals f.comp s by prismSimplex_bottom_face.
  have hsimp : (prismSimplex (i' + 1) ⟨i' + 1, by omega⟩ H s).comp
        (stdSimplexFaceInclusion (i' + 1) ⟨i' + 2, by omega⟩) = f.comp s := by
    ext p
    -- prismSimplex_bottom_face : prismSimplex n ⟨n, _⟩ H s (δ_{Fin.last (n+1)} p) = f (s p)
    -- For n = i'+1: ⟨n, _⟩ = ⟨i'+1, _⟩ and Fin.last (i'+2) = ⟨i'+2, _⟩ definitionally.
    exact prismSimplex_bottom_face (n := i' + 1) H s p
  rw [hsimp]
  -- Sign: (i'+1) + 1 + (i'+2) = 2 * (i'+2) is even, so (-1)^(...) = 1.
  show ((-1 : ℤ) ^ ((i' + 1) + 1 + (i' + 2))) • singChain_basis (f.comp s) =
      singChain_basis (f.comp s)
  have heven : Even ((i' + 1) + 1 + (i' + 2)) := ⟨i' + 2, by ring⟩
  rw [heven.neg_one_pow, one_zsmul]

/-- **Diagonal cancellation.** The pair of summands at
`(l, l+1)` and `(l+1, l+1)` add to `0`.

Proof sketch (≤ 60 LOC):
* Sign at diagUpper: `(-1)^(l + 1 + (l + 1)) = +1`.
* Sign at diagLower: `(-1)^((l + 1) + 1 + (l + 1)) = -1`.
* The two compositions are equal as continuous maps via
  `prismSimplex_diagonal_face` applied with `ι = l`, then
  `ContinuousMap.ext`.
* `+basis(...) + (-1) • basis(...) = 0` since the simplices match.
-/
theorem prismChain_diagonalCancellation
    {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
    {f g : C(X, Y)} (H : ContinuousMap.Homotopy f g) (i' : ℕ)
    (s : SingSimplex (i' + 1) X) (l : Fin (i' + 1)) :
    prismChain_LHS_summand H i' s (prismIndex.diagUpper i' l) +
      prismChain_LHS_summand H i' s (prismIndex.diagLower i' l) = 0 := by
  unfold prismChain_LHS_summand prismIndex.diagUpper prismIndex.diagLower
  -- The two compositions are equal as continuous maps via prismSimplex_diagonal_face.
  have hsimp : (prismSimplex (i' + 1) ⟨l.val + 1, by have := l.isLt; omega⟩ H s).comp
        (stdSimplexFaceInclusion (i' + 1) ⟨l.val + 1, by have := l.isLt; omega⟩) =
      (prismSimplex (i' + 1) ⟨l.val, by have := l.isLt; omega⟩ H s).comp
        (stdSimplexFaceInclusion (i' + 1) ⟨l.val + 1, by have := l.isLt; omega⟩) := by
    ext p
    exact (prismSimplex_diagonal_face (n := i' + 1) H s l p).symm
  rw [hsimp]
  -- Sign at diagUpper: (-1)^(l + 1 + (l + 1)) = (-1)^(2l + 2) = +1
  -- Sign at diagLower: (-1)^((l + 1) + 1 + (l + 1)) = (-1)^(2l + 3) = -1
  have h1 : Even (l.val + 1 + (l.val + 1)) := ⟨l.val + 1, by ring⟩
  have h2 : (l.val + 1) + 1 + (l.val + 1) = (l.val + 1 + (l.val + 1)) + 1 := by ring
  rw [h1.neg_one_pow, h2, pow_succ, h1.neg_one_pow, one_mul, one_zsmul, neg_one_zsmul]
  exact add_neg_cancel _

/-! ### Side-face re-indexings

The two side regions of the partition together give the lower and
upper halves of the dNext double sum, with an overall sign flip. -/

/-- **Lower side re-indexing.** The sum of LHS summands over
`(l, j)` with `j.val < l.val` equals the negative of the dNext
sub-sum over `(j', l')` with `j'.val ≤ l'.val`.

Bijection: `(l, j) ↦ (j' := ⟨j.val, _⟩, l' := ⟨l.val - 1, _⟩)`.

Proof sketch (≤ 100 LOC):
* Apply `prismSimplex_side_face_lower` to rewrite each LHS
  composition as `prismSimplex i' ⟨l - 1, _⟩ H (s ∘ δ_⟨j, _⟩)`
  (pointwise, then `ContinuousMap.ext`).
* `(-1)^(l + 1 + j) = (-1)^((l - 1) + 1 + 1 + j) = -(-1)^((l-1) + 1 + j)`,
  matching `-((-1)^(j' + l' + 1))`.
* Apply `Finset.sum_bij` with the bijection above; both sides have
  size `(i'+1)(i'+2)/2`.
-/
theorem prismChain_lowerSideReindex
    {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
    {f g : C(X, Y)} (H : ContinuousMap.Homotopy f g) (i' : ℕ)
    (s : SingSimplex (i' + 1) X) :
    (∑ lj ∈ (Finset.univ : Finset (prismIndex i')).filter
        (fun lj => lj.2.val < lj.1.val),
      prismChain_LHS_summand H i' s lj) =
      -(∑ jl ∈ (Finset.univ : Finset (Fin (i' + 2) × Fin (i' + 1))).filter
          (fun jl => jl.1.val ≤ jl.2.val),
        prismChain_dNext_summand H i' s jl.1 jl.2) := by
  sorry

/-- **Upper side re-indexing.** The sum of LHS summands over
`(l, j)` with `l.val + 1 < j.val` equals the negative of the dNext
sub-sum over `(j', l')` with `j'.val > l'.val`.

Bijection: `(l, j) ↦ (j' := ⟨j.val - 1, _⟩, l' := ⟨l.val, _⟩)`.

Proof sketch (≤ 100 LOC):
* Apply `prismSimplex_side_face_upper` to rewrite each LHS
  composition as `prismSimplex i' ⟨l, _⟩ H (s ∘ δ_⟨j - 1, _⟩)`.
* Sign: `(-1)^(l + 1 + j) = (-1)^(l + 1 + (j' + 1)) = (-1)^(l + j' + 2) = (-1)^(l' + j')`,
  matching `-((-1)^(j' + l' + 1))`.
* Apply `Finset.sum_bij` with the bijection above.
-/
theorem prismChain_upperSideReindex
    {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
    {f g : C(X, Y)} (H : ContinuousMap.Homotopy f g) (i' : ℕ)
    (s : SingSimplex (i' + 1) X) :
    (∑ lj ∈ (Finset.univ : Finset (prismIndex i')).filter
        (fun lj => lj.1.val + 1 < lj.2.val),
      prismChain_LHS_summand H i' s lj) =
      -(∑ jl ∈ (Finset.univ : Finset (Fin (i' + 2) × Fin (i' + 1))).filter
          (fun jl => jl.2.val < jl.1.val),
        prismChain_dNext_summand H i' s jl.1 jl.2) := by
  sorry

/-! ### Assembly

The five contributions partition the full LHS index set. Combined
with `Finset.sum_product'` (collapsing the double sum to a sum over
the Cartesian product) and `Finset.sum_disjUnion` (splitting the
product into the five regions), the boundary identity follows. -/

/-- **The full combinatorial identity, in summand form.** The total
LHS sum over the Cartesian product `prismIndex i'` equals
`-basis(g ∘ s) + basis(f ∘ s)` minus the dNext double sum (also
over the Cartesian product).

This is the named obligation that `prismChain_succ_combinatorial_identity`
in `PrismChainHomotopy.lean` unwinds to after applying
`Finset.sum_product'` to both sides.

Proof sketch (≤ 80 LOC):
* Partition `Finset.univ : Finset (prismIndex i')` into:
  - `{prismIndex.top i'}` (singleton)
  - `{prismIndex.bot i'}` (singleton)
  - image of `prismIndex.diagUpper i'` (size `i' + 1`, by injectivity)
  - image of `prismIndex.diagLower i'` (size `i' + 1`, by injectivity)
  - the lower-side filter `{lj | lj.2.val < lj.1.val}`
  - the upper-side filter `{lj | lj.1.val + 1 < lj.2.val}`.
* Sum each region using the named contribution above.
* Pair diagUpper/diagLower via `prismChain_diagonalCancellation`,
  yielding `0`.
* Pair lower/upper sides via the dNext re-indexings, yielding
  `-(dNext_sum)` (the union of `{j' ≤ l'}` and `{j' > l'}` covers
  the full dNext index set `Fin(i'+2) × Fin(i'+1)`).
-/
theorem prismChain_LHS_eq_partition
    {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
    {f g : C(X, Y)} (H : ContinuousMap.Homotopy f g) (i' : ℕ)
    (s : SingSimplex (i' + 1) X) :
    (∑ lj : prismIndex i', prismChain_LHS_summand H i' s lj) =
      -singChain_basis (g.comp s) + singChain_basis (f.comp s)
        - (∑ jl : Fin (i' + 2) × Fin (i' + 1),
            prismChain_dNext_summand H i' s jl.1 jl.2) := by
  sorry

end JacobianChallenge.Periods

end
