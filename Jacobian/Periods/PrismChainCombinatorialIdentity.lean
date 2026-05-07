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

All six named obligations are **sorry-free**:

* `prismChain_topContribution` — top-face contribution.
* `prismChain_bottomContribution` — bottom-face contribution.
* `prismChain_diagonalCancellation` — the two diagonal sums cancel
  (uses `prismSimplex_diagonal_face`).
* `prismChain_lowerSideReindex` — lower-side sum re-indexes to
  `-(j' ≤ l')` part of `dNext_sum` (uses `prismSimplex_side_face_lower`
  and `Finset.sum_nbij'`).
* `prismChain_upperSideReindex` — upper-side sum re-indexes to
  `-(j' > l')` part of `dNext_sum` (uses `prismSimplex_side_face_upper`
  and `Finset.sum_nbij'`).
* `prismChain_LHS_eq_partition` — assembly via the 6-region partition
  (`{top}`, `{bot}`, `image diagUpper`, `image diagLower`, lower-side
  filter, upper-side filter), with the diagonal sums cancelling
  pairwise.

This file fully discharges the residual combinatorial identity in
`prismChain_succ_combinatorial_identity`.
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
  rw [← Finset.sum_neg_distrib]
  -- Total forward / inverse maps using min-capping for the bounds.
  refine Finset.sum_nbij'
    (fun (lj : prismIndex i') =>
      ((⟨min lj.2.val (i' + 1), by omega⟩ : Fin (i' + 2)),
       (⟨lj.1.val - 1, by have := lj.1.isLt; omega⟩ : Fin (i' + 1))))
    (fun (jl : Fin (i' + 2) × Fin (i' + 1)) =>
      ((⟨jl.2.val + 1, by have := jl.2.isLt; omega⟩ : Fin (i' + 2)),
       (⟨jl.1.val, by have := jl.1.isLt; omega⟩ : Fin (i' + 3))))
    ?_ ?_ ?_ ?_ ?_
  · -- forward image lands in target filter
    intro lj hlj
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hlj ⊢
    have hbound : lj.1.val < i' + 2 := lj.1.isLt
    omega
  · -- inverse image lands in source filter
    intro jl hjl
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hjl ⊢
    omega
  · -- left_inv: inv(forward(lj)) = lj
    intro lj hlj
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hlj
    have hbound : lj.1.val < i' + 2 := lj.1.isLt
    have hge : 1 ≤ lj.1.val := by omega
    have hmin : min lj.2.val (i' + 1) = lj.2.val := by omega
    refine Prod.ext (Fin.ext ?_) (Fin.ext ?_)
    · show lj.1.val - 1 + 1 = lj.1.val
      omega
    · show min lj.2.val (i' + 1) = lj.2.val
      exact hmin
  · -- right_inv: forward(inv(jl)) = jl
    intro jl _hjl
    have hbound : jl.1.val ≤ i' + 1 := by have := jl.1.isLt; omega
    refine Prod.ext (Fin.ext ?_) (Fin.ext ?_)
    · show min jl.1.val (i' + 1) = jl.1.val
      exact min_eq_left hbound
    · rfl
  · -- equation: LHS_summand lj = -dNext_summand at the bijected index
    intro lj hlj
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hlj
    have hjl : lj.2.val < lj.1.val := hlj
    have hbound : lj.1.val < i' + 2 := lj.1.isLt
    -- The bijected index has j.val component = min lj.2.val (i'+1) = lj.2.val
    -- (since lj.2.val < lj.1.val ≤ i' + 1).
    have hmin : min lj.2.val (i' + 1) = lj.2.val := by omega
    -- Sign factorization: (-1)^(l + 1 + j) = - (-1)^(j + (l-1) + 1)
    have hsign : ((-1 : ℤ) ^ (lj.1.val + 1 + lj.2.val)) =
        -((-1 : ℤ) ^ (lj.2.val + (lj.1.val - 1) + 1)) := by
      have heq : lj.1.val + 1 + lj.2.val =
          (lj.2.val + (lj.1.val - 1) + 1) + 1 := by omega
      rw [heq, pow_succ]; ring
    -- Simplex equality from prismSimplex_side_face_lower.
    have hsimp : (prismSimplex (i' + 1) lj.1 H s).comp
          (stdSimplexFaceInclusion (i' + 1) lj.2) =
        prismSimplex i' ⟨lj.1.val - 1, by omega⟩ H
          (s.comp (stdSimplexFaceInclusion i' ⟨lj.2.val, by omega⟩)) := by
      ext p
      have := prismSimplex_side_face_lower (n := i') H lj.1 lj.2 hjl s p
      simpa [stdSimplexFaceInclusion] using this
    show prismChain_LHS_summand H i' s lj =
      -prismChain_dNext_summand H i' s
        ⟨min lj.2.val (i' + 1), by omega⟩ ⟨lj.1.val - 1, by omega⟩
    unfold prismChain_LHS_summand prismChain_dNext_summand
    -- The dNext summand uses ⟨min lj.2.val (i'+1), _⟩ which equals ⟨lj.2.val, _⟩.
    have hmin_fin : (⟨min lj.2.val (i' + 1), by omega⟩ : Fin (i' + 2)) =
        ⟨lj.2.val, by omega⟩ := Fin.ext hmin
    rw [hmin_fin, hsimp, hsign, neg_zsmul]

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
  rw [← Finset.sum_neg_distrib]
  refine Finset.sum_nbij'
    (fun (lj : prismIndex i') =>
      ((⟨lj.2.val - 1, by have := lj.2.isLt; omega⟩ : Fin (i' + 2)),
       (⟨min lj.1.val i', by omega⟩ : Fin (i' + 1))))
    (fun (jl : Fin (i' + 2) × Fin (i' + 1)) =>
      ((⟨jl.2.val, by have := jl.2.isLt; omega⟩ : Fin (i' + 2)),
       (⟨jl.1.val + 1, by have := jl.1.isLt; omega⟩ : Fin (i' + 3))))
    ?_ ?_ ?_ ?_ ?_
  · -- forward image lands in target filter (jl.2.val < jl.1.val)
    intro lj hlj
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hlj ⊢
    have hbound : lj.2.val < i' + 3 := lj.2.isLt
    omega
  · -- inverse image lands in source filter (lj.1.val + 1 < lj.2.val)
    intro jl hjl
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hjl ⊢
    omega
  · -- left_inv: inv(forward(lj)) = lj
    intro lj hlj
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hlj
    have hbound : lj.2.val < i' + 3 := lj.2.isLt
    have hge : 1 ≤ lj.2.val := by omega
    have hmin_l : min lj.1.val i' = lj.1.val := by omega
    refine Prod.ext (Fin.ext ?_) (Fin.ext ?_)
    · show min lj.1.val i' = lj.1.val
      exact hmin_l
    · show lj.2.val - 1 + 1 = lj.2.val
      omega
  · -- right_inv: forward(inv(jl)) = jl
    intro jl _hjl
    have hbound : jl.2.val ≤ i' := by have := jl.2.isLt; omega
    refine Prod.ext (Fin.ext ?_) (Fin.ext ?_)
    · rfl
    · show min jl.2.val i' = jl.2.val
      exact min_eq_left hbound
  · -- equation: LHS_summand lj = -dNext_summand at the bijected index
    intro lj hlj
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hlj
    have hjl : lj.1.val + 1 < lj.2.val := hlj
    have hbound1 : lj.1.val < i' + 2 := lj.1.isLt
    have hbound2 : lj.2.val < i' + 3 := lj.2.isLt
    have hmin_l : min lj.1.val i' = lj.1.val := by omega
    -- Sign factorization: (-1)^(l + 1 + j) = -(-1)^((j-1) + l + 1)
    have hsign : ((-1 : ℤ) ^ (lj.1.val + 1 + lj.2.val)) =
        -((-1 : ℤ) ^ ((lj.2.val - 1) + lj.1.val + 1)) := by
      have heq : lj.1.val + 1 + lj.2.val =
          ((lj.2.val - 1) + lj.1.val + 1) + 1 := by omega
      rw [heq, pow_succ]; ring
    -- Simplex equality from prismSimplex_side_face_upper.
    have hsimp : (prismSimplex (i' + 1) lj.1 H s).comp
          (stdSimplexFaceInclusion (i' + 1) lj.2) =
        prismSimplex i' ⟨lj.1.val, by omega⟩ H
          (s.comp (stdSimplexFaceInclusion i' ⟨lj.2.val - 1, by omega⟩)) := by
      ext p
      have := prismSimplex_side_face_upper (n := i') H lj.1 lj.2 hjl s p
      simpa [stdSimplexFaceInclusion] using this
    show prismChain_LHS_summand H i' s lj =
      -prismChain_dNext_summand H i' s
        ⟨lj.2.val - 1, by omega⟩ ⟨min lj.1.val i', by omega⟩
    unfold prismChain_LHS_summand prismChain_dNext_summand
    have hmin_fin : (⟨min lj.1.val i', by omega⟩ : Fin (i' + 1)) =
        ⟨lj.1.val, by omega⟩ := Fin.ext hmin_l
    rw [hmin_fin, hsimp, hsign, neg_zsmul]

/-! ### Assembly

The five contributions partition the full LHS index set. Combined
with `Finset.sum_product'` (collapsing the double sum to a sum over
the Cartesian product) and `Finset.sum_disjUnion` (splitting the
product into the five regions), the boundary identity follows.

#### Partition helper

The full Cartesian sum decomposes as the sum of six disjoint
sub-sums. We prove this as a single named partition equation, using
`Finset.sum_filter_add_sum_filter_not` to peel off regions and
`Finset.sum_image` for the diagonal sub-sums. -/

private lemma diagUpper_injective (i' : ℕ) :
    Function.Injective (prismIndex.diagUpper i') := by
  intro l₁ l₂ h
  simp only [prismIndex.diagUpper, Prod.mk.injEq] at h
  obtain ⟨h1, _⟩ := h
  exact Fin.ext (Fin.mk.injEq _ _ _ _ |>.mp h1)

private lemma diagLower_injective (i' : ℕ) :
    Function.Injective (prismIndex.diagLower i') := by
  intro l₁ l₂ h
  simp only [prismIndex.diagLower, Prod.mk.injEq] at h
  obtain ⟨h1, _⟩ := h
  exact Fin.ext (by
    have h2 : l₁.val + 1 = l₂.val + 1 := Fin.mk.injEq _ _ _ _ |>.mp h1
    omega)

/-- **The full combinatorial identity, in summand form.** The total
LHS sum over the Cartesian product `prismIndex i'` equals
`-basis(g ∘ s) + basis(f ∘ s)` minus the dNext double sum (also
over the Cartesian product).

This is the named obligation that `prismChain_succ_combinatorial_identity`
in `PrismChainHomotopy.lean` unwinds to after applying
`Finset.sum_product'` to both sides. -/
theorem prismChain_LHS_eq_partition
    {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
    {f g : C(X, Y)} (H : ContinuousMap.Homotopy f g) (i' : ℕ)
    (s : SingSimplex (i' + 1) X) :
    (∑ lj : prismIndex i', prismChain_LHS_summand H i' s lj) =
      -singChain_basis (g.comp s) + singChain_basis (f.comp s)
        - (∑ jl : Fin (i' + 2) × Fin (i' + 1),
            prismChain_dNext_summand H i' s jl.1 jl.2) := by
  -- Notation.
  set fLHS : prismIndex i' → (ModuleCat.of ℤ ℤ ⟶ singChain (i' + 1) Y) :=
    fun lj => prismChain_LHS_summand H i' s lj with hfLHS_def
  set fdN : Fin (i' + 2) × Fin (i' + 1) → (ModuleCat.of ℤ ℤ ⟶ singChain (i' + 1) Y) :=
    fun jl => prismChain_dNext_summand H i' s jl.1 jl.2 with hfdN_def
  -- Filter equalities for the partition.
  -- (1) The `j = l` filter equals `{top} ∪ image(diagLower)`.
  have h_eq_l : ((Finset.univ : Finset (prismIndex i')).filter
        (fun lj => lj.2.val = lj.1.val)) =
      {prismIndex.top i'} ∪
      (Finset.univ : Finset (Fin (i' + 1))).image (prismIndex.diagLower i') := by
    apply Finset.ext; intro lj
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_union,
      Finset.mem_singleton, Finset.mem_image]
    constructor
    · intro h
      by_cases hl0 : lj.1.val = 0
      · left
        apply Prod.ext
        · apply Fin.ext; show lj.1.val = 0; exact hl0
        · apply Fin.ext; show lj.2.val = 0; omega
      · right
        have hbound : lj.1.val < i' + 2 := lj.1.isLt
        refine ⟨⟨lj.1.val - 1, by omega⟩, ?_⟩
        apply Prod.ext
        · apply Fin.ext; show lj.1.val - 1 + 1 = lj.1.val; omega
        · apply Fin.ext; show lj.1.val - 1 + 1 = lj.2.val; omega
    · rintro (rfl | ⟨l, rfl⟩)
      · show (prismIndex.top i').2.val = (prismIndex.top i').1.val
        rfl
      · show (prismIndex.diagLower i' l).2.val = (prismIndex.diagLower i' l).1.val
        rfl
  -- (2) The `j = l + 1` filter equals `image(diagUpper) ∪ {bot}`.
  have h_eq_l1 : ((Finset.univ : Finset (prismIndex i')).filter
        (fun lj => lj.2.val = lj.1.val + 1)) =
      (Finset.univ : Finset (Fin (i' + 1))).image (prismIndex.diagUpper i') ∪
      {prismIndex.bot i'} := by
    apply Finset.ext; intro lj
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_union,
      Finset.mem_singleton, Finset.mem_image]
    constructor
    · intro h
      by_cases hl_top : lj.1.val = i' + 1
      · right
        apply Prod.ext
        · apply Fin.ext; show lj.1.val = i' + 1; exact hl_top
        · apply Fin.ext; show lj.2.val = i' + 2; omega
      · left
        have hbound : lj.1.val < i' + 2 := lj.1.isLt
        refine ⟨⟨lj.1.val, by omega⟩, ?_⟩
        apply Prod.ext
        · apply Fin.ext; show lj.1.val = lj.1.val; rfl
        · apply Fin.ext; show lj.1.val + 1 = lj.2.val; omega
    · rintro (⟨l, rfl⟩ | rfl)
      · show (prismIndex.diagUpper i' l).2.val = (prismIndex.diagUpper i' l).1.val + 1
        rfl
      · show (prismIndex.bot i').2.val = (prismIndex.bot i').1.val + 1
        rfl
  -- (3) The `l ≤ j ≤ l+1` filter equals (j = l filter) ∪ (j = l+1 filter).
  have h_le_le : ((Finset.univ : Finset (prismIndex i')).filter
        (fun lj => lj.1.val ≤ lj.2.val ∧ lj.2.val ≤ lj.1.val + 1)) =
      ((Finset.univ : Finset (prismIndex i')).filter (fun lj => lj.2.val = lj.1.val)) ∪
      ((Finset.univ : Finset (prismIndex i')).filter (fun lj => lj.2.val = lj.1.val + 1)) := by
    apply Finset.ext; intro lj
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_union]
    omega
  -- (4) The `l ≤ j` filter equals (l + 1 < j filter) ∪ (l ≤ j ∧ j ≤ l + 1 filter).
  have h_le : ((Finset.univ : Finset (prismIndex i')).filter
        (fun lj => lj.1.val ≤ lj.2.val)) =
      ((Finset.univ : Finset (prismIndex i')).filter (fun lj => lj.1.val + 1 < lj.2.val)) ∪
      ((Finset.univ : Finset (prismIndex i')).filter
        (fun lj => lj.1.val ≤ lj.2.val ∧ lj.2.val ≤ lj.1.val + 1)) := by
    apply Finset.ext; intro lj
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_union]
    omega
  -- (5) `¬ (lj.2.val < lj.1.val)` is the same as `lj.1.val ≤ lj.2.val`.
  have h_not_lower : (Finset.univ : Finset (prismIndex i')).filter
        (fun lj => ¬ lj.2.val < lj.1.val) =
      (Finset.univ : Finset (prismIndex i')).filter (fun lj => lj.1.val ≤ lj.2.val) := by
    apply Finset.filter_congr
    intros; constructor <;> intros <;> omega
  -- Disjointness facts for the unions above.
  have h_disj_eql : Disjoint
      ({prismIndex.top i'} : Finset (prismIndex i'))
      ((Finset.univ : Finset (Fin (i' + 1))).image (prismIndex.diagLower i')) := by
    rw [Finset.disjoint_left]
    intros lj h1 h2
    rw [Finset.mem_singleton] at h1
    rw [Finset.mem_image] at h2
    obtain ⟨l, _, hl⟩ := h2
    have h1val : (prismIndex.diagLower i' l).1.val = (prismIndex.top i').1.val := by
      rw [hl, h1]
    -- By definition (prismIndex.diagLower i' l).1.val = l.val + 1
    -- and (prismIndex.top i').1.val = 0.
    have : l.val + 1 = 0 := h1val
    omega
  have h_disj_eql1 : Disjoint
      ((Finset.univ : Finset (Fin (i' + 1))).image (prismIndex.diagUpper i'))
      ({prismIndex.bot i'} : Finset (prismIndex i')) := by
    rw [Finset.disjoint_left]
    intros lj h1 h2
    rw [Finset.mem_image] at h1
    rw [Finset.mem_singleton] at h2
    obtain ⟨l, _, hl⟩ := h1
    have h1val : (prismIndex.diagUpper i' l).1.val = (prismIndex.bot i').1.val := by
      rw [hl, h2]
    -- By definition (prismIndex.diagUpper i' l).1.val = l.val
    -- and (prismIndex.bot i').1.val = i' + 1.
    have hbound : l.val < i' + 1 := l.isLt
    have : l.val = i' + 1 := h1val
    omega
  have h_disj_le_le : Disjoint
      ((Finset.univ : Finset (prismIndex i')).filter (fun lj => lj.2.val = lj.1.val))
      ((Finset.univ : Finset (prismIndex i')).filter (fun lj => lj.2.val = lj.1.val + 1)) := by
    rw [Finset.disjoint_filter]
    intros lj _ h₁ h₂; omega
  have h_disj_le : Disjoint
      ((Finset.univ : Finset (prismIndex i')).filter (fun lj => lj.1.val + 1 < lj.2.val))
      ((Finset.univ : Finset (prismIndex i')).filter
        (fun lj => lj.1.val ≤ lj.2.val ∧ lj.2.val ≤ lj.1.val + 1)) := by
    rw [Finset.disjoint_filter]
    intros lj _ h₁ h₂; omega
  -- Step 1: peel off lowerSide via sum_filter_add_sum_filter_not.
  rw [← Finset.sum_filter_add_sum_filter_not (Finset.univ : Finset (prismIndex i'))
    (fun lj => lj.2.val < lj.1.val) fLHS]
  rw [h_not_lower, h_le, Finset.sum_union h_disj_le, h_le_le,
    Finset.sum_union h_disj_le_le, h_eq_l, Finset.sum_union h_disj_eql,
    Finset.sum_singleton, Finset.sum_image
      (fun l _ l' _ heq => diagLower_injective i' heq), h_eq_l1,
    Finset.sum_union h_disj_eql1, Finset.sum_image
      (fun l _ l' _ heq => diagUpper_injective i' heq), Finset.sum_singleton]
  -- Apply named contributions.
  show (∑ lj ∈ Finset.univ.filter (fun lj : prismIndex i' => lj.2.val < lj.1.val),
            prismChain_LHS_summand H i' s lj) +
      ((∑ lj ∈ Finset.univ.filter (fun lj : prismIndex i' => lj.1.val + 1 < lj.2.val),
              prismChain_LHS_summand H i' s lj) +
        ((prismChain_LHS_summand H i' s (prismIndex.top i') +
            ∑ x ∈ (Finset.univ : Finset (Fin (i' + 1))),
              prismChain_LHS_summand H i' s (prismIndex.diagLower i' x)) +
          ((∑ x ∈ (Finset.univ : Finset (Fin (i' + 1))),
              prismChain_LHS_summand H i' s (prismIndex.diagUpper i' x)) +
            prismChain_LHS_summand H i' s (prismIndex.bot i')))) = _
  rw [prismChain_topContribution, prismChain_bottomContribution]
  -- Combine diagonal sums via diagonalCancellation.
  have h_diag :
      (∑ x : Fin (i' + 1), prismChain_LHS_summand H i' s (prismIndex.diagUpper i' x)) +
      (∑ x : Fin (i' + 1), prismChain_LHS_summand H i' s (prismIndex.diagLower i' x)) = 0 := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_eq_zero
    intro l _
    exact prismChain_diagonalCancellation H i' s l
  -- Apply lower/upper side reindexings.
  rw [prismChain_lowerSideReindex, prismChain_upperSideReindex]
  -- Combine the two dNext partial sums into the full sum.
  have h_dNext_partition :
      (∑ jl ∈ (Finset.univ : Finset (Fin (i' + 2) × Fin (i' + 1))).filter
            (fun jl => jl.1.val ≤ jl.2.val),
          prismChain_dNext_summand H i' s jl.1 jl.2) +
      (∑ jl ∈ (Finset.univ : Finset (Fin (i' + 2) × Fin (i' + 1))).filter
            (fun jl => jl.2.val < jl.1.val),
          prismChain_dNext_summand H i' s jl.1 jl.2) =
      (∑ jl : Fin (i' + 2) × Fin (i' + 1),
          prismChain_dNext_summand H i' s jl.1 jl.2) := by
    rw [← Finset.sum_filter_add_sum_filter_not (Finset.univ : Finset _)
      (fun jl : Fin (i' + 2) × Fin (i' + 1) => jl.1.val ≤ jl.2.val)]
    congr 1
    apply Finset.sum_congr _ (fun _ _ => rfl)
    apply Finset.filter_congr
    intros; constructor <;> intros <;> omega
  -- Final algebraic rearrangement using the diagonal cancellation and dNext partition.
  rw [← h_dNext_partition]
  -- Goal: lowerSide_partial + (upperSide_partial +
  --         ((-basis_g + diagL_sum) + (diagU_sum + basis_f))) =
  --       -basis_g + basis_f - (∑T_L + ∑T_U)
  -- After applying topContribution and bottomContribution (already done above),
  -- and lowerSideReindex/upperSideReindex (already done above),
  -- this reduces to: (-(∑T_L) + (-(∑T_U) + ((-basis_g + diagL) + (diagU + basis_f)))
  --                  = -basis_g + basis_f - (∑T_L + ∑T_U).
  -- Using h_diag (diagU + diagL = 0):
  set diagL_sum := ∑ x : Fin (i' + 1), prismChain_LHS_summand H i' s (prismIndex.diagLower i' x)
  set diagU_sum := ∑ x : Fin (i' + 1), prismChain_LHS_summand H i' s (prismIndex.diagUpper i' x)
  have hD : diagU_sum + diagL_sum = 0 := h_diag
  -- The remaining algebra is just commutativity/associativity using hD.
  set bg := singChain_basis (g.comp s)
  set bf := singChain_basis (f.comp s)
  set sL := ∑ jl ∈ (Finset.univ : Finset (Fin (i' + 2) × Fin (i' + 1))).filter
      (fun jl => jl.1.val ≤ jl.2.val), prismChain_dNext_summand H i' s jl.1 jl.2
  set sU := ∑ jl ∈ (Finset.univ : Finset (Fin (i' + 2) × Fin (i' + 1))).filter
      (fun jl => jl.2.val < jl.1.val), prismChain_dNext_summand H i' s jl.1 jl.2
  -- Goal: -sL + (-sU + ((-bg + diagL_sum) + (diagU_sum + bf))) = -bg + bf - (sL + sU)
  -- Rearrange via abel + hD.
  calc -sL + (-sU + ((-bg + diagL_sum) + (diagU_sum + bf)))
      = -bg + bf + (diagU_sum + diagL_sum) + (-sL + -sU) := by abel
    _ = -bg + bf + 0 + (-sL + -sU) := by rw [hD]
    _ = -bg + bf - (sL + sU) := by abel

end JacobianChallenge.Periods

end
