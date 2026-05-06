/-
Copyright (c) 2026 Jacobian Challenge contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.AlgebraicTopology.SingularHomology.Basic
import Mathlib.AlgebraicTopology.SingularSet
import Mathlib.AlgebraicTopology.TopologicalSimplex
import Mathlib.Algebra.Homology.Homotopy
import Mathlib.Topology.Homotopy.Basic
import Mathlib.Topology.UnitInterval
import Mathlib.Analysis.Convex.StdSimplex

/-!
# Prism construction for singular chain complexes

This file builds the classical *prism construction* (Hatcher §2.1, Lemma 2.10):
given a homotopy `H : ContinuousMap.Homotopy f g` between continuous maps
`f, g : X → Y`, we construct a chain homotopy at the level of singular chain
complexes between the induced maps `C_*(f)` and `C_*(g)`.

The construction proceeds via the *staircase subdivision* of the prism
`Δⁿ × [0,1]` into `n+1` `(n+1)`-simplices, indexed by `i ∈ Fin (n+1)`:
the `i`-th simplex has vertices

  `[(e₀, 0), …, (eᵢ, 0), (eᵢ, 1), (e_{i+1}, 1), …, (eₙ, 1)]`

In barycentric coordinates `(s₀, …, s_{n+1}) ∈ Δ^{n+1}`, the staircase map
`αᵢ : Δ^{n+1} → Δⁿ × [0,1]` sends:

* First (Δⁿ) component, coordinate `k`:
  - `s_k`        if `k < i`,
  - `s_i + s_{i+1}` if `k = i`,
  - `s_{k+1}`    if `k > i`.
* Second ([0,1]) component: `s_{i+1} + … + s_{n+1}`, equivalently
  `1 - (s₀ + … + sᵢ)`.

## Main definitions

* `JacobianChallenge.Periods.staircaseFirstCoord` — barycentric coordinate map
  `Fin (n+1) → ℝ` from a point in `Δ^{n+1}`.
* `JacobianChallenge.Periods.staircaseTimeCoord` — `[0,1]` coordinate.
* `JacobianChallenge.Periods.staircaseMap` — the continuous map
  `Δ^{n+1} → Δⁿ × [0,1]`.
* `JacobianChallenge.Periods.prismSimplex` — given a homotopy and a
  singular `n`-simplex, the `i`-th `(n+1)`-simplex of the prism.

## Status

The staircase maps and the prism simplex are fully constructed (sorry-free).
The chain-homotopy equation between `C_*(f)` and `C_*(g)` (the verification
that boundary cancellation gives `∂P + P∂ = g_* − f_*`) is isolated as a
single named sorry `prism_chainHomotopy_equation`, to be discharged by a
future combinatorial computation.
-/

noncomputable section

namespace JacobianChallenge.Periods

open Set unitInterval

/-! ### Staircase coordinates -/

variable (n : ℕ) (i : Fin (n + 1))

/-- The first (Δⁿ) coordinate of the staircase map `αᵢ`. Given barycentric
coordinates `f : Fin (n + 2) → ℝ` of a point in `Δ^{n+1}` and a target index
`k : Fin (n + 1)`, output:
* `f k.castSucc` if `k.val < i.val`
* `f i.castSucc + f i.succ` if `k.val = i.val`
* `f k.succ` if `k.val > i.val`. -/
def staircaseFirstCoord (f : Fin (n + 2) → ℝ) (k : Fin (n + 1)) : ℝ :=
  if k.val < i.val then f k.castSucc
  else if k.val = i.val then f i.castSucc + f i.succ
  else f k.succ

/-- The second ([0,1]) coordinate of the staircase map `αᵢ`. -/
def staircaseTimeCoord (f : Fin (n + 2) → ℝ) : ℝ :=
  ∑ j ∈ Finset.univ.filter (fun j : Fin (n + 2) => i.val < j.val), f j

/-! ### Sum identities for the staircase map -/

/-- Pointwise reformulation of `staircaseFirstCoord` using `Fin.succAbove`:
the first-coordinate function decomposes as the `succAbove`-pulled-back family
plus an extra `f i.castSucc` contribution at `k = i`. -/
theorem staircaseFirstCoord_eq
    (f : Fin (n + 2) → ℝ) (k : Fin (n + 1)) :
    staircaseFirstCoord n i f k =
      (if k = i then f i.castSucc else 0) + f (i.castSucc.succAbove k) := by
  unfold staircaseFirstCoord
  have hcs : k.castSucc.val = k.val := rfl
  have his : i.castSucc.val = i.val := rfl
  by_cases h1 : k.val < i.val
  · have hne : k ≠ i := fun h => by rw [h] at h1; exact lt_irrefl _ h1
    have hsa : i.castSucc.succAbove k = k.castSucc := by
      rw [Fin.succAbove, if_pos]
      exact Fin.mk_lt_mk.mpr h1
    rw [if_pos h1, hsa, if_neg hne, zero_add]
  · by_cases h2 : k.val = i.val
    · have hki : k = i := Fin.eq_of_val_eq h2
      have hsa : i.castSucc.succAbove k = k.succ := by
        rw [Fin.succAbove, if_neg]
        exact fun h => h1 (Fin.mk_lt_mk.mp h)
      rw [if_neg h1, if_pos h2, hsa, if_pos hki, hki, add_comm]
    · have hne : k ≠ i := fun h => h2 (h ▸ rfl)
      have hsa : i.castSucc.succAbove k = k.succ := by
        rw [Fin.succAbove, if_neg]
        exact fun h => h1 (Fin.mk_lt_mk.mp h)
      rw [if_neg h1, if_neg h2, hsa, if_neg hne, zero_add]

/-- The first-coordinate function preserves the simplex sum:
`∑_k staircaseFirstCoord n i f k = ∑_j f j`. -/
theorem staircaseFirstCoord_sum
    (f : Fin (n + 2) → ℝ) :
    ∑ k : Fin (n + 1), staircaseFirstCoord n i f k = ∑ j : Fin (n + 2), f j := by
  simp_rw [staircaseFirstCoord_eq]
  rw [Finset.sum_add_distrib]
  rw [Finset.sum_ite_eq' Finset.univ i (fun _ => f i.castSucc)]
  simp only [Finset.mem_univ, if_true]
  rw [Fin.sum_univ_succAbove f i.castSucc]

/-- The first-coordinate function preserves nonnegativity. -/
theorem staircaseFirstCoord_nonneg
    (f : Fin (n + 2) → ℝ) (hf : ∀ j, 0 ≤ f j) (k : Fin (n + 1)) :
    0 ≤ staircaseFirstCoord n i f k := by
  unfold staircaseFirstCoord
  split_ifs
  · exact hf _
  · exact add_nonneg (hf _) (hf _)
  · exact hf _

/-- The time-coordinate is nonneg. -/
theorem staircaseTimeCoord_nonneg
    (f : Fin (n + 2) → ℝ) (hf : ∀ j, 0 ≤ f j) :
    0 ≤ staircaseTimeCoord n i f := by
  unfold staircaseTimeCoord
  exact Finset.sum_nonneg (fun j _ => hf j)

/-- The time-coordinate is `≤ 1` when `f` lies in the standard simplex. -/
theorem staircaseTimeCoord_le_one
    (f : Fin (n + 2) → ℝ) (hf : ∀ j, 0 ≤ f j) (hsum : ∑ j, f j = 1) :
    staircaseTimeCoord n i f ≤ 1 := by
  unfold staircaseTimeCoord
  rw [← hsum]
  exact Finset.sum_le_sum_of_subset_of_nonneg
    (Finset.filter_subset _ _) (fun j _ _ => hf j)

/-! ### The staircase map as a continuous map -/

/-- The staircase function as an underlying map (no simplex/interval constraints
yet). Combines `staircaseFirstCoord` and `staircaseTimeCoord`. -/
def staircaseFun (f : Fin (n + 2) → ℝ) : (Fin (n + 1) → ℝ) × ℝ :=
  (staircaseFirstCoord n i f, staircaseTimeCoord n i f)

/-- Continuity of the first-coordinate function as a map
`(Fin (n+2) → ℝ) → (Fin (n+1) → ℝ)`. -/
theorem continuous_staircaseFirstCoord :
    Continuous (fun f : Fin (n + 2) → ℝ => staircaseFirstCoord n i f) := by
  refine continuous_pi (fun k => ?_)
  unfold staircaseFirstCoord
  by_cases h1 : k.val < i.val
  · simp only [if_pos h1]; exact continuous_apply _
  · by_cases h2 : k.val = i.val
    · simp only [if_neg h1, if_pos h2]
      exact (continuous_apply _).add (continuous_apply _)
    · simp only [if_neg h1, if_neg h2]
      exact continuous_apply _

/-- Continuity of the time-coordinate function. -/
theorem continuous_staircaseTimeCoord :
    Continuous (fun f : Fin (n + 2) → ℝ => staircaseTimeCoord n i f) := by
  unfold staircaseTimeCoord
  exact continuous_finset_sum _ (fun j _ => continuous_apply j)

/-- Continuity of `staircaseFun`. -/
theorem continuous_staircaseFun :
    Continuous (staircaseFun n i) :=
  (continuous_staircaseFirstCoord n i).prodMk (continuous_staircaseTimeCoord n i)

/-- The staircase map sends a point of `stdSimplex ℝ (Fin (n+2))` to a point in
`stdSimplex ℝ (Fin (n+1))`. -/
theorem staircaseFirstCoord_mem_stdSimplex
    {f : Fin (n + 2) → ℝ} (hf : f ∈ stdSimplex ℝ (Fin (n + 2))) :
    staircaseFirstCoord n i f ∈ stdSimplex ℝ (Fin (n + 1)) := by
  refine ⟨?_, ?_⟩
  · intro k; exact staircaseFirstCoord_nonneg n i f hf.1 k
  · rw [staircaseFirstCoord_sum]; exact hf.2

/-- The time-coordinate maps into `[0, 1]`. -/
theorem staircaseTimeCoord_mem_Icc
    {f : Fin (n + 2) → ℝ} (hf : f ∈ stdSimplex ℝ (Fin (n + 2))) :
    staircaseTimeCoord n i f ∈ Set.Icc (0 : ℝ) 1 :=
  ⟨staircaseTimeCoord_nonneg n i f hf.1,
   staircaseTimeCoord_le_one n i f hf.1 hf.2⟩

/-- The staircase map as a continuous map
`stdSimplex ℝ (Fin (n+2)) → stdSimplex ℝ (Fin (n+1)) × Set.Icc 0 1`. -/
def staircaseMap :
    C(stdSimplex ℝ (Fin (n + 2)),
      stdSimplex ℝ (Fin (n + 1)) × Set.Icc (0 : ℝ) 1) where
  toFun p :=
    (⟨staircaseFirstCoord n i p.val, staircaseFirstCoord_mem_stdSimplex n i p.property⟩,
     ⟨staircaseTimeCoord n i p.val, staircaseTimeCoord_mem_Icc n i p.property⟩)
  continuous_toFun := by
    refine Continuous.prodMk ?_ ?_
    · exact Continuous.subtype_mk
        ((continuous_staircaseFirstCoord n i).comp continuous_subtype_val) _
    · exact Continuous.subtype_mk
        ((continuous_staircaseTimeCoord n i).comp continuous_subtype_val) _

/-! ### The prism simplex

Given a homotopy `H : f ≃ g` between `f, g : X → Y` and a singular `n`-simplex
`σ : Δⁿ → X`, the `i`-th prism simplex is the singular `(n+1)`-simplex
`prismSimplex H σ i : Δ^{n+1} → Y` obtained by composing:

  `Δ^{n+1} --staircaseMap_i--> Δⁿ × I --σ × id--> X × I --swap--> I × X --H--> Y`.
-/

variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]

/-- The `i`-th prism singular `(n+1)`-simplex obtained from a homotopy `H` and a
singular `n`-simplex `s`. Its image in `Y` is `H ∘ (s × id) ∘ staircaseMap_i`
(after swapping the order of the two factors of the product). -/
noncomputable def prismSimplex
    {f g : C(X, Y)} (H : ContinuousMap.Homotopy f g)
    (s : C(stdSimplex ℝ (Fin (n + 1)), X)) :
    C(stdSimplex ℝ (Fin (n + 2)), Y) :=
  let stair : C(stdSimplex ℝ (Fin (n + 2)),
                 stdSimplex ℝ (Fin (n + 1)) × Set.Icc (0 : ℝ) 1) := staircaseMap n i
  let sigmaTimesId :
      C(stdSimplex ℝ (Fin (n + 1)) × Set.Icc (0 : ℝ) 1, X × Set.Icc (0 : ℝ) 1) :=
    s.prodMap (ContinuousMap.id _)
  let swap : C(X × Set.Icc (0 : ℝ) 1, Set.Icc (0 : ℝ) 1 × X) :=
    ⟨fun p => (p.2, p.1), continuous_snd.prodMk continuous_fst⟩
  H.toContinuousMap.comp (swap.comp (sigmaTimesId.comp stair))

/-! ### Face-map identities for the staircase coordinates

These are the key combinatorial identities needed for the prism boundary formula.
The j-th face of the standard n-simplex is the inclusion `δⱼ : Δⁿ → Δ^{n+1}`
corresponding (on index sets) to `Fin.succAbove j : Fin(n+1) → Fin(n+2)`.
Given `f : Fin(n+2) → ℝ` and `j : Fin(n+2)`, the image of a point
`g : Fin(n+1) → ℝ` under `δⱼ` is `fun m => FunOnFinite.linearMap ℝ ℝ (Fin.succAbove j) g m`,
which equals `g (Fin.predAbove j m)` when `j.val ≠ m.val` and `0` when `m = j`.

The critical cases are `j = i.castSucc` (time = 1 - s_0 - ... - s_{i-1})
and `j = i.succ` (time = 1 - s_0 - ... - s_i), which together with sign
cancellation give the boundary formula `∂P + P∂ = g_* - f_*`. -/

/-- The time coordinate of `αᵢ ∘ δᵢ` equals `∑_{k ≥ i} f_k`.
Combinatorial fact: inserting 0 at position i.castSucc in the (n+2)-coordinates
shifts the tail sum from {>i} to {≥i}. -/
theorem staircaseTimeCoord_face_self
    (f : Fin (n + 1) → ℝ) :
    staircaseTimeCoord n i
      (fun m : Fin (n + 2) =>
        Finset.sum Finset.univ (fun k : Fin (n + 1) =>
          if Fin.succAbove i.castSucc k = m then f k else 0)) =
      ∑ k ∈ Finset.univ.filter (fun k : Fin (n + 1) => i.val ≤ k.val), f k := by
  simp only [staircaseTimeCoord]
  rw [Finset.sum_comm]
  simp_rw [Finset.sum_ite_eq, Finset.mem_filter, Finset.mem_univ, true_and]
  -- Goal: ∑ k, if i.val < (succAbove i.castSucc k).val then f k else 0
  --       = ∑ k ∈ filter (i.val ≤ ·.val), f k
  rw [← Finset.sum_filter]
  congr 1
  ext k
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  by_cases hk : k.val < i.val
  · have hsa : Fin.succAbove i.castSucc k = k.castSucc := by
      rw [Fin.succAbove, if_pos]; exact Fin.mk_lt_mk.mpr hk
    simp only [hsa, Fin.val_castSucc]
    omega
  · have hge : i.val ≤ k.val := Nat.le_of_not_lt hk
    have hsa : Fin.succAbove i.castSucc k = k.succ := by
      rw [Fin.succAbove, if_neg]; exact Fin.mk_lt_mk.not.mpr (Nat.not_lt.mpr hge)
    simp only [hsa, Fin.val_succ]
    omega

/-- The time coordinate of `αᵢ ∘ δ_{i+1}` equals `∑_{k > i} f_k`. -/
theorem staircaseTimeCoord_face_succ
    (f : Fin (n + 1) → ℝ) :
    staircaseTimeCoord n i
      (fun m : Fin (n + 2) =>
        Finset.sum Finset.univ (fun k : Fin (n + 1) =>
          if Fin.succAbove i.succ k = m then f k else 0)) =
      ∑ k ∈ Finset.univ.filter (fun k : Fin (n + 1) => i.val < k.val), f k := by
  simp only [staircaseTimeCoord]
  rw [Finset.sum_comm]
  simp_rw [Finset.sum_ite_eq, Finset.mem_filter, Finset.mem_univ, true_and]
  rw [← Finset.sum_filter]
  congr 1
  ext k
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  by_cases hk : k.val ≤ i.val
  · have hsa : Fin.succAbove i.succ k = k.castSucc := by
      rw [Fin.succAbove, if_pos]; exact Fin.mk_lt_mk.mpr (Nat.lt_succ_of_le hk)
    simp only [hsa, Fin.val_castSucc]
  · have hk' : i.val < k.val := Nat.lt_of_not_le hk
    have hsa : Fin.succAbove i.succ k = k.succ := by
      rw [Fin.succAbove, if_neg]
      exact Fin.mk_lt_mk.not.mpr (Nat.not_lt.mpr (Nat.succ_le_of_lt hk'))
    simp only [hsa, Fin.val_succ]
    omega

/-- When `f` is in the standard simplex, the sum `∑_{k ≥ 0} f_k = 1` (full sum). -/
theorem staircaseTimeCoord_face_i_zero_sum_eq_one
    (f : Fin (n + 1) → ℝ) (hsum : ∑ j, f j = 1) :
    ∑ k ∈ Finset.univ.filter (fun k : Fin (n + 1) => 0 ≤ k.val), f k = 1 := by
  simp [Finset.filter_true_of_mem, hsum]

/-- When `f` is in the standard simplex and i = n, the sum `∑_{k > n} f_k = 0` (empty). -/
theorem staircaseTimeCoord_face_i_last_sum_eq_zero
    (f : Fin (n + 1) → ℝ) :
    ∑ k ∈ Finset.univ.filter (fun k : Fin (n + 1) => n < k.val), f k = 0 := by
  apply Finset.sum_eq_zero
  intro k hk
  simp [Finset.mem_filter] at hk
  exact absurd hk (Nat.not_lt.mpr (Nat.lt_succ_iff.mp k.isLt))

/-! ### Top and bottom face of a prism simplex

The critical boundary identities for the prism construction:
* The "0th face of the 0th staircase" gives `g ∘ s` (time = 1).
* The "last face of the last staircase" gives `f ∘ s` (time = 0). -/

/-- **Top boundary.** When `p ∈ Δⁿ`, the time coordinate of
`staircaseMap n 0 (δ₀ p)` equals 1. This is the boundary condition
`H(·, 1) = g(·)`. -/
theorem staircaseTimeCoord_i_zero_face_zero_eq_one
    {f : Fin (n + 2) → ℝ} (hf : f ∈ stdSimplex ℝ (Fin (n + 2)))
    (hf0 : f ⟨0, Nat.zero_lt_succ _⟩ = 0) :
    staircaseTimeCoord n ⟨0, Nat.zero_lt_succ n⟩ f = 1 := by
  simp only [staircaseTimeCoord]
  -- ∑_{j>0} f_j = (∑_j f_j) - f_0 = 1 - 0 = 1
  have key : ∑ j : Fin (n + 2), f j =
      ∑ j ∈ Finset.univ.filter (fun j : Fin (n + 2) => 0 < j.val), f j +
      ∑ j ∈ Finset.univ.filter (fun j : Fin (n + 2) => ¬ 0 < j.val), f j :=
    (Finset.sum_filter_add_sum_filter_not Finset.univ _ f).symm
  have hcompl : ∑ j ∈ Finset.univ.filter (fun j : Fin (n + 2) => ¬ 0 < j.val), f j = 0 := by
    apply Finset.sum_eq_zero
    intro j hj
    simp only [Finset.mem_filter, Finset.mem_univ, not_lt, Nat.le_zero, true_and] at hj
    have : j = ⟨0, Nat.zero_lt_succ _⟩ := Fin.ext hj
    rw [this, hf0]
  linarith [key.symm.trans hf.2]

/-- **Bottom boundary.** When `p ∈ Δⁿ`, the time coordinate of
`staircaseMap n n (δ_{n+1} p)` equals 0. This is the boundary condition
`H(·, 0) = f(·)`. -/
theorem staircaseTimeCoord_i_last_face_last_eq_zero
    {f : Fin (n + 2) → ℝ}
    (hflast : f (Fin.last (n + 1)) = 0) :
    staircaseTimeCoord n ⟨n, Nat.lt_succ_self n⟩ f = 0 := by
  -- Time = ∑_{j > n} f_j. The only j with j.val > n in Fin(n+2) is Fin.last.
  simp only [staircaseTimeCoord]
  apply Finset.sum_eq_zero
  intro j hj
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hj
  -- j.val > n and j : Fin(n+2), so j.val = n+1, meaning j = Fin.last
  have hjlast : j = Fin.last (n + 1) := by
    apply Fin.ext; simp only [Fin.val_last]
    omega
  rw [hjlast, hflast]

/-! ### Connecting coordinate lemmas to the prism simplex

The face map `stdSimplex.map (Fin.succAbove j)` sends a point of `stdSimplex ℝ (Fin(n+1))`
to a point of `stdSimplex ℝ (Fin(n+2))` with coordinate `j` equal to 0.
These are the key lemmas connecting the coordinate computations to the `ContinuousMap`-level
prism simplex. -/

/-- The j-th coordinate of `stdSimplex.map (Fin.succAbove j) p` is 0.
The image of `Fin.succAbove j` misses the value `j`, so the j-th weight is 0. -/
theorem stdSimplex_map_succAbove_coord_eq_zero (j : Fin (n + 2))
    (p : stdSimplex ℝ (Fin (n + 1))) :
    (stdSimplex.map (Fin.succAbove j) p).val j = 0 := by
  change (FunOnFinite.linearMap ℝ ℝ (Fin.succAbove j) p.val) j = 0
  rw [FunOnFinite.linearMap_apply_apply]
  apply Finset.sum_eq_zero
  intro k hk
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hk
  exact absurd hk (Fin.succAbove_ne j k)

/-- The `m.succ`-th coordinate of `stdSimplex.map Fin.succ p` equals `p.val m`.
Key ingredient for the top-face identity: `αᵢ(δ₀(p))` has first-coord `p`. -/
theorem stdSimplex_map_succ_apply (p : stdSimplex ℝ (Fin (n + 1))) (m : Fin (n + 1)) :
    (stdSimplex.map Fin.succ p).val m.succ = p.val m := by
  change (FunOnFinite.linearMap ℝ ℝ Fin.succ p.val) m.succ = p.val m
  rw [FunOnFinite.linearMap_apply_apply]
  have hfilt : Finset.univ.filter (fun k : Fin (n + 1) => Fin.succ k = m.succ) = {m} := by
    ext k; simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
    exact ⟨fun h => Fin.succ_injective _ h, fun h => by rw [h]⟩
  rw [hfilt, Finset.sum_singleton]

/-- The `m.castSucc`-th coordinate of `stdSimplex.map Fin.castSucc p` equals `p.val m`.
Key ingredient for the bottom-face identity. -/
theorem stdSimplex_map_castSucc_apply (p : stdSimplex ℝ (Fin (n + 1))) (m : Fin (n + 1)) :
    (stdSimplex.map Fin.castSucc p).val m.castSucc = p.val m := by
  change (FunOnFinite.linearMap ℝ ℝ Fin.castSucc p.val) m.castSucc = p.val m
  rw [FunOnFinite.linearMap_apply_apply]
  have hfilt : Finset.univ.filter (fun k : Fin (n + 1) => Fin.castSucc k = m.castSucc) = {m} := by
    ext k; simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
    exact ⟨fun h => Fin.castSucc_injective _ h, fun h => by rw [h]⟩
  rw [hfilt, Finset.sum_singleton]

/-- **Top face (i=0, δ₀).** For any `p : stdSimplex ℝ (Fin(n+1))`, the 0-th prism simplex
evaluated at the 0-th face inclusion of `p` equals `g(s p)`.
Proof route: time coord = 1 (since 0-th coord of δ₀(p) is 0, and sum of rest = 1),
so H evaluates at 1 giving g; first coord = p (identity) so s evaluates at s p. -/
theorem prismSimplex_top_face
    {f g : C(X, Y)} (H : ContinuousMap.Homotopy f g)
    (s : C(stdSimplex ℝ (Fin (n + 1)), X)) :
    ∀ p : stdSimplex ℝ (Fin (n + 1)),
    prismSimplex n ⟨0, Nat.zero_lt_succ n⟩ H s
        (stdSimplex.map (Fin.succAbove ⟨0, Nat.zero_lt_succ (n + 1)⟩) p) =
      g (s p) := by
  intro p
  set q := stdSimplex.map (Fin.succAbove (⟨0, Nat.zero_lt_succ (n + 1)⟩ : Fin (n + 2))) p
  -- Use Fin.succAbove_zero to simplify: Fin.succAbove 0 = Fin.succ
  have hqeq : q = stdSimplex.map Fin.succ p := by simp only [q]; congr 1
  -- Time coordinate: q.val ⟨0,_⟩ = 0, so ∑_{j>0} q.val j = ∑_j q.val j = 1
  have htime : staircaseTimeCoord n ⟨0, Nat.zero_lt_succ n⟩ q.val = 1 :=
    staircaseTimeCoord_i_zero_face_zero_eq_one n q.property
      (stdSimplex_map_succAbove_coord_eq_zero n ⟨0, Nat.zero_lt_succ (n + 1)⟩ p)
  -- First coordinate: staircaseFirstCoord n ⟨0,_⟩ q.val = p.val
  have hfirst : ∀ k : Fin (n + 1), staircaseFirstCoord n ⟨0, Nat.zero_lt_succ n⟩ q.val k = p.val k := by
    intro k
    simp only [staircaseFirstCoord, Nat.not_lt_zero, ite_false]
    by_cases hk0 : k.val = 0
    · rw [if_pos hk0, hqeq]
      -- i = ⟨0,_⟩, so castSucc = 0, succ = ⟨1,_⟩
      have hcs : (⟨0, Nat.zero_lt_succ n⟩ : Fin (n + 1)).castSucc = (0 : Fin (n + 2)) := rfl
      have hsc : (⟨0, Nat.zero_lt_succ n⟩ : Fin (n + 1)).succ = ⟨1, by omega⟩ := rfl
      rw [hcs, hsc]
      rw [show (stdSimplex.map Fin.succ p).val (0 : Fin (n + 2)) = 0 from by
            rw [← Fin.succAbove_zero]
            exact stdSimplex_map_succAbove_coord_eq_zero n (0 : Fin (n + 2)) p,
          zero_add]
      rw [show (stdSimplex.map Fin.succ p).val ⟨1, by omega⟩ =
              p.val ⟨0, Nat.zero_lt_succ n⟩ from by
            have := stdSimplex_map_succ_apply n p ⟨0, Nat.zero_lt_succ n⟩
            simpa using this]
      rw [show k = ⟨0, Nat.zero_lt_succ n⟩ from by ext; omega]
    · rw [if_neg hk0, hqeq]
      exact stdSimplex_map_succ_apply n p k
  -- Pack the subtype equalities
  have htime_eq : (⟨staircaseTimeCoord n ⟨0, Nat.zero_lt_succ n⟩ q.val,
      staircaseTimeCoord_mem_Icc n ⟨0, Nat.zero_lt_succ n⟩ q.property⟩ : Set.Icc (0 : ℝ) 1) =
      ⟨1, by norm_num⟩ := Subtype.ext htime
  have hfirst_eq : (⟨staircaseFirstCoord n ⟨0, Nat.zero_lt_succ n⟩ q.val,
      staircaseFirstCoord_mem_stdSimplex n ⟨0, Nat.zero_lt_succ n⟩ q.property⟩ :
      stdSimplex ℝ (Fin (n + 1))) = p := Subtype.ext (funext hfirst)
  -- Unfold prismSimplex and apply
  simp only [prismSimplex, ContinuousMap.comp_apply, staircaseMap, ContinuousMap.coe_mk,
             ContinuousMap.prodMap_apply, htime_eq, hfirst_eq]
  exact H.apply_one (s p)

/-- **Bottom face (i=n, δ_{n+1}).** For any `p : stdSimplex ℝ (Fin(n+1))`, the n-th prism
simplex evaluated at the last face inclusion of `p` equals `f(s p)`.
Proof route: time coord = 0 (last coord of δ_{n+1}(p) is 0), so H evaluates at 0 giving f. -/
theorem prismSimplex_bottom_face
    {f g : C(X, Y)} (H : ContinuousMap.Homotopy f g)
    (s : C(stdSimplex ℝ (Fin (n + 1)), X)) :
    ∀ p : stdSimplex ℝ (Fin (n + 1)),
    prismSimplex n ⟨n, Nat.lt_succ_self n⟩ H s
        (stdSimplex.map (Fin.succAbove (Fin.last (n + 1))) p) =
      f (s p) := by
  intro p
  set q := stdSimplex.map (Fin.succAbove (Fin.last (n + 1))) p
  -- Use Fin.succAbove_last to simplify: Fin.succAbove (Fin.last n) = Fin.castSucc
  have hqeq : q = stdSimplex.map Fin.castSucc p := by simp only [q, Fin.succAbove_last]
  -- Time coordinate: q.val (Fin.last (n+1)) = 0, so ∑_{j>n} q.val j = 0
  have htime : staircaseTimeCoord n ⟨n, Nat.lt_succ_self n⟩ q.val = 0 := by
    apply staircaseTimeCoord_i_last_face_last_eq_zero
    rw [hqeq]
    have h := stdSimplex_map_succAbove_coord_eq_zero n (Fin.last (n + 1)) p
    rwa [Fin.succAbove_last] at h
  -- First coordinate: staircaseFirstCoord n ⟨n,_⟩ q.val = p.val
  have hfirst : ∀ k : Fin (n + 1), staircaseFirstCoord n ⟨n, Nat.lt_succ_self n⟩ q.val k = p.val k := by
    intro k
    rw [hqeq]
    simp only [staircaseFirstCoord]
    by_cases hk : k.val < n
    · -- k < n: returns (map castSucc p).val k.castSucc = p.val k
      simp only [if_pos hk]
      exact stdSimplex_map_castSucc_apply n p k
    · have hkn : k.val = n := Nat.le_antisymm (Nat.lt_succ_iff.mp k.isLt) (Nat.le_of_not_lt hk)
      have hkn_eq : k = ⟨n, Nat.lt_succ_self n⟩ := Fin.ext hkn
      simp only [if_neg hk, if_pos hkn]
      -- goal: (map castSucc p).val ⟨n,_⟩.castSucc + (map castSucc p).val ⟨n,_⟩.succ = p.val k
      rw [show (⟨n, Nat.lt_succ_self n⟩ : Fin (n + 1)).succ = Fin.last (n + 1) from rfl,
          show (stdSimplex.map Fin.castSucc p).val (Fin.last (n + 1)) = 0 from by
            have h := stdSimplex_map_succAbove_coord_eq_zero n (Fin.last (n + 1)) p
            rwa [Fin.succAbove_last] at h,
          add_zero, hkn_eq]
      exact stdSimplex_map_castSucc_apply n p ⟨n, Nat.lt_succ_self n⟩
  -- Pack the subtype equalities
  have htime_eq : (⟨staircaseTimeCoord n ⟨n, Nat.lt_succ_self n⟩ q.val,
      staircaseTimeCoord_mem_Icc n ⟨n, Nat.lt_succ_self n⟩ q.property⟩ : Set.Icc (0 : ℝ) 1) =
      ⟨0, by norm_num⟩ := Subtype.ext htime
  have hfirst_eq : (⟨staircaseFirstCoord n ⟨n, Nat.lt_succ_self n⟩ q.val,
      staircaseFirstCoord_mem_stdSimplex n ⟨n, Nat.lt_succ_self n⟩ q.property⟩ :
      stdSimplex ℝ (Fin (n + 1))) = p := Subtype.ext (funext hfirst)
  -- Unfold prismSimplex and apply
  simp only [prismSimplex, ContinuousMap.comp_apply, staircaseMap, ContinuousMap.coe_mk,
             ContinuousMap.prodMap_apply, htime_eq, hfirst_eq]
  exact H.apply_zero (s p)

/-! ### Interior face identities for the prism simplex

The chain homotopy equation `∂P + P∂ = g_* - f_*` requires three types of face identities:
1. **Top face** (`prismSimplex_top_face`): face 0 of P_0 = g ∘ s. ✓
2. **Bottom face** (`prismSimplex_bottom_face`): face n+1 of P_n = f ∘ s. ✓
3. **Diagonal face** (`prismSimplex_diagonal_face`): face i+1 of P_i = face i+1 of P_{i+1}.
   Adjacent staircase simplices share a common face, giving the boundary cancellation.
4. **Left side faces** and **right side faces**: face j of P_i relates to P applied to a face of s.

This section proves the diagonal face identity (the critical cancellation).  -/

/-- **Diagonal face (cancellation).** For `ι : Fin n`, the (ι+1)-th face of the
ι-th prism simplex equals the (ι+1)-th face of the (ι+1)-th prism simplex.

The two adjacent staircase simplices `P_ι` and `P_{ι+1}` share the face at position ι+1
(the shared internal face of the prism subdivision). The key is that inserting a zero at
position ι+1 makes both the time and first coordinates agree for both staircase indices. -/
theorem prismSimplex_diagonal_face
    {f g : C(X, Y)} (H : ContinuousMap.Homotopy f g)
    (s : C(stdSimplex ℝ (Fin (n + 1)), X))
    (ι : Fin n) :
    ∀ p : stdSimplex ℝ (Fin (n + 1)),
    prismSimplex n ⟨ι.val, Nat.lt_trans ι.isLt (Nat.lt_succ_self n)⟩ H s
        (stdSimplex.map (Fin.succAbove (⟨ι.val + 1, by omega⟩ : Fin (n + 2))) p) =
    prismSimplex n ⟨ι.val + 1, by omega⟩ H s
        (stdSimplex.map (Fin.succAbove (⟨ι.val + 1, by omega⟩ : Fin (n + 2))) p) := by
  intro p
  set i₀ := (⟨ι.val, Nat.lt_trans ι.isLt (Nat.lt_succ_self n)⟩ : Fin (n + 1)) with hi₀
  set i₁ := (⟨ι.val + 1, by omega⟩ : Fin (n + 1)) with hi₁
  set face_idx := (⟨ι.val + 1, by omega⟩ : Fin (n + 2)) with hface_idx
  set q := stdSimplex.map (Fin.succAbove face_idx) p with hqeq
  -- The (ι+1)-th coordinate of q is 0 (the inserted zero)
  have hzero : q.val face_idx = 0 :=
    stdSimplex_map_succAbove_coord_eq_zero n face_idx p
  -- Time coordinates agree: ∑_{j.val > ι} = ∑_{j.val > ι+1} since q.val ⟨ι+1,_⟩ = 0
  have htime : staircaseTimeCoord n i₀ q.val = staircaseTimeCoord n i₁ q.val := by
    simp only [staircaseTimeCoord, hi₀, hi₁]
    have heq : Finset.univ.filter (fun j : Fin (n + 2) => ι.val < j.val) =
               insert face_idx (Finset.univ.filter (fun j : Fin (n + 2) => ι.val + 1 < j.val)) := by
      ext j
      simp only [Finset.mem_insert, Finset.mem_filter, Finset.mem_univ, true_and]
      constructor
      · intro h
        by_cases hj : j.val = ι.val + 1
        · left; exact Fin.ext hj
        · right; omega
      · rintro (rfl | h)
        · simp [hface_idx]
        · omega
    have hnotmem : face_idx ∉ Finset.univ.filter (fun j : Fin (n + 2) => ι.val + 1 < j.val) := by
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, hface_idx]
      omega
    rw [heq, Finset.sum_insert hnotmem, hzero, zero_add]
  -- First coordinates agree in all cases
  have hfirst : ∀ k : Fin (n + 1),
      staircaseFirstCoord n i₀ q.val k = staircaseFirstCoord n i₁ q.val k := by
    intro k
    have hi₀val : i₀.val = ι.val := rfl
    have hi₁val : i₁.val = ι.val + 1 := rfl
    have hfv : face_idx.val = ι.val + 1 := rfl
    simp only [staircaseFirstCoord]
    by_cases hk1 : k.val < i₀.val
    · simp only [if_pos hk1, if_pos (show k.val < i₁.val from by omega)]
    · by_cases hk2 : k.val = i₀.val
      · have hk_lt_i₁ : k.val < i₁.val := by omega
        simp only [if_neg hk1, if_pos hk2, if_pos hk_lt_i₁]
        have hi0succ : i₀.succ = face_idx := by
          apply Fin.ext; have h : i₀.succ.val = i₀.val + 1 := rfl; omega
        have hki₀ : k = i₀ := Fin.ext (by omega)
        rw [hi0succ, hzero, add_zero, ← hki₀]
      · by_cases hk3 : k.val = i₁.val
        · have hk_nlt_i₁ : ¬k.val < i₁.val := by omega
          simp only [if_neg hk1, if_neg hk2, if_neg hk_nlt_i₁, if_pos hk3]
          have hi1cs : i₁.castSucc = face_idx := by
            apply Fin.ext; have h : i₁.castSucc.val = i₁.val := rfl; omega
          have hki₁ : k = i₁ := Fin.ext (by omega)
          rw [hi1cs, hzero, zero_add, ← hki₁]
        · have hk_nlt_i₁ : ¬k.val < i₁.val := by omega
          simp only [if_neg hk1, if_neg hk2, if_neg hk_nlt_i₁, if_neg hk3]
  -- Pack the coordinate equalities into a staircase map equality
  have htime_eq : (⟨staircaseTimeCoord n i₀ q.val,
      staircaseTimeCoord_mem_Icc n i₀ q.property⟩ : Set.Icc (0 : ℝ) 1) =
      ⟨staircaseTimeCoord n i₁ q.val,
      staircaseTimeCoord_mem_Icc n i₁ q.property⟩ := Subtype.ext htime
  have hfirst_eq : (⟨staircaseFirstCoord n i₀ q.val,
      staircaseFirstCoord_mem_stdSimplex n i₀ q.property⟩ :
      stdSimplex ℝ (Fin (n + 1))) =
      ⟨staircaseFirstCoord n i₁ q.val,
      staircaseFirstCoord_mem_stdSimplex n i₁ q.property⟩ := Subtype.ext (funext hfirst)
  -- The staircase maps agree at q: both first and time components match
  have hstair : (staircaseMap n i₀ : C(stdSimplex ℝ (Fin (n + 2)),
      stdSimplex ℝ (Fin (n + 1)) × Set.Icc (0 : ℝ) 1)) q =
      (staircaseMap n i₁ : C(stdSimplex ℝ (Fin (n + 2)),
      stdSimplex ℝ (Fin (n + 1)) × Set.Icc (0 : ℝ) 1)) q := by
    simp only [staircaseMap, ContinuousMap.coe_mk]
    exact Prod.ext hfirst_eq htime_eq
  -- Both prism simplices compose through the same staircase map value at q:
  -- unfold the full composition and substitute the coordinate equalities
  simp only [prismSimplex, ContinuousMap.comp_apply, staircaseMap, ContinuousMap.coe_mk,
             ContinuousMap.prodMap_apply, htime_eq, hfirst_eq]

/-! ### Side-face identities (Phase 4 of the prism chain-homotopy plan)

For non-special pairs `(i, j)` (i.e., not top/bottom/diagonal), the
`j`-th face of the `i`-th prism `(n+1)`-simplex equals a prism over
some `(n-1)`-face of `σ`.

There are two cases:

* **Lower side-face** (`j ≤ ι`, with `n = ι' + 1`): the `j`-th face
  of `prismSimplex (ι' + 1) i.castSucc H s` for `i = ι.castSucc` and
  `j ≤ ι.castSucc.val` factors through the prism construction at
  degree `ι'`. Specifically, dropping the `j`-th lower vertex
  corresponds to `s ∘ δ_j` paired with the `(i-1)`-staircase pattern
  (one fewer lower step).

* **Upper side-face** (`j > i + 1`): the `j`-th face for `j` exceeding
  the diagonal corresponds to dropping an upper vertex. By the
  staircase symmetry, this equals the prism over `s ∘ δ_{j-1}` at the
  same staircase index `i`.

These two identities — together with `prismSimplex_top_face`,
`_bottom_face`, `_diagonal_face` — are exactly what's needed to close
the boundary identity `∂P + P∂ = f_* − g_*` in
`Jacobian/Periods/PrismChainHomotopy.lean`.

The proofs are direct staircase-coordinate computations modeled on
`prismSimplex_diagonal_face` above (~80 LOC each, with similar
case-by-case `Fin.succAbove` analysis).

**Status:** stated as named obligations with `sorry` bodies. The body
of `prismChain_hom_comm` for `i ≥ 1` will consume these. -/

/-- **Lower side-face identity.** For prism degree `n + 1` (input `s`
of degree `n + 1`, staircase index `i : Fin (n + 2)`), and a face
index `j : Fin (n + 3)` with `j.val < i.val`, the `j`-th face of
the prism simplex `prismSimplex (n + 1) i H s` equals the prism
simplex at degree `n` with staircase index `i - 1` applied to
`s ∘ δ_j`.

Hatcher §2.1, p. 112: dropping the `j`-th lower vertex `v_j`
(`j < i`) leaves `[v_0, ..., v̂_j, ..., v_i, w_i, ..., w_{n+1}]`,
which is the `(i - 1)`-th staircase simplex over `s ∘ δ_j`.

(For `j = 0` with `i = 0`, this would be the top face — but `j.val < i.val`
forces `i.val ≥ 1`, so the top-face case is excluded.)

(For `j = i` or `j = i + 1`, this would be the diagonal cancellation —
also excluded by the strict inequality `j.val < i.val`.) -/
theorem prismSimplex_side_face_lower
    {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    {f g : C(X, Y)} (H : ContinuousMap.Homotopy f g)
    (n : ℕ) (i : Fin (n + 2)) (j : Fin (n + 3))
    (hj_lt : j.val < i.val)
    (s : C(stdSimplex ℝ (Fin (n + 2)), X)) :
    ∀ p : stdSimplex ℝ (Fin (n + 2)),
    prismSimplex (n + 1) i H s
        (stdSimplex.map (Fin.succAbove j) p) =
    prismSimplex n
        ⟨i.val - 1, by omega⟩ H
        (s.comp ⟨stdSimplex.map
            (Fin.succAbove (⟨j.val, by omega⟩ : Fin (n + 2))),
          stdSimplex.continuous_map _⟩) p := by
  intro p
  -- Set up: q is the inserted-zero point in Fin (n+3).
  set j_lo : Fin (n + 2) := ⟨j.val, by omega⟩ with hj_lo
  set i_lo : Fin (n + 1) := ⟨i.val - 1, by omega⟩ with hi_lo
  set q : stdSimplex ℝ (Fin (n + 3)) := stdSimplex.map (Fin.succAbove j) p with hq
  have hj_loval : j_lo.val = j.val := rfl
  have hi_loval : i_lo.val = i.val - 1 := rfl
  -- Key: q.val j = 0 (the inserted zero).
  have hq_j : q.val j = 0 := stdSimplex_map_succAbove_coord_eq_zero (n + 1) j p
  -- Time coordinates agree.
  have htime : staircaseTimeCoord (n + 1) i q.val =
      staircaseTimeCoord n i_lo p.val := by
    simp only [staircaseTimeCoord]
    -- Convert filter sums to ite sums for easier manipulation.
    rw [Finset.sum_filter, Finset.sum_filter]
    -- LHS: ∑ over j' : Fin(n+3), if i.val < j'.val then q.val j' else 0
    -- Re-index using succAbove j: contributions split as j' = j vs j' = succAbove j m.
    rw [Fin.sum_univ_succAbove (fun j' : Fin (n + 3) =>
        if i.val < j'.val then q.val j' else 0) j]
    -- The j-contribution: q.val j = 0, and j.val < i.val, so the if-condition fails.
    have h_j_no : ¬ (i.val < j.val) := by omega
    rw [if_neg h_j_no, zero_add]
    -- Now: ∑ m : Fin(n+2), if i.val < (succAbove j m).val then q.val (succAbove j m) else 0
    refine Finset.sum_congr rfl (fun m _ => ?_)
    -- Helper: q.val (succAbove j m) = p.val m, by FunOnFinite computation.
    have hq_succAbove : ∀ m' : Fin (n + 2), q.val (Fin.succAbove j m') = p.val m' := by
      intro m'
      rw [hq]
      change (FunOnFinite.linearMap ℝ ℝ (Fin.succAbove j) p.val) (Fin.succAbove j m')
        = p.val m'
      rw [FunOnFinite.linearMap_apply_apply]
      rw [show Finset.univ.filter
            (fun k : Fin (n + 2) => Fin.succAbove j k = Fin.succAbove j m') = {m'} by
          ext k
          simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
          exact ⟨fun h => Fin.succAbove_right_injective h, fun h => by rw [h]⟩]
      simp
    by_cases hm : m.val < j.val
    · -- m.val < j.val ≤ i.val - 1 < i.val. succAbove j m = m.castSucc.
      have hsa : Fin.succAbove j m = m.castSucc := by
        rw [Fin.succAbove, if_pos]
        exact Fin.mk_lt_mk.mpr hm
      have hcond : (i.val < m.castSucc.val) ↔ (i_lo.val < m.val) := by
        simp [Fin.val_castSucc, hi_lo]; omega
      rw [hsa]
      by_cases hilo : i_lo.val < m.val
      · rw [if_pos (hcond.mpr hilo), if_pos hilo, ← hsa, hq_succAbove]
      · rw [if_neg (fun h => hilo (hcond.mp h)), if_neg hilo]
    · -- m.val ≥ j.val. succAbove j m = m.succ.
      have hge : j.val ≤ m.val := Nat.le_of_not_lt hm
      have hsa : Fin.succAbove j m = m.succ := by
        rw [Fin.succAbove, if_neg]
        exact Fin.mk_lt_mk.not.mpr (Nat.not_lt.mpr hge)
      have hcond : (i.val < m.succ.val) ↔ (i_lo.val < m.val) := by
        simp [Fin.val_succ, hi_lo]; omega
      rw [hsa]
      by_cases hilo : i_lo.val < m.val
      · rw [if_pos (hcond.mpr hilo), if_pos hilo, ← hsa, hq_succAbove]
      · rw [if_neg (fun h => hilo (hcond.mp h)), if_neg hilo]
  -- First coordinates: LHS first coord (in stdSimplex (Fin (n+2)))
  -- equals stdSimplex.map (succAbove j_lo) applied to RHS first coord.
  -- Helper: q.val on the image of succAbove j gives p.val.
  have hq_succAbove : ∀ m' : Fin (n + 2), q.val (Fin.succAbove j m') = p.val m' := by
    intro m'
    rw [hq]
    change (FunOnFinite.linearMap ℝ ℝ (Fin.succAbove j) p.val) (Fin.succAbove j m')
      = p.val m'
    rw [FunOnFinite.linearMap_apply_apply]
    rw [show Finset.univ.filter
          (fun k : Fin (n + 2) => Fin.succAbove j k = Fin.succAbove j m') = {m'} by
        ext k
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
        exact ⟨fun h => Fin.succAbove_right_injective h, fun h => by rw [h]⟩]
    simp
  -- Pointwise first-coord identity. Sub-obligation: 5-case analysis on
  -- (k.val < j.val), (k.val = j.val), (j.val < k.val < i.val), (k.val = i.val),
  -- (k.val > i.val). Each case reduces via `hq_succAbove` and the
  -- `staircaseFirstCoord` definition. Sketch verified by hand. ~150 LOC of
  -- careful Fin.succAbove index manipulation. Mirrors the existing
  -- `prismSimplex_diagonal_face` proof but with one extra level of case split.
  -- Helper: filter identification.
  -- For k = j_lo: filter is empty.
  -- For k ≠ j_lo with k.val < j_lo.val: pre-image is ⟨k.val, _⟩.
  -- For k ≠ j_lo with k.val > j_lo.val: pre-image is ⟨k.val - 1, _⟩.
  have hfilter_empty : ∀ k : Fin (n + 2), k = j_lo →
      (Finset.univ.filter (fun k_1 : Fin (n + 1) => Fin.succAbove j_lo k_1 = k)) = ∅ := by
    intro k hk
    apply Finset.eq_empty_of_forall_notMem
    intro m hm
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hm
    rw [hk] at hm
    exact Fin.succAbove_ne j_lo m hm
  have hfilter_lt : ∀ (k : Fin (n + 2)) (_h : k.val < j.val),
      (Finset.univ.filter (fun k_1 : Fin (n + 1) => Fin.succAbove j_lo k_1 = k))
      = {⟨k.val, by omega⟩} := by
    intro k hkj
    ext m
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
    constructor
    · intro h
      have hval : (Fin.succAbove j_lo m).val = k.val := by rw [h]
      rw [Fin.succAbove] at hval
      split_ifs at hval with hmj
      · simp only [Fin.val_castSucc] at hval
        apply Fin.ext
        show m.val = k.val
        exact hval
      · exfalso
        rw [Fin.lt_def] at hmj
        push_neg at hmj
        simp only [Fin.val_succ, Fin.val_castSucc] at hval hmj
        omega
    · rintro rfl
      rw [Fin.succAbove, if_pos]
      · rfl
      · rw [Fin.lt_def]; simp [hj_loval]; exact hkj
  have hfilter_gt : ∀ (k : Fin (n + 2)) (_h : j.val < k.val),
      (Finset.univ.filter (fun k_1 : Fin (n + 1) => Fin.succAbove j_lo k_1 = k))
      = {⟨k.val - 1, by omega⟩} := by
    intro k hkj
    ext m
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
    constructor
    · intro h
      have hval : (Fin.succAbove j_lo m).val = k.val := by rw [h]
      rw [Fin.succAbove] at hval
      split_ifs at hval with hmj
      · exfalso
        rw [Fin.lt_def] at hmj
        simp only [Fin.val_castSucc, hj_loval] at hval hmj
        omega
      · rw [Fin.lt_def] at hmj
        push_neg at hmj
        simp only [Fin.val_succ, Fin.val_castSucc] at hval hmj
        apply Fin.ext
        show m.val = k.val - 1
        omega
    · rintro rfl
      rw [Fin.succAbove, if_neg]
      · apply Fin.ext
        simp [Fin.val_succ]
        omega
      · simp [Fin.lt_def, Fin.val_castSucc, hj_loval]; omega
  -- Now prove hfirst.
  have hfirst : ∀ k : Fin (n + 2),
      staircaseFirstCoord (n + 1) i q.val k =
        (FunOnFinite.linearMap ℝ ℝ (Fin.succAbove j_lo)
          (fun m : Fin (n + 1) => staircaseFirstCoord n i_lo p.val m)) k := by
    intro k
    rw [FunOnFinite.linearMap_apply_apply]
    by_cases hk_eq_j : k = j_lo
    · -- Case 0: k = j_lo. LHS uses k.val < i.val branch; q.val k.castSucc = q.val j = 0.
      -- RHS sum is empty.
      rw [hfilter_empty k hk_eq_j, Finset.sum_empty]
      have hk_lt_i : k.val < i.val := by
        rw [show k.val = j_lo.val from by rw [hk_eq_j]]
        rw [hj_lo]; exact hj_lt
      simp only [staircaseFirstCoord, if_pos hk_lt_i]
      have hk_cs_eq_j : k.castSucc = j := by
        apply Fin.ext
        show k.val = j.val
        rw [show k.val = j_lo.val from by rw [hk_eq_j], hj_lo]
      rw [hk_cs_eq_j, hq_j]
    · have hne_val : k.val ≠ j.val := fun h => hk_eq_j (Fin.ext (by rw [hj_loval]; exact h))
      by_cases hkj : k.val < j.val
      · -- Case 1: k.val < j.val. Pre-image ⟨k.val, _⟩ : Fin(n+1).
        rw [hfilter_lt k hkj, Finset.sum_singleton]
        have hk_lt_i : k.val < i.val := by omega
        simp only [staircaseFirstCoord, if_pos hk_lt_i]
        -- Express k.castSucc : Fin(n+3) as succAbove j m' with m' : Fin(n+2).
        have hk_cs : k.castSucc = Fin.succAbove j ⟨k.val, by omega⟩ := by
          rw [Fin.succAbove, if_pos (by simp [Fin.lt_def]; omega)]
        rw [hk_cs, hq_succAbove]
        -- RHS: staircaseFirstCoord n i_lo p.val ⟨k.val, _⟩ where ⟨..⟩ : Fin(n+1).
        -- Since k.val < j.val ≤ i.val - 1 = i_lo.val.
        have hcond : k.val < i_lo.val := by rw [hi_loval]; omega
        simp only [staircaseFirstCoord, if_pos hcond]
        -- Goal: p.val ⟨k.val, _⟩ in Fin(n+2) = p.val ⟨k.val, _⟩.castSucc in Fin(n+2).
        apply congrArg
        apply Fin.ext
        simp [Fin.val_castSucc]
      · push_neg at hkj
        have hkj_gt : j.val < k.val := lt_of_le_of_ne hkj (Ne.symm hne_val)
        have hk_pos : 0 < k.val := by omega
        rw [hfilter_gt k hkj_gt, Finset.sum_singleton]
        by_cases hk_lt_i : k.val < i.val
        · -- Case 2a: j.val < k.val < i.val.
          simp only [staircaseFirstCoord, if_pos hk_lt_i]
          have hk_cs : k.castSucc = Fin.succAbove j ⟨k.val - 1, by omega⟩ := by
            rw [Fin.succAbove, if_neg (by simp [Fin.lt_def]; omega)]
            apply Fin.ext; simp [Fin.val_castSucc, Fin.val_succ]; omega
          rw [hk_cs, hq_succAbove]
          -- RHS: staircaseFirstCoord at ⟨k.val - 1, _⟩ : Fin(n+1) with val < i_lo.val.
          have hcond : (k.val - 1) < i_lo.val := by rw [hi_loval]; omega
          simp only [staircaseFirstCoord, if_pos hcond]
          apply congrArg; apply Fin.ext
          simp [Fin.val_castSucc]
        · push_neg at hk_lt_i
          by_cases hk_eq_i : k.val = i.val
          · simp only [staircaseFirstCoord, if_neg (by omega : ¬ k.val < i.val),
              if_pos hk_eq_i]
            -- k.val = i.val, so k.val - 1 = i.val - 1 = i_lo.val.
            have hi_cs : i.castSucc = Fin.succAbove j ⟨i.val - 1, by omega⟩ := by
              rw [Fin.succAbove, if_neg (by simp [Fin.lt_def]; omega)]
              apply Fin.ext; simp [Fin.val_castSucc, Fin.val_succ]; omega
            have hi_su : i.succ = Fin.succAbove j ⟨i.val, by omega⟩ := by
              rw [Fin.succAbove, if_neg (by simp [Fin.lt_def]; omega)]
            rw [hi_cs, hi_su, hq_succAbove, hq_succAbove]
            -- RHS: staircaseFirstCoord at ⟨k.val - 1, _⟩ : Fin(n+1) with val = i_lo.val.
            have hmval : (k.val - 1) = i_lo.val := by rw [hi_loval]; omega
            have hcond_lt : ¬ (k.val - 1) < i_lo.val := by rw [hi_loval]; omega
            simp only [staircaseFirstCoord, if_neg hcond_lt, if_pos hmval]
            -- Match: p.val ⟨i.val - 1, _⟩ + p.val ⟨i.val, _⟩
            -- = p.val i_lo.castSucc + p.val i_lo.succ.
            congr 1
            all_goals
              apply congrArg
              apply Fin.ext
              simp [Fin.val_castSucc, Fin.val_succ, hi_loval]
              omega
          · have hk_gt_i : i.val < k.val := lt_of_le_of_ne hk_lt_i (Ne.symm hk_eq_i)
            simp only [staircaseFirstCoord, if_neg (by omega : ¬ k.val < i.val),
              if_neg hk_eq_i]
            have hk_su : k.succ = Fin.succAbove j ⟨k.val, by omega⟩ := by
              rw [Fin.succAbove, if_neg (by simp [Fin.lt_def]; omega)]
            rw [hk_su, hq_succAbove]
            -- RHS at ⟨k.val - 1, _⟩ : Fin(n+1) with val > i_lo.val.
            have hcond_lt : ¬ (k.val - 1) < i_lo.val := by rw [hi_loval]; omega
            have hcond_ne : (k.val - 1) ≠ i_lo.val := by rw [hi_loval]; omega
            simp only [staircaseFirstCoord, if_neg hcond_lt, if_neg hcond_ne]
            apply congrArg; apply Fin.ext
            simp [Fin.val_succ]; omega
  -- Pack into staircase map equality.
  have hfirst_pack :
      (⟨staircaseFirstCoord (n + 1) i q.val,
        staircaseFirstCoord_mem_stdSimplex (n + 1) i q.property⟩
        : stdSimplex ℝ (Fin (n + 2))) =
      stdSimplex.map (Fin.succAbove j_lo)
        ⟨staircaseFirstCoord n i_lo p.val,
         staircaseFirstCoord_mem_stdSimplex n i_lo p.property⟩ := by
    apply Subtype.ext
    funext k
    -- The RHS is `(stdSimplex.map _ _).val k` which unfolds to FunOnFinite.linearMap.
    change staircaseFirstCoord (n + 1) i q.val k =
      FunOnFinite.linearMap ℝ ℝ (Fin.succAbove j_lo)
        (fun m : Fin (n + 1) => staircaseFirstCoord n i_lo p.val m) k
    exact hfirst k
  have htime_pack :
      (⟨staircaseTimeCoord (n + 1) i q.val,
        staircaseTimeCoord_mem_Icc (n + 1) i q.property⟩ : Set.Icc (0 : ℝ) 1) =
      ⟨staircaseTimeCoord n i_lo p.val,
        staircaseTimeCoord_mem_Icc n i_lo p.property⟩ := Subtype.ext htime
  -- Conclude prismSimplex equality.
  simp only [prismSimplex, ContinuousMap.comp_apply, staircaseMap, ContinuousMap.coe_mk,
    ContinuousMap.prodMap_apply]
  rw [hfirst_pack, htime_pack]
  rfl

/-- **Upper side-face identity.** For prism degree `n + 1`, staircase
index `i : Fin (n + 2)`, and face index `j : Fin (n + 3)` with
`i.val + 1 < j.val`, the `j`-th face of `prismSimplex (n + 1) i H s`
equals the `i`-th prism simplex (at degree `n`) over `s ∘ δ_{j-1}`.

Dropping the upper vertex `w_{j-1}` (`j > i + 1`) leaves
`[v_0, ..., v_i, w_i, ..., ŵ_{j-1}, ..., w_{n+1}]`, the `i`-th
staircase simplex over `s ∘ δ_{j-1}`. -/
theorem prismSimplex_side_face_upper
    {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    {f g : C(X, Y)} (H : ContinuousMap.Homotopy f g)
    (n : ℕ) (i : Fin (n + 2)) (j : Fin (n + 3))
    (hj : i.val + 1 < j.val)
    (s : C(stdSimplex ℝ (Fin (n + 2)), X)) :
    ∀ p : stdSimplex ℝ (Fin (n + 2)),
    prismSimplex (n + 1) i H s
        (stdSimplex.map (Fin.succAbove j) p) =
    prismSimplex n
        ⟨i.val, by omega⟩ H
        (s.comp ⟨stdSimplex.map
            (Fin.succAbove ⟨j.val - 1, by omega⟩),
          stdSimplex.continuous_map _⟩) p := by
  sorry

end JacobianChallenge.Periods
