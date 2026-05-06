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

end JacobianChallenge.Periods
