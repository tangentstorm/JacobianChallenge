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

end JacobianChallenge.Periods
