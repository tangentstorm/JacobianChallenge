import Jacobian.Periods.PathIntegralViaCoverWithRefinementInvariant

/-!
# Path-additivity (`_trans`) for `pathIntegralViaCoverWith` (aligned partition)

**Phase 6 deliverable**, used to discharge Sorry 1
(`pathIntegralViaCover_trans_eq_add` in `PullbackNaturality.lean`).

States: for an aligned uniform chart partition of `γ.trans γ'` of size
`2 * n` whose first `n` segments cover `γ` (with `pickA`) and last `n`
segments cover `γ'` (with `pickB`), the cover-with sum splits:

  `pathIntegralViaCoverWith ω (γ.trans γ') (2*n) _ pickT hcovT =
   pathIntegralViaCoverWith ω γ n hn pickA hcovA +
   pathIntegralViaCoverWith ω γ' n hn pickB hcovB`.

## Strategy

`pathIntegralViaCoverWith ω (γ.trans γ') (2*n) _ pickT hcovT` unfolds
to a `Finset.sum` over `Fin (2*n)`. Reindex via `Fin (2*n) ≃
Fin n ⊕ Fin n` (`Fin.sumFinAddFin`). The first-half summands
correspond to subpaths of `γ.trans γ'` on `[0, 1/2]`, which by
`Path.extend_trans_of_le_half` are reparameterisations of subpaths of
`γ` on `[0, 1]`. The second-half summands correspond to subpaths on
`[1/2, 1]`, reparameterisations of subpaths of `γ'` on `[0, 1]`.

The reparameterisation is the key step — same flavour as
`curveIntegral_subpath_of_le` in `CurveIntegralSubpath.lean`, but
specialised to the half-affine maps `s ↦ s/2` and `s ↦ (s+1)/2`.

## Status

A single named sorry. Proof is mechanical Fin-bookkeeping plus the
half-affine reparameterisation invariance for
`pathIntegralViaChartCorrect` (which itself needs the curve-integral
reparameterisation lemma).
-/

namespace JacobianChallenge.Periods

open Set unitInterval JacobianChallenge.HolomorphicForms

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  {X : Type*} [TopologicalSpace X] [ChartedSpace E X]
  [IsManifold (modelWithCornersSelf ℂ E) (⊤ : WithTop ℕ∞) X]

/-- The aligned-`pickT` for `γ.trans γ'` of size `2 * n`: the first
`n` indices use `pickA`, the last `n` use `pickB`. -/
noncomputable def alignedPickT
    (n : ℕ) (pickA pickB : Fin n → X) (j : Fin (2 * n)) : X :=
  if hlt : j.val < n then pickA ⟨j.val, hlt⟩
  else pickB ⟨j.val - n, by have h := j.isLt; omega⟩

/-- **Phase 6 (single named gap): With-level path additivity on aligned partition.**

For partitions `(n, pickA, hcovA)` of `γ` and `(n, pickB, hcovB)` of `γ'`
that combine into an aligned partition `(2*n, alignedPickT n pickA pickB,
hcovT)` of `γ.trans γ'`, the cover-with sum splits.

Proof reduces to a Fin-reindexing of the `2*n` sum into two `n`-sums
plus the half-affine reparameterisation invariance — see file-level
docstring. -/
theorem pathIntegralViaCoverWith_aligned_trans
    (ω : HolomorphicOneForm E X) {a b c : X}
    (γ : Path a b) (γ' : Path b c)
    (n : ℕ) (hn : 0 < n)
    (pickA pickB : Fin n → X)
    (hcovA : ∀ (i : Fin n) (t : unitInterval),
      (i : ℝ) / n ≤ (t : ℝ) → (t : ℝ) ≤ ((i : ℝ) + 1) / n →
      γ t ∈ (chartAt E (pickA i)).source)
    (hcovB : ∀ (i : Fin n) (t : unitInterval),
      (i : ℝ) / n ≤ (t : ℝ) → (t : ℝ) ≤ ((i : ℝ) + 1) / n →
      γ' t ∈ (chartAt E (pickB i)).source)
    (hcovT : ∀ (j : Fin (2 * n)) (t : unitInterval),
      (j : ℝ) / ((2 * n : ℕ) : ℝ) ≤ (t : ℝ) →
      (t : ℝ) ≤ ((j : ℝ) + 1) / ((2 * n : ℕ) : ℝ) →
      (γ.trans γ') t ∈ (chartAt E (alignedPickT n pickA pickB j)).source) :
    pathIntegralViaCoverWith ω (γ.trans γ') (2 * n)
        (Nat.mul_pos (by omega) hn)
        (alignedPickT n pickA pickB) hcovT =
      pathIntegralViaCoverWith ω γ n hn pickA hcovA +
      pathIntegralViaCoverWith ω γ' n hn pickB hcovB := by
  sorry

/-! ### Existence of aligned partition for `γ.trans γ'`

Given paths `γ`, `γ'` we can extract uniform chart partitions for each
via `exists_uniform_chart_partition`, refine to a common multiple, and
combine into an aligned `(2*n, alignedPickT)` partition for
`γ.trans γ'`. This reduces Sorry 1
(`pathIntegralViaCover_trans_eq_add` in `PullbackNaturality.lean`) to
`pathIntegralViaCoverWith_aligned_trans` plus refinement invariance.

Discharged Phase 6b: the existence theorem is now sorry-free. -/

variable (X) in
/-- Existence of a common-multiple aligned chart partition for
`γ.trans γ'` given partition data for `γ` and `γ'` separately.

The bookkeeping aligns:
* a partition of `γ` of size `n_A`, refined to `n_A * n_B`,
* a partition of `γ'` of size `n_B`, refined to `n_A * n_B`,
* combined into a `(2 * n_A * n_B, alignedPickT _ pickA' pickB')`
  partition of `γ.trans γ'` whose first half covers γ and second
  half covers γ'.

The cover hypotheses for the refined and combined partitions follow
mechanically from the originals via `Path.trans_apply`'s formula. -/
theorem exists_aligned_partition_for_trans
    {a b c : X} (γ : Path a b) (γ' : Path b c) :
    ∃ (n : ℕ) (hn : 0 < n)
      (pickA pickB : Fin n → X)
      (hcovA : ∀ (i : Fin n) (t : unitInterval),
        (i : ℝ) / n ≤ (t : ℝ) → (t : ℝ) ≤ ((i : ℝ) + 1) / n →
        γ t ∈ (chartAt E (pickA i)).source)
      (hcovB : ∀ (i : Fin n) (t : unitInterval),
        (i : ℝ) / n ≤ (t : ℝ) → (t : ℝ) ≤ ((i : ℝ) + 1) / n →
        γ' t ∈ (chartAt E (pickB i)).source),
      ∀ (j : Fin (2 * n)) (t : unitInterval),
        (j : ℝ) / ((2 * n : ℕ) : ℝ) ≤ (t : ℝ) →
        (t : ℝ) ≤ ((j : ℝ) + 1) / ((2 * n : ℕ) : ℝ) →
        (γ.trans γ') t ∈ (chartAt E (alignedPickT n pickA pickB j)).source := by
  -- Step 1: extract uniform chart partitions for γ and γ' separately.
  obtain ⟨nA, hnA, pickArAW, hcovArAW⟩ :=
    exists_uniform_chart_partition E γ.toContinuousMap
  obtain ⟨nB, hnB, pickBraw, hcovBraw⟩ :=
    exists_uniform_chart_partition E γ'.toContinuousMap
  -- Casting helpers for ℝ-side arithmetic.
  have hnA_pos : (0 : ℝ) < (nA : ℝ) := by exact_mod_cast hnA
  have hnB_pos : (0 : ℝ) < (nB : ℝ) := by exact_mod_cast hnB
  have hnAB_pos : (0 : ℝ) < (nA : ℝ) * (nB : ℝ) := mul_pos hnA_pos hnB_pos
  have hcast : ((nA * nB : ℕ) : ℝ) = (nA : ℝ) * (nB : ℝ) := by push_cast; ring
  have hidiv_A : ∀ i : Fin (nA * nB), i.val / nB < nA := fun i =>
    (Nat.div_lt_iff_lt_mul hnB).mpr i.isLt
  have hidiv_B : ∀ i : Fin (nA * nB), i.val / nA < nB := fun i =>
    (Nat.div_lt_iff_lt_mul hnA).mpr (Nat.mul_comm nA nB ▸ i.isLt)
  -- Refined cover hypothesis for γ at granularity nA * nB (mirrors
  -- `pathIntegralViaCover_partition_compat_under_smooth`).
  have hcovA : ∀ (i : Fin (nA * nB)) (t : unitInterval),
      (i : ℝ) / ((nA * nB : ℕ) : ℝ) ≤ (t : ℝ) →
      (t : ℝ) ≤ ((i : ℝ) + 1) / ((nA * nB : ℕ) : ℝ) →
      γ t ∈ (chartAt E (pickArAW ⟨i.val / nB, hidiv_A i⟩)).source := by
    intro i t ht1 ht2
    refine hcovArAW ⟨i.val / nB, hidiv_A i⟩ t ?_ ?_
    · have hmul : ((i.val / nB : ℕ) : ℝ) * (nB : ℝ) ≤ (i.val : ℝ) := by
        exact_mod_cast Nat.div_mul_le_self i.val nB
      have hstep : ((i.val / nB : ℕ) : ℝ) / (nA : ℝ) ≤ (i.val : ℝ) / ((nA * nB : ℕ) : ℝ) := by
        rw [hcast, div_le_div_iff₀ hnA_pos hnAB_pos]
        nlinarith [hmul, hnA_pos, hnB_pos]
      exact hstep.trans ht1
    · have h_nat : i.val + 1 ≤ ((i.val / nB) + 1) * nB := by
        have h_lt : i.val / nB < (i.val / nB) + 1 := Nat.lt_succ_self _
        have := (Nat.div_lt_iff_lt_mul hnB).mp h_lt
        omega
      have h_real : (i.val : ℝ) + 1 ≤ (((i.val / nB) + 1 : ℕ) : ℝ) * (nB : ℝ) := by
        push_cast; exact_mod_cast h_nat
      have hstep : ((i.val : ℝ) + 1) / ((nA * nB : ℕ) : ℝ) ≤
          (((i.val / nB : ℕ) + 1 : ℕ) : ℝ) / (nA : ℝ) := by
        rw [hcast, div_le_div_iff₀ hnAB_pos hnA_pos]
        nlinarith [h_real, hnA_pos, hnB_pos]
      have hcast_succ :
          (((i.val / nB : ℕ) + 1 : ℕ) : ℝ) = ((i.val / nB : ℕ) : ℝ) + 1 := by push_cast; ring
      rw [hcast_succ] at hstep
      exact ht2.trans hstep
  have hcovB : ∀ (i : Fin (nA * nB)) (t : unitInterval),
      (i : ℝ) / ((nA * nB : ℕ) : ℝ) ≤ (t : ℝ) →
      (t : ℝ) ≤ ((i : ℝ) + 1) / ((nA * nB : ℕ) : ℝ) →
      γ' t ∈ (chartAt E (pickBraw ⟨i.val / nA, hidiv_B i⟩)).source := by
    intro i t ht1 ht2
    refine hcovBraw ⟨i.val / nA, hidiv_B i⟩ t ?_ ?_
    · have hmul : ((i.val / nA : ℕ) : ℝ) * (nA : ℝ) ≤ (i.val : ℝ) := by
        exact_mod_cast Nat.div_mul_le_self i.val nA
      have hstep : ((i.val / nA : ℕ) : ℝ) / (nB : ℝ) ≤ (i.val : ℝ) / ((nA * nB : ℕ) : ℝ) := by
        rw [hcast, div_le_div_iff₀ hnB_pos hnAB_pos]
        nlinarith [hmul, hnA_pos, hnB_pos]
      exact hstep.trans ht1
    · have h_nat : i.val + 1 ≤ ((i.val / nA) + 1) * nA := by
        have h_lt : i.val / nA < (i.val / nA) + 1 := Nat.lt_succ_self _
        have := (Nat.div_lt_iff_lt_mul hnA).mp h_lt
        omega
      have h_real : (i.val : ℝ) + 1 ≤ (((i.val / nA) + 1 : ℕ) : ℝ) * (nA : ℝ) := by
        push_cast; exact_mod_cast h_nat
      have hstep : ((i.val : ℝ) + 1) / ((nA * nB : ℕ) : ℝ) ≤
          (((i.val / nA : ℕ) + 1 : ℕ) : ℝ) / (nB : ℝ) := by
        rw [hcast, div_le_div_iff₀ hnAB_pos hnB_pos]
        nlinarith [h_real, hnA_pos, hnB_pos]
      have hcast_succ :
          (((i.val / nA : ℕ) + 1 : ℕ) : ℝ) = ((i.val / nA : ℕ) : ℝ) + 1 := by push_cast; ring
      rw [hcast_succ] at hstep
      exact ht2.trans hstep
  -- Assemble the existential: choose `n := nA * nB`, the refined chart picks,
  -- the refined cover hypotheses, and discharge the aligned-partition condition.
  refine ⟨nA * nB, Nat.mul_pos hnA hnB,
    fun i => pickArAW ⟨i.val / nB, hidiv_A i⟩,
    fun i => pickBraw ⟨i.val / nA, hidiv_B i⟩,
    hcovA, hcovB, ?_⟩
  intro j t hj1 hj2
  -- Cast helpers for the `2 * n` granularity.
  have hn_pos : (0 : ℝ) < ((nA * nB : ℕ) : ℝ) := by rw [hcast]; exact hnAB_pos
  have h2cast : ((2 * (nA * nB) : ℕ) : ℝ) = 2 * ((nA * nB : ℕ) : ℝ) := by push_cast; ring
  have h2nAB_pos : (0 : ℝ) < 2 * ((nA * nB : ℕ) : ℝ) := by positivity
  by_cases hjn : j.val < nA * nB
  · -- Case: j.val < nA * nB. The aligned pick is `pickA ⟨j.val, hjn⟩`.
    -- From the cell bound `t ≤ (j+1)/(2n)` and `j+1 ≤ n`, conclude `t ≤ 1/2`,
    -- so `(γ.trans γ') t = γ ⟨2 * t, _⟩` by `Path.trans_apply`. Apply hcovA.
    have h_aligned_eq :
        alignedPickT (nA * nB)
          (fun i => pickArAW ⟨i.val / nB, hidiv_A i⟩)
          (fun i => pickBraw ⟨i.val / nA, hidiv_B i⟩) j =
        pickArAW ⟨j.val / nB, hidiv_A ⟨j.val, hjn⟩⟩ := by
      unfold alignedPickT; exact dif_pos hjn
    rw [h_aligned_eq]
    have hjn_real : ((j : ℝ) + 1) ≤ ((nA * nB : ℕ) : ℝ) := by
      have h : j.val + 1 ≤ nA * nB := hjn
      exact_mod_cast h
    have ht_half : (t : ℝ) ≤ 1 / 2 := by
      have hub : ((j : ℝ) + 1) / ((2 * (nA * nB) : ℕ) : ℝ) ≤ 1 / 2 := by
        rw [h2cast, div_le_div_iff₀ h2nAB_pos (by norm_num : (0:ℝ) < 2)]
        linarith
      exact hj2.trans hub
    rw [Path.trans_apply, dif_pos ht_half]
    have h_2t_in : 2 * (t : ℝ) ∈ unitInterval := by
      refine ⟨?_, ?_⟩
      · have := t.2.1; linarith
      · linarith
    have h_jval_eq :
        ((⟨j.val, hjn⟩ : Fin (nA * nB)) : ℝ) = (j : ℝ) := rfl
    refine hcovA ⟨j.val, hjn⟩ ⟨2 * (t : ℝ), h_2t_in⟩ ?_ ?_
    · -- ((j.val : ℕ) : ℝ) / (nA * nB) ≤ 2 * (t : ℝ)
      rw [h_jval_eq]
      have h_jt : (j : ℝ) / ((2 * (nA * nB) : ℕ) : ℝ) ≤ (t : ℝ) := hj1
      rw [h2cast] at h_jt
      rw [div_le_iff₀ hn_pos]
      rw [div_le_iff₀ h2nAB_pos] at h_jt
      linarith
    · -- 2 * (t : ℝ) ≤ ((j.val : ℕ) : ℝ + 1) / (nA * nB)
      rw [h_jval_eq]
      have h_jt : (t : ℝ) ≤ ((j : ℝ) + 1) / ((2 * (nA * nB) : ℕ) : ℝ) := hj2
      rw [h2cast] at h_jt
      rw [le_div_iff₀ hn_pos]
      rw [le_div_iff₀ h2nAB_pos] at h_jt
      linarith
  · -- Case: j.val ≥ nA * nB. The aligned pick is `pickB ⟨j.val - n, _⟩`.
    push_neg at hjn
    have h_aligned_eq :
        alignedPickT (nA * nB)
          (fun i => pickArAW ⟨i.val / nB, hidiv_A i⟩)
          (fun i => pickBraw ⟨i.val / nA, hidiv_B i⟩) j =
        pickBraw ⟨(j.val - nA * nB) / nA,
          hidiv_B ⟨j.val - nA * nB, by have h := j.isLt; omega⟩⟩ := by
      unfold alignedPickT; exact dif_neg (not_lt.mpr hjn)
    rw [h_aligned_eq]
    -- `j.val ≥ n` implies `j/(2n) ≥ 1/2`, hence `t ≥ 1/2`.
    have hj_ge_half : (1 : ℝ) / 2 ≤ (j : ℝ) / ((2 * (nA * nB) : ℕ) : ℝ) := by
      rw [h2cast, le_div_iff₀ h2nAB_pos]
      have : ((nA * nB : ℕ) : ℝ) ≤ (j.val : ℝ) := by exact_mod_cast hjn
      linarith
    have ht_ge_half : (1 : ℝ) / 2 ≤ (t : ℝ) := hj_ge_half.trans hj1
    by_cases ht_gt_half : 1 / 2 < (t : ℝ)
    · -- Subcase: t > 1/2. Use `Path.trans_apply`'s `dif_neg` branch.
      rw [Path.trans_apply, dif_neg (not_le.mpr ht_gt_half)]
      have h_2t_sub_in : 2 * (t : ℝ) - 1 ∈ unitInterval := by
        refine ⟨?_, ?_⟩
        · linarith
        · have := t.2.2; linarith
      have h_nat_sub : ((j.val - nA * nB : ℕ) : ℝ) = (j.val : ℝ) - ((nA * nB : ℕ) : ℝ) := by
        rw [Nat.cast_sub hjn]
      have h_idx_cast :
          ((⟨j.val - nA * nB, by have h := j.isLt; omega⟩ : Fin (nA * nB)) : ℝ) =
          (j.val : ℝ) - ((nA * nB : ℕ) : ℝ) := by
        change ((j.val - nA * nB : ℕ) : ℝ) = (j.val : ℝ) - ((nA * nB : ℕ) : ℝ)
        exact h_nat_sub
      refine hcovB ⟨j.val - nA * nB, by have h := j.isLt; omega⟩
        ⟨2 * (t : ℝ) - 1, h_2t_sub_in⟩ ?_ ?_
      · rw [h_idx_cast]
        have h_jt : (j : ℝ) / ((2 * (nA * nB) : ℕ) : ℝ) ≤ (t : ℝ) := hj1
        rw [h2cast] at h_jt
        rw [div_le_iff₀ hn_pos]
        rw [div_le_iff₀ h2nAB_pos] at h_jt
        change (j.val : ℝ) - ((nA * nB : ℕ) : ℝ) ≤ (2 * (t : ℝ) - 1) * ((nA * nB : ℕ) : ℝ)
        have hjr : (j : ℝ) = (j.val : ℝ) := rfl
        rw [hjr] at h_jt
        nlinarith
      · rw [h_idx_cast]
        have h_jt : (t : ℝ) ≤ ((j : ℝ) + 1) / ((2 * (nA * nB) : ℕ) : ℝ) := hj2
        rw [h2cast] at h_jt
        rw [le_div_iff₀ hn_pos]
        rw [le_div_iff₀ h2nAB_pos] at h_jt
        change (2 * (t : ℝ) - 1) * ((nA * nB : ℕ) : ℝ) ≤
            (j.val : ℝ) - ((nA * nB : ℕ) : ℝ) + 1
        have hjr : (j : ℝ) = (j.val : ℝ) := rfl
        rw [hjr] at h_jt
        nlinarith
    · -- Subcase: t ≤ 1/2. Combined with `t ≥ 1/2`, we have `t = 1/2`, and the
      -- aligned-cell bound forces `j.val = nA * nB`. Then
      -- `(γ.trans γ') t = γ ⟨1, _⟩ = b = γ' 0`, so `γ' 0 ∈ chart` follows
      -- from `hcovBraw` at `i = 0`, `t' = 0`.
      push_neg at ht_gt_half
      have ht_eq : (t : ℝ) = 1 / 2 := le_antisymm ht_gt_half ht_ge_half
      have hj_eq : j.val = nA * nB := by
        have hj1' : (j : ℝ) / ((2 * (nA * nB) : ℕ) : ℝ) ≤ 1 / 2 := by
          rw [ht_eq] at hj1; exact hj1
        have hj_eq_real : (j : ℝ) / ((2 * (nA * nB) : ℕ) : ℝ) = 1 / 2 :=
          le_antisymm hj1' hj_ge_half
        rw [h2cast, div_eq_iff (ne_of_gt h2nAB_pos)] at hj_eq_real
        have h_real : (j.val : ℝ) = ((nA * nB : ℕ) : ℝ) := by
          have hjr : (j : ℝ) = (j.val : ℝ) := rfl
          rw [hjr] at hj_eq_real
          linarith
        exact_mod_cast h_real
      -- Show the chart in the goal equals `chartAt E (pickBraw ⟨0, hnB⟩)`.
      have h_chart_eq :
          chartAt E (pickBraw ⟨(j.val - nA * nB) / nA,
              hidiv_B ⟨j.val - nA * nB, by have h := j.isLt; omega⟩⟩) =
          chartAt E (pickBraw ⟨0, hnB⟩) := by
        congr 2
        apply Fin.ext
        change (j.val - nA * nB) / nA = 0
        rw [hj_eq, Nat.sub_self, Nat.zero_div]
      rw [h_chart_eq]
      -- Now show `(γ.trans γ') t ∈ chartAt E (pickBraw ⟨0, hnB⟩).source`.
      -- Compute `(γ.trans γ') t = γ ⟨1, _⟩ = b = γ' 0` and apply `hcovBraw`.
      rw [Path.trans_apply, dif_pos ht_gt_half]
      have h2t : 2 * (t : ℝ) = 1 := by linarith
      have h_one_in : (1 : ℝ) ∈ unitInterval :=
        ⟨zero_le_one, le_refl 1⟩
      rw [show (⟨2 * (t : ℝ),
            (mul_pos_mem_iff zero_lt_two).2 ⟨t.2.1, ht_gt_half⟩⟩ : unitInterval) =
              (1 : unitInterval) from Subtype.ext h2t]
      rw [γ.target]
      rw [show b = γ' (0 : unitInterval) from γ'.source.symm]
      refine hcovBraw ⟨0, hnB⟩ (0 : unitInterval) ?_ ?_
      · simp
      · simp

end JacobianChallenge.Periods
