import Jacobian.Periods.PathIntegralViaCover
import Jacobian.Periods.PathIntegralChartCorrectSplit
import Jacobian.Periods.CurveIntegralSubpath
import Jacobian.Periods.PathIntegralCongr
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Order.Interval.Finset.Nat

set_option linter.unusedSectionVars false

/-!
# Refinement-by-multiple for `pathIntegralViaCoverWith`

States that refining a uniform chart partition of size `n` by an
integer factor `k > 0` (giving size `n * k`) preserves the cover-with
sum, provided the refined chart picks satisfy
`pickChart' j = pickChart ⟨j.val / k, _⟩`.

## Strategy

1. **Reindex the RHS sum.** `Fin (n * k) ≃ Fin n × Fin k` via
   `j ↦ (⟨j.val / k, _⟩, ⟨j.val % k, _⟩)`. The RHS sum then becomes
   a double sum `∑ i : Fin n, ∑ j' : Fin k, F(i, j')`.

2. **Each i-th block aggregates to the i-th LHS term.** For fixed
   `i : Fin n`, the inner sum `∑ j' : Fin k, F(i, j')` equals the i-th
   LHS summand. This is `k`-fold segment additivity, packaged as the
   auxiliary lemma `pathIntegralViaChartCorrect_split_uniform`.

3. **Sum over i** to recover the LHS.

## Integrability hypothesis
-/

namespace JacobianChallenge.Periods

open Set MeasureTheory Path
open scoped unitInterval
open JacobianChallenge.HolomorphicForms

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  {X : Type*} [TopologicalSpace X] [ChartedSpace E X]
  [IsManifold (modelWithCornersSelf ℂ E) (⊤ : WithTop ℕ∞) X]

omit [NormedSpace ℂ E] [IsManifold (modelWithCornersSelf ℂ E) (⊤ : WithTop ℕ∞) X] in
/--
Range of the i-th uniform partition segment lies in the chart
source given a uniform-cover hypothesis.
-/
theorem range_segment_subset_source_of_hcov
    {a b : X} (γ : Path a b) (n : ℕ) (hn : 0 < n) (pickChart : Fin n → X)
    (hcov : ∀ (i : Fin n) (t : unitInterval),
      (i : ℝ) / n ≤ (t : ℝ) → (t : ℝ) ≤ ((i : ℝ) + 1) / n →
      γ t ∈ (chartAt E (pickChart i)).source)
    (i : Fin n) :
    range (γ.subpath (divFinIcc n hn i.val (le_of_lt i.isLt))
                     (divFinIcc n hn (i.val + 1) i.isLt))
      ⊆ (chartAt E (pickChart i)).source := by
  rw [Path.range_subpath, Set.uIcc_of_le (divFinIcc_le_succ n hn i.val i.isLt)]
  rintro x ⟨t, ht, rfl⟩
  rcases Set.mem_Icc.mp ht with ⟨h1, h2⟩
  have hle1 : ((i.val : ℝ) / n) ≤ (t : ℝ) := h1
  have hle2 : (t : ℝ) ≤ ((i.val : ℝ) + 1) / n := by
    have h2' : (t : ℝ) ≤ (divFinIcc n hn (i.val + 1) i.isLt : ℝ) := h2
    rw [divFinIcc_val] at h2'
    push_cast at h2'
    exact h2'
  exact hcov i t hle1 hle2


theorem pathIntegralViaChartCorrect_split_uniform
    (c : OpenPartialHomeomorph X E) (ω : HolomorphicOneForm E X)
    {a b : X} (γ : Path a b) (hrange : range γ ⊆ c.source)
    (k : ℕ) (hk : 0 < k)
    (hsub : ∀ j : Fin k,
      range (γ.subpath (divFinIcc k hk j.val (le_of_lt j.isLt))
                       (divFinIcc k hk (j.val + 1) j.isLt))
        ⊆ c.source)
    (hint : IntervalIntegrable
      (fun t => (chartedFormPullback c ω) ((chartLift c γ hrange).extend t)
        (derivWithin (chartLift c γ hrange).extend (Set.Icc 0 1) t))
      volume 0 1) :
    pathIntegralViaChartCorrect c ω γ hrange =
      ∑ j : Fin k, pathIntegralViaChartCorrect c ω
        (γ.subpath (divFinIcc k hk j.val (le_of_lt j.isLt))
                   (divFinIcc k hk (j.val + 1) j.isLt))
        (hsub j) := by
  set gtilde := chartLift c γ hrange with hgtilde
  set omtilde := chartedFormPullback c ω with homtilde
  -- Bridge: integrand expressed as `curveIntegralFun`.
  have h_fun_eq :
      (fun t => omtilde (gtilde.extend t)
        (derivWithin gtilde.extend (Set.Icc 0 1) t))
      = curveIntegralFun omtilde gtilde := by
    funext t
    rw [curveIntegralFun_def]
  have hint' : IntervalIntegrable
      (curveIntegralFun omtilde gtilde) volume 0 1 := h_fun_eq ▸ hint
  -- Each summand reduces to an interval integral over [j/k, (j+1)/k].
  have h_summand : ∀ j : Fin k,
      pathIntegralViaChartCorrect c ω
        (γ.subpath (divFinIcc k hk j.val (le_of_lt j.isLt))
                   (divFinIcc k hk (j.val + 1) j.isLt))
        (hsub j) =
      ∫ t in ((j.val : ℝ) / k)..((j.val + 1 : ℕ) : ℝ) / k,
        curveIntegralFun omtilde gtilde t := by
    intro j
    show curveIntegral omtilde (chartLift c (γ.subpath _ _) (hsub j)) = _
    rw [chartLift_subpath c γ hrange _ _ (hsub j),
        curveIntegral_subpath_of_le omtilde gtilde _ _
          (divFinIcc_le_succ k hk j.val j.isLt)]
    rw [show (divFinIcc k hk j.val (le_of_lt j.isLt) : ℝ) = (j.val : ℝ) / k from rfl,
        show (divFinIcc k hk (j.val + 1) j.isLt : ℝ) = ((j.val + 1 : ℕ) : ℝ) / k from rfl]
    refine intervalIntegral.integral_congr (fun t _ => ?_)
    rw [curveIntegralFun_def]
  -- Apply the per-summand identity.
  rw [Finset.sum_congr rfl (fun j _ => h_summand j)]
  -- LHS expanded as ∫ t in 0..1, curveIntegralFun.
  show curveIntegral omtilde gtilde = _
  rw [curveIntegral_def]
  -- Convert ∑ j : Fin k, ... to ∑ j ∈ Finset.range k, ...
  rw [show (∑ j : Fin k,
              ∫ t in ((j.val : ℝ) / k)..((j.val + 1 : ℕ) : ℝ) / k,
                curveIntegralFun omtilde gtilde t)
        = ∑ j ∈ Finset.range k,
              ∫ t in ((j : ℝ) / k)..((j + 1 : ℕ) : ℝ) / k,
                curveIntegralFun omtilde gtilde t from
      Fin.sum_univ_eq_sum_range
        (fun j => ∫ t in ((j : ℝ) / k)..((j + 1 : ℕ) : ℝ) / k,
          curveIntegralFun omtilde gtilde t) k]
  -- Apply sum_integral_adjacent_intervals (the range-form version).
  have hk_pos : (0 : ℝ) < k := by exact_mod_cast hk
  have hk_ne : (k : ℝ) ≠ 0 := hk_pos.ne'
  set aₖ : ℕ → ℝ := fun j => (j : ℝ) / k with haₖ_def
  have hsum :
      ∑ j ∈ Finset.range k,
          (∫ t in aₖ j..aₖ (j + 1), curveIntegralFun omtilde gtilde t)
        = ∫ t in aₖ 0..aₖ k, curveIntegralFun omtilde gtilde t := by
    refine intervalIntegral.sum_integral_adjacent_intervals
      (f := curveIntegralFun omtilde gtilde) (μ := volume) (n := k) ?_
    intro j hj
    refine hint'.mono_set ?_
    rw [Set.uIcc_of_le, Set.uIcc_of_le]
    · refine Set.Icc_subset_Icc ?_ ?_
      · exact div_nonneg (Nat.cast_nonneg _) hk_pos.le
      · rw [div_le_one hk_pos]
        exact_mod_cast hj
    · exact zero_le_one
    · rw [div_le_div_iff_of_pos_right hk_pos]
      exact_mod_cast Nat.le_succ j
  -- aₖ 0 = 0, aₖ k = 1
  have h_aₖ_zero : aₖ 0 = 0 := by simp [haₖ_def]
  have h_aₖ_k : aₖ k = 1 := by
    simp [haₖ_def, div_self hk_ne]
  -- Rewrite the goal to match `hsum`.
  show (∫ t in (0 : ℝ)..1, curveIntegralFun omtilde gtilde t) =
       ∑ j ∈ Finset.range k,
           ∫ t in ((j : ℝ) / k)..((j + 1 : ℕ) : ℝ) / k,
             curveIntegralFun omtilde gtilde t
  have h_eq : ∀ j : ℕ, ((j + 1 : ℕ) : ℝ) / k = aₖ (j + 1) := by
    intro j
    show ((j + 1 : ℕ) : ℝ) / k = ((j + 1 : ℕ) : ℝ) / k
    rfl
  rw [show (∑ j ∈ Finset.range k,
              (∫ t in ((j : ℝ) / k)..((j + 1 : ℕ) : ℝ) / k,
                curveIntegralFun omtilde gtilde t))
        = ∑ j ∈ Finset.range k,
              (∫ t in aₖ j..aₖ (j + 1), curveIntegralFun omtilde gtilde t) from
      Finset.sum_congr rfl (fun j _ => by rw [h_eq j])]
  rw [hsum, h_aₖ_zero, h_aₖ_k]

/--
**Single-application boundary identity.** For `i : Fin n` and
`j : Fin k`, the affine-interpolation point at `(j/k)` on the segment
from `(i/n)` to `((i+1)/n)` equals `((i*k+j)/(n*k))` as a unit-interval
element.
-/
theorem subpathAux_divFinIcc_apply_divFinIcc
    (n k : ℕ) (hn : 0 < n) (hk : 0 < k) (i : Fin n) (j : ℕ) (hj : j ≤ k) :
    Path.subpathAux (divFinIcc n hn i.val (le_of_lt i.isLt))
                    (divFinIcc n hn (i.val + 1) i.isLt)
                    (divFinIcc k hk j hj) =
      divFinIcc (n * k) (Nat.mul_pos hn hk) (i.val * k + j)
        (by
          have hi1 : i.val + 1 ≤ n := i.isLt
          calc i.val * k + j ≤ i.val * k + k := Nat.add_le_add_left hj _
            _ = (i.val + 1) * k := by ring
            _ ≤ n * k := Nat.mul_le_mul_right k hi1) := by
  apply Subtype.ext
  show (1 - ((j : ℝ) / k)) * ((i.val : ℝ) / n) +
       ((j : ℝ) / k) * (((i.val + 1 : ℕ) : ℝ) / n) =
       ((i.val * k + j : ℕ) : ℝ) / ((n * k : ℕ) : ℝ)
  have hn_ne : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hn.ne'
  have hk_ne : (k : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hk.ne'
  push_cast
  field_simp
  ring

/--
**Nested-application identity.** The composition of two
affine-interpolations (outer `(i/n) → ((i+1)/n)` and inner `(j/k) →
((j+1)/k)`) equals the affine-interpolation `((i*k+j)/(n*k)) →
((i*k+j+1)/(n*k))` directly.
-/
theorem subpathAux_subpathAux_eq
    (n k : ℕ) (hn : 0 < n) (hk : 0 < k) (i : Fin n) (j : Fin k)
    (s : unitInterval) :
    Path.subpathAux (divFinIcc n hn i.val (le_of_lt i.isLt))
                    (divFinIcc n hn (i.val + 1) i.isLt)
                    (Path.subpathAux (divFinIcc k hk j.val (le_of_lt j.isLt))
                                     (divFinIcc k hk (j.val + 1) j.isLt) s) =
      Path.subpathAux
        (divFinIcc (n * k) (Nat.mul_pos hn hk) (i.val * k + j.val)
          (by
            have hi1 : i.val + 1 ≤ n := i.isLt
            have hj1 : j.val ≤ k := le_of_lt j.isLt
            calc i.val * k + j.val ≤ i.val * k + k := Nat.add_le_add_left hj1 _
              _ = (i.val + 1) * k := by ring
              _ ≤ n * k := Nat.mul_le_mul_right k hi1))
        (divFinIcc (n * k) (Nat.mul_pos hn hk) (i.val * k + j.val + 1)
          (by
            have hi1 : i.val + 1 ≤ n := i.isLt
            have hj1 : j.val + 1 ≤ k := j.isLt
            calc i.val * k + j.val + 1
                = i.val * k + (j.val + 1) := by ring
              _ ≤ i.val * k + k := Nat.add_le_add_left hj1 _
              _ = (i.val + 1) * k := by ring
              _ ≤ n * k := Nat.mul_le_mul_right k hi1))
        s := by
  apply Subtype.ext
  have hn_ne : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hn.ne'
  have hk_ne : (k : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hk.ne'
  show (1 - ((1 - (s : ℝ)) * ((j.val : ℝ) / k) +
              (s : ℝ) * (((j.val + 1 : ℕ) : ℝ) / k))) * ((i.val : ℝ) / n) +
       (((1 - (s : ℝ)) * ((j.val : ℝ) / k) +
         (s : ℝ) * (((j.val + 1 : ℕ) : ℝ) / k))) * (((i.val + 1 : ℕ) : ℝ) / n) =
       (1 - (s : ℝ)) * (((i.val * k + j.val : ℕ) : ℝ) / ((n * k : ℕ) : ℝ)) +
       (s : ℝ) * (((i.val * k + j.val + 1 : ℕ) : ℝ) / ((n * k : ℕ) : ℝ))
  push_cast
  field_simp
  ring

/--
Two paths whose underlying functions agree and whose endpoints are
propositionally equal are HEq.
-/
theorem Path.heq_of_toFun_eq
    {Y : Type*} [TopologicalSpace Y]
    {a b a' b' : Y} (γ : Path a b) (γ' : Path a' b')
    (ha : a = a') (hb : b = b')
    (htoFun : (γ : unitInterval → Y) = (γ' : unitInterval → Y)) : HEq γ γ' := by
  subst ha
  subst hb
  rw [heq_eq_eq]
  exact Path.ext htoFun

/--
Combined chart-change + path-HEq variant of
`pathIntegralViaChartCorrect_eq_of_path_eq`. Useful when the chart is
indexed via two different but equal expressions and the path's
endpoints are propositionally (not definitionally) equal.
-/
theorem pathIntegralViaChartCorrect_eq_of_chart_path_heq
    {c c' : OpenPartialHomeomorph X E} (hc : c = c')
    (ω : HolomorphicOneForm E X)
    {a b a' b' : X} (ha : a = a') (hb : b = b')
    {γ : Path a b} {γ' : Path a' b'} (hγ : HEq γ γ')
    (h : range γ ⊆ c.source) (h' : range γ' ⊆ c'.source) :
    pathIntegralViaChartCorrect c ω γ h =
      pathIntegralViaChartCorrect c' ω γ' h' := by
  subst hc
  exact pathIntegralViaChartCorrect_eq_of_heq c ω ha hb hγ h h'


theorem pathIntegralViaCoverWith_refine_to_multiple
    (ω : HolomorphicOneForm E X) {a b : X} (γ : Path a b)
    (n k : ℕ) (hn : 0 < n) (hk : 0 < k)
    (pickChart : Fin n → X)
    (hcov : ∀ (i : Fin n) (t : unitInterval),
      (i : ℝ) / n ≤ (t : ℝ) → (t : ℝ) ≤ ((i : ℝ) + 1) / n →
      γ t ∈ (chartAt E (pickChart i)).source)
    (hcov' : ∀ (j : Fin (n * k)) (t : unitInterval),
      (j : ℝ) / ((n * k : ℕ) : ℝ) ≤ (t : ℝ) →
      (t : ℝ) ≤ ((j : ℝ) + 1) / ((n * k : ℕ) : ℝ) →
      γ t ∈ (chartAt E (pickChart
        ⟨j.val / k, (Nat.div_lt_iff_lt_mul hk).mpr j.isLt⟩)).source)
    (hint : ∀ i : Fin n, IntervalIntegrable
      (fun t => (chartedFormPullback (chartAt E (pickChart i)) ω)
        ((chartLift (chartAt E (pickChart i))
          (γ.subpath (divFinIcc n hn i.val (le_of_lt i.isLt))
                     (divFinIcc n hn (i.val + 1) i.isLt))
          (range_segment_subset_source_of_hcov γ n hn pickChart hcov i)).extend t)
        (derivWithin (chartLift (chartAt E (pickChart i))
          (γ.subpath (divFinIcc n hn i.val (le_of_lt i.isLt))
                     (divFinIcc n hn (i.val + 1) i.isLt))
          (range_segment_subset_source_of_hcov γ n hn pickChart hcov i)).extend
          (Set.Icc 0 1) t))
      volume 0 1) :
    pathIntegralViaCoverWith ω γ n hn pickChart hcov =
      pathIntegralViaCoverWith ω γ (n * k) (Nat.mul_pos hn hk)
        (fun j => pickChart ⟨j.val / k, (Nat.div_lt_iff_lt_mul hk).mpr j.isLt⟩)
        hcov' := by
  -- Notation
  set hnk := Nat.mul_pos hn hk with hnk_def
  set pickChart' : Fin (n * k) → X :=
    fun j => pickChart ⟨j.val / k, (Nat.div_lt_iff_lt_mul hk).mpr j.isLt⟩
    with hpickChart'_def
  -- Unfold both sides.
  unfold pathIntegralViaCoverWith
  -- Reindex RHS sum from Fin (n*k) to Fin n × Fin k via finProdFinEquiv.
  rw [show (∑ j : Fin (n * k),
              pathIntegralViaChartCorrect (chartAt E (pickChart' j)) ω
                (γ.subpath (divFinIcc (n * k) hnk j.val (le_of_lt j.isLt))
                           (divFinIcc (n * k) hnk (j.val + 1) j.isLt)) _)
        = ∑ p : Fin n × Fin k,
              pathIntegralViaChartCorrect
                (chartAt E (pickChart' (finProdFinEquiv p))) ω
                (γ.subpath
                  (divFinIcc (n * k) hnk (finProdFinEquiv p).val
                    (le_of_lt (finProdFinEquiv p).isLt))
                  (divFinIcc (n * k) hnk ((finProdFinEquiv p).val + 1)
                    (finProdFinEquiv p).isLt))
                _ from
      (Fintype.sum_equiv finProdFinEquiv _ _ (fun _ => rfl)).symm]
  -- Decompose Fin n × Fin k product into nested sum.
  rw [Fintype.sum_prod_type]
  -- Now goal:
  --   ∑ i : Fin n, (i-th LHS term)
  --     = ∑ i : Fin n, ∑ j' : Fin k, (i,j')-th refined term
  refine Finset.sum_congr rfl (fun i _ => ?_)
  -- For each i, identify the inner sum with the i-th LHS term.
  -- Let δ_i := γ.subpath (divFinIcc n hn i ...) (divFinIcc n hn (i+1) ...)
  set δ_i := γ.subpath (divFinIcc n hn i.val (le_of_lt i.isLt))
                       (divFinIcc n hn (i.val + 1) i.isLt) with hδ_i_def
  -- Range of δ_i in chart (pickChart i).source.
  have hδ_i_range : range δ_i ⊆ (chartAt E (pickChart i)).source := by
    rw [hδ_i_def]
    exact range_segment_subset_source_of_hcov γ n hn pickChart hcov i
  -- For each j' : Fin k, the (i, j')-th RHS sub-segment lies in chart (pickChart i).source.
  have hsub_inner : ∀ j' : Fin k,
      range (δ_i.subpath (divFinIcc k hk j'.val (le_of_lt j'.isLt))
                          (divFinIcc k hk (j'.val + 1) j'.isLt))
        ⊆ (chartAt E (pickChart i)).source := by
    intro j'
    refine subset_trans ?_ hδ_i_range
    rw [Path.range_subpath]
    intro x hx
    rcases hx with ⟨t, ht, rfl⟩
    exact ⟨_, rfl⟩
  -- Apply the auxiliary uniform-split lemma to the i-th LHS segment.
  rw [pathIntegralViaChartCorrect_split_uniform
        (chartAt E (pickChart i)) ω δ_i hδ_i_range k hk hsub_inner (hint i)]
  -- Now goal: ∑ j' : Fin k, (chart-corrected integral over δ_i.subpath j')
  --         = ∑ j' : Fin k, (chart-corrected integral over γ.subpath ((ik+j')/(nk)) ((ik+j'+1)/(nk)))
  refine Finset.sum_congr rfl (fun j' _ => ?_)
  -- Notation for the inner subpath bounds (LHS).
  set p_lo := divFinIcc k hk j'.val (le_of_lt j'.isLt) with hp_lo_def
  set p_hi := divFinIcc k hk (j'.val + 1) j'.isLt with hp_hi_def
  -- Reindexed RHS chart pick is `pickChart i`.
  have hpc : pickChart' (finProdFinEquiv (i, j')) = pickChart i := by
    show pickChart ⟨_, _⟩ = pickChart i
    congr 1
    apply Fin.ext
    show (finProdFinEquiv (i, j')).val / k = i.val
    show (j'.val + k * i.val) / k = i.val
    rw [Nat.add_mul_div_left _ _ hk, Nat.div_eq_of_lt j'.isLt, zero_add]
  -- Index identities.
  have hidx_lo : (finProdFinEquiv (i, j')).val = i.val * k + j'.val := by
    show j'.val + k * i.val = i.val * k + j'.val
    ring
  -- The bound 0 < n*k is hnk.
  have hbound_lo : (finProdFinEquiv (i, j')).val ≤ n * k :=
    le_of_lt (finProdFinEquiv (i, j')).isLt
  have hbound_hi : (finProdFinEquiv (i, j')).val + 1 ≤ n * k :=
    (finProdFinEquiv (i, j')).isLt
  -- subpathAux applied at lo and hi positions equals the corresponding divFinIcc on Fin (n*k).
  have hsubpath_lo :
      Path.subpathAux (divFinIcc n hn i.val (le_of_lt i.isLt))
                      (divFinIcc n hn (i.val + 1) i.isLt) p_lo =
      divFinIcc (n * k) hnk (finProdFinEquiv (i, j')).val hbound_lo := by
    rw [hp_lo_def]
    rw [subpathAux_divFinIcc_apply_divFinIcc n k hn hk i j'.val (le_of_lt j'.isLt)]
    apply Subtype.ext
    show ((i.val * k + j'.val : ℕ) : ℝ) / ((n * k : ℕ) : ℝ) =
         ((finProdFinEquiv (i, j')).val : ℝ) / ((n * k : ℕ) : ℝ)
    congr 1
    exact_mod_cast hidx_lo.symm
  have hsubpath_hi :
      Path.subpathAux (divFinIcc n hn i.val (le_of_lt i.isLt))
                      (divFinIcc n hn (i.val + 1) i.isLt) p_hi =
      divFinIcc (n * k) hnk ((finProdFinEquiv (i, j')).val + 1) hbound_hi := by
    rw [hp_hi_def]
    rw [subpathAux_divFinIcc_apply_divFinIcc n k hn hk i (j'.val + 1) j'.isLt]
    apply Subtype.ext
    show ((i.val * k + j'.val + 1 : ℕ) : ℝ) / ((n * k : ℕ) : ℝ) =
         (((finProdFinEquiv (i, j')).val + 1 : ℕ) : ℝ) / ((n * k : ℕ) : ℝ)
    congr 1
    push_cast
    have : (i.val * k + j'.val : ℝ) = ((finProdFinEquiv (i, j')).val : ℝ) := by
      exact_mod_cast hidx_lo.symm
    linarith
  -- Endpoint equalities in X (matching the goal's RHS form).
  have ha_eq : δ_i p_lo =
      γ (divFinIcc (n * k) hnk (finProdFinEquiv (i, j')).val hbound_lo) := by
    rw [hδ_i_def]
    show γ (Path.subpathAux _ _ p_lo) = γ _
    rw [hsubpath_lo]
  have hb_eq : δ_i p_hi =
      γ (divFinIcc (n * k) hnk ((finProdFinEquiv (i, j')).val + 1) hbound_hi) := by
    rw [hδ_i_def]
    show γ (Path.subpathAux _ _ p_hi) = γ _
    rw [hsubpath_hi]
  -- Apply combined chart-change + path-HEq lemma.
  refine pathIntegralViaChartCorrect_eq_of_chart_path_heq
    (congr_arg (chartAt E) hpc.symm) ω ha_eq hb_eq ?_ (hsub_inner j') ?_
  · -- HEq of paths via Path.heq_of_toFun_eq.
    refine Path.heq_of_toFun_eq _ _ ha_eq hb_eq ?_
    funext s
    show δ_i (Path.subpathAux p_lo p_hi s) = γ (Path.subpathAux _ _ s)
    rw [hδ_i_def]
    show γ (Path.subpathAux _ _ (Path.subpathAux p_lo p_hi s)) =
         γ (Path.subpathAux _ _ s)
    congr 1
    rw [hp_lo_def, hp_hi_def]
    rw [subpathAux_subpathAux_eq n k hn hk i j' s]
    -- Now both sides are subpathAux of divFinIcc (n*k); show equality of indices.
    apply Subtype.ext
    have h_lo : ((i.val * k + j'.val : ℕ) : ℝ) = ((finProdFinEquiv (i, j')).val : ℝ) := by
      exact_mod_cast hidx_lo.symm
    have h_hi : ((i.val * k + j'.val + 1 : ℕ) : ℝ) =
                (((finProdFinEquiv (i, j')).val + 1 : ℕ) : ℝ) := by
      have : i.val * k + j'.val + 1 = (finProdFinEquiv (i, j')).val + 1 := by
        rw [hidx_lo]
      exact_mod_cast this
    show (1 - (s : ℝ)) * (((i.val * k + j'.val : ℕ) : ℝ) / ((n * k : ℕ) : ℝ)) +
         (s : ℝ) * (((i.val * k + j'.val + 1 : ℕ) : ℝ) / ((n * k : ℕ) : ℝ)) =
         (1 - (s : ℝ)) * (((finProdFinEquiv (i, j')).val : ℝ) / ((n * k : ℕ) : ℝ)) +
         (s : ℝ) * ((((finProdFinEquiv (i, j')).val + 1 : ℕ) : ℝ) / ((n * k : ℕ) : ℝ))
    rw [h_lo, h_hi]

end JacobianChallenge.Periods
