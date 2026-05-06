import Jacobian.Periods.PathIntegralViaCover
import Jacobian.Periods.PathIntegralChartCorrectSplit

/-!
# Refinement-by-multiple for `pathIntegralViaCoverWith`

**Phase 3 deliverable** of the path-integral well-definedness chain.

States that refining a uniform chart partition of size `n` by an
integer factor `k > 0` (giving size `n * k`) preserves the cover-with
sum, provided the refined chart picks satisfy
`pickChart' j = pickChart ⟨j.val / k, _⟩`.

This is the load-bearing step for Phase 4 (refinement invariance,
sorry 4 in `PullbackNaturality.lean`): two arbitrary partitions
`(n, _)` and `(n', _)` of the same path can both be refined to the
common multiple `(n * n', _)` via this lemma applied twice (with
`k = n'` and `k = n` respectively), and both equal the value at
the common refinement.

## Strategy (proof sketch for the sorry below)

1. **Reindex the RHS sum.** `Fin (n * k) ≃ Fin n × Fin k` via
   `j ↦ (⟨j.val / k, _⟩, ⟨j.val % k, _⟩)`. The RHS sum then becomes
   a double sum `∑ i : Fin n, ∑ j' : Fin k, F(i, j')`.

2. **Each i-th block aggregates to the i-th LHS term.** For fixed
   `i : Fin n`, the inner sum `∑ j' : Fin k, F(i, j')` equals
   `pathIntegralViaChartCorrect (chartAt E (pickChart i)) ω
       (γ.subpath (divFinIcc n hn i.val _) (divFinIcc n hn (i.val+1) _))`
   — i.e. the i-th LHS summand. This is `k`-fold segment additivity:
   the i-th LHS segment splits into k consecutive sub-segments, each
   of which is the j'-th RHS sub-segment within that block, and each
   uses the same chart pick `pickChart i`. Apply
   `pathIntegralViaChartCorrect_split_subpath` (Phase 2) `k - 1`
   times by induction on `k`.

3. **Sum over i** to recover the LHS.

The combinatorial bookkeeping for step 1 is in
`Mathlib.Data.Fin.Basic`/`Mathlib.Algebra.BigOperators.Fin`
(`Finset.sum_fin_eq_sum_range`, `Finset.sum_div_add_mod_succ`, etc.).
The recursive split for step 2 is the genuinely new content; it
needs an inductive auxiliary lemma:

```
lemma pathIntegralViaChartCorrect_eq_sum_subpath_uniform
    (c : OpenPartialHomeomorph X E) (ω : HolomorphicOneForm E X)
    {a b : X} (γ : Path a b) (hrange : range γ ⊆ c.source)
    (k : ℕ) (hk : 0 < k)
    (hint : ∀ j : Fin k, IntervalIntegrable ...) :
    pathIntegralViaChartCorrect c ω γ hrange =
      ∑ j : Fin k, pathIntegralViaChartCorrect c ω
        (γ.subpath (divFinIcc k hk j.val _) (divFinIcc k hk (j.val+1) _)) _
```

proven by induction on `k` with Phase 2 as the inductive step.

## Status

The Phase 3 statement is locked in. Its proof body is a single sorry,
isolating the combinatorial-plus-segment-additivity content into one
focused packet (~3–5 days). With Phase 3 in hand, Phase 4 (refinement
invariance) becomes a direct two-step reduction.
-/

namespace JacobianChallenge.Periods

open Set MeasureTheory Path
open scoped unitInterval
open JacobianChallenge.HolomorphicForms

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  {X : Type*} [TopologicalSpace X] [ChartedSpace E X]
  [IsManifold (modelWithCornersSelf ℂ E) (⊤ : WithTop ℕ∞) X]

/-- **Phase 3 deliverable.** Refining a uniform chart partition of
`γ` by an integer factor `k > 0` (from size `n` to `n * k`, with the
new chart pick `pickChart' j = pickChart ⟨j.val / k, _⟩`) preserves
the value of `pathIntegralViaCoverWith`.

The cover hypothesis on the refined partition is taken explicitly;
its existence (given the original `hcov`) is an immediate consequence
of `Nat.div_mul_le_self` (each refined sub-segment lies inside the
original's chart-source).

Proof currently a `sorry`; see the file-level docstring for the
strategy (Fin-reindex + recursive Phase 2 split). -/
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
        ⟨j.val / k, (Nat.div_lt_iff_lt_mul hk).mpr j.isLt⟩)).source) :
    pathIntegralViaCoverWith ω γ n hn pickChart hcov =
      pathIntegralViaCoverWith ω γ (n * k) (Nat.mul_pos hn hk)
        (fun j => pickChart ⟨j.val / k, (Nat.div_lt_iff_lt_mul hk).mpr j.isLt⟩)
        hcov' := by
  sorry

end JacobianChallenge.Periods
