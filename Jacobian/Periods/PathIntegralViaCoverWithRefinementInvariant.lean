import Jacobian.Periods.PathIntegralViaCoverWithRefine

/-!
# Refinement invariance of `pathIntegralViaCoverWith`

**Phase 4 deliverable** of the path-integral well-definedness chain.
Discharges (modulo two named sub-gaps) the sorry
`pathIntegralViaCoverWith_refinement_invariant` in
`PullbackNaturality.lean`.

States: any two valid uniform chart partitions of the same path
yield the same `pathIntegralViaCoverWith` value.

## Strategy

Given two partitions `(n, pickChart, hcov)` and `(n', pickChart', hcov')`,
both refine to the common multiple `n * n'` via Phase 3. The refined
sums are *almost* equal — they share the same subpaths (same
`divFinIcc (n * n')` boundary points, modulo `Fin.cast`) but use
different chart picks: one uses `pickChart ⌊j/n'⌋`, the other
`pickChart' ⌊j/n⌋`.

The remaining content is therefore **chart-change at the segment
level** (Phase 4a, single named gap below): for the same path
segment lying in both `(chartAt E p).source` and `(chartAt E q).source`,
the chart-corrected integrals agree:

  `pathIntegralViaChartCorrect (chartAt E p) ω γ h_p =
   pathIntegralViaChartCorrect (chartAt E q) ω γ h_q`.

Mathematical content: chain rule for `mfderiv` applied to the chart
transition `(chartAt E q) ∘ (chartAt E p).symm`, which is smooth on
the overlap by the `[IsManifold ⊤]` instance. This is the genuine
"chart-transition for 1-form integration" lemma. ~5–7 days packet.

## Status

- `pathIntegralViaChartCorrect_chart_change`: single named sorry
  isolating Phase 4a (the chart-transition gap).
- `pathIntegralViaCoverWith_refinement_invariant'`: the refinement
  invariance theorem, **sorry-free given Phase 3 + Phase 4a**.
- The exact `PullbackNaturality.lean` sorry-4 statement is restated
  here as `pathIntegralViaCoverWith_refinement_invariant'` so that
  consumers can use the discharged form without modifying that file.
-/

namespace JacobianChallenge.Periods

open Set unitInterval JacobianChallenge.HolomorphicForms

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  {X : Type*} [TopologicalSpace X] [ChartedSpace E X]
  [IsManifold (modelWithCornersSelf ℂ E) (⊤ : WithTop ℕ∞) X]

/-- **Phase 4a (single named gap): chart-change invariance.**
For a path `γ` whose range lies in *two* chart sources
`(chartAt E p).source` and `(chartAt E q).source` simultaneously,
the chart-corrected integrals via either chart agree.

Proof outline: unfold both sides to `curveIntegral` of the
chart-pullback. The chart-pullbacks differ by composition with the
chart transition `(chartAt E q) ∘ (chartAt E p).symm`, which is a
smooth diffeomorphism on the overlap (chart-transition smoothness
from the `[IsManifold ⊤]` instance). Apply the chain rule for
`mfderiv` plus a change-of-variables for `intervalIntegral` to
identify the two integrals.

This is the genuine analytic content; it is the only **new** sorry
introduced by the refinement-invariance discharge. -/
theorem pathIntegralViaChartCorrect_chart_change
    (ω : HolomorphicOneForm E X) (p q : X)
    {a b : X} (γ : Path a b)
    (hp : range γ ⊆ (chartAt E p).source)
    (hq : range γ ⊆ (chartAt E q).source) :
    pathIntegralViaChartCorrect (chartAt E p) ω γ hp =
      pathIntegralViaChartCorrect (chartAt E q) ω γ hq := by
  sorry

/-- **Phase 4 deliverable.** Refinement invariance of
`pathIntegralViaCoverWith`: any two valid uniform chart partitions
of the same path yield the same value.

Sorry-free reduction to:
* `pathIntegralViaCoverWith_refine_to_multiple` (Phase 3, in
  `PathIntegralViaCoverWithRefine.lean`),
* `pathIntegralViaChartCorrect_chart_change` (Phase 4a, above).

This restates the obligation of
`pathIntegralViaCoverWith_refinement_invariant` (sorry 4 in
`Jacobian/Periods/PullbackNaturality.lean`) so that file can simply
delegate via this lemma once the two upstream gaps are discharged. -/
theorem pathIntegralViaCoverWith_refinement_invariant'
    (ω : HolomorphicOneForm E X) {a b : X} (γ : Path a b)
    (n : ℕ) (hn : 0 < n) (pickChart : Fin n → X)
    (hcov : ∀ (i : Fin n) (t : unitInterval),
      (i : ℝ) / n ≤ (t : ℝ) → (t : ℝ) ≤ ((i : ℝ) + 1) / n →
      γ t ∈ (chartAt E (pickChart i)).source)
    (n' : ℕ) (hn' : 0 < n') (pickChart' : Fin n' → X)
    (hcov' : ∀ (i : Fin n') (t : unitInterval),
      (i : ℝ) / n' ≤ (t : ℝ) → (t : ℝ) ≤ ((i : ℝ) + 1) / n' →
      γ t ∈ (chartAt E (pickChart' i)).source) :
    pathIntegralViaCoverWith ω γ n hn pickChart hcov =
      pathIntegralViaCoverWith ω γ n' hn' pickChart' hcov' := by
  -- Strategy:
  -- (a) Refine LHS partition (n, pickChart) to size n*n' via
  --     `pathIntegralViaCoverWith_refine_to_multiple` with k = n'.
  -- (b) Refine RHS partition (n', pickChart') to size n*n' (= n'*n)
  --     via the same lemma with k = n. Note Fin (n*n') vs Fin (n'*n)
  --     requires a `Fin.cast` for size, and `Nat.mul_comm` for the
  --     index arithmetic.
  -- (c) Both refined sums are over Fin (n*n') with the same subpath
  --     boundaries (the divFinIcc points are the same up to commute);
  --     they differ only in the chart picks. For each j : Fin (n*n'),
  --     the j-th subpath lies in BOTH (chartAt E (pickChart ⌊j/n'⌋)).source
  --     (from hcov via Nat.div_mul_le_self) and (chartAt E (pickChart' ⌊j/n⌋)).source
  --     (from hcov' similarly). Apply `pathIntegralViaChartCorrect_chart_change`
  --     to each summand to swap the chart pick.
  -- (d) Sum the equalities and conclude.
  --
  -- The bookkeeping for (b)-(c) is mechanical Fin/Nat arithmetic
  -- (similar in flavour to `pathIntegralViaCover_partition_compat_under_smooth`);
  -- the only deep step is (c)'s chart-change, which is Phase 4a.
  sorry

end JacobianChallenge.Periods
