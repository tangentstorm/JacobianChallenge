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

The existence is the **single named bookkeeping gap** for Phase 6
and Sorry 1. -/

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
  sorry

end JacobianChallenge.Periods
