import Jacobian.Periods.PathContDiffObligation
import Jacobian.Periods.PathIntegralViaCoverPick
import Jacobian.Periods.PathIntegralViaCoverPickRefl
import Jacobian.Periods.PathIntegralViaCoverWithRefinementInvariant
import Jacobian.Periods.PathIntegralViaCoverWithTrans
import Jacobian.TraceDegree.PiecewiseC1Def
import Jacobian.TraceDegree.PiecewiseC1Instance
import Jacobian.Periods.PiecewiseC1Path

/-!
# Unparameterised path-additivity for `pathIntegralViaCover`

Relocated from `Jacobian/Periods/PullbackNaturality.lean` so it sits
upstream of `Jacobian/HolomorphicForms/DeRhamComparisonMap.lean` in the
import DAG and can be used to discharge `ClosedForm.lineIntegral_trans`
there. The body is unchanged from the original `PullbackNaturality.lean`
definition; only the file layout moves.
-/

namespace JacobianChallenge.Periods

set_option linter.unusedSectionVars false

open scoped Manifold ContDiff
open JacobianChallenge.HolomorphicForms
open JacobianChallenge.TraceDegree

variable {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
  [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X]
  [StableChartAt ℂ X]
  [PiecewiseC1PathRegularity X]

-- `path_contDiffOn_obligation` is now defined once in
-- `Jacobian.Periods.PathContDiffObligation` and reused here and in
-- `PathIntegralViaCoverPickSymm.lean`. Call sites in this file
-- reference the shared definition directly via the open namespace.

/-- **Path-additivity (with explicit per-path witnesses).** Takes
`IsChartContDiffPath` hypotheses for `γ`, `γ'`, and `γ.trans γ'`
explicitly, instead of relying on the universally-quantified
`path_contDiffOn_obligation` typeclass route. Sorry-free under
`[StableChartAt ℂ X]` alone (no `[PiecewiseC1PathRegularity X]`
needed), with per-path regularity supplied by the caller.

Stage III variant eliminating `path_contDiffOn_obligation` (and
transitively `cyclePathRegularity_obligation`) from the flagship
descent. -/
theorem pathIntegralViaCover_trans_eq_add_of_witnesses
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X]
    [StableChartAt ℂ X]
    (η : HolomorphicOneForm ℂ X) {a b c : X}
    (γ : Path a b) (γ' : Path b c)
    (hγ : IsChartContDiffPath γ) (hγ' : IsChartContDiffPath γ')
    (hγγ' : IsChartContDiffPath (γ.trans γ')) :
    pathIntegralViaCover η (γ.trans γ') =
      pathIntegralViaCover η γ + pathIntegralViaCover η γ' := by
  obtain ⟨n, hn, pickA, pickB, hcovA, hcovB, hcovT⟩ :=
    exists_aligned_partition_for_trans (E := ℂ) X γ γ'
  have hT : pathIntegralViaCover η (γ.trans γ') =
      pathIntegralViaCoverWith η (γ.trans γ') (2 * n)
        (Nat.mul_pos (by omega) hn)
        (alignedPickT n pickA pickB) hcovT := by
    unfold pathIntegralViaCover
    exact pathIntegralViaCoverWith_refinement_invariant'
      η (γ.trans γ') hγγ' _ _ _ _
      (2 * n) (Nat.mul_pos (by omega) hn)
      (alignedPickT n pickA pickB) hcovT
  have hA : pathIntegralViaCover η γ =
      pathIntegralViaCoverWith η γ n hn pickA hcovA := by
    unfold pathIntegralViaCover
    exact pathIntegralViaCoverWith_refinement_invariant'
      η γ hγ _ _ _ _ n hn pickA hcovA
  have hB : pathIntegralViaCover η γ' =
      pathIntegralViaCoverWith η γ' n hn pickB hcovB := by
    unfold pathIntegralViaCover
    exact pathIntegralViaCoverWith_refinement_invariant'
      η γ' hγ' _ _ _ _ n hn pickB hcovB
  rw [hT, hA, hB]
  exact pathIntegralViaCoverWith_aligned_trans
    η γ γ' n hn pickA pickB hcovA hcovB hcovT

/-- **Path-additivity at cover level.** For any holomorphic form `ω`
on `X` and concatenable paths `γ : Path a b`, `γ' : Path b c`,
`pathIntegralViaCover ω (γ.trans γ') =
  pathIntegralViaCover ω γ + pathIntegralViaCover ω γ'`. Delegates to
the witness form by supplying the universally-quantified
`path_contDiffOn_obligation` as the three per-path witnesses. -/
theorem pathIntegralViaCover_trans_eq_add
    (η : HolomorphicOneForm ℂ X) {a b c : X}
    (γ : Path a b) (γ' : Path b c) :
    pathIntegralViaCover η (γ.trans γ') =
      pathIntegralViaCover η γ + pathIntegralViaCover η γ' :=
  pathIntegralViaCover_trans_eq_add_of_witnesses η γ γ'
    (fun p => path_contDiffOn_obligation X γ p)
    (fun p => path_contDiffOn_obligation X γ' p)
    (fun p => path_contDiffOn_obligation X (γ.trans γ') p)

end JacobianChallenge.Periods
