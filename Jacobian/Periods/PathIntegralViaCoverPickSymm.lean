import Jacobian.Periods.PathContDiffObligation
import Jacobian.Periods.PathIntegralViaCoverPick
import Jacobian.Periods.PathIntegralViaCoverSymm
import Jacobian.Periods.PathIntegralViaCoverWithRefinementInvariant
import Jacobian.Periods.PathPartitionCoverSymm
import Jacobian.TraceDegree.PiecewiseC1Def
import Jacobian.TraceDegree.PiecewiseC1Instance
import Jacobian.Periods.PiecewiseC1Path

/-!
# Unparameterised path-reversal sign for `pathIntegralViaCover`

`pathIntegralViaCover η γ.symm = - pathIntegralViaCover η γ`.

Strategy: extract a chart-cover partition for `γ` via
`exists_uniform_chart_partition`; reverse it via `Fin.rev` and
`cover_symm_of_cover` to get one for `γ.symm`; use
`pathIntegralViaCoverWith_refinement_invariant'` to bridge each
unparameterised `pathIntegralViaCover` to the parameterised
`pathIntegralViaCoverWith` on these partitions; apply the already-proved
parameterised `pathIntegralViaCoverWith_symm`.
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
-- `PathIntegralViaCoverTrans.lean`. The private duplicate that used to
-- live here has been removed; call sites below reference the shared
-- definition directly via the open namespace.

/-- **Path-reversal sign (with explicit per-path witnesses).** Takes
`IsChartContDiffPath` hypotheses for `γ` and `γ.symm` explicitly.
Sorry-free under `[StableChartAt ℂ X]` alone (no
`[PiecewiseC1PathRegularity X]` needed).

Stage III variant eliminating the universal `path_contDiffOn_obligation`
from the flagship descent. -/
theorem pathIntegralViaCover_symm_eq_neg_of_witnesses
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X]
    [StableChartAt ℂ X]
    (η : HolomorphicOneForm ℂ X) {a b : X} (γ : Path a b)
    (hγ : IsChartContDiffPath γ)
    (hγsymm : IsChartContDiffPath γ.symm) :
    pathIntegralViaCover η γ.symm = - pathIntegralViaCover η γ := by
  obtain ⟨n, hn, pickChart, hcov⟩ :=
    exists_uniform_chart_partition ℂ γ.toContinuousMap
  set pickRev : Fin n → X := pickChart ∘ Fin.rev
  have hcovRev : ∀ (i : Fin n) (t : unitInterval),
      (i : ℝ) / n ≤ (t : ℝ) → (t : ℝ) ≤ ((i : ℝ) + 1) / n →
      γ.symm t ∈ (chartAt ℂ (pickRev i)).source :=
    cover_symm_of_cover γ n hn pickChart hcov
  have hγ_eq : pathIntegralViaCover η γ =
      pathIntegralViaCoverWith η γ n hn pickChart hcov := by
    unfold pathIntegralViaCover
    exact pathIntegralViaCoverWith_refinement_invariant'
      η γ hγ _ _ _ _ n hn pickChart hcov
  have hγsymm_eq : pathIntegralViaCover η γ.symm =
      pathIntegralViaCoverWith η γ.symm n hn pickRev hcovRev := by
    unfold pathIntegralViaCover
    exact pathIntegralViaCoverWith_refinement_invariant'
      η γ.symm hγsymm _ _ _ _ n hn pickRev hcovRev
  rw [hγsymm_eq, hγ_eq, pathIntegralViaCoverWith_symm η γ n hn pickChart hcov]

/-- **Path-reversal sign at cover level.** The unparameterised path
integral negates with the path: `pathIntegralViaCover η γ.symm =
- pathIntegralViaCover η γ`. Delegates to the witness form by
supplying the universally-quantified `path_contDiffOn_obligation` as
the per-path witnesses. -/
theorem pathIntegralViaCover_symm_eq_neg
    (η : HolomorphicOneForm ℂ X) {a b : X} (γ : Path a b) :
    pathIntegralViaCover η γ.symm = - pathIntegralViaCover η γ :=
  pathIntegralViaCover_symm_eq_neg_of_witnesses η γ
    (fun p => path_contDiffOn_obligation X γ p)
    (fun p => path_contDiffOn_obligation X γ.symm p)

end JacobianChallenge.Periods
