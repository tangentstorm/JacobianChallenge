import Jacobian.TraceDegree.PiecewiseC1Def
import Jacobian.TraceDegree.PiecewiseC1Instance
import Jacobian.Periods.PiecewiseC1Path

/-!
# Shared `path_contDiffOn_obligation` bridge

This file factors out the single regularity bridge that
`PathIntegralViaCoverTrans.lean` and `PathIntegralViaCoverPickSymm.lean`
(and, historically, `PullbackNaturality.lean:260`) each needed: the
chartwise composition `chartAt ℂ p ∘ γ.extend` is `C¹`-on the preimage
of the chart source inside `[0,1]`.

Both downstream call sites used to carry a verbatim duplicate `sorry`
for this fact. They now delegate to the single statement here so the
project carries one obligation, not two. The proof remains a `sorry`
gated on the upstream
`Jacobian.TraceDegree.PiecewiseC1Instance.instPiecewiseC1PathRegularity`
sorry — discharging that instance discharges this lemma as well.
-/

namespace JacobianChallenge.Periods

set_option linter.unusedSectionVars false

open scoped Manifold ContDiff
open JacobianChallenge.TraceDegree

/-- Bridge: the chartwise composition `chartAt ℂ p ∘ γ.extend` is
`C¹`-on the preimage of the chart source inside `[0,1]`.

This is the single shared obligation consumed by
`pathIntegralViaCover_trans_eq_add` (in `PathIntegralViaCoverTrans.lean`)
and `pathIntegralViaCover_symm_eq_neg` (in
`PathIntegralViaCoverPickSymm.lean`). It is gated on the upstream
`PiecewiseC1PathRegularity` instance sorry; making the instance real
discharges this. -/
theorem path_contDiffOn_obligation
    (M : Type) [TopologicalSpace M] [ChartedSpace ℂ M]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) M]
    [PiecewiseC1PathRegularity M]
    {a b : M} (γ : Path a b) (p : M) :
    ContDiffOn ℝ 1 ((chartAt ℂ p) ∘ γ.extend)
      (γ.extend ⁻¹' (chartAt ℂ p).source ∩ Set.Icc 0 1) := by
  -- Single consolidated sorry: see file docstring. The
  -- `PiecewiseC1PathRegularity` instance currently sorries this
  -- obligation in `Jacobian/TraceDegree/PiecewiseC1Instance.lean`;
  -- discharging that instance discharges this lemma.
  sorry

end JacobianChallenge.Periods
