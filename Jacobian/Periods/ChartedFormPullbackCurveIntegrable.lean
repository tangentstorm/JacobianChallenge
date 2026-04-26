import Jacobian.Periods.ChartedFormPullback
import Jacobian.Periods.ChartedFormPullbackSimp
import Jacobian.Periods.ChartedFormPullbackSmul
import Jacobian.Periods.ChartedFormPullbackSub
import Mathlib.MeasureTheory.Integral.CurveIntegral.Basic

/-!
# Curve integrability of `chartedFormPullback`

Packet F target file. The full theorem (general form, general path)
is the substantive geometric step that unblocks `_add` for the path
integral. Zero-form case lands here; the full case is left as a
top-level `sorry`-stubbed declaration with the corrected hypothesis
list (per Recon update 2026-04-26).

The full case requires `ContDiffOn ℝ 1 γ.extend I` for the path
because Mathlib v4.28.0 has only `ContinuousOn.curveIntegrable_of_contDiffOn`
(no continuous-only variant). See `PathIntegralViaCoverRecon.lean`
for the design discussion.
-/

namespace JacobianChallenge.Periods

open JacobianChallenge.HolomorphicForms

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  {X : Type*} [TopologicalSpace X] [ChartedSpace E X]
  [IsManifold (modelWithCornersSelf ℂ E) (⊤ : WithTop ℕ∞) X]

/-- The chart pullback of the zero form is curve-integrable along
any path. Proved by reducing to `CurveIntegrable.zero` via the
function-equation `chartedFormPullback_zero`. -/
theorem chartedFormPullback_zero_curveIntegrable
    (c : OpenPartialHomeomorph X E) {a b : E} (γ : Path a b) :
    CurveIntegrable (chartedFormPullback c (0 : HolomorphicOneForm E X)) γ := by
  rw [chartedFormPullback_zero]
  exact CurveIntegrable.zero

/-- If the chart pullback of `ω` is curve-integrable along `γ`, then so
is the chart pullback of `-ω`. Reduces to `CurveIntegrable.neg` via
`chartedFormPullback_neg`. -/
theorem chartedFormPullback_neg_curveIntegrable
    (c : OpenPartialHomeomorph X E) {ω : HolomorphicOneForm E X}
    {a b : E} {γ : Path a b}
    (h : CurveIntegrable (chartedFormPullback c ω) γ) :
    CurveIntegrable (chartedFormPullback c (-ω)) γ := by
  rw [chartedFormPullback_neg]
  exact h.neg

/-- If the chart pullback of `ω` is curve-integrable along `γ`, then so
is the chart pullback of `k • ω`. Reduces to `CurveIntegrable.smul`
via `chartedFormPullback_smul`. -/
theorem chartedFormPullback_smul_curveIntegrable
    (c : OpenPartialHomeomorph X E) {ω : HolomorphicOneForm E X}
    {a b : E} {γ : Path a b}
    (h : CurveIntegrable (chartedFormPullback c ω) γ) (k : ℂ) :
    CurveIntegrable (chartedFormPullback c (k • ω)) γ := by
  rw [chartedFormPullback_smul]
  exact h.smul

/-- If the chart pullbacks of `ω` and `η` are both curve-integrable
along `γ`, then so is the chart pullback of `ω + η`. Reduces to
`CurveIntegrable.add` via `chartedFormPullback_add`. -/
theorem chartedFormPullback_add_curveIntegrable
    (c : OpenPartialHomeomorph X E) {ω η : HolomorphicOneForm E X}
    {a b : E} {γ : Path a b}
    (hω : CurveIntegrable (chartedFormPullback c ω) γ)
    (hη : CurveIntegrable (chartedFormPullback c η) γ) :
    CurveIntegrable (chartedFormPullback c (ω + η)) γ := by
  rw [chartedFormPullback_add]
  exact hω.add hη

/-- If the chart pullbacks of `ω` and `η` are both curve-integrable
along `γ`, then so is the chart pullback of `ω - η`. Reduces to
`CurveIntegrable.sub` via `chartedFormPullback_sub`. -/
theorem chartedFormPullback_sub_curveIntegrable
    (c : OpenPartialHomeomorph X E) {ω η : HolomorphicOneForm E X}
    {a b : E} {γ : Path a b}
    (hω : CurveIntegrable (chartedFormPullback c ω) γ)
    (hη : CurveIntegrable (chartedFormPullback c η) γ) :
    CurveIntegrable (chartedFormPullback c (ω - η)) γ := by
  rw [chartedFormPullback_sub]
  exact hω.sub hη

end JacobianChallenge.Periods
