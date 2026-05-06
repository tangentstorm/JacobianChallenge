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

/-! ### Phase 1 main theorem: general curve-integrability

This isolates the genuine analytic content (continuity of the chart
pullback as an `E → E →L[ℂ] ℂ`-valued function) into a single named
lemma `chartedFormPullback_continuousOn`. The curve-integrability
result then follows sorry-free via Mathlib's
`ContinuousOn.curveIntegrable_of_contDiffOn`.

The continuity gap is the same trivialization-extraction issue
flagged in `Jacobian/HolomorphicForms/GenusZeroClassification.lean`
for the inversion-chart coefficient (see
`ContMDiffSection_localRepr_inversionChart_continuousAt_zero`). It
reduces to:

1. Continuity of `e ↦ ω.toFun (c.symm e)` viewed as `E →L[ℂ] ℂ`-valued
   on `c.target`. This requires extracting the section `ω` of the
   cotangent bundle through a fiber-bundle trivialization at each
   point of `c.symm '' c.target`. With the project's
   `ContMDiffSection.continuous_totalSpaceMk` and a global
   trivialization of the cotangent bundle on a self-modeled chart, this
   is structurally available; the missing piece is the
   `ContMDiffSection.continuousOn_localRepr` API.
2. Continuity of `e ↦ mfderiv 𝓘(ℂ,E) 𝓘(ℂ,E) c.symm e` on `c.target`.
   Follows from `c.symm` being `ContMDiff ⊤` on `c.target` (chart of
   a smooth manifold) and the standard fact that the `mfderiv` of a
   `C¹⁺` function is continuous.
3. Bilinear continuity of `ContinuousLinearMap.comp` to combine (1)
   and (2).

This `_continuousOn` gap is the one packet-sized, well-localised
remainder for Phase 1.
-/

/-- **Continuity of the chart pullback.** The function
`chartedFormPullback c ω : E → E →L[ℂ] ℂ` is continuous on the
chart's target.

Currently a `sorry`-stubbed declaration. The proof requires the chart
trivialization of the cotangent bundle (see the file-level docstring
above for the reduction). This is the genuine analytic gap that
unblocks Phase 1's `_curveIntegrable` and, via that, the segment-
additivity chain (Phases 2–4 in the supporting infrastructure plan
on branch `claude/prove-pullback-naturality-PedxJ`). -/
theorem chartedFormPullback_continuousOn
    (c : OpenPartialHomeomorph X E) (ω : HolomorphicOneForm E X) :
    ContinuousOn (chartedFormPullback c ω) c.target := by
  sorry

/-- **Phase 1 deliverable.** For a `C¹` path `γ : Path a b` whose range
lies in `c.target`, the chart pullback `chartedFormPullback c ω` is
curve-integrable along `γ`.

Sorry-free reduction to `chartedFormPullback_continuousOn` via
Mathlib's `ContinuousOn.curveIntegrable_of_contDiffOn`. The
hypothesis `ContDiffOn ℝ 1 γ.extend (Set.Icc 0 1)` matches Mathlib's
form (path-integral expects `Set.Icc 0 1`, the unit interval extended
to ℝ).

This unblocks `pathIntegralViaChartCorrect_add` (gated on Packet F
in `PathIntegralViaCoverRecon.lean`) and downstream segment-
additivity / refinement lemmas. -/
theorem chartedFormPullback_curveIntegrable
    (c : OpenPartialHomeomorph X E) (ω : HolomorphicOneForm E X)
    {a b : E} (γ : Path a b)
    (hγ : ContDiffOn ℝ 1 γ.extend (Set.Icc 0 1))
    (hrange : ∀ t, γ t ∈ c.target) :
    CurveIntegrable (chartedFormPullback c ω) γ :=
  (chartedFormPullback_continuousOn c ω).curveIntegrable_of_contDiffOn hγ hrange

end JacobianChallenge.Periods
