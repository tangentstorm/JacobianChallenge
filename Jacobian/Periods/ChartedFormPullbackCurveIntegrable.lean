import Jacobian.Periods.ChartedFormPullback
import Jacobian.Periods.ChartedFormPullbackSimp
import Jacobian.Periods.ChartedFormPullbackSmul
import Jacobian.Periods.ChartedFormPullbackSub
import Mathlib.MeasureTheory.Integral.CurveIntegral.Basic
import Mathlib.Geometry.Manifold.ContMDiff.Atlas
import Mathlib.Geometry.Manifold.MFDeriv.Basic

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

The genuine content factors into two named sub-obligations:

* `chartedSection_localRepr_continuousOn` — continuity of
  `e ↦ ω.toFun (c.symm e)` viewed as `E →L[ℂ] ℂ`-valued on `c.target`.
  This is the **trivialization-extraction gap** (same flavour as
  `ContMDiffSection_localRepr_inversionChart_continuousAt_zero` in
  `Jacobian/HolomorphicForms/GenusZeroClassification.lean`).

* `mfderiv_chartSymm_continuousOn` — continuity of
  `e ↦ mfderiv 𝓘(ℂ,E) 𝓘(ℂ,E) c.symm e` on `c.target`.
  Follows from `c.symm` being `ContMDiffOn ⊤ c.target` plus the
  standard "smoothness gives `mfderiv` continuity" reduction. The
  proof can mirror Mathlib's
  `ContMDiffWithinAt.mfderivWithin_const` (which lives in
  `Mathlib/Geometry/Manifold/ContMDiffMFDeriv.lean`).

Once both sub-obligations land, `chartedFormPullback_continuousOn` is
a sorry-free assembly via the bilinear continuity of
`ContinuousLinearMap.comp`.

The recent project-local `clm_compose_of_inCoordinates` (in
`Jacobian/HolomorphicForms/CLMBundleCompose.lean`) discharges the
section-level smoothness of `pullbackFormsBundledLM`. The *same*
machinery, in `ContMDiffWithinAt` form, would discharge both
sub-obligations here and the analogous gaps in Phases 4a and 5.
-/

/-- **Continuity of the section's chart-local representative.** For a
smooth section `ω` of the cotangent bundle of `X` and a chart `c` on
`X`, the function `e ↦ ω.toFun (c.symm e)` (in the cotangent fiber,
which collapses to `E →L[ℂ] ℂ` for self-model) is continuous on
`c.target`.

This is the **trivialization-extraction gap**: from
`ContMDiffSection.continuous_totalSpaceMk` we get continuity of
`x ↦ ⟨x, ω.toFun x⟩` into the cotangent bundle's total space; the
missing step is to compose with a chart trivialisation to recover
the fiber value as a continuous `E →L[ℂ] ℂ`-valued function on
`c.source`, then precompose with `c.symm` (continuous on `c.target`).

For self-model bundles the trivialisation is structurally simple
(the chart-coordinate identification is essentially an identity in
the appropriate sense), so this gap is bookkeeping plus the
trivialisation-fiber-projection continuity.

The statement uses `(ω.toFun (c.symm e) : E →L[ℂ] ℂ)` via the
definitional equality `CotangentSpace E X x = E →L[ℂ] ℂ` (constant
fibers, self-model). The `show … from rfl` bridges the two forms. -/
theorem chartedSection_localRepr_continuousOn
    (c : OpenPartialHomeomorph X E) (ω : HolomorphicOneForm E X) :
    ContinuousOn (fun e =>
      show E →L[ℂ] ℂ from ω.toFun (c.symm e)) c.target := by
  sorry

/-- **Continuity of the chart-inverse `mfderiv`.** For `c` in the
maximal atlas of `X` and the source manifold being the model space
`E` (with self-model `𝓘(ℂ, E)`), the map
`e ↦ mfderiv 𝓘(ℂ,E) 𝓘(ℂ,E) c.symm e` is continuous on `c.target`
viewed as `E →L[ℂ] E`-valued.

## Strategy

For `e₀ ∈ c.target`, set `p₀ := c.symm e₀` and `c' := chartAt E p₀`.
The chart-change `c' ∘ c.symm` is smooth on a neighborhood of `e₀`.
The chain rule gives:
```
fderiv ℂ (c' ∘ c.symm) e = mfderiv c' (c.symm e) ∘L mfderiv c.symm e
```
The first factor is the identity at `e = e₀` (chart's mfderiv at its
base point), and operator-continuous on a neighborhood (via the
bundle trivialization continuity for finite-dim fibers). Inverting,
we extract continuity of `mfderiv c.symm`.

The full proof requires:
* `ContMDiffWithinAt.mfderivWithin_const` for smoothness in
  `inTangentCoordinates` form.
* A bridge from `inTangentCoordinates` back to `mfderiv` using the
  trivialization's invertibility on its base set.
* For finite-dim `E`, `Trivialization.continuousOn` plus joint-to-
  operator continuity of bilinear maps with compact unit ball.
* `NormedRing.inverse_continuousAt` for the inverse continuity. -/
theorem mfderiv_chartSymm_continuousOn
    [FiniteDimensional ℂ E]
    (c : OpenPartialHomeomorph X E)
    (hc : c ∈ IsManifold.maximalAtlas (modelWithCornersSelf ℂ E)
      (⊤ : WithTop ℕ∞) X) :
    ContinuousOn (fun e =>
      show E →L[ℂ] E from
        mfderiv (modelWithCornersSelf ℂ E) (modelWithCornersSelf ℂ E)
          c.symm e) c.target := by
  -- Smoothness of c.symm via maximalAtlas membership.
  have hsmoothOn : ContMDiffOn (modelWithCornersSelf ℂ E)
      (modelWithCornersSelf ℂ E) (⊤ : WithTop ℕ∞) c.symm c.target :=
    contMDiffOn_symm_of_mem_maximalAtlas hc
  -- Convert to mfderivWithin (they agree on the open set c.target).
  refine ContinuousOn.congr (f := fun e =>
      show E →L[ℂ] E from
        mfderivWithin (modelWithCornersSelf ℂ E)
          (modelWithCornersSelf ℂ E) c.symm c.target e) ?_ ?_
  · -- Continuity of mfderivWithin via tangent map continuity.
    -- The bundle smoothness gives joint continuity of (e, v) ↦
    -- mfderivWithin e v in the trivialization-coordinates.
    -- Combined with finite-dim and the chain rule via a fixed chart
    -- chartAt E (c.symm e₀), we extract operator continuity.
    -- The detailed proof is technical; the essential infrastructure
    -- is `ContMDiffWithinAt.mfderivWithin_const` (smoothness of
    -- inCoordinates form) plus the bridge via chart-change derivatives
    -- (`inTangentCoordinates_eq_mfderiv_comp`) plus FiniteDim joint-
    -- to-operator continuity. For completeness here we use the
    -- alternative route via `ContDiffOn.continuousOn_fderivWithin`
    -- applied to the chart-change.
    sorry
  · intro e he
    exact (mfderivWithin_of_isOpen c.open_target he).symm

/-- **Continuity of the chart pullback.** Sorry-free assembly of
`chartedSection_localRepr_continuousOn` and
`mfderiv_chartSymm_continuousOn` via the (jointly) continuous
bilinear `ContinuousLinearMap.comp`. -/
theorem chartedFormPullback_continuousOn
    [FiniteDimensional ℂ E]
    (c : OpenPartialHomeomorph X E)
    (hc : c ∈ IsManifold.maximalAtlas (modelWithCornersSelf ℂ E)
      (⊤ : WithTop ℕ∞) X)
    (ω : HolomorphicOneForm E X) :
    ContinuousOn (chartedFormPullback c ω) c.target := by
  -- Unfold definitionally: chartedFormPullback c ω e =
  --   (ω.toFun (c.symm e)).comp (mfderiv c.symm e).
  -- Apply the continuous bilinear `compL` operator to the two
  -- continuous component functions.
  have hcomp : Continuous fun p : (E →L[ℂ] ℂ) × (E →L[ℂ] E) => p.1.comp p.2 :=
    isBoundedBilinearMap_comp.continuous
  exact hcomp.comp_continuousOn
    ((chartedSection_localRepr_continuousOn c ω).prodMk
      (mfderiv_chartSymm_continuousOn c hc))

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
    [FiniteDimensional ℂ E]
    (c : OpenPartialHomeomorph X E)
    (hc : c ∈ IsManifold.maximalAtlas (modelWithCornersSelf ℂ E)
      (⊤ : WithTop ℕ∞) X)
    (ω : HolomorphicOneForm E X)
    {a b : E} (γ : Path a b)
    (hγ : ContDiffOn ℝ 1 γ.extend (Set.Icc 0 1))
    (hrange : ∀ t, γ t ∈ c.target) :
    CurveIntegrable (chartedFormPullback c ω) γ :=
  (chartedFormPullback_continuousOn c hc ω).curveIntegrable_of_contDiffOn hγ hrange

end JacobianChallenge.Periods
