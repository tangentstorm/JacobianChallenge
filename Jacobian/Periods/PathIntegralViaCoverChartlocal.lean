import Jacobian.Periods.PathIntegralViaCoverPick
import Jacobian.Periods.PathIntegralViaCoverPickRefl
import Jacobian.Periods.PathIntegralViaCoverTrans
import Jacobian.Periods.PathIntegralViaCoverWithRefinementInvariant
import Jacobian.Periods.ChartedFormPullback
import Jacobian.Periods.HolomorphicOneFormToFunContinuous
import Jacobian.TraceDegree.PiecewiseC1Def
import Jacobian.TraceDegree.PiecewiseC1Instance
import Mathlib.Analysis.Calculus.FDeriv.Basic
import Mathlib.Analysis.Complex.HasPrimitives
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-!
# Chart-local path-integral identity

Bridge between the repo's `pathIntegralViaCover` and Mathlib's
`intervalIntegral` on a single chart segment. This is the analytic
core of the chartwise FTC argument used to discharge
`pathPotentialAsForm_exteriorDerivative` in
`Jacobian/HolomorphicForms/DeRhamComparisonMap.lean`.

Provides:
* `exists_ballShaped_chartAt` — every point has a chart neighborhood
  whose image is a Mathlib `Metric.ball` (sorry-free; ~20 LOC of
  chart bookkeeping).
* `chartPullbackFun` — scalar chart-pullback of a holomorphic 1-form on
  a Riemann surface: evaluate the genuine chart pullback at the
  standard tangent vector `1 ∈ ℂ`, producing a function `ℂ → ℂ` that
  Mathlib's `DifferentiableOn.isExactOn_ball` can primitive.
* `chartPullbackFun_differentiableOn` — focused frontier sorry: the
  chart pullback of a holomorphic 1-form is holomorphic on the chart's
  target.
* `pathIntegralViaCover_eq_primitive_diff` — focused frontier sorry
  on the chart-local Euclidean FTC, now with the correct primitive
  hypothesis (`HasDerivAt F (chartPullbackFun c α z) z`).
-/

namespace JacobianChallenge.Periods

set_option linter.unusedSectionVars false

open JacobianChallenge.HolomorphicForms Set
open scoped Manifold

variable {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
  [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X]

/-- **Chart shrinking to a ball.** Every point `p : X` admits a
radius `r > 0` such that the ball of radius `r` around the chart
basepoint `chartAt ℂ p p` is contained in `(chartAt ℂ p).target`. -/
theorem exists_ballShaped_chartAt (p : X) :
    ∃ r > (0 : ℝ),
      Metric.ball ((chartAt ℂ p) p) r ⊆ (chartAt ℂ p).target := by
  -- The chart's target is open, and `chartAt ℂ p p` lies in it, so
  -- there is a small ball around the basepoint contained in the
  -- target.
  set z₀ := (chartAt ℂ p) p
  have hz₀ : z₀ ∈ (chartAt ℂ p).target := mem_chart_target ℂ p
  exact Metric.isOpen_iff.mp (chartAt ℂ p).open_target z₀ hz₀

/-- **Scalar chart-pullback of a holomorphic 1-form on a Riemann
surface.** Evaluates the genuine chart pullback `chartedFormPullback`
(which produces a CLM `ℂ →L[ℂ] ℂ` at each chart-target point) at the
standard tangent vector `1 : ℂ`, yielding a scalar function
`ℂ → ℂ` whose Euclidean primitive can be extracted via Mathlib's
`DifferentiableOn.isExactOn_ball`. -/
noncomputable def chartPullbackFun
    (c : OpenPartialHomeomorph X ℂ) (ω : HolomorphicOneForm ℂ X) :
    ℂ → ℂ :=
  fun z => chartedFormPullback c ω z (1 : ℂ)

/-- Unfolding `chartPullbackFun`. -/
theorem chartPullbackFun_apply
    (c : OpenPartialHomeomorph X ℂ) (ω : HolomorphicOneForm ℂ X) (z : ℂ) :
    chartPullbackFun c ω z = chartedFormPullback c ω z (1 : ℂ) := rfl

/-- **Helper.** Evaluating `chartedFormPullback c α z` at an arbitrary
`L : ℂ` reduces to `L • chartPullbackFun c α z`, because the value
`chartedFormPullback c α z : ℂ →L[ℂ] ℂ` is itself ℂ-linear and any
`L : ℂ` equals `L • 1`. This is the cleanest algebraic bridge from
the bundled CLM-form to the scalar-multiplication-by-derivative form
used in the FTC integrand. -/
theorem chartedFormPullback_apply_eq_chartPullbackFun_smul
    (c : OpenPartialHomeomorph X ℂ) (α : HolomorphicOneForm ℂ X) (z L : ℂ) :
    chartedFormPullback c α z L = L • chartPullbackFun c α z := by
  -- `L = L • 1` as a ℂ-scalar action on ℂ.
  have hL : L = L • (1 : ℂ) := by
    rw [smul_eq_mul, mul_one]
  -- Use the CLM's `map_smul` to push the scalar out.
  conv_lhs => rw [hL]
  rw [(chartedFormPullback c α z).map_smul L (1 : ℂ)]
  rfl

/-- **Mfderiv of `(chartAt ℂ p₀).symm` is identity under `StableChartAt`.**
Symm counterpart of `mfderiv_chartAt_eq_id_of_stable`. Routes through:
* MDifferentiable: `chartAt ℂ p₀` is in the atlas, hence MDifferentiable
  (uses `IsManifold (n=1)` derived from the project's `n=⊤` instance via
  `IsManifold.of_le`).
* `comp_symm_deriv`: `(mfderiv chart) ∘ (mfderiv chart.symm) = id` on the
  chart's target.
* `mfderiv_chartAt_eq_id_of_stable`: under `StableChartAt`, the chart's
  mfderiv at any chart-source point IS the identity.
* Substitution + `id.comp f = f` gives `mfderiv chart.symm z = id`. -/
theorem mfderiv_chartAt_symm_eq_id_of_stable
    [StableChartAt ℂ X] (p₀ : X) {z : ℂ}
    (hz : z ∈ (chartAt ℂ p₀).target) :
    mfderiv (modelWithCornersSelf ℂ ℂ) (modelWithCornersSelf ℂ ℂ)
      (chartAt ℂ p₀).symm z = ContinuousLinearMap.id ℂ ℂ := by
  haveI : IsManifold (modelWithCornersSelf ℂ ℂ) (1 : WithTop ℕ∞) X :=
    IsManifold.of_le le_top
  -- chartAt ℂ p₀ is MDifferentiable, as it lies in the atlas.
  have h_chart_mdiff :
      (chartAt ℂ p₀).MDifferentiable
        (modelWithCornersSelf ℂ ℂ) (modelWithCornersSelf ℂ ℂ) :=
    mdifferentiable_of_mem_atlas (chart_mem_atlas ℂ p₀)
  -- comp_symm_deriv: (mfderiv chart at chart.symm z).comp (mfderiv chart.symm z) = id.
  have h_comp := h_chart_mdiff.comp_symm_deriv hz
  -- Under StableChartAt, mfderiv chart at chart.symm z = id.
  have h_chart_eq_id :
      mfderiv (modelWithCornersSelf ℂ ℂ) (modelWithCornersSelf ℂ ℂ)
        (chartAt ℂ p₀) ((chartAt ℂ p₀).symm z) = ContinuousLinearMap.id ℂ ℂ :=
    mfderiv_chartAt_eq_id_of_stable (I := modelWithCornersSelf ℂ ℂ) p₀
      ((chartAt ℂ p₀).map_target hz)
  rw [h_chart_eq_id] at h_comp
  -- `h_comp : (id ℂ ℂ).comp (mfderiv chart.symm z) = id ℂ (TangentSpace 𝓘 z)`.
  -- TangentSpace 𝓘(ℂ,ℂ) z reduces to ℂ.
  -- Reduce via ContinuousLinearMap.ext + apply to v.
  refine ContinuousLinearMap.ext fun v => ?_
  have hv := congrArg (fun (L : ℂ →L[ℂ] ℂ) => L v) h_comp
  simpa using hv

/-- **Definitional unfold** of `chartedFormPullback (chartAt ℂ p₀) ω`
under `StableChartAt`: the mfderiv factor collapses to identity by
`mfderiv_chartAt_symm_eq_id_of_stable`, so the chart pullback at `z`
equals `ω.toFun ((chartAt ℂ p₀).symm z)` (as a CLM `ℂ →L[ℂ] ℂ`).

This is the key simp lemma that turns "smoothness of chart pullback"
into "smoothness of ω.toFun precomposed with chart.symm", which is the
standard smooth-section-pulled-back-by-a-smooth-map shape. -/
theorem chartedFormPullback_chartAt_eq_of_stable
    [StableChartAt ℂ X] (p₀ : X) (ω : HolomorphicOneForm ℂ X)
    {z : ℂ} (hz : z ∈ (chartAt ℂ p₀).target) :
    chartedFormPullback (chartAt ℂ p₀) ω z = ω.toFun ((chartAt ℂ p₀).symm z) := by
  show (ω.toFun ((chartAt ℂ p₀).symm z)).comp _ = ω.toFun ((chartAt ℂ p₀).symm z)
  rw [mfderiv_chartAt_symm_eq_id_of_stable p₀ hz]
  exact ContinuousLinearMap.comp_id _

/-- **Smoothness of the chart pullback for `chartAt`.** Under
`[StableChartAt ℂ X]`, the chart pullback `chartedFormPullback
(chartAt ℂ p₀) ω` is `C^⊤` on `(chartAt ℂ p₀).target`. Routes through:

1. `chartedFormPullback_chartAt_eq_of_stable`: on `chart.target`, the
   chart pullback reduces to `ω.toFun (chart.symm z)`.
2. `holomorphicOneForm_toFun_contMDiff`: `ω.toFun` (as `cotangent_value
   ω`) is `C^⊤` globally.
3. `contMDiffOn_chart_symm`: chart inverse is `C^⊤` on chart.target.
4. Compose + `ContMDiffOn.congr` to transfer smoothness across the
   chart-pullback identity. -/
theorem chartedFormPullback_chartAt_contMDiffOn
    [StableChartAt ℂ X] (p₀ : X) (ω : HolomorphicOneForm ℂ X) :
    ContMDiffOn (modelWithCornersSelf ℂ ℂ) 𝓘(ℂ, ℂ →L[ℂ] ℂ)
      (⊤ : WithTop ℕ∞) (chartedFormPullback (chartAt ℂ p₀) ω)
      (chartAt ℂ p₀).target := by
  -- Step 1: smoothness of `cotangent_value ω : X → (ℂ →L[ℂ] ℂ)` globally.
  have h_omega_smooth :
      ContMDiff (modelWithCornersSelf ℂ ℂ) 𝓘(ℂ, ℂ →L[ℂ] ℂ) ⊤
        (cotangent_value (X := X) (E := ℂ) ω) :=
    holomorphicOneForm_toFun_contMDiff ω
  -- Step 2: smoothness of chart inverse on chart.target.
  have h_symm_smooth :
      ContMDiffOn (modelWithCornersSelf ℂ ℂ) (modelWithCornersSelf ℂ ℂ)
        (⊤ : WithTop ℕ∞) (chartAt ℂ p₀).symm (chartAt ℂ p₀).target :=
    contMDiffOn_chart_symm (n := (⊤ : WithTop ℕ∞))
      (I := modelWithCornersSelf ℂ ℂ) (M := X) (x := p₀)
  -- Step 3: compose to get smoothness of (cotangent_value ω ∘ chart.symm).
  have h_comp :
      ContMDiffOn (modelWithCornersSelf ℂ ℂ) 𝓘(ℂ, ℂ →L[ℂ] ℂ) ⊤
        ((cotangent_value (X := X) (E := ℂ) ω) ∘ (chartAt ℂ p₀).symm)
        (chartAt ℂ p₀).target :=
    h_omega_smooth.comp_contMDiffOn h_symm_smooth
  -- Step 4: transfer smoothness via the chart-pullback identity.
  apply h_comp.congr
  intro z hz
  -- Goal: chartedFormPullback (chartAt ℂ p₀) ω z = (cotangent_value ω ∘ chart.symm) z.
  -- RHS unfolds to `cotangent_value ω (chart.symm z) = ω.toFun (chart.symm z)`.
  exact chartedFormPullback_chartAt_eq_of_stable p₀ ω hz

/-- **Frontier sub-obligation (chart-pullback smoothness, general `c`).**
For an arbitrary `OpenPartialHomeomorph c : X ↔ ℂ`, the chart pullback
need not be smooth (it requires `c` to be in the atlas). For the chart
case, see `chartedFormPullback_chartAt_contMDiffOn`. -/
theorem chartedFormPullback_contMDiffOn
    (c : OpenPartialHomeomorph X ℂ) (ω : HolomorphicOneForm ℂ X) :
    ContMDiffOn (modelWithCornersSelf ℂ ℂ) 𝓘(ℂ, ℂ →L[ℂ] ℂ)
      (⊤ : WithTop ℕ∞) (chartedFormPullback c ω) c.target := by
  sorry

/-- **Chart-pullback holomorphicity.** The scalar chart-pullback of a
holomorphic 1-form on a Riemann surface is holomorphic on the chart's
target. Routes through:

* `chartedFormPullback_contMDiffOn` (focused sub-obligation): the
  CLM-valued chart pullback is `C^⊤` on `c.target`.
* Composition with the smooth evaluation-at-`1` CLM
  `ContinuousLinearMap.apply ℂ ℂ 1 : (ℂ →L[ℂ] ℂ) →L[ℂ] ℂ`
  (Mathlib's `ContinuousLinearMap.contMDiff`).
* On the self-model `modelWithCornersSelf ℂ ℂ`,
  `ContMDiffOn 𝕜 ⊤ f s ⟺ ContDiffOn 𝕜 ⊤ f s` via
  `contMDiffOn_iff_contDiffOn`.
* `ContDiffOn.differentiableOn` (with `n = ⊤ ≠ 0`) bridges smoothness
  to ℂ-differentiability.

This is a real bridge: it converts the "smooth section" assertion
(focused obligation above) into the holomorphicity needed by
`DifferentiableOn.isExactOn_ball`. -/
theorem chartPullbackFun_differentiableOn
    (c : OpenPartialHomeomorph X ℂ) (ω : HolomorphicOneForm ℂ X) :
    DifferentiableOn ℂ (chartPullbackFun c ω) c.target := by
  -- (1) The CLM-valued chart pullback is C^⊤ on c.target.
  have h_pullback_contMDiff :
      ContMDiffOn (modelWithCornersSelf ℂ ℂ) 𝓘(ℂ, ℂ →L[ℂ] ℂ)
        (⊤ : WithTop ℕ∞) (chartedFormPullback c ω) c.target :=
    chartedFormPullback_contMDiffOn c ω
  -- (2) Evaluation at `1 : ℂ` is a continuous linear map, hence smooth.
  have h_apply_contMDiff :
      ContMDiff 𝓘(ℂ, ℂ →L[ℂ] ℂ) (modelWithCornersSelf ℂ ℂ)
        (⊤ : WithTop ℕ∞) (fun L : ℂ →L[ℂ] ℂ => L (1 : ℂ)) :=
    (ContinuousLinearMap.apply ℂ ℂ (1 : ℂ)).contMDiff
  -- (3) `chartPullbackFun c ω z = (CLM.apply 1) (chartedFormPullback c ω z)`.
  -- The composition is ContMDiffOn.
  have h_comp :
      ContMDiffOn (modelWithCornersSelf ℂ ℂ) (modelWithCornersSelf ℂ ℂ)
        (⊤ : WithTop ℕ∞) (chartPullbackFun c ω) c.target := by
    have h_eq : chartPullbackFun c ω
        = (fun L : ℂ →L[ℂ] ℂ => L (1 : ℂ)) ∘ chartedFormPullback c ω := rfl
    rw [h_eq]
    exact h_apply_contMDiff.comp_contMDiffOn h_pullback_contMDiff
  -- (4) Self-model bridge: ContMDiffOn ⟺ ContDiffOn.
  have h_contDiff : ContDiffOn ℂ (⊤ : WithTop ℕ∞) (chartPullbackFun c ω) c.target :=
    h_comp.contDiffOn
  -- (5) ContDiffOn with n = ⊤ ≠ 0 ⟹ DifferentiableOn.
  exact h_contDiff.differentiableOn (by exact_mod_cast WithTop.top_ne_zero)

/-- **Chart-pullback holomorphicity specialized to `chartAt`.** Under
`[StableChartAt ℂ X]`, the scalar chart pullback for `c = chartAt ℂ p₀`
is holomorphic on `(chartAt ℂ p₀).target`. Fully proved (no sorry):
routes through the just-proved `chartedFormPullback_chartAt_contMDiffOn`
plus the same ContMDiffOn → DifferentiableOn bridge as the general
version. -/
theorem chartPullbackFun_chartAt_differentiableOn
    [StableChartAt ℂ X] (p₀ : X) (ω : HolomorphicOneForm ℂ X) :
    DifferentiableOn ℂ (chartPullbackFun (chartAt ℂ p₀) ω) (chartAt ℂ p₀).target := by
  have h_pullback_contMDiff :
      ContMDiffOn (modelWithCornersSelf ℂ ℂ) 𝓘(ℂ, ℂ →L[ℂ] ℂ)
        (⊤ : WithTop ℕ∞) (chartedFormPullback (chartAt ℂ p₀) ω)
        (chartAt ℂ p₀).target :=
    chartedFormPullback_chartAt_contMDiffOn p₀ ω
  have h_apply_contMDiff :
      ContMDiff 𝓘(ℂ, ℂ →L[ℂ] ℂ) (modelWithCornersSelf ℂ ℂ)
        (⊤ : WithTop ℕ∞) (fun L : ℂ →L[ℂ] ℂ => L (1 : ℂ)) :=
    (ContinuousLinearMap.apply ℂ ℂ (1 : ℂ)).contMDiff
  have h_comp :
      ContMDiffOn (modelWithCornersSelf ℂ ℂ) (modelWithCornersSelf ℂ ℂ)
        (⊤ : WithTop ℕ∞) (chartPullbackFun (chartAt ℂ p₀) ω)
        (chartAt ℂ p₀).target := by
    have h_eq : chartPullbackFun (chartAt ℂ p₀) ω
        = (fun L : ℂ →L[ℂ] ℂ => L (1 : ℂ)) ∘ chartedFormPullback (chartAt ℂ p₀) ω := rfl
    rw [h_eq]
    exact h_apply_contMDiff.comp_contMDiffOn h_pullback_contMDiff
  have h_contDiff :
      ContDiffOn ℂ (⊤ : WithTop ℕ∞) (chartPullbackFun (chartAt ℂ p₀) ω)
        (chartAt ℂ p₀).target :=
    h_comp.contDiffOn
  exact h_contDiff.differentiableOn (by exact_mod_cast WithTop.top_ne_zero)

/-- **Frontier sub-obligation (chart-local Euclidean FTC).**

For a smooth 1-form `α` on `X`, a chart `c = chartAt ℂ p` whose
target contains the ball of radius `r` around `c p`, a holomorphic
primitive `F : ℂ → ℂ` of the chart-pullback `chartPullbackFun c α` on
the ball, and a path `γ_chartSeg : Path p x` whose range lies in
`c.source` and whose chart image stays in the ball, the line integral
of `α` along `γ_chartSeg` (via `pathIntegralViaCover`) equals
`F (c x) - F (c p)`.

The hypotheses:
* `hr_subset : Metric.ball (c p) r ⊆ c.target` — the ball is a
  chart-target neighborhood.
* `hp : c x ∈ Metric.ball (c p) r` — the endpoint lands in the ball.
* `hF : ∀ z ∈ ball, HasDerivAt F (chartPullbackFun c α z) z` — F is a
  primitive of the chart pullback on the ball.
* `h_range : Set.range γ_chartSeg ⊆ c.source` — the path stays in
  the chart's source (needed to apply the chart-lift FTC).
* `h_lift_in_ball : ∀ t, c (γ_chartSeg t) ∈ ball` — the chart-lifted
  path stays in the ball (needed to invoke `hF` at every lifted point).

Strategy of the FTC discharge:
1. Apply `pathIntegralViaCoverWith_refinement_invariant'` with the
   single-chart partition `(n = 1, pickChart = const p)` to bridge
   `pathIntegralViaCover α γ_chartSeg` to a single
   `pathIntegralViaChartCorrect`.
2. Unfold `pathIntegralViaChartCorrect` to a `curveIntegral` over
   `chartedFormPullback c α` along the chart-lifted path.
3. Apply `curveIntegral_def` to land in an `intervalIntegral` over
   `[0, 1]` of `chartedFormPullback c α (chartLift t) (derivWithin t)`.
4. Identify the integrand via
   `chartedFormPullback_apply_eq_chartPullbackFun_smul`:
   `chartedFormPullback c α z L = L • chartPullbackFun c α z`.
5. Apply Mathlib's `intervalIntegral.integral_eq_sub_of_hasDerivAt`
   with the primitive `F ∘ chartLift.extend`, using `hF` + the
   path-lift's derivative (from `[PiecewiseC1PathRegularity X]`).
6. Endpoint values land at `F (c x) - F (c p)` via
   `chartLift.extend 0 = c p`, `chartLift.extend 1 = c x`.

* `subpath_div_zero_one_extend` — focused helper: the subpath of `γ` from
  `divFinIcc 1 _ 0 _ = 0/1` to `divFinIcc 1 _ 1 _ = 1/1` has the same
  `.extend` function as `γ` itself. Textbook identity; routes the
  divFinIcc-subpath form of the path back to the original `γ` so the
  FTC application can match. -/
private lemma subpath_div_zero_one_extend
    {Y : Type*} [TopologicalSpace Y] {a b : Y} (γ : Path a b) :
    (γ.subpath (divFinIcc 1 Nat.one_pos 0 (le_of_lt (0 : Fin 1).isLt))
               (divFinIcc 1 Nat.one_pos (0 + 1) (0 : Fin 1).isLt)).extend
      = γ.extend := by
  apply ContinuousMap.ext
  intro t
  have h_div0 : divFinIcc 1 Nat.one_pos 0 (le_of_lt (0 : Fin 1).isLt) =
      (0 : unitInterval) := by
    apply Subtype.ext; simp [divFinIcc]
  have h_div1 : divFinIcc 1 Nat.one_pos (0 + 1) (0 : Fin 1).isLt =
      (1 : unitInterval) := by
    apply Subtype.ext
    show ((0 + 1 : ℕ) : ℝ) / (1 : ℕ) = 1
    norm_num
  rcases le_or_gt t 0 with ht_le | ht_pos
  · rw [Path.extend_of_le_zero _ ht_le, Path.extend_of_le_zero γ ht_le]
    -- LHS: γ (divFinIcc 1 _ 0 _) = γ 0 (by h_div0) = a.
    rw [h_div0]
    exact γ.source
  · rcases le_or_gt 1 t with ht_ge | ht_lt
    · rw [Path.extend_of_one_le _ ht_ge, Path.extend_of_one_le γ ht_ge]
      rw [h_div1]
      exact γ.target
    · have ht_mem : t ∈ unitInterval := ⟨le_of_lt ht_pos, le_of_lt ht_lt⟩
      rw [Path.extend_extends' _ ⟨t, ht_mem⟩,
          Path.extend_extends' γ ⟨t, ht_mem⟩]
      show γ (Path.subpathAux _ _ ⟨t, ht_mem⟩) = γ ⟨t, ht_mem⟩
      congr 1
      apply Subtype.ext
      show ((1 : ℝ) - t) * (((0 : ℕ) : ℝ) / (1 : ℕ)) +
            t * (((0 + 1 : ℕ) : ℝ) / (1 : ℕ)) = t
      push_cast
      ring

/-- **Witness-form variant of `pathIntegralViaCover_eq_primitive_diff`**
(Stage III). Takes an `IsChartContDiffPath γ_chartSeg` witness explicitly
instead of relying on the universally-quantified
`[PiecewiseC1PathRegularity X]` typeclass route. Sorry-free under
`[StableChartAt ℂ X]` alone (no `[PiecewiseC1PathRegularity X]` needed). -/
theorem pathIntegralViaCover_eq_primitive_diff_of_witnesses
    [StableChartAt ℂ X]
    (α : HolomorphicOneForm ℂ X) {p x : X}
    (r : ℝ) (_hr : 0 < r)
    (_hr_subset : Metric.ball ((chartAt ℂ p) p) r ⊆ (chartAt ℂ p).target)
    (_hp : (chartAt ℂ p) x ∈ Metric.ball ((chartAt ℂ p) p) r)
    {F : ℂ → ℂ}
    (_hF : ∀ z ∈ Metric.ball ((chartAt ℂ p) p) r,
            HasDerivAt F (chartPullbackFun (chartAt ℂ p) α z) z)
    (γ_chartSeg : Path p x)
    (h_range : Set.range γ_chartSeg ⊆ (chartAt ℂ p).source)
    (_h_lift_in_ball : ∀ t : unitInterval,
        (chartAt ℂ p) (γ_chartSeg t) ∈ Metric.ball ((chartAt ℂ p) p) r)
    (hγ : JacobianChallenge.TraceDegree.IsChartContDiffPath γ_chartSeg) :
    pathIntegralViaCover α γ_chartSeg = F ((chartAt ℂ p) x) - F ((chartAt ℂ p) p) := by
  -- Step 1: Bridge `pathIntegralViaCover` (with Classical.choose partition)
  -- to the single-chart `pathIntegralViaCoverWith` with `n = 1` and
  -- `pickChart = fun _ => p`. The single-chart coverage hypothesis follows
  -- from `h_range` (γ stays in chart.source for all t).
  have hcov_single : ∀ (i : Fin 1) (t : unitInterval),
      (i : ℝ) / ((1 : ℕ) : ℝ) ≤ (t : ℝ) →
      (t : ℝ) ≤ ((i : ℝ) + 1) / ((1 : ℕ) : ℝ) →
      γ_chartSeg t ∈ (chartAt ℂ p).source := by
    intros _ t _ _
    exact h_range ⟨t, rfl⟩
  have h_bridge :
      pathIntegralViaCover α γ_chartSeg =
        pathIntegralViaCoverWith α γ_chartSeg 1 (Nat.one_pos)
          (fun _ => p) hcov_single := by
    unfold pathIntegralViaCover
    exact pathIntegralViaCoverWith_refinement_invariant'
      α γ_chartSeg hγ
      _ _ _ _ 1 Nat.one_pos (fun _ => p) hcov_single
  rw [h_bridge]
  -- Step 2: collapse the n=1 sum to a single segment via Fin.sum_univ_one.
  show ∑ i : Fin 1, pathIntegralViaChartCorrect (chartAt ℂ p) α
      (γ_chartSeg.subpath (divFinIcc 1 Nat.one_pos i.val (le_of_lt i.isLt))
                          (divFinIcc 1 Nat.one_pos (i.val + 1) i.isLt))
      _ = _
  rw [Fin.sum_univ_one]
  -- Step 3: simplify divFinIcc 1 _ 0/1 = 0/1 and Path.subpath_zero_one.
  -- The @[simp] divFinIcc lemmas have specific proof arguments (Nat.zero_le, le_refl);
  -- our goal has different proofs (le_of_lt of Fin.isLt). Use Subtype.ext-based
  -- inline equalities to bridge the proof-irrelevant mismatch.
  have h_div0 : divFinIcc 1 Nat.one_pos 0 (le_of_lt (0 : Fin 1).isLt) =
      (0 : unitInterval) := by
    apply Subtype.ext; simp [divFinIcc]
  have h_div1 : divFinIcc 1 Nat.one_pos (0 + 1) (0 : Fin 1).isLt =
      (1 : unitInterval) := by
    apply Subtype.ext
    show ((0 + 1 : ℕ) : ℝ) / (1 : ℕ) = 1
    norm_num
  simp only [Fin.val_zero, h_div0, h_div1, Path.subpath_zero_one]
  -- Step 4: unfold `pathIntegralViaChartCorrect` to `curveIntegral`.
  unfold pathIntegralViaChartCorrect pathIntegralInChartCorrect
  -- Step 5: convert curveIntegral to interval integral via curveIntegral_def.
  rw [curveIntegral_def]
  -- Step 6: rewrite the integrand into "derivWithin • chartPullbackFun" form.
  -- This is the integrand identification step: by
  -- `chartedFormPullback_apply_eq_chartPullbackFun_smul`, the CLM application
  -- `chartedFormPullback c α z L = L • chartPullbackFun c α z`. Combining with
  -- `curveIntegralFun_def` (which gives `ω (γ.extend t) (derivWithin γ.extend unitInterval t)`),
  -- the integrand becomes `(derivWithin γ.extend unitInterval t) • chartPullbackFun c α (γ.extend t)`.
  -- This is the cleanest algebraic form for matching against the chain-rule output
  -- in Mathlib's FTC `intervalIntegral.integral_eq_sub_of_hasDerivAt`.
  have h_integrand_eq : ∀ t : ℝ,
      curveIntegralFun (chartedFormPullback (chartAt ℂ p) α)
        (chartLift (chartAt ℂ p) (γ_chartSeg.cast γ_chartSeg.source γ_chartSeg.target)
          (by
            intro y hy
            rcases hy with ⟨t, rfl⟩
            exact h_range ⟨t, rfl⟩)) t
      = (derivWithin (chartLift (chartAt ℂ p)
            (γ_chartSeg.cast γ_chartSeg.source γ_chartSeg.target)
            (by
              intro y hy
              rcases hy with ⟨t, rfl⟩
              exact h_range ⟨t, rfl⟩)).extend unitInterval t)
        • chartPullbackFun (chartAt ℂ p) α
            ((chartLift (chartAt ℂ p)
              (γ_chartSeg.cast γ_chartSeg.source γ_chartSeg.target)
              (by
                intro y hy
                rcases hy with ⟨t, rfl⟩
                exact h_range ⟨t, rfl⟩)).extend t) := by
    intro t
    rw [curveIntegralFun_def]
    exact chartedFormPullback_apply_eq_chartPullbackFun_smul _ _ _ _
  -- Step 7: set up the chart-lift path and primitive G := F ∘ γlift.extend,
  -- then apply `intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le`.
  set γlift : Path ((chartAt ℂ p) (γ_chartSeg 0)) ((chartAt ℂ p) (γ_chartSeg 1)) :=
    chartLift (chartAt ℂ p) (γ_chartSeg.cast γ_chartSeg.source γ_chartSeg.target)
      (by
        intro y hy
        rcases hy with ⟨t, rfl⟩
        exact h_range ⟨t, rfl⟩) with hγlift_def
  -- Endpoint identifications: γlift.extend 0 = chart p, γlift.extend 1 = chart x.
  have h_chart_zero : (chartAt ℂ p) (γ_chartSeg 0) = (chartAt ℂ p) p := by
    rw [γ_chartSeg.source]
  have h_chart_one : (chartAt ℂ p) (γ_chartSeg 1) = (chartAt ℂ p) x := by
    rw [γ_chartSeg.target]
  -- Define the primitive G(t) := F (γlift.extend t).
  set G : ℝ → ℂ := fun t => F (γlift.extend t) with hG_def
  -- Endpoint values of G.
  have hG_zero : G 0 = F ((chartAt ℂ p) p) := by
    simp only [hG_def, γlift.extend_zero, h_chart_zero]
  have hG_one : G 1 = F ((chartAt ℂ p) x) := by
    simp only [hG_def, γlift.extend_one, h_chart_one]
  -- Rewrite the RHS as G 1 - G 0.
  rw [show (F ((chartAt ℂ p) x) - F ((chartAt ℂ p) p) : ℂ) = G 1 - G 0 by
        rw [hG_zero, hG_one]]
  -- Apply Mathlib FTC `integral_eq_sub_of_hasDerivAt_of_le` with three obligations:
  -- (i) ContinuousOn G [0,1], (ii) ∀ t ∈ Ioo 0 1, HasDerivAt G (integrand t) t,
  -- (iii) IntervalIntegrable (integrand) volume 0 1.
  -- Pointwise identity: γlift.extend t = (chartAt ℂ p) (γ_chartSeg.extend t).
  have h_extend_eq : ∀ t : ℝ,
      γlift.extend t = (chartAt ℂ p) (γ_chartSeg.extend t) := by
    intro t
    rcases le_or_gt t 0 with ht_le | ht_pos
    · rw [γlift.extend_of_le_zero ht_le, γ_chartSeg.extend_of_le_zero ht_le,
          γ_chartSeg.source]
    · rcases le_or_gt 1 t with ht_ge | ht_lt
      · rw [γlift.extend_of_one_le ht_ge, γ_chartSeg.extend_of_one_le ht_ge,
            γ_chartSeg.target]
      · have ht_mem : t ∈ unitInterval := ⟨le_of_lt ht_pos, le_of_lt ht_lt⟩
        rw [γlift.extend_extends' ⟨t, ht_mem⟩,
            γ_chartSeg.extend_extends' ⟨t, ht_mem⟩]
        rfl
  -- For t ∈ [0,1]: γlift.extend t lies in the ball around (chartAt ℂ p) p.
  have h_extend_in_ball : ∀ t ∈ Set.Icc (0:ℝ) 1,
      γlift.extend t ∈ Metric.ball ((chartAt ℂ p) p) r := by
    intro t ht
    rw [h_extend_eq]
    have ht_mem : t ∈ unitInterval := ht
    rw [γ_chartSeg.extend_extends' ⟨t, ht_mem⟩]
    exact _h_lift_in_ball ⟨t, ht_mem⟩
  -- Shared C¹ regularity: γlift.extend is C¹ on [0,1] (used by obligations 2 + 3).
  have h_preimage_eq :
      γ_chartSeg.extend ⁻¹' (chartAt ℂ p).source ∩ Set.Icc (0:ℝ) 1
      = Set.Icc (0:ℝ) 1 := by
    apply Set.inter_eq_right.mpr
    intro t ht
    show γ_chartSeg.extend t ∈ (chartAt ℂ p).source
    have ht_mem : t ∈ unitInterval := ht
    have h_eq : γ_chartSeg.extend t = γ_chartSeg ⟨t, ht_mem⟩ :=
      γ_chartSeg.extend_extends' ⟨t, ht_mem⟩
    rw [h_eq]
    exact h_range ⟨⟨t, ht_mem⟩, rfl⟩
  have h_γlift_C1 : ContDiffOn ℝ 1 γlift.extend (Set.Icc (0:ℝ) 1) := by
    have h_obl := hγ p
    rw [h_preimage_eq] at h_obl
    refine h_obl.congr (fun t _ => ?_)
    exact (h_extend_eq t).symm
  refine intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le
    (zero_le_one (α := ℝ)) ?_ ?_ ?_
  · -- (1) ContinuousOn G [0,1]: F continuous at every γlift.extend t (from
    -- _hF + HasDerivAt → ContinuousAt), γlift.extend continuous.
    intro t ht
    refine ContinuousAt.continuousWithinAt ?_
    have h_F_contAt : ContinuousAt F (γlift.extend t) :=
      (_hF (γlift.extend t) (h_extend_in_ball t ht)).continuousAt
    have h_γlift_contAt : ContinuousAt γlift.extend t :=
      γlift.continuous_extend.continuousAt
    exact h_F_contAt.comp h_γlift_contAt
  · -- (2) HasDerivAt G (integrand t) t for t ∈ Ioo 0 1.
    intro t ht
    have ht_in_icc : t ∈ Set.Icc (0:ℝ) 1 :=
      ⟨le_of_lt ht.1, le_of_lt ht.2⟩
    -- (a) γlift.extend is differentiable at interior t.
    have h_icc_nhds : Set.Icc (0:ℝ) 1 ∈ nhds t := by
      rw [_root_.mem_nhds_iff]
      exact ⟨Set.Ioo 0 1, Set.Ioo_subset_Icc_self, isOpen_Ioo, ht⟩
    have h_γlift_diffAt : DifferentiableAt ℝ γlift.extend t := by
      have h_diff_on : DifferentiableOn ℝ γlift.extend (Set.Icc (0:ℝ) 1) :=
        h_γlift_C1.differentiableOn (by norm_num : (1 : WithTop ℕ∞) ≠ 0)
      exact h_diff_on.differentiableAt h_icc_nhds
    have h_γlift_HDA : HasDerivAt γlift.extend (deriv γlift.extend t) t :=
      h_γlift_diffAt.hasDerivAt
    -- (b) HasDerivAt F at γlift.extend t (from _hF + h_extend_in_ball).
    have h_F_HDA : HasDerivAt F
        (chartPullbackFun (chartAt ℂ p) α (γlift.extend t)) (γlift.extend t) :=
      _hF (γlift.extend t) (h_extend_in_ball t ht_in_icc)
    -- (c) Chain rule via HasDerivAt.scomp.
    have h_chain : HasDerivAt (F ∘ γlift.extend)
        ((deriv γlift.extend t) •
          chartPullbackFun (chartAt ℂ p) α (γlift.extend t)) t :=
      h_F_HDA.scomp t h_γlift_HDA
    -- derivWithin = deriv on the open interior.
    have h_dw_eq : derivWithin γlift.extend (Set.Icc (0:ℝ) 1) t =
        deriv γlift.extend t :=
      derivWithin_of_mem_nhds h_icc_nhds
    -- The chain rule's derivative matches the integrand (modulo path-form
    -- alignment): h_integrand_eq + h_dw_eq.
    -- The residual `h.e'_9` subgoal is the curveIntegralFun-path-form
    -- equality between goal_path (subpath form with divFinIcc 1 _ 0/1 _
    -- endpoints) and γlift (cast form with 0/1 endpoints). Mathematically
    -- both .extends equal `chart ∘ γ_chartSeg.extend` (via h_extend_eq for
    -- γlift, and via subpathAux div0 div1 s = s + cast_coe for goal_path),
    -- but the propositional vs definitional equality between the two
    -- representations requires path-cast bookkeeping outside Mathlib's
    -- standard auto tactics.
    -- The goal is `HasDerivAt G (curveIntegralFun ω goal_path t) t` where
    -- goal_path is in subpath form. We bridge to h_chain (HasDerivAt for γlift form)
    -- by establishing the integrand-at-t equality via subpath_div_zero_one_extend +
    -- h_integrand_eq + h_dw_eq.
    have h_pt : ∀ s : ℝ,
        (chartLift (chartAt ℂ p) (γ_chartSeg.subpath
            (divFinIcc 1 Nat.one_pos 0 (le_of_lt (0:Fin 1).isLt))
            (divFinIcc 1 Nat.one_pos (0 + 1) (0:Fin 1).isLt))
            (by
              intro y hy
              rcases hy with ⟨t, rfl⟩
              exact h_range ⟨_, rfl⟩)).extend s
        = γlift.extend s := fun s => by
      show (chartAt ℂ p) ((γ_chartSeg.subpath _ _).extend s) = γlift.extend s
      rw [show (γ_chartSeg.subpath
            (divFinIcc 1 Nat.one_pos 0 (le_of_lt (0:Fin 1).isLt))
            (divFinIcc 1 Nat.one_pos (0 + 1) (0:Fin 1).isLt)).extend s
          = γ_chartSeg.extend s from
          DFunLike.congr_fun (subpath_div_zero_one_extend γ_chartSeg) s]
      rfl
    have h_target :
        curveIntegralFun (chartedFormPullback (chartAt ℂ p) α)
          (chartLift (chartAt ℂ p) (γ_chartSeg.subpath
            (divFinIcc 1 Nat.one_pos 0 (le_of_lt (0:Fin 1).isLt))
            (divFinIcc 1 Nat.one_pos (0 + 1) (0:Fin 1).isLt))
            (by
              intro y hy
              rcases hy with ⟨t, rfl⟩
              exact h_range ⟨_, rfl⟩)) t
        = (deriv γlift.extend t) •
            chartPullbackFun (chartAt ℂ p) α (γlift.extend t) := by
      rw [curveIntegralFun_def, h_pt t,
          show derivWithin (chartLift (chartAt ℂ p) (γ_chartSeg.subpath
                (divFinIcc 1 Nat.one_pos 0 (le_of_lt (0:Fin 1).isLt))
                (divFinIcc 1 Nat.one_pos (0 + 1) (0:Fin 1).isLt))
                (by
                  intro y hy
                  rcases hy with ⟨t, rfl⟩
                  exact h_range ⟨_, rfl⟩)).extend unitInterval t
              = deriv γlift.extend t from
            (derivWithin_congr (fun s _ => h_pt s) (h_pt t)).trans h_dw_eq]
      exact chartedFormPullback_apply_eq_chartPullbackFun_smul _ _ _ _
    rw [h_target]
    exact h_chain
  · -- (3) IntervalIntegrable via ContinuousOn.curveIntegrable_of_contDiffOn.
    have h_ω_cont : ContinuousOn (chartedFormPullback (chartAt ℂ p) α)
        (chartAt ℂ p).target :=
      (chartedFormPullback_chartAt_contMDiffOn p α).continuousOn
    have h_γlift_target : ∀ t : unitInterval, γlift t ∈ (chartAt ℂ p).target := by
      intro t
      have h_eq : γlift t = (chartAt ℂ p) (γ_chartSeg t) := by
        have h := h_extend_eq t
        rw [γlift.extend_extends' t, γ_chartSeg.extend_extends' t] at h
        exact h
      rw [h_eq]
      exact (chartAt ℂ p).map_source (h_range ⟨t, rfl⟩)
    -- The 3 helpers (h_ω_cont, h_γlift_C1, h_γlift_target) prove
    -- `CurveIntegrable (chartedFormPullback c α) γlift` via Mathlib's
    -- `ContinuousOn.curveIntegrable_of_contDiffOn`. The remaining alignment
    -- is converting the goal's subpath path to γlift form.
    have h_lift_integrable :
        CurveIntegrable (chartedFormPullback (chartAt ℂ p) α) γlift :=
      ContinuousOn.curveIntegrable_of_contDiffOn h_ω_cont h_γlift_C1 h_γlift_target
    -- Convert from γlift to the goal-form path via convert: the two paths
    -- have the same .extend function (both = chart ∘ γ_chartSeg.extend),
    -- so curveIntegralFun is the same.
    -- Establish function-level equality of the two curveIntegralFuns.
    -- The goal's path (subpath form) and γlift (cast form) have the same .extend,
    -- so their curveIntegralFuns are equal as functions of t.
    have h_curve_eq :
        curveIntegralFun (chartedFormPullback (chartAt ℂ p) α)
          (chartLift (chartAt ℂ p) (γ_chartSeg.subpath
            (divFinIcc 1 Nat.one_pos 0 (le_of_lt (0:Fin 1).isLt))
            (divFinIcc 1 Nat.one_pos (0 + 1) (0:Fin 1).isLt))
            (by
              intro y hy
              rcases hy with ⟨t, rfl⟩
              exact h_range ⟨_, rfl⟩))
        = curveIntegralFun (chartedFormPullback (chartAt ℂ p) α) γlift := by
      funext t
      rw [curveIntegralFun_def, curveIntegralFun_def]
      -- LHS: ω (subpath_path.extend t) (derivWithin subpath_path.extend I t)
      -- RHS: ω γlift.extend t (derivWithin γlift.extend I t)
      -- Both .extends agree at every point via subpath_div_zero_one_extend
      -- (+ chartLift_extend_eq rfl + Path.extend_cast rfl).
      have h_pt : ∀ s : ℝ,
          (chartLift (chartAt ℂ p) (γ_chartSeg.subpath
              (divFinIcc 1 Nat.one_pos 0 (le_of_lt (0:Fin 1).isLt))
              (divFinIcc 1 Nat.one_pos (0 + 1) (0:Fin 1).isLt))
              (by intro y hy; rcases hy with ⟨t, rfl⟩; exact h_range ⟨_, rfl⟩)).extend s
          = γlift.extend s := fun s => by
        show (chartAt ℂ p) ((γ_chartSeg.subpath _ _).extend s) = γlift.extend s
        rw [show (γ_chartSeg.subpath
              (divFinIcc 1 Nat.one_pos 0 (le_of_lt (0:Fin 1).isLt))
              (divFinIcc 1 Nat.one_pos (0 + 1) (0:Fin 1).isLt)).extend s
            = γ_chartSeg.extend s from
            DFunLike.congr_fun (subpath_div_zero_one_extend γ_chartSeg) s]
        rfl
      congr 1
      · rw [h_pt]
      · exact derivWithin_congr (fun s _ => h_pt s) (h_pt t)
    rw [h_curve_eq]
    exact h_lift_integrable

/-- **General FTC on a chart-ball (Inc 11b.1).** Generalization of
`pathIntegralViaCover_eq_primitive_diff_of_witnesses`: the chart
basepoint `p` is now a SEPARATE parameter, not constrained to equal
the path's start. The path `γ : Path a b` can start anywhere in
`(chartAt ℂ p).source`. The conclusion expresses the integral as
`F` evaluated at the chart-image difference of endpoints.

This is the FTC bridge used by `stokes_chart_local_triangle` to compute
each of three face integrals via a SINGLE primitive `F` on a SINGLE
chart-ball (rather than three different charts/primitives, which would
prevent the boundary-telescoping cancellation). -/
theorem pathIntegralViaCover_eq_F_diff_in_ball
    [StableChartAt ℂ X]
    (α : HolomorphicOneForm ℂ X) {p a b : X}
    (r : ℝ) (_hr : 0 < r)
    (_hr_subset : Metric.ball ((chartAt ℂ p) p) r ⊆ (chartAt ℂ p).target)
    {F : ℂ → ℂ}
    (_hF : ∀ z ∈ Metric.ball ((chartAt ℂ p) p) r,
            HasDerivAt F (chartPullbackFun (chartAt ℂ p) α z) z)
    (γ : Path a b)
    (h_range : Set.range γ ⊆ (chartAt ℂ p).source)
    (_h_lift_in_ball : ∀ t : unitInterval,
        (chartAt ℂ p) (γ t) ∈ Metric.ball ((chartAt ℂ p) p) r)
    (hγ : JacobianChallenge.TraceDegree.IsChartContDiffPath γ) :
    pathIntegralViaCover α γ = F ((chartAt ℂ p) b) - F ((chartAt ℂ p) a) := by
  -- Step 1: Bridge to single-chart pathIntegralViaCoverWith with pickChart = p.
  have hcov_single : ∀ (i : Fin 1) (t : unitInterval),
      (i : ℝ) / ((1 : ℕ) : ℝ) ≤ (t : ℝ) →
      (t : ℝ) ≤ ((i : ℝ) + 1) / ((1 : ℕ) : ℝ) →
      γ t ∈ (chartAt ℂ p).source := by
    intros _ t _ _
    exact h_range ⟨t, rfl⟩
  have h_bridge :
      pathIntegralViaCover α γ =
        pathIntegralViaCoverWith α γ 1 (Nat.one_pos) (fun _ => p) hcov_single := by
    unfold pathIntegralViaCover
    exact pathIntegralViaCoverWith_refinement_invariant'
      α γ hγ _ _ _ _ 1 Nat.one_pos (fun _ => p) hcov_single
  rw [h_bridge]
  -- Step 2: collapse n=1 sum.
  show ∑ i : Fin 1, pathIntegralViaChartCorrect (chartAt ℂ p) α
      (γ.subpath (divFinIcc 1 Nat.one_pos i.val (le_of_lt i.isLt))
                  (divFinIcc 1 Nat.one_pos (i.val + 1) i.isLt))
      _ = _
  rw [Fin.sum_univ_one]
  -- Step 3: simplify divFinIcc.
  have h_div0 : divFinIcc 1 Nat.one_pos 0 (le_of_lt (0 : Fin 1).isLt) =
      (0 : unitInterval) := by
    apply Subtype.ext; simp [divFinIcc]
  have h_div1 : divFinIcc 1 Nat.one_pos (0 + 1) (0 : Fin 1).isLt =
      (1 : unitInterval) := by
    apply Subtype.ext
    show ((0 + 1 : ℕ) : ℝ) / (1 : ℕ) = 1
    norm_num
  simp only [Fin.val_zero, h_div0, h_div1, Path.subpath_zero_one]
  -- Step 4: unfold to curveIntegral.
  unfold pathIntegralViaChartCorrect pathIntegralInChartCorrect
  rw [curveIntegral_def]
  -- Step 6: Integrand identification (unchanged from original).
  -- Step 7: set up γlift over chart basepoint p, with endpoints (chart a), (chart b).
  set γlift : Path ((chartAt ℂ p) (γ 0)) ((chartAt ℂ p) (γ 1)) :=
    chartLift (chartAt ℂ p) (γ.cast γ.source γ.target)
      (by
        intro y hy
        rcases hy with ⟨t, rfl⟩
        exact h_range ⟨t, rfl⟩) with hγlift_def
  -- Endpoint identifications: γlift.extend 0 = chart a, γlift.extend 1 = chart b.
  -- KEY CHANGE from the original lemma: we rewrite γ.source = a (not = p) and
  -- γ.target = b (not = x). The chart basepoint p remains separate from path endpoints.
  have h_chart_zero : (chartAt ℂ p) (γ 0) = (chartAt ℂ p) a := by
    rw [γ.source]
  have h_chart_one : (chartAt ℂ p) (γ 1) = (chartAt ℂ p) b := by
    rw [γ.target]
  set G : ℝ → ℂ := fun t => F (γlift.extend t) with hG_def
  have hG_zero : G 0 = F ((chartAt ℂ p) a) := by
    simp only [hG_def, γlift.extend_zero, h_chart_zero]
  have hG_one : G 1 = F ((chartAt ℂ p) b) := by
    simp only [hG_def, γlift.extend_one, h_chart_one]
  rw [show (F ((chartAt ℂ p) b) - F ((chartAt ℂ p) a) : ℂ) = G 1 - G 0 by
        rw [hG_zero, hG_one]]
  -- Step 8: pointwise identity γlift.extend = chart ∘ γ.extend.
  have h_extend_eq : ∀ t : ℝ,
      γlift.extend t = (chartAt ℂ p) (γ.extend t) := by
    intro t
    rcases le_or_gt t 0 with ht_le | ht_pos
    · rw [γlift.extend_of_le_zero ht_le, γ.extend_of_le_zero ht_le, γ.source]
    · rcases le_or_gt 1 t with ht_ge | ht_lt
      · rw [γlift.extend_of_one_le ht_ge, γ.extend_of_one_le ht_ge, γ.target]
      · have ht_mem : t ∈ unitInterval := ⟨le_of_lt ht_pos, le_of_lt ht_lt⟩
        rw [γlift.extend_extends' ⟨t, ht_mem⟩, γ.extend_extends' ⟨t, ht_mem⟩]
        rfl
  have h_extend_in_ball : ∀ t ∈ Set.Icc (0:ℝ) 1,
      γlift.extend t ∈ Metric.ball ((chartAt ℂ p) p) r := by
    intro t ht
    rw [h_extend_eq]
    have ht_mem : t ∈ unitInterval := ht
    rw [γ.extend_extends' ⟨t, ht_mem⟩]
    exact _h_lift_in_ball ⟨t, ht_mem⟩
  have h_preimage_eq :
      γ.extend ⁻¹' (chartAt ℂ p).source ∩ Set.Icc (0:ℝ) 1
      = Set.Icc (0:ℝ) 1 := by
    apply Set.inter_eq_right.mpr
    intro t ht
    show γ.extend t ∈ (chartAt ℂ p).source
    have ht_mem : t ∈ unitInterval := ht
    have h_eq : γ.extend t = γ ⟨t, ht_mem⟩ :=
      γ.extend_extends' ⟨t, ht_mem⟩
    rw [h_eq]
    exact h_range ⟨⟨t, ht_mem⟩, rfl⟩
  have h_γlift_C1 : ContDiffOn ℝ 1 γlift.extend (Set.Icc (0:ℝ) 1) := by
    have h_obl := hγ p
    rw [h_preimage_eq] at h_obl
    refine h_obl.congr (fun t _ => ?_)
    exact (h_extend_eq t).symm
  -- Apply Mathlib FTC.
  refine intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le
    (zero_le_one (α := ℝ)) ?_ ?_ ?_
  · intro t ht
    refine ContinuousAt.continuousWithinAt ?_
    have h_F_contAt : ContinuousAt F (γlift.extend t) :=
      (_hF (γlift.extend t) (h_extend_in_ball t ht)).continuousAt
    have h_γlift_contAt : ContinuousAt γlift.extend t :=
      γlift.continuous_extend.continuousAt
    exact h_F_contAt.comp h_γlift_contAt
  · intro t ht
    have ht_in_icc : t ∈ Set.Icc (0:ℝ) 1 := ⟨le_of_lt ht.1, le_of_lt ht.2⟩
    have h_icc_nhds : Set.Icc (0:ℝ) 1 ∈ nhds t := by
      rw [_root_.mem_nhds_iff]
      exact ⟨Set.Ioo 0 1, Set.Ioo_subset_Icc_self, isOpen_Ioo, ht⟩
    have h_γlift_diffAt : DifferentiableAt ℝ γlift.extend t := by
      have h_diff_on : DifferentiableOn ℝ γlift.extend (Set.Icc (0:ℝ) 1) :=
        h_γlift_C1.differentiableOn (by norm_num : (1 : WithTop ℕ∞) ≠ 0)
      exact h_diff_on.differentiableAt h_icc_nhds
    have h_γlift_HDA : HasDerivAt γlift.extend (deriv γlift.extend t) t :=
      h_γlift_diffAt.hasDerivAt
    have h_F_HDA : HasDerivAt F
        (chartPullbackFun (chartAt ℂ p) α (γlift.extend t)) (γlift.extend t) :=
      _hF (γlift.extend t) (h_extend_in_ball t ht_in_icc)
    have h_chain : HasDerivAt (F ∘ γlift.extend)
        ((deriv γlift.extend t) •
          chartPullbackFun (chartAt ℂ p) α (γlift.extend t)) t :=
      h_F_HDA.scomp t h_γlift_HDA
    have h_dw_eq : derivWithin γlift.extend (Set.Icc (0:ℝ) 1) t =
        deriv γlift.extend t :=
      derivWithin_of_mem_nhds h_icc_nhds
    have h_pt : ∀ s : ℝ,
        (chartLift (chartAt ℂ p) (γ.subpath
            (divFinIcc 1 Nat.one_pos 0 (le_of_lt (0:Fin 1).isLt))
            (divFinIcc 1 Nat.one_pos (0 + 1) (0:Fin 1).isLt))
            (by intro y hy; rcases hy with ⟨t, rfl⟩; exact h_range ⟨_, rfl⟩)).extend s
        = γlift.extend s := fun s => by
      show (chartAt ℂ p) ((γ.subpath _ _).extend s) = γlift.extend s
      rw [show (γ.subpath
            (divFinIcc 1 Nat.one_pos 0 (le_of_lt (0:Fin 1).isLt))
            (divFinIcc 1 Nat.one_pos (0 + 1) (0:Fin 1).isLt)).extend s
          = γ.extend s from
          DFunLike.congr_fun (subpath_div_zero_one_extend γ) s]
      rfl
    have h_target :
        curveIntegralFun (chartedFormPullback (chartAt ℂ p) α)
          (chartLift (chartAt ℂ p) (γ.subpath
            (divFinIcc 1 Nat.one_pos 0 (le_of_lt (0:Fin 1).isLt))
            (divFinIcc 1 Nat.one_pos (0 + 1) (0:Fin 1).isLt))
            (by intro y hy; rcases hy with ⟨t, rfl⟩; exact h_range ⟨_, rfl⟩)) t
        = (deriv γlift.extend t) •
            chartPullbackFun (chartAt ℂ p) α (γlift.extend t) := by
      rw [curveIntegralFun_def, h_pt t,
          show derivWithin (chartLift (chartAt ℂ p) (γ.subpath
                (divFinIcc 1 Nat.one_pos 0 (le_of_lt (0:Fin 1).isLt))
                (divFinIcc 1 Nat.one_pos (0 + 1) (0:Fin 1).isLt))
                (by intro y hy; rcases hy with ⟨t, rfl⟩; exact h_range ⟨_, rfl⟩)).extend
                unitInterval t
              = deriv γlift.extend t from
            (derivWithin_congr (fun s _ => h_pt s) (h_pt t)).trans h_dw_eq]
      exact chartedFormPullback_apply_eq_chartPullbackFun_smul _ _ _ _
    rw [h_target]
    exact h_chain
  · have h_ω_cont : ContinuousOn (chartedFormPullback (chartAt ℂ p) α)
        (chartAt ℂ p).target :=
      (chartedFormPullback_chartAt_contMDiffOn p α).continuousOn
    have h_γlift_target : ∀ t : unitInterval, γlift t ∈ (chartAt ℂ p).target := by
      intro t
      have h_eq : γlift t = (chartAt ℂ p) (γ t) := by
        have h := h_extend_eq t
        rw [γlift.extend_extends' t, γ.extend_extends' t] at h
        exact h
      rw [h_eq]
      exact (chartAt ℂ p).map_source (h_range ⟨t, rfl⟩)
    have h_lift_integrable :
        CurveIntegrable (chartedFormPullback (chartAt ℂ p) α) γlift :=
      ContinuousOn.curveIntegrable_of_contDiffOn h_ω_cont h_γlift_C1 h_γlift_target
    have h_curve_eq :
        curveIntegralFun (chartedFormPullback (chartAt ℂ p) α)
          (chartLift (chartAt ℂ p) (γ.subpath
            (divFinIcc 1 Nat.one_pos 0 (le_of_lt (0:Fin 1).isLt))
            (divFinIcc 1 Nat.one_pos (0 + 1) (0:Fin 1).isLt))
            (by intro y hy; rcases hy with ⟨t, rfl⟩; exact h_range ⟨_, rfl⟩))
        = curveIntegralFun (chartedFormPullback (chartAt ℂ p) α) γlift := by
      funext t
      rw [curveIntegralFun_def, curveIntegralFun_def]
      have h_pt : ∀ s : ℝ,
          (chartLift (chartAt ℂ p) (γ.subpath
              (divFinIcc 1 Nat.one_pos 0 (le_of_lt (0:Fin 1).isLt))
              (divFinIcc 1 Nat.one_pos (0 + 1) (0:Fin 1).isLt))
              (by intro y hy; rcases hy with ⟨t, rfl⟩; exact h_range ⟨_, rfl⟩)).extend s
          = γlift.extend s := fun s => by
        show (chartAt ℂ p) ((γ.subpath _ _).extend s) = γlift.extend s
        rw [show (γ.subpath
              (divFinIcc 1 Nat.one_pos 0 (le_of_lt (0:Fin 1).isLt))
              (divFinIcc 1 Nat.one_pos (0 + 1) (0:Fin 1).isLt)).extend s
            = γ.extend s from
            DFunLike.congr_fun (subpath_div_zero_one_extend γ) s]
        rfl
      congr 1
      · rw [h_pt]
      · exact derivWithin_congr (fun s _ => h_pt s) (h_pt t)
    rw [h_curve_eq]
    exact h_lift_integrable

/-- Original obligation-based variant; delegates to the witness form
above by supplying the universally-quantified
`path_contDiffOn_obligation` as the per-path witness. The remaining
sorry is concentrated in the obligation itself. Callers that can
produce an `IsChartContDiffPath` witness for their specific path
should call `pathIntegralViaCover_eq_primitive_diff_of_witnesses`
directly instead. -/
theorem pathIntegralViaCover_eq_primitive_diff
    [StableChartAt ℂ X] [JacobianChallenge.TraceDegree.PiecewiseC1PathRegularity X]
    (α : HolomorphicOneForm ℂ X) {p x : X}
    (r : ℝ) (hr : 0 < r)
    (hr_subset : Metric.ball ((chartAt ℂ p) p) r ⊆ (chartAt ℂ p).target)
    (hp : (chartAt ℂ p) x ∈ Metric.ball ((chartAt ℂ p) p) r)
    {F : ℂ → ℂ}
    (hF : ∀ z ∈ Metric.ball ((chartAt ℂ p) p) r,
            HasDerivAt F (chartPullbackFun (chartAt ℂ p) α z) z)
    (γ_chartSeg : Path p x)
    (h_range : Set.range γ_chartSeg ⊆ (chartAt ℂ p).source)
    (h_lift_in_ball : ∀ t : unitInterval,
        (chartAt ℂ p) (γ_chartSeg t) ∈ Metric.ball ((chartAt ℂ p) p) r) :
    pathIntegralViaCover α γ_chartSeg = F ((chartAt ℂ p) x) - F ((chartAt ℂ p) p) :=
  pathIntegralViaCover_eq_primitive_diff_of_witnesses α r hr hr_subset hp hF γ_chartSeg
    h_range h_lift_in_ball (fun q => path_contDiffOn_obligation X γ_chartSeg q)

/-- **Inc E.2 — Chart-correct level FTC on a chart-ball.** A path
`γ : Path a b` whose range lies in `(chartAt ℂ p).source` and whose
chart-lift lies in `Metric.ball ((chartAt ℂ p) p) r`, paired with an
`IsChartContDiffPath` witness, has its chart-correct integral against
`α` equal to `F((c) b) - F((c) a)` for any primitive `F` of the
chart-pullback function on the ball.

This is the per-segment FTC at chart-correct level used by E.3 (the
per-simplex FTC for smooth simplices): for each segment of a uniform
chart partition, this lemma collapses the chart-correct contribution
to a primitive endpoint difference. The proof bridges
`pathIntegralViaChartCorrect (chartAt ℂ p) α γ` to `pathIntegralViaCover
α γ` via the n=1 case of `pathIntegralViaCoverWith_refinement_invariant'`
plus a chartLift-extend congruence on the subpath, then applies
`pathIntegralViaCover_eq_F_diff_in_ball`. -/
theorem pathIntegralViaChartCorrect_eq_F_diff_in_ball
    [StableChartAt ℂ X]
    (α : HolomorphicOneForm ℂ X) {p a b : X}
    (r : ℝ) (hr : 0 < r)
    (hr_subset : Metric.ball ((chartAt ℂ p) p) r ⊆ (chartAt ℂ p).target)
    {F : ℂ → ℂ}
    (hF : ∀ z ∈ Metric.ball ((chartAt ℂ p) p) r,
            HasDerivAt F (chartPullbackFun (chartAt ℂ p) α z) z)
    (γ : Path a b)
    (h_range : Set.range γ ⊆ (chartAt ℂ p).source)
    (h_lift_in_ball : ∀ t : unitInterval,
        (chartAt ℂ p) (γ t) ∈ Metric.ball ((chartAt ℂ p) p) r)
    (hγ : JacobianChallenge.TraceDegree.IsChartContDiffPath γ) :
    pathIntegralViaChartCorrect (chartAt ℂ p) α γ h_range
      = F ((chartAt ℂ p) b) - F ((chartAt ℂ p) a) := by
  have hcov_single : ∀ (i : Fin 1) (t : unitInterval),
      (i : ℝ) / ((1 : ℕ) : ℝ) ≤ (t : ℝ) →
      (t : ℝ) ≤ ((i : ℝ) + 1) / ((1 : ℕ) : ℝ) →
      γ t ∈ (chartAt ℂ p).source := by
    intros _ t _ _; exact h_range ⟨t, rfl⟩
  -- Step 1: bridge pathIntegralViaCover to pathIntegralViaCoverWith with n=1.
  have h_bridge :
      pathIntegralViaCover α γ =
        pathIntegralViaCoverWith α γ 1 (Nat.one_pos) (fun _ => p) hcov_single := by
    unfold pathIntegralViaCover
    exact pathIntegralViaCoverWith_refinement_invariant'
      α γ hγ _ _ _ _ 1 Nat.one_pos (fun _ => p) hcov_single
  -- Step 2: bridge pathIntegralViaCover to pathIntegralViaChartCorrect (via h_bridge +
  -- n=1 sum collapse + subpath-extend congruence on chartLift).
  have h_chart_eq :
      pathIntegralViaChartCorrect (chartAt ℂ p) α γ h_range
        = pathIntegralViaCover α γ := by
    rw [h_bridge]
    show pathIntegralViaChartCorrect (chartAt ℂ p) α γ h_range
        = ∑ i : Fin 1, pathIntegralViaChartCorrect (chartAt ℂ p) α
            (γ.subpath (divFinIcc 1 Nat.one_pos i.val (le_of_lt i.isLt))
                       (divFinIcc 1 Nat.one_pos (i.val + 1) i.isLt)) _
    rw [Fin.sum_univ_one]
    simp only [Fin.val_zero]
    -- Reduce to chartLift-extend congruence.
    unfold pathIntegralViaChartCorrect pathIntegralInChartCorrect
    rw [curveIntegral_def, curveIntegral_def]
    apply intervalIntegral.integral_congr
    intro t _
    rw [curveIntegralFun_def, curveIntegralFun_def]
    have h_pt : ∀ s : ℝ,
        (chartLift (chartAt ℂ p) (γ.subpath
            (divFinIcc 1 Nat.one_pos 0 (le_of_lt (0 : Fin 1).isLt))
            (divFinIcc 1 Nat.one_pos (0 + 1) (0 : Fin 1).isLt))
            (by intro y hy; rcases hy with ⟨t, rfl⟩; exact h_range ⟨_, rfl⟩)).extend s
        = (chartLift (chartAt ℂ p) γ h_range).extend s := fun s => by
      show (chartAt ℂ p) ((γ.subpath _ _).extend s)
          = (chartAt ℂ p) (γ.extend s)
      rw [show (γ.subpath
              (divFinIcc 1 Nat.one_pos 0 (le_of_lt (0 : Fin 1).isLt))
              (divFinIcc 1 Nat.one_pos (0 + 1) (0 : Fin 1).isLt)).extend s
            = γ.extend s from
            DFunLike.congr_fun (subpath_div_zero_one_extend γ) s]
    -- Use h_pt to rewrite the RHS (subpath) to the LHS (γ).
    rw [show ((chartLift (chartAt ℂ p) (γ.subpath
              (divFinIcc 1 Nat.one_pos 0 (le_of_lt (0 : Fin 1).isLt))
              (divFinIcc 1 Nat.one_pos (0 + 1) (0 : Fin 1).isLt))
              (by intro y hy; rcases hy with ⟨t, rfl⟩; exact h_range ⟨_, rfl⟩)).extend
            : ℝ → ℂ)
          = (chartLift (chartAt ℂ p) γ h_range).extend from funext h_pt]
  rw [h_chart_eq]
  exact pathIntegralViaCover_eq_F_diff_in_ball α r hr hr_subset hF γ
    h_range h_lift_in_ball hγ

end JacobianChallenge.Periods
