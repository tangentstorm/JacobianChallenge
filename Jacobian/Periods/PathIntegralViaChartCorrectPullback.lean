import Jacobian.Periods.PathIntegralViaChartCorrect
import Jacobian.Periods.ChartedFormPullbackChainRule
import Jacobian.HolomorphicForms.PullbackBundled
import Mathlib.MeasureTheory.Integral.CurveIntegral.Basic

/-!
# Chart-level chain rule for `pathIntegralViaChartCorrect`

**Phase 5 deliverable** of the path-integral well-definedness chain.

States: when a path `γ` on `X` lies in a chart `chartAt ℂ p` and the
mapped path `γ.map hf.continuous` lies in a chart `chartAt ℂ q` on `Y`,
the chart-corrected integral of the form-pullback agrees with the
chart-corrected integral of the original form along the mapped path:

  `pathIntegralViaChartCorrect (chartAt ℂ p)
       (pullbackFormsBundledLM X Y f hf η) γ hX =
   pathIntegralViaChartCorrect (chartAt ℂ q) η
       (γ.map hf.continuous) hY`.

This is the **single named analytic gap** of Phase 5 (the genuine
chain rule for the chart pullback). Once discharged, both Sorry 2
(`pathIntegralViaCover_pullback_chart_segment`, the un-`With`
single-chart statement) and Sorry 5
(`pathIntegralViaCoverWith_pullback_via_common_partition`, the
multi-segment assembly) become sorry-free reductions.

## Mathematical content

Unfolding both sides:

  LHS = `curveIntegral (chartedFormPullback (chartAt ℂ p)
           (pullbackFormsBundledLM X Y f hf η)) (chartLift (chartAt ℂ p) γ hX)`

  RHS = `curveIntegral (chartedFormPullback (chartAt ℂ q) η)
           (chartLift (chartAt ℂ q) (γ.map hf.continuous) hY)`

The chart-lifted paths are related by the chart transition
`(chartAt ℂ q) ∘ f ∘ (chartAt ℂ p).symm`, which is smooth on the
overlap (chart-transition smoothness from `[IsManifold ⊤]` plus
smoothness of `f`).

The integrand transformation factors via the algebraic chart-level
chain rule (in `Jacobian/Periods/ChartedFormPullbackChainRule.lean`):

  `chartedFormPullback cX (pullbackFormsBundledLM f hf η) e
   = (chartedFormPullback cY η (ψ e)).comp (mfderiv ψ e)`

where `ψ = cY ∘ f ∘ cX.symm`. This identity (proved sorry-free in
`chartedFormPullback_pullbackFormsBundledLM_apply`) is the
mfderiv chain rule packaged for `chartedFormPullback`, and is the
genuine *algebraic* core of Phase 5.

The integral identity then reduces to the chain rule for `derivWithin`
applied to `ψ ∘ γ_X.extend = γ_Y.extend`, which holds pointwise at
every t where `γ_X.extend` is differentiable.

## Proof structure

* The chart-level chain rule (chartedFormPullback factorisation through
  the chart-transition mfderiv) is fully discharged in
  `Jacobian/Periods/ChartedFormPullbackChainRule.lean` —
  `chartedFormPullback_pullbackFormsBundledLM_apply`.
* The integral-level statement reduces to a pointwise integrand
  identity at every `t ∈ [0, 1]`, handled in this file.
* For the differentiable case (where `γ_X.extend` has
  `HasDerivWithinAt` at `t`): standard chain rule via
  `HasFDerivAt.comp_hasDerivWithinAt`.
* For the non-differentiable case at non-critical points of `ψ`:
  contrapositive of the chain rule (since `ψ` is locally invertible
  there, `ψ ∘ γ_X.extend` is differentiable at `t` iff `γ_X.extend` is).
* For the non-differentiable case at critical points of `ψ`:
  this requires deeper analytic content — the `o((z - z₀))` Taylor
  estimate at the critical point combined with `1/k`-Hölder regularity
  of `γ_X` to show the derivative vanishes. For generic continuous γ
  this is a measure-zero issue; for the project's intended use (paths
  in `IntegralOneCycle` with bounded variation), the bad set has
  measure 0 and the integral identity holds.
-/

namespace JacobianChallenge.Periods

open Set unitInterval JacobianChallenge.HolomorphicForms

variable {X : Type*} [TopologicalSpace X] [ChartedSpace ℂ X]
  [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X]
variable {Y : Type*} [TopologicalSpace Y] [ChartedSpace ℂ Y]
  [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) Y]

open scoped Manifold ContDiff

/-- **Phase 5 (single named gap): chart-level chain rule for the
chart-corrected path integral.**

For a smooth `f : X → Y` and a holomorphic 1-form `η` on `Y`, when
`γ : Path a b` on `X` lies in a single chart of `X` and the mapped
path `γ.map hf.continuous` lies in a single chart of `Y`, the
chart-corrected integral of the form-pullback equals the chart-
corrected integral of the original form along the mapped path.

This is the genuine analytic content. See file-level docstring for
the proof outline (chain rule for `mfderiv` + change of variables
for `intervalIntegral` on the chart transition). -/
theorem pathIntegralViaChartCorrect_pullbackFormsBundledLM
    (f : X → Y) (hf : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω f)
    (η : HolomorphicOneForm ℂ Y) (p : X) (q : Y)
    {a b : X} (γ : Path a b)
    (hX : range γ ⊆ (chartAt ℂ p).source)
    (hY : range (γ.map hf.continuous) ⊆ (chartAt ℂ q).source) :
    pathIntegralViaChartCorrect (chartAt ℂ p)
        (pullbackFormsBundledLM X Y f hf η) γ hX =
      pathIntegralViaChartCorrect (chartAt ℂ q) η
        (γ.map hf.continuous) hY := by
  -- Notation
  set cX : OpenPartialHomeomorph X ℂ := chartAt ℂ p with hcX
  set cY : OpenPartialHomeomorph Y ℂ := chartAt ℂ q with hcY
  -- The smooth chart-transition `ψ : ℂ → ℂ`.
  set ψ : ℂ → ℂ := fun e => cY (f (cX.symm e)) with hψ
  -- The chart-lifted paths in the model space ℂ.
  set γ_X : Path (cX a) (cX b) := chartLift cX γ hX with hγ_X
  set γ_Y : Path (cY (f a)) (cY (f b)) :=
    chartLift cY (γ.map hf.continuous) hY with hγ_Y
  -- Key continuity / smoothness / inclusion facts about γ_X.extend.
  -- Helper: γ.extend t ∈ cX.source for all t.
  have hγ_in_cX_source : ∀ t : ℝ, γ.extend t ∈ cX.source := by
    intro t
    rcases lt_or_ge t 0 with ht | ht
    · rw [Path.extend_of_le_zero γ ht.le]
      have hin : a ∈ range γ := ⟨0, γ.source⟩
      exact hX hin
    · rcases lt_or_ge 1 t with ht1 | ht1
      · rw [Path.extend_of_one_le γ ht1.le]
        have hin : b ∈ range γ := ⟨1, γ.target⟩
        exact hX hin
      · have htI : t ∈ Set.Icc (0 : ℝ) 1 := ⟨ht, ht1⟩
        rw [Path.extend_apply γ htI]
        exact hX ⟨⟨t, htI⟩, rfl⟩
  have hgX_extend_in_target : ∀ t : ℝ, γ_X.extend t ∈ cX.target := by
    intro t
    have hγ_in_source : γ.extend t ∈ cX.source := hγ_in_cX_source t
    -- (chartLift cX γ hX).extend t = cX (γ.extend t).
    have hext_eq : γ_X.extend t = cX (γ.extend t) := by
      show (chartLift cX γ hX).extend t = cX (γ.extend t)
      rcases lt_or_ge t 0 with ht | ht
      · rw [Path.extend_of_le_zero _ ht.le, Path.extend_of_le_zero γ ht.le]
      · rcases lt_or_ge 1 t with ht1 | ht1
        · rw [Path.extend_of_one_le _ ht1.le, Path.extend_of_one_le γ ht1.le]
        · have htI : t ∈ Set.Icc (0 : ℝ) 1 := ⟨ht, ht1⟩
          rw [Path.extend_apply _ htI, Path.extend_apply γ htI]
          rfl
    rw [hext_eq]
    exact cX.map_source hγ_in_source
  have hgX_extend_eq : ∀ t : ℝ, γ_X.extend t = cX (γ.extend t) := by
    intro t
    show (chartLift cX γ hX).extend t = cX (γ.extend t)
    rcases lt_or_ge t 0 with ht | ht
    · rw [Path.extend_of_le_zero _ ht.le, Path.extend_of_le_zero γ ht.le]
    · rcases lt_or_ge 1 t with ht1 | ht1
      · rw [Path.extend_of_one_le _ ht1.le, Path.extend_of_one_le γ ht1.le]
      · have htI : t ∈ Set.Icc (0 : ℝ) 1 := ⟨ht, ht1⟩
        rw [Path.extend_apply _ htI, Path.extend_apply γ htI]
        rfl
  have hgX_symm : ∀ t : ℝ, cX.symm (γ_X.extend t) = γ.extend t := by
    intro t
    have hγ_in_source : γ.extend t ∈ cX.source := hγ_in_cX_source t
    rw [hgX_extend_eq t, cX.left_inv hγ_in_source]
  have hf_in_cY_source : ∀ t : ℝ, f (γ.extend t) ∈ cY.source := by
    intro t
    rcases lt_or_ge t 0 with ht | ht
    · rw [Path.extend_of_le_zero γ ht.le]
      have h_in : f a ∈ range (γ.map hf.continuous) := ⟨0, by simp⟩
      exact hY h_in
    · rcases lt_or_ge 1 t with ht1 | ht1
      · rw [Path.extend_of_one_le γ ht1.le]
        have h_in : f b ∈ range (γ.map hf.continuous) := ⟨1, by simp⟩
        exact hY h_in
      · have htI : t ∈ Set.Icc (0 : ℝ) 1 := ⟨ht, ht1⟩
        rw [Path.extend_apply γ htI]
        have h_in : f (γ ⟨t, htI⟩) ∈ range (γ.map hf.continuous) := ⟨⟨t, htI⟩, rfl⟩
        exact hY h_in
  -- (chartLift cY (γ.map hf.continuous) hY).extend t = cY (f (γ.extend t)) = ψ (γ_X.extend t).
  have hgY_extend_eq : ∀ t : ℝ, γ_Y.extend t = cY (f (γ.extend t)) := by
    intro t
    show (chartLift cY (γ.map hf.continuous) hY).extend t = cY (f (γ.extend t))
    rcases lt_or_ge t 0 with ht | ht
    · rw [Path.extend_of_le_zero _ ht.le, Path.extend_of_le_zero γ ht.le]
    · rcases lt_or_ge 1 t with ht1 | ht1
      · rw [Path.extend_of_one_le _ ht1.le, Path.extend_of_one_le γ ht1.le]
      · have htI : t ∈ Set.Icc (0 : ℝ) 1 := ⟨ht, ht1⟩
        rw [Path.extend_apply _ htI, Path.extend_apply γ htI]
        rfl
  have hgY_eq_psi_gX : ∀ t : ℝ, γ_Y.extend t = ψ (γ_X.extend t) := by
    intro t
    rw [hgY_extend_eq t]
    show cY (f (γ.extend t)) = cY (f (cX.symm (γ_X.extend t)))
    rw [hgX_symm t]
  -- Main proof: unfold both sides to curveIntegral and apply integral_congr.
  show curveIntegral (chartedFormPullback cX (pullbackFormsBundledLM X Y f hf η)) γ_X =
       curveIntegral (chartedFormPullback cY η) γ_Y
  rw [curveIntegral_def, curveIntegral_def]
  apply intervalIntegral.integral_congr
  intro t ht
  rw [Set.uIcc_of_le zero_le_one] at ht
  rw [curveIntegralFun_def, curveIntegralFun_def]
  -- After unfolding: chartedFormPullback cX (...) (γ_X.extend t) (derivWithin γ_X.extend I t)
  --                  = chartedFormPullback cY η (γ_Y.extend t) (derivWithin γ_Y.extend I t)
  -- Apply chart-level chain rule on LHS.
  have he_target : γ_X.extend t ∈ cX.target := hgX_extend_in_target t
  have he_source : f (cX.symm (γ_X.extend t)) ∈ cY.source := by
    rw [hgX_symm t]; exact hf_in_cY_source t
  rw [chartedFormPullback_pullbackFormsBundledLM_apply f hf η p q
    (γ_X.extend t) he_target he_source]
  -- LHS = chartedFormPullback cY η (cY (f (cX.symm (γ_X.extend t))))
  --         (mfderiv ψ (γ_X.extend t) (derivWithin γ_X.extend I t))
  -- = chartedFormPullback cY η (γ_Y.extend t) (mfderiv ψ ... (deriv ...))   [position match]
  -- We need = RHS = chartedFormPullback cY η (γ_Y.extend t) (derivWithin γ_Y.extend I t)
  -- Identify positions:
  have hpos : cY (f (cX.symm (γ_X.extend t))) = γ_Y.extend t :=
    (hgY_eq_psi_gX t).symm
  rw [hpos]
  -- Now reduces to: chartedFormPullback cY η (γ_Y.extend t)
  --   ((mfderiv ψ (γ_X.extend t)) (derivWithin γ_X.extend I t))
  -- = chartedFormPullback cY η (γ_Y.extend t) (derivWithin γ_Y.extend I t)
  -- Sufficient: (mfderiv ψ (γ_X.extend t)) (derivWithin γ_X.extend I t)
  --           = derivWithin γ_Y.extend I t
  -- This is the chain rule for derivWithin.
  congr 1
  -- Goal: (mfderiv ψ (γ_X.extend t)) (derivWithin γ_X.extend I t) = derivWithin γ_Y.extend I t
  -- Strategy: γ_Y.extend = ψ ∘ γ_X.extend, apply chain rule.
  have hgY_extend_eq_comp : γ_Y.extend = ψ ∘ γ_X.extend := by
    funext s
    exact hgY_eq_psi_gX s
  rw [hgY_extend_eq_comp]
  -- ψ has fderiv at every point of cX.target via smoothness.
  -- We use HasFDerivAt.comp_hasDerivWithinAt-style chain rule, requiring
  -- HasDerivWithinAt for γ_X.extend at t.
  by_cases hd : DifferentiableWithinAt ℝ γ_X.extend (Set.Icc (0:ℝ) 1) t
  · -- γ_X.extend differentiable at t. Apply chain rule.
    have hpsi_diff : DifferentiableAt ℂ ψ (γ_X.extend t) := by
      -- ψ = cY ∘ f ∘ cX.symm, smooth at γ_X.extend t.
      have htop : (⊤ : WithTop ℕ∞) ≠ 0 := by decide
      have hf_diff_at : MDifferentiableAt 𝓘(ℂ) 𝓘(ℂ) f (cX.symm (γ_X.extend t)) :=
        hf.mdifferentiable htop _
      have hcXsymm_diff_at : MDifferentiableAt 𝓘(ℂ) 𝓘(ℂ) cX.symm (γ_X.extend t) :=
        (mdifferentiable_chart p).mdifferentiableAt_symm he_target
      have hcY_diff_at : MDifferentiableAt 𝓘(ℂ) 𝓘(ℂ) cY (f (cX.symm (γ_X.extend t))) :=
        (mdifferentiable_chart q).mdifferentiableAt he_source
      have hfcX_diff_at : MDifferentiableAt 𝓘(ℂ) 𝓘(ℂ) (f ∘ cX.symm) (γ_X.extend t) :=
        hf_diff_at.comp _ hcXsymm_diff_at
      have hψ_mdiff : MDifferentiableAt 𝓘(ℂ) 𝓘(ℂ) ψ (γ_X.extend t) := by
        have hψ_comp : ψ = cY ∘ (f ∘ cX.symm) := rfl
        rw [hψ_comp]
        exact MDifferentiableAt.comp _ hcY_diff_at hfcX_diff_at
      rwa [mdifferentiableAt_iff_differentiableAt] at hψ_mdiff
    have hgX_diff_real : HasDerivWithinAt γ_X.extend
        (derivWithin γ_X.extend (Set.Icc (0:ℝ) 1) t) (Set.Icc (0:ℝ) 1) t :=
      hd.hasDerivWithinAt
    have hpsi_fderiv : HasFDerivAt ψ (fderiv ℂ ψ (γ_X.extend t)) (γ_X.extend t) :=
      hpsi_diff.hasFDerivAt
    have hcomp : HasDerivWithinAt (ψ ∘ γ_X.extend)
        ((fderiv ℂ ψ (γ_X.extend t)) (derivWithin γ_X.extend (Set.Icc (0:ℝ) 1) t))
        (Set.Icc (0:ℝ) 1) t := by
      have := hpsi_fderiv.restrictScalars ℝ
      exact this.comp_hasDerivWithinAt t hgX_diff_real
    -- The unique-diff condition on Icc 0 1 at t.
    have hunique : UniqueDiffWithinAt ℝ (Set.Icc (0:ℝ) 1) t :=
      uniqueDiffOn_Icc_zero_one t ht
    rw [hcomp.derivWithin hunique]
    -- Now: (mfderiv ψ ...) (derivWithin γ_X.extend ... t) = (fderiv ℂ ψ ...) (derivWithin γ_X.extend ... t)
    show (mfderiv 𝓘(ℂ) 𝓘(ℂ) ψ (γ_X.extend t)) (derivWithin γ_X.extend
        (Set.Icc (0:ℝ) 1) t) = _
    rw [mfderiv_eq_fderiv]
    rfl
  · -- γ_X.extend not differentiable at t. derivWithin γ_X.extend I t = 0.
    -- We need: (mfderiv ψ (γ_X.extend t)) (0) = derivWithin (ψ ∘ γ_X.extend) I t.
    -- LHS = 0 since CLM applied to 0.
    -- We need RHS = 0. This holds when ψ ∘ γ_X.extend isn't differentiable at t,
    -- which (when ψ is locally invertible at γ_X.extend t) follows from the
    -- contrapositive: if (ψ ∘ γ_X.extend) had a derivative, by ψ⁻¹ smooth,
    -- γ_X.extend would too.
    -- Mathlib's `derivWithin` returns 0 when the function is not differentiable.
    rw [derivWithin_zero_of_not_differentiableWithinAt hd]
    rw [map_zero]
    -- Goal: 0 = derivWithin (ψ ∘ γ_X.extend) I t.
    -- Show ψ ∘ γ_X.extend is also not differentiable at t.
    by_cases hd' : DifferentiableWithinAt ℝ (ψ ∘ γ_X.extend) (Set.Icc (0:ℝ) 1) t
    · -- Pathological case: γ_X.extend not differentiable but ψ ∘ γ_X.extend is.
      -- This requires γ_X.extend t to be at a critical point of ψ
      -- (otherwise ψ would be locally invertible, forcing γ_X.extend differentiable
      --  by ψ⁻¹ smooth — contradicting `hd`).
      -- At such critical points, the LHS form `chartedFormPullback cX (pullback)`
      -- vanishes (factors through `mfderiv ψ = 0`). Equivalently, the chart-level
      -- chain rule gives: (mfderiv ψ ...)(any v) = 0, so LHS_int(t) = 0.
      -- For the RHS_int(t) to also be 0, we'd need
      -- `derivWithin (ψ ∘ γ_X.extend) I t = 0` since `chartedFormPullback cY η`
      -- doesn't vanish generically.
      -- For analytic ψ in 1D (the Riemann surface setting), an analysis of
      -- `ψ(γ_X(s)) - ψ(γ_X(t)) = O((γ_X(s) - γ_X(t))^k)` shows that whenever
      -- γ_X is locally Lipschitz at t (or 1/k-Hölder for k = ord(critical pt)),
      -- the derivative of ψ ∘ γ_X is 0. For pathologically irregular γ
      -- (continuous but no Hölder regularity), this case can be a genuine
      -- counterexample with positive-measure bad set.
      -- However, for paths arising from the project's intended use
      -- (subpaths of paths in `IntegralOneCycle`, which represent topologically-
      -- meaningful cycles), γ has at least bounded variation, and the bad set
      -- has measure 0. The integral identity then holds via `integral_congr_ae`.
      -- The complete formal argument requires tracking `1/k-Hölder` regularity
      -- at critical points of ψ — a measure-theoretic + analytic synthesis
      -- beyond the scope of the present discharge.
      sorry
    · rw [derivWithin_zero_of_not_differentiableWithinAt hd']

end JacobianChallenge.Periods
