import Jacobian.Periods.PathIntegralViaCoverWithRefine
import Jacobian.Periods.ChartedFormPullbackChartChange
import Jacobian.Periods.ChartedFormPullbackCurveIntegrable
import Jacobian.Periods.TrivializationContinuousLinearMapAt
import Mathlib.Geometry.Manifold.MFDeriv.FDeriv
import Mathlib.Analysis.Calculus.FDeriv.RestrictScalars

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
level** (Phase 4a, discharged below): for the same path
segment lying in both `(chartAt E p).source` and `(chartAt E q).source`,
the chart-corrected integrals agree:

  `pathIntegralViaChartCorrect (chartAt E p) ω γ h_p =
   pathIntegralViaChartCorrect (chartAt E q) ω γ h_q`.

Mathematical content: chain rule for `mfderiv` applied to the chart
transition `(chartAt E q) ∘ (chartAt E p).symm`, which is smooth on
the overlap by the `[IsManifold ⊤]` instance. Combined with a chain
rule for `derivWithin` on path lifts.

## Status

- `pathIntegralViaChartCorrect_chart_change`: **discharged** (no sorry).
- `pathIntegralViaCoverWith_refinement_invariant'`: the refinement
  invariance theorem, now sorry-free given Phase 3 + Phase 4a (requires
  C¹ regularity for integrability).
-/

namespace JacobianChallenge.Periods

open Set unitInterval JacobianChallenge.HolomorphicForms

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  {X : Type*} [TopologicalSpace X] [ChartedSpace E X]
  [IsManifold (modelWithCornersSelf ℂ E) (⊤ : WithTop ℕ∞) X]

/-! ### Helpers for the chart-change theorem -/

omit [IsManifold (modelWithCornersSelf ℂ E) ⊤ X] in
/-- The extend of a `chartLift c γ h` factors as `c ∘ γ.extend` (definitionally). -/
private lemma chartLift_extend_eq
    (c : OpenPartialHomeomorph X E)
    {a b : X} (γ : Path a b) (h : range γ ⊆ c.source) :
    (chartLift c γ h).extend = (c : X → E) ∘ γ.extend := rfl

/-- The path-extension `γ.extend t` lies in `range γ` for any `t : ℝ`. -/
private lemma extend_mem_range
    {a b : X} (γ : Path a b) (t : ℝ) :
    γ.extend t ∈ range γ := by
  rw [← Path.extend_range γ]
  exact ⟨t, rfl⟩

omit [NormedSpace ℂ E] [IsManifold (modelWithCornersSelf ℂ E) ⊤ X] in
/-- Under chart change, the local equality `(chartAt E q) ∘ γ.extend
=ᶠ[𝓝 t] ((chartAt E q) ∘ (chartAt E p).symm) ∘ ((chartAt E p) ∘ γ.extend)` holds
on the open set where `γ.extend` stays in both chart sources. -/
private lemma chart_compose_eventuallyEq
    (p q : X) {a b : X} (γ : Path a b)
    (hp : range γ ⊆ (chartAt E p).source) (_hq : range γ ⊆ (chartAt E q).source)
    (t : ℝ) :
    ((chartAt E q : X → E) ∘ γ.extend) =ᶠ[nhds t]
      (((chartAt E q : X → E) ∘ ((chartAt E p).symm : E → X)) ∘
        ((chartAt E p : X → E) ∘ γ.extend)) := by
  -- The path γ has range in both chart sources, so γ.extend stays in
  -- the open intersection (chartAt E p).source ∩ (chartAt E q).source.
  have h_subset : ∀ s : ℝ, γ.extend s ∈ (chartAt E p).source := by
    intro s
    have : γ.extend s ∈ range γ.extend := mem_range_self s
    rw [Path.extend_range] at this
    exact hp this
  have h_open : IsOpen ((chartAt E p).source) := (chartAt E p).open_source
  have h_pre_open : IsOpen (γ.extend ⁻¹' (chartAt E p).source) :=
    h_open.preimage γ.continuous_extend
  have h_pre_mem : t ∈ γ.extend ⁻¹' (chartAt E p).source := h_subset t
  refine Filter.eventually_of_mem (h_pre_open.mem_nhds h_pre_mem) ?_
  intro s hs
  show (chartAt E q) (γ.extend s) =
    (chartAt E q) ((chartAt E p).symm ((chartAt E p) (γ.extend s)))
  rw [(chartAt E p).left_inv hs]

/-- The chart transition `(chartAt E q) ∘ (chartAt E p).symm` has a
Fréchet derivative at every point `(chartAt E p) x` for
`x ∈ (chartAt E p).source ∩ (chartAt E q).source`. The derivative
agrees with `mfderiv` of the same composition. -/
private lemma chartTransition_hasFDerivAt
    (p q : X) (x : X)
    (hp : x ∈ (chartAt E p).source) (hq : x ∈ (chartAt E q).source) :
    HasFDerivAt ((chartAt E q : X → E) ∘ ((chartAt E p).symm : E → X))
      (mfderiv (modelWithCornersSelf ℂ E) (modelWithCornersSelf ℂ E)
        ((chartAt E q : X → E) ∘ ((chartAt E p).symm : E → X)) ((chartAt E p) x))
      ((chartAt E p) x) := by
  have h_mdiff : MDifferentiableAt (modelWithCornersSelf ℂ E)
      (modelWithCornersSelf ℂ E)
      ((chartAt E q : X → E) ∘ ((chartAt E p).symm : E → X))
      ((chartAt E p) x) :=
    chartTransition_mdifferentiableAt p q x hp hq
  -- Convert MDifferentiableAt (with trivial models on E → E) to DifferentiableAt over ℂ:
  have h_diff_C : DifferentiableAt ℂ
      ((chartAt E q : X → E) ∘ ((chartAt E p).symm : E → X)) ((chartAt E p) x) := by
    rw [mdifferentiableAt_iff_differentiableAt] at h_mdiff
    exact h_mdiff
  -- The HasFDerivAt of the ℂ-fderiv:
  have h_hf : HasFDerivAt
      ((chartAt E q : X → E) ∘ ((chartAt E p).symm : E → X))
      (fderiv ℂ ((chartAt E q : X → E) ∘ ((chartAt E p).symm : E → X)) ((chartAt E p) x))
      ((chartAt E p) x) := h_diff_C.hasFDerivAt
  -- Identify mfderiv with fderiv ℂ (both source and target are vector spaces):
  rw [show mfderiv (modelWithCornersSelf ℂ E) (modelWithCornersSelf ℂ E)
        ((chartAt E q : X → E) ∘ ((chartAt E p).symm : E → X)) ((chartAt E p) x) =
      fderiv ℂ ((chartAt E q : X → E) ∘ ((chartAt E p).symm : E → X))
        ((chartAt E p) x) from mfderiv_eq_fderiv]
  exact h_hf

/-- **Lemma B (chart-transition chain rule for `derivWithin`).** For a
path γ with range in both `(chartAt E p).source` and `(chartAt E q).source`,
and `t ∈ Icc 0 1`, the derivWithin of the q-chart-lifted path equals
the chart-transition derivative applied to the derivWithin of the
p-chart-lifted path.

The proof case-splits on whether `(chartAt E p) ∘ γ.extend` is
differentiable within `Icc 0 1` at `t`. In the differentiable case,
it's a direct chain rule. In the non-differentiable case, the
`(chartAt E q) ∘ γ.extend` is also non-differentiable (transferred
back via the inverse chart transition), so both `derivWithin`s are 0. -/
private lemma derivWithin_chart_transition_chain_rule
    (p q : X) {a b : X} (γ : Path a b)
    (hp : range γ ⊆ (chartAt E p).source) (hq : range γ ⊆ (chartAt E q).source)
    (t : ℝ) (ht : t ∈ Set.Icc (0:ℝ) 1) :
    derivWithin ((chartAt E q : X → E) ∘ γ.extend) (Set.Icc (0:ℝ) 1) t =
      (mfderiv (modelWithCornersSelf ℂ E) (modelWithCornersSelf ℂ E)
        ((chartAt E q : X → E) ∘ ((chartAt E p).symm : E → X)))
        ((chartAt E p) (γ.extend t))
        (derivWithin ((chartAt E p : X → E) ∘ γ.extend) (Set.Icc (0:ℝ) 1) t) := by
  -- Setup notations
  set f_p : ℝ → E := (chartAt E p : X → E) ∘ γ.extend with hf_p
  set f_q : ℝ → E := (chartAt E q : X → E) ∘ γ.extend with hf_q
  set ψ : E → E := (chartAt E q : X → E) ∘ ((chartAt E p).symm : E → X) with hψ
  set ψ_inv : E → E := (chartAt E p : X → E) ∘ ((chartAt E q).symm : E → X) with hψ_inv
  set s : Set ℝ := Set.Icc (0:ℝ) 1
  -- γ.extend t is in the overlap because range γ ⊆ both chart sources
  have hγt_p : γ.extend t ∈ (chartAt E p).source :=
    hp (extend_mem_range γ t)
  have hγt_q : γ.extend t ∈ (chartAt E q).source :=
    hq (extend_mem_range γ t)
  -- ψ has FDerivAt at f_p t = (chartAt E p) (γ.extend t):
  have h_ψ_fderiv : HasFDerivAt ψ
      (mfderiv (modelWithCornersSelf ℂ E) (modelWithCornersSelf ℂ E) ψ
        ((chartAt E p) (γ.extend t)))
      ((chartAt E p) (γ.extend t)) :=
    chartTransition_hasFDerivAt p q (γ.extend t) hγt_p hγt_q
  -- ψ_inv has FDerivAt at f_q t = (chartAt E q) (γ.extend t):
  have h_ψ_inv_fderiv : HasFDerivAt ψ_inv
      (mfderiv (modelWithCornersSelf ℂ E) (modelWithCornersSelf ℂ E) ψ_inv
        ((chartAt E q) (γ.extend t)))
      ((chartAt E q) (γ.extend t)) :=
    chartTransition_hasFDerivAt q p (γ.extend t) hγt_q hγt_p
  -- f_q =ᶠ[𝓝 t] ψ ∘ f_p (locally near t)
  have h_eq_ψfp : f_q =ᶠ[nhds t] ψ ∘ f_p :=
    chart_compose_eventuallyEq p q γ hp hq t
  -- f_p =ᶠ[𝓝 t] ψ_inv ∘ f_q (locally near t)
  have h_eq_ψinvfq : f_p =ᶠ[nhds t] ψ_inv ∘ f_q :=
    chart_compose_eventuallyEq q p γ hq hp t
  -- Case split on differentiability of f_p:
  by_cases h_diff : DifferentiableWithinAt ℝ f_p s t
  · -- Differentiable case: direct chain rule
    have h_fp_hasDeriv : HasDerivWithinAt f_p (derivWithin f_p s t) s t :=
      h_diff.hasDerivWithinAt
    -- Restrict ψ's fderiv to ℝ:
    have h_ψ_fderiv_R : HasFDerivAt ψ
        ((mfderiv (modelWithCornersSelf ℂ E) (modelWithCornersSelf ℂ E) ψ
          ((chartAt E p) (γ.extend t))).restrictScalars ℝ)
        ((chartAt E p) (γ.extend t)) :=
      h_ψ_fderiv.restrictScalars ℝ
    -- Apply chain rule:
    have h_comp : HasDerivWithinAt (ψ ∘ f_p)
        ((mfderiv (modelWithCornersSelf ℂ E) (modelWithCornersSelf ℂ E) ψ
          ((chartAt E p) (γ.extend t))) (derivWithin f_p s t)) s t := by
      have := h_ψ_fderiv_R.comp_hasDerivWithinAt t h_fp_hasDeriv
      -- this : HasDerivWithinAt (ψ ∘ f_p)
      --   ((... .restrictScalars ℝ) (derivWithin f_p s t)) s t
      -- The restrictScalars application equals the original application as a value
      convert this using 1
    -- Transfer to f_q via eventually equality:
    have h_fq_hasDeriv : HasDerivWithinAt f_q
        ((mfderiv (modelWithCornersSelf ℂ E) (modelWithCornersSelf ℂ E) ψ
          ((chartAt E p) (γ.extend t))) (derivWithin f_p s t)) s t := by
      apply h_comp.congr_of_eventuallyEq
      · exact h_eq_ψfp.filter_mono nhdsWithin_le_nhds
      · exact h_eq_ψfp.self_of_nhds
    -- Take derivWithin:
    rw [h_fq_hasDeriv.derivWithin (uniqueDiffOn_Icc_zero_one t ht)]
  · -- Non-differentiable case: both derivWithin values are 0
    have h_fp_zero : derivWithin f_p s t = 0 :=
      derivWithin_zero_of_not_differentiableWithinAt h_diff
    -- Show f_q is also non-differentiable at t (within s).
    have h_fq_not_diff : ¬ DifferentiableWithinAt ℝ f_q s t := by
      intro h_fq_diff
      apply h_diff
      -- f_p =ᶠ[𝓝 t] ψ_inv ∘ f_q, so DifferentiableWithinAt f_p s t follows from
      -- DifferentiableWithinAt (ψ_inv ∘ f_q) s t.
      -- Use chain rule with ψ_inv smooth at f_q t.
      have h_fq_hd : HasDerivWithinAt f_q (derivWithin f_q s t) s t :=
        h_fq_diff.hasDerivWithinAt
      have h_ψinv_R : HasFDerivAt ψ_inv
          ((mfderiv (modelWithCornersSelf ℂ E) (modelWithCornersSelf ℂ E) ψ_inv
            ((chartAt E q) (γ.extend t))).restrictScalars ℝ)
          ((chartAt E q) (γ.extend t)) :=
        h_ψ_inv_fderiv.restrictScalars ℝ
      have h_psi_inv_fq : HasDerivWithinAt (ψ_inv ∘ f_q)
          ((mfderiv (modelWithCornersSelf ℂ E) (modelWithCornersSelf ℂ E) ψ_inv
            ((chartAt E q) (γ.extend t))) (derivWithin f_q s t)) s t := by
        have := h_ψinv_R.comp_hasDerivWithinAt t h_fq_hd
        convert this using 1
      -- f_p =ᶠ[𝓝 t] ψ_inv ∘ f_q gives f_p has same derivative at t.
      have h_fp_hd : HasDerivWithinAt f_p
          ((mfderiv (modelWithCornersSelf ℂ E) (modelWithCornersSelf ℂ E) ψ_inv
            ((chartAt E q) (γ.extend t))) (derivWithin f_q s t)) s t := by
        apply h_psi_inv_fq.congr_of_eventuallyEq
        · exact h_eq_ψinvfq.filter_mono nhdsWithin_le_nhds
        · exact h_eq_ψinvfq.self_of_nhds
      exact h_fp_hd.differentiableWithinAt
    have h_fq_zero : derivWithin f_q s t = 0 :=
      derivWithin_zero_of_not_differentiableWithinAt h_fq_not_diff
    rw [h_fq_zero, h_fp_zero, ContinuousLinearMap.map_zero]

/-- **Phase 4a: chart-change invariance.**
For a path `γ` whose range lies in *two* chart sources
`(chartAt E p).source` and `(chartAt E q).source` simultaneously,
the chart-corrected integrals via either chart agree.

Proof: unfold both sides to `curveIntegral` of the chart-pullback,
then to interval integrals. Pointwise, the integrands agree:
the chart-pullbacks are related by `chartedFormPullback_chart_change_apply`,
and the chart-lifted derivatives by `derivWithin_chart_transition_chain_rule`. -/
theorem pathIntegralViaChartCorrect_chart_change
    (ω : HolomorphicOneForm E X) (p q : X)
    {a b : X} (γ : Path a b)
    (hp : range γ ⊆ (chartAt E p).source)
    (hq : range γ ⊆ (chartAt E q).source) :
    pathIntegralViaChartCorrect (chartAt E p) ω γ hp =
      pathIntegralViaChartCorrect (chartAt E q) ω γ hq := by
  -- Both sides are curveIntegral of chartedFormPullback
  show curveIntegral (chartedFormPullback (chartAt E p) ω) (chartLift (chartAt E p) γ hp) =
       curveIntegral (chartedFormPullback (chartAt E q) ω) (chartLift (chartAt E q) γ hq)
  rw [curveIntegral_def, curveIntegral_def]
  apply intervalIntegral.integral_congr
  intro t ht
  rw [Set.uIcc_of_le zero_le_one] at ht
  -- ht : t ∈ Set.Icc 0 1
  rw [curveIntegralFun_def, curveIntegralFun_def]
  -- Goal: chartedFormPullback (chartAt E p) ω ((chartLift (chartAt E p) γ hp).extend t)
  --         (derivWithin (chartLift (chartAt E p) γ hp).extend (Set.Icc 0 1) t) =
  --       chartedFormPullback (chartAt E q) ω ((chartLift (chartAt E q) γ hq).extend t)
  --         (derivWithin (chartLift (chartAt E q) γ hq).extend (Set.Icc 0 1) t)
  -- (chartLift c γ h).extend t = c (γ.extend t) and (chartLift c γ h).extend = c ∘ γ.extend
  -- Since these are definitionally equal, we can rewrite via show:
  show chartedFormPullback (chartAt E p) ω ((chartAt E p) (γ.extend t))
        (derivWithin ((chartAt E p : X → E) ∘ γ.extend) (Set.Icc 0 1) t) =
       chartedFormPullback (chartAt E q) ω ((chartAt E q) (γ.extend t))
        (derivWithin ((chartAt E q : X → E) ∘ γ.extend) (Set.Icc 0 1) t)
  -- Apply Lemma B to relate the derivWithins:
  rw [derivWithin_chart_transition_chain_rule p q γ hp hq t ht]
  -- Now LHS: chartedFormPullback (chartAt E p) ω (chartAt E p (γ.extend t)) (derivWithin (c_p ∘ γ.extend) ... t)
  --   = chartedFormPullback (chartAt E p) ω (chartAt E p (γ.extend t)) v_p
  -- RHS: chartedFormPullback (chartAt E q) ω (chartAt E q (γ.extend t))
  --        (mfderiv ψ (c_p (γ.extend t)) v_p)
  -- where v_p = derivWithin (chartAt E p ∘ γ.extend) ... t
  -- Apply Lemma A (chartedFormPullback chain rule):
  -- have : γ.extend t ∈ (chartAt E p).source ∩ (chartAt E q).source := ...
  have hγt_p : γ.extend t ∈ (chartAt E p).source :=
    hp (extend_mem_range γ t)
  have hγt_q : γ.extend t ∈ (chartAt E q).source :=
    hq (extend_mem_range γ t)
  exact chartedFormPullback_chart_change_apply p q ω (γ.extend t) _ hγt_p hγt_q

/-- **Phase 4 deliverable.** Refinement invariance of
`pathIntegralViaCoverWith`: any two valid uniform chart partitions
of the same path yield the same value.

Requires `[StableChartAt]` and `C¹` regularity for the path to
discharge the integrability obligations of Phase 3 (refinement by
multiple).

Sorry-free reduction to:
* `pathIntegralViaCoverWith_refine_to_multiple` (Phase 3, in
  `PathIntegralViaCoverWithRefine.lean`),
* `pathIntegralViaChartCorrect_chart_change` (Phase 4a, above). -/
theorem pathIntegralViaCoverWith_refinement_invariant'
    [StableChartAt (modelWithCornersSelf ℂ E) X]
    (ω : HolomorphicOneForm E X) {a b : X} (γ : Path a b)
    (hγ : ContDiffOn ℝ 1 γ.extend (Set.Icc 0 1))
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
  -- Common multiple size
  set hnn' := Nat.mul_pos hn hn'
  -- 1. Helper: refinement of cover property to n * n'
  have hcov_refined : ∀ (n k : ℕ) (hn : 0 < n) (hk : 0 < k)
      (pick : Fin n → X)
      (h : ∀ (i : Fin n) (t : unitInterval),
        (i : ℝ) / n ≤ (t : ℝ) → (t : ℝ) ≤ ((i : ℝ) + 1) / n →
        γ t ∈ (chartAt E (pick i)).source),
      ∀ (j : Fin (n * k)) (t : unitInterval),
        (j : ℝ) / (n * k) ≤ (t : ℝ) → (t : ℝ) ≤ ((j : ℝ) + 1) / (n * k) →
        γ t ∈ (chartAt E (pick ⟨j.val / k, (Nat.div_lt_iff_lt_mul hk).mpr j.isLt⟩)).source := by
    intro n_ k_ hn_ hk_ pick_ h_ j t ht1 ht2
    set i := j.val / k
    have hi : i < n_ := (Nat.div_lt_iff_lt_mul hk_).mpr j.isLt
    apply h_ ⟨i, hi⟩ t
    · calc (i : ℝ) / n_ = (i * k_ : ℝ) / (n_ * k_) := by
        rw [Nat.cast_mul, div_mul_div_cancel_right₀]
        · exact Nat.cast_ne_zero.mpr hk_.ne'
        · exact Nat.cast_ne_zero.mpr hn_.ne'
      _ ≤ (j.val : ℝ) / (n_ * k_) := by
        gcongr
        exact_mod_cast Nat.div_mul_le_self j.val k_
      _ ≤ t := ht1
    · calc (t : ℝ) ≤ ((j : ℝ) + 1) / (n_ * k_) := ht2
      _ ≤ ((i + 1) * k_ : ℝ) / (n_ * k_) := by
        gcongr
        show (j.val : ℕ) + 1 ≤ (j.val / k_ + 1) * k_
        exact Nat.succ_le_of_lt ((Nat.div_lt_iff_lt_mul hk_).mp (Nat.lt_succ_self _))
      _ = (i + 1 : ℝ) / n_ := by
        rw [Nat.cast_mul, div_mul_div_cancel_right₀]
        · exact Nat.cast_ne_zero.mpr hk_.ne'
        · exact Nat.cast_ne_zero.mpr hn_.ne'
  -- 2. Helper: integrability of refined segments from C¹ hypothesis
  have hint_refined : ∀ (n_ : ℕ) (hn_ : 0 < n_) (pick_ : Fin n_ → X)
      (h_ : ∀ (i : Fin n_) (t : unitInterval),
        (i : ℝ) / n_ ≤ (t : ℝ) → (t : ℝ) ≤ ((i : ℝ) + 1) / n_ →
        γ t ∈ (chartAt E (pick_ i)).source),
      ∀ i : Fin n_, IntervalIntegrable
        (fun t => (chartedFormPullback (chartAt E (pick_ i)) ω)
          ((chartLift (chartAt E (pick_ i))
            (γ.subpath (divFinIcc n_ hn_ i.val (le_of_lt i.isLt))
                       (divFinIcc n_ hn_ (i.val + 1) i.isLt))
            (range_segment_subset_source_of_hcov γ n_ hn_ pick_ h_ i)).extend t)
          (derivWithin (chartLift (chartAt E (pick_ i))
            (γ.subpath (divFinIcc n_ hn_ i.val (le_of_lt i.isLt))
                       (divFinIcc n_ hn_ (i.val + 1) i.isLt))
            (range_segment_subset_source_of_hcov γ n_ hn_ pick_ h_ i)).extend
            (Set.Icc 0 1) t))
        volume 0 1 := by
    intro n_ hn_ pick_ h_ i
    set c := chartAt E (pick_ i)
    set γ_i := γ.subpath (divFinIcc n_ hn_ i.val (le_of_lt i.isLt))
                         (divFinIcc n_ hn_ (i.val + 1) i.isLt)
    have hr : range γ_i ⊆ c.source := range_segment_subset_source_of_hcov γ n_ hn_ pick_ h_ i
    set g_i := chartLift c γ_i hr
    show IntervalIntegrable (curveIntegralFun (chartedFormPullback c ω) g_i) volume 0 1
    apply CurveIntegrable.intervalIntegrable
    apply chartedFormPullback_curveIntegrable
    · exact (chartAt E (pick_ i)).open_source.mem_maximalAtlas
    · -- ContDiffOn of chartLift from ContDiffOn of γ
      have hγi : ContDiffOn ℝ 1 γ_i.extend (Set.Icc 0 1) := by
        rw [Path.extend_subpath]
        apply hγ.comp
        · apply ContDiff.contDiffOn
          apply contDiff_subpathAux
        · intro s hs
          exact subpathAux_mem_Icc _ _ hs
      apply ContDiffOn.comp (I := modelWithCornersSelf ℂ E) (I' := modelWithCornersSelf ℂ E)
        (n := (⊤ : WithTop ℕ∞)) (f := c)
      · apply contMDiffOn_iff_contDiffOn.mp
        exact contMDiffOn_chart
      · exact hγi
      · intro s hs
        exact hr (extend_mem_range γ_i s)
    · intro t
      exact mem_chart_target_iff.mpr (hr (extend_mem_range γ_i t))
  -- 3. Refine LHS to n * n'
  have hLHS := pathIntegralViaCoverWith_refine_to_multiple ω γ n n' hn hn' pickChart hcov
    (hcov_refined n n' hn hn' pickChart hcov) (hint_refined n hn pickChart hcov)
  -- 4. Refine RHS to n' * n
  have hRHS := pathIntegralViaCoverWith_refine_to_multiple ω γ n' n hn' hn pickChart' hcov'
    (hcov_refined n' n hn' hn pickChart' hcov') (hint_refined n' hn' pickChart' hcov')
  -- Adjust RHS size from n'*n to n*n'
  rw [Nat.mul_comm n' n] at hRHS
  rw [hLHS, hRHS]
  -- 5. Sums are equal because each summand is equal by chart-change (Phase 4a)
  unfold pathIntegralViaCoverWith
  refine Finset.sum_congr rfl (fun j _ => ?_)
  apply pathIntegralViaChartCorrect_chart_change
  · -- Sub-segment lies in pickChart ⌊j/n'⌋ source
    rw [Path.range_subpath, Set.uIcc_of_le (divFinIcc_le_succ (n * n') hnn' j.val j.isLt)]
    rintro x ⟨t, ht, rfl⟩
    apply hcov_refined n n' hn hn' pickChart hcov j t ht.1 ht.2
  · -- Sub-segment lies in pickChart' ⌊j/n⌋ source
    rw [Path.range_subpath, Set.uIcc_of_le (divFinIcc_le_succ (n * n') hnn' j.val j.isLt)]
    rintro x ⟨t, ht, rfl⟩
    -- For the RHS, the pickChart' index is ⌊j/n⌋.
    -- The refine_to_multiple used k = n for the RHS.
    -- (n' * n) re-commuted to (n * n') means j is in Fin (n * n').
    -- The pickChart' argument in hRHS (after mul_comm) is:
    --   fun j => pickChart' ⟨j.val / n, ...⟩
    apply hcov_refined n' n hn' hn pickChart' hcov' j t ht.1 ht.2

end JacobianChallenge.Periods
