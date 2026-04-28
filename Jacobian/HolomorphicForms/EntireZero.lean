import Mathlib

/-!
# Entire functions vanishing at infinity are zero

Small helper file collecting two corollaries of Liouville's theorem
that are useful when proving the Liouville core of the genus-zero
classification (`holomorphicOneForm_onePointCx_subsingleton` in
`Jacobian/HolomorphicForms/GenusZeroClassification.lean`).

Both lemmas are direct corollaries of Mathlib's
`Differentiable.eq_const_of_tendsto_cocompact`. They are not in
Mathlib v4.28.0 in this exact form.

* `Differentiable.eq_zero_of_tendsto_zero_cocompact`
  — entire and tends to `0` along `cocompact ℂ` ⇒ identically `0`.
* `Differentiable.eq_zero_of_inv_decay_at_infty`
  — entire and `‖f z‖ ≤ C / ‖z‖` for `‖z‖ ≥ R` ⇒ identically `0`.

The second is the simplest growth-bound form. The standard quadratic
form `‖f z‖ ≤ C / ‖z‖^2` (which arises from the inversion-chart
holomorphicity condition for a 1-form on `ℂℙ¹`) reduces to this via
the trivial bound `1 / ‖z‖^2 ≤ 1 / ‖z‖` for `‖z‖ ≥ 1`.
-/

namespace JacobianChallenge.HolomorphicForms.EntireZero

open Filter Topology

/-- If `f : ℂ → ℂ` is entire and tends to `0` at infinity (along the
cocompact filter), then `f` is identically `0`.

Direct corollary of `Differentiable.eq_const_of_tendsto_cocompact`. -/
theorem _root_.Differentiable.eq_zero_of_tendsto_zero_cocompact
    {f : ℂ → ℂ} (hf : Differentiable ℂ f)
    (h : Tendsto f (cocompact ℂ) (𝓝 0)) :
    f = 0 := by
  have hconst : f = Function.const ℂ (0 : ℂ) :=
    hf.eq_const_of_tendsto_cocompact h
  funext z
  simp [hconst]

/-- If `f : ℂ → ℂ` is entire and satisfies a `1 / r` decay bound at
infinity, then `f` is identically `0`.

The bound `‖f z‖ ≤ C / ‖z‖` is enough — the standard quadratic form
`‖f z‖ ≤ C' / ‖z‖^2` that arises from the inversion-chart
holomorphicity condition implies this since
`C' / ‖z‖^2 ≤ C' / ‖z‖` for `‖z‖ ≥ 1`. -/
theorem _root_.Differentiable.eq_zero_of_inv_decay_at_infty
    {f : ℂ → ℂ} (hf : Differentiable ℂ f)
    {C R : ℝ} (h : ∀ z : ℂ, R ≤ ‖z‖ → ‖f z‖ ≤ C / ‖z‖) :
    f = 0 := by
  refine hf.eq_zero_of_tendsto_zero_cocompact ?_
  rw [tendsto_zero_iff_norm_tendsto_zero]
  have hnorm_atTop : Tendsto (fun z : ℂ => ‖z‖) (cocompact ℂ) atTop :=
    tendsto_norm_cocompact_atTop
  -- The controlling sequence `C / ‖z‖` tends to `0` along `cocompact ℂ`.
  have hctrl : Tendsto (fun z : ℂ => C / ‖z‖) (cocompact ℂ) (𝓝 0) := by
    have h0 : Tendsto (fun z : ℂ => ‖z‖⁻¹) (cocompact ℂ) (𝓝 0) :=
      tendsto_inv_atTop_zero.comp hnorm_atTop
    have h1 : Tendsto (fun z : ℂ => C * ‖z‖⁻¹) (cocompact ℂ) (𝓝 (C * 0)) :=
      h0.const_mul C
    simpa [div_eq_mul_inv] using h1
  -- Squeeze with eventual upper bound from `h`.
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hctrl
    (Eventually.of_forall fun z => norm_nonneg _) ?_
  filter_upwards [hnorm_atTop.eventually_ge_atTop R] with z hz using h z hz

end JacobianChallenge.HolomorphicForms.EntireZero
