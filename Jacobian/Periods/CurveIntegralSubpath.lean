import Mathlib.MeasureTheory.Integral.CurveIntegral.Basic
import Mathlib.Topology.Subpath

/-!
# Reparameterisation: `curveIntegral` of a `Path.subpath`

**Phase 2 prerequisite** for the path-integral well-definedness chain.

States that integrating a 1-form along a subpath `γ.subpath t₀ t₁`
agrees with the interval integral of the same integrand over the
sub-interval `[t₀, t₁]` in parameter space.

Specifically, for `0 ≤ t₀ ≤ t₁ ≤ 1`:

  `curveIntegral ω (γ.subpath t₀ t₁) =
     ∫ t in (t₀ : ℝ)..(t₁ : ℝ), ω (γ.extend t) (derivWithin γ.extend I t)`

This is the change-of-variables identity `u = subpathAux t₀ t₁ s =
(1-s) t₀ + s t₁`, which has `du/ds = (t₁ - t₀)`, applied to
Mathlib's `curveIntegral_def`. The chart-corrected split lemma
`pathIntegralViaChartCorrect_split_subpath` reduces directly to this
once the chart-lifted path is identified via `Path.subpath`-on-`map'`.

## Status

This is the **single named analytic gap** for Phase 2. The proof
requires:
* Reparameterisation of `Path.extend` under affine substitution (the
  inner subpath is `γ ∘ subpathAux t₀ t₁` and its `extend` factors
  through the affine reparameterisation);
* `intervalIntegral.integral_comp_mul_left` (or its general affine
  variant) to rescale the integral on `[0, 1]` to `[t₀, t₁]`;
* Chain rule for `derivWithin` under the affine substitution to
  cancel the Jacobian factor `(t₁ - t₀)`.

All three pieces are in Mathlib v4.28.0; the obstruction is the
boilerplate of bridging `Path.subpath`'s definition to a direct
affine reparameterisation. Roughly a one-week packet.
-/

namespace JacobianChallenge.Periods

open Set MeasureTheory Path
open scoped unitInterval

variable {𝕜 E F : Type*} [RCLike 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F] [NormedSpace ℝ F]

/-- Curve integral over a `Path.subpath` reduces to the interval
integral of the original path's integrand over the sub-interval
`[t₀, t₁]`.

Stated for the orientation `t₀ ≤ t₁`; the reverse orientation
follows from `curveIntegral_symm` + `Path.symm_subpath`. -/
theorem curveIntegral_subpath_of_le
    {a b : E} (ω : E → E →L[𝕜] F) (γ : Path a b)
    (t₀ t₁ : unitInterval) (hle : t₀ ≤ t₁) :
    curveIntegral ω (γ.subpath t₀ t₁) =
      ∫ t in (t₀ : ℝ)..(t₁ : ℝ),
        ω (γ.extend t) (derivWithin γ.extend (Set.Icc 0 1) t) := by
  sorry

end JacobianChallenge.Periods
