import Mathlib.Analysis.Complex.Harmonic.MeanValue
import Mathlib.MeasureTheory.Integral.CircleAverage
import Mathlib.MeasureTheory.Integral.CircleIntegral
import Jacobian.HolomorphicForms.PerronRemovableSingularity

/-!
# Harmonic weak maximum principle — local max propagation (Perron engine B2 toolbox W1, M1)

Blueprint node: `lem:stage-harmonic-max-principle` (this file is the M1
leaf; the full principle and the `WeakMaxPrincipleInput` discharge land
in M2).  Tracking: GitHub issue #232, B2 pricing doc
`docs/perron-b2-dirichlet-phase0.md` §4 row W1.

This commit lands the ℂ-side **local maximum propagation** leaf, sorry-
free: a function harmonic on a neighborhood of a closed disc and
maximized at the center is constant on the closed disc
(`eq_const_closedBall_of_harmonicOnNhd_of_le`).  The route is the
mean-value property (`HarmonicOnNhd.circleAverage_eq`,
`Mathlib/Analysis/Complex/Harmonic/MeanValue.lean`) combined with the
averaging-rigidity leaf `eq_const_sphere_of_circleAverage_eq_of_le`: a
continuous function on a circle, bounded above by its own circle
average, is constant on that circle (strict-gap comparison of interval
integrals).

M2 consumes this through the clopen/connected-component argument: the
set where a harmonic `w` attains its max over `closure V` is open by
this lemma, closed in `V` by continuity, hence a full bounded component
whose closure meets `frontier V` — note `PerronStageMaxPrinciple.lean`
(B3a) is the holomorphic-`Re` statement and is NOT this theorem.
-/

namespace JacobianChallenge.HolomorphicForms

open Filter InnerProductSpace Metric Real

open scoped Topology

/--
**Averaging rigidity on a circle.**  A function continuous on the circle
of radius `ρ > 0` about `x`, bounded above by `a` there, whose circle
average equals `a`, is identically `a` on the circle: any strict gap at
one point forces a strict gap of interval integrals against the constant
`a`, contradicting the average.
-/
theorem eq_const_sphere_of_circleAverage_eq_of_le {g : ℂ → ℝ} {x : ℂ} {ρ a : ℝ}
    (hρ : 0 < ρ) (hg : ContinuousOn g (sphere x ρ))
    (hle : ∀ ζ ∈ sphere x ρ, g ζ ≤ a) (havg : circleAverage g x ρ = a) :
    ∀ ζ ∈ sphere x ρ, g ζ = a := by
  intro ζ hζ
  refine le_antisymm (hle ζ hζ) (le_of_not_gt fun hlt => ?_)
  obtain ⟨θ₀, hθ₀, hζ'⟩ : ∃ θ₀ ∈ Set.Ioc 0 (2 * π), circleMap x ρ θ₀ = ζ := by
    have h := image_circleMap_Ioc x ρ
    rw [abs_of_pos hρ] at h
    rw [← h] at hζ
    exact hζ
  have hu : Continuous fun θ => g (circleMap x ρ θ) :=
    hg.comp_continuous (continuous_circleMap x ρ) fun θ =>
      circleMap_mem_sphere x hρ.le θ
  have hint : (∫ θ in (0 : ℝ)..2 * π, g (circleMap x ρ θ)) <
      ∫ _ in (0 : ℝ)..2 * π, a := by
    refine intervalIntegral.integral_lt_integral_of_continuousOn_of_le_of_exists_lt
      two_pi_pos hu.continuousOn continuousOn_const
      (fun θ _ => hle _ (circleMap_mem_sphere x hρ.le θ)) ?_
    exact ⟨θ₀, Set.Ioc_subset_Icc_self hθ₀, by rw [hζ']; exact hlt⟩
  have hI : (∫ θ in (0 : ℝ)..2 * π, g (circleMap x ρ θ)) = 2 * π * a := by
    rw [circleAverage_def, smul_eq_mul,
      inv_mul_eq_iff_eq_mul₀ (by positivity : (2 * π : ℝ) ≠ 0)] at havg
    exact havg
  rw [intervalIntegral.integral_const, smul_eq_mul, sub_zero, hI] at hint
  exact lt_irrefl _ hint

/--
**Local maximum propagation** (W1 M1 leaf of
`lem:stage-harmonic-max-principle`).  A function harmonic on a
neighborhood of a closed disc and maximized at the center is constant on
the closed disc: each concentric circle through a point of the disc has
circle average equal to the central value by the mean-value property,
and averaging rigidity forces equality on the whole circle.
-/
theorem eq_const_closedBall_of_harmonicOnNhd_of_le {w : ℂ → ℝ} {x : ℂ} {r : ℝ}
    (hw : HarmonicOnNhd w (closedBall x r))
    (hle : ∀ z ∈ closedBall x r, w z ≤ w x) :
    ∀ z ∈ closedBall x r, w z = w x := by
  intro z hz
  rcases eq_or_ne z x with rfl | hzx
  · rfl
  have hρ : 0 < dist z x := dist_pos.mpr hzx
  have hρr : dist z x ≤ r := mem_closedBall.mp hz
  have hsub : closedBall x (dist z x) ⊆ closedBall x r :=
    closedBall_subset_closedBall hρr
  have havg : circleAverage w x (dist z x) = w x :=
    HarmonicOnNhd.circleAverage_eq (by rw [abs_of_pos hρ]; exact hw.mono hsub)
  have hsph : sphere x (dist z x) ⊆ closedBall x r :=
    sphere_subset_closedBall.trans hsub
  exact eq_const_sphere_of_circleAverage_eq_of_le hρ
    ((continuousOn_of_harmonicOnNhd hw).mono hsph)
    (fun ζ hζ => hle ζ (hsph hζ)) havg z (mem_sphere.mpr rfl)

end JacobianChallenge.HolomorphicForms
