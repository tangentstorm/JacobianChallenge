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

/--
**Harmonic weak maximum principle** on a bounded open set `V ⊆ ℂ`
(W1 M2, blueprint `lem:stage-harmonic-max-principle`, harmonic form):
`w` harmonic on `V`, continuous on `closure V`, nonpositive on
`frontier V` is nonpositive on `V`.

Route: the max `w x₀` over the compact `closure V` is attained; if at an
interior point, local max propagation
(`eq_const_closedBall_of_harmonicOnNhd_of_le`) makes the level set
`{w = w x₀}` open, hence — being also closed by continuity — all of
`connectedComponentIn V x₀`.  **Boundedness is load-bearing here**: the
component is bounded, so it cannot be clopen in the connected space `ℂ`
(it would be `univ`, which is unbounded), giving a point of
`closure U \ U ⊆ frontier V` where continuity forces `w = w x₀ ≤ 0`.
-/
theorem le_zero_of_harmonicOnNhd_of_frontier_le_zero
    {V : Set ℂ} {w : ℂ → ℝ} (hV : IsOpen V) (hVb : Bornology.IsBounded V)
    (hw : HarmonicOnNhd w V) (hwc : ContinuousOn w (closure V))
    (hfr : ∀ ζ ∈ frontier V, w ζ ≤ 0) : ∀ z ∈ V, w z ≤ 0 := by
  intro z hz
  obtain ⟨x₀, hx₀cl, hmax⟩ :=
    hVb.isCompact_closure.exists_isMaxOn ⟨z, subset_closure hz⟩ hwc
  suffices hM0 : w x₀ ≤ 0 from le_trans (hmax (subset_closure hz)) hM0
  by_cases hx₀V : x₀ ∈ V
  swap
  · exact hfr x₀ (by rw [hV.frontier_eq]; exact ⟨hx₀cl, hx₀V⟩)
  set U := connectedComponentIn V x₀ with hU
  have hUV : U ⊆ V := connectedComponentIn_subset V x₀
  have hUopen : IsOpen U := hV.connectedComponentIn
  have hx₀U : x₀ ∈ U := mem_connectedComponentIn hx₀V
  -- the maximum propagates over the whole connected component
  set A : Set ℂ := {ζ ∈ U | w ζ = w x₀} with hA
  have hAopen : IsOpen A := by
    rw [Metric.isOpen_iff]
    rintro a ⟨haU, haM⟩
    obtain ⟨ρ, hρpos, hball⟩ :=
      nhds_basis_closedBall.mem_iff.mp (hV.mem_nhds (hUV haU))
    have hconst : ∀ ζ ∈ closedBall a ρ, w ζ = w a := by
      refine eq_const_closedBall_of_harmonicOnNhd_of_le (hw.mono hball)
        fun ζ hζ => ?_
      rw [haM]
      exact hmax (subset_closure (hball hζ))
    have hballV : ball a ρ ⊆ V := fun y hy => hball (ball_subset_closedBall hy)
    have hpc : IsPreconnected (ball a ρ) := (convex_ball a ρ).isPreconnected
    have hballU : ball a ρ ⊆ U := by
      rw [hU, connectedComponentIn_eq haU]
      exact hpc.subset_connectedComponentIn (mem_ball_self hρpos) hballV
    exact ⟨ρ, hρpos, fun ζ hζ =>
      ⟨hballU hζ, (hconst ζ (ball_subset_closedBall hζ)).trans haM⟩⟩
  have hUA : U ⊆ A := by
    refine isPreconnected_connectedComponentIn.subset_of_closure_inter_subset
      hAopen ⟨x₀, hx₀U, hx₀U, rfl⟩ ?_
    rintro ζ ⟨hζcl, hζU⟩
    haveI : (𝓝[A] ζ).NeBot := mem_closure_iff_nhdsWithin_neBot.mp hζcl
    have h1 : Tendsto w (𝓝[A] ζ) (𝓝 (w ζ)) :=
      (hw ζ (hUV hζU)).1.continuousAt.continuousWithinAt
    have h2 : Tendsto w (𝓝[A] ζ) (𝓝 (w x₀)) := by
      refine Tendsto.congr' ?_ tendsto_const_nhds
      filter_upwards [self_mem_nhdsWithin] with y hy
      exact hy.2.symm
    exact ⟨hζU, tendsto_nhds_unique h1 h2⟩
  -- the bounded component is not clopen, so its closure leaves it ...
  obtain ⟨ζ, hζcl, hζU⟩ : ∃ ζ, ζ ∈ closure U ∧ ζ ∉ U := by
    by_contra h
    push Not at h
    rcases isClopen_iff.mp ⟨isClosed_of_closure_subset h, hUopen⟩ with h0 | huniv
    · exact (h0 ▸ hx₀U : x₀ ∈ (∅ : Set ℂ)).elim
    · exact NormedSpace.unbounded_univ ℝ ℂ (huniv ▸ hVb.subset hUV)
  -- ... and the exit point is outside V, hence on the frontier
  have hζV : ζ ∉ V := by
    intro hζV
    obtain ⟨y, hyC, hyU⟩ :=
      mem_closure_iff.mp hζcl _ hV.connectedComponentIn (mem_connectedComponentIn hζV)
    apply hζU
    have hUeq : connectedComponentIn V x₀ = connectedComponentIn V ζ :=
      (connectedComponentIn_eq hyU).trans (connectedComponentIn_eq hyC).symm
    rw [hU, hUeq]
    exact mem_connectedComponentIn hζV
  -- continuity transports the maximum value to the frontier point
  have hζclV : ζ ∈ closure V := closure_mono hUV hζcl
  have hwζ : w ζ = w x₀ := by
    haveI : (𝓝[U] ζ).NeBot := mem_closure_iff_nhdsWithin_neBot.mp hζcl
    have h1 : Tendsto w (𝓝[U] ζ) (𝓝 (w ζ)) :=
      (hwc ζ hζclV).mono_left (nhdsWithin_mono ζ (hUV.trans subset_closure))
    have h2 : Tendsto w (𝓝[U] ζ) (𝓝 (w x₀)) := by
      refine Tendsto.congr' ?_ tendsto_const_nhds
      filter_upwards [self_mem_nhdsWithin] with y hy
      exact (hUA hy).2.symm
    exact tendsto_nhds_unique h1 h2
  have : w ζ ≤ 0 := hfr ζ (by rw [hV.frontier_eq]; exact ⟨hζclV, hζV⟩)
  exact hwζ ▸ this

/--
**The W1 named discharge**: the frozen obligation
`WeakMaxPrincipleInput` (`PerronRemovableSingularity.lean`) holds.
Consumers (`PerronSubOn.of_harmonicOnNhd`, the two-harmonic disc
comparison, `eq_dirichletSolution_of_bounded_punctured`, the W6
extension chain) can now be supplied by this theorem instead of a
hypothesis.
-/
theorem weakMaxPrincipleInput_holds : WeakMaxPrincipleInput :=
  fun _V _w hV hVb hw hwc hfr =>
    le_zero_of_harmonicOnNhd_of_frontier_le_zero hV hVb hw hwc hfr

end JacobianChallenge.HolomorphicForms
