import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Convex.PathConnected
import Mathlib.Topology.Germ
import Jacobian.HolomorphicForms.HarmonicConjugate

/-!
# Uniqueness of harmonic conjugates on preconnected opens

B4 work item W1 (`docs/perron-b4-conjugate-phase0.md`): two harmonic
conjugates of the same `u` on a preconnected open differ by a real
constant — first on `U ⊆ ℂ` (W1a), then on `U ⊆ X` for a charted `X` via
the chart-transfer lemma (W1b).  This is the discreteness input for the
conjugate-germ covering space planned in W3/W4.
-/

namespace JacobianChallenge.HolomorphicForms

/-- A `ℂ`-linear continuous map `D : ℂ →L[ℂ] ℂ` whose values all have
vanishing real part is zero: evaluating at `1` kills `(D 1).re`, evaluating
at `I` kills `(D 1).im` (since `D I = I * D 1`), and `ℂ`-linearity recovers
`D z = z * D 1`. -/
private lemma clm_eq_zero_of_re_apply_eq_zero (D : ℂ →L[ℂ] ℂ)
    (h : ∀ z : ℂ, (D z).re = 0) : D = 0 := by
  have hDI : D Complex.I = Complex.I * D 1 := by
    have := D.map_smul Complex.I 1
    simpa [smul_eq_mul] using this
  have him : (D 1).im = 0 := by
    have hre : (Complex.I * D 1).re = -(D 1).im := by
      simp [Complex.mul_re]
    have hI := h Complex.I
    rw [hDI, hre] at hI
    linarith
  have hD1 : D 1 = 0 := by
    apply Complex.ext
    · simpa using h 1
    · simpa using him
  ext
  simpa using hD1

/-- Pointwise kernel for conjugate uniqueness on `ℂ`: if `v₁` and `v₂` are
both harmonic conjugates of the same `u` at `x` (in the
`IsHarmonicConjugateAtReal` sense), then the purely imaginary difference
`z ↦ I * (v₂ z - v₁ z)` has vanishing complex derivative at `x`.

Proof: subtract the two `HasFDerivAt` witnesses (the self-chart pullback on
`ℂ` collapses definitionally); the difference function has identically zero
real part, so composing with `Complex.reCLM` and comparing with the constant
function forces the real part of the `ℂ`-linear derivative to vanish
everywhere, and `clm_eq_zero_of_re_apply_eq_zero` kills it. -/
theorem conjugate_diff_hasFDerivAt_zero {u v₁ v₂ : ℂ → ℝ} {x : ℂ}
    (h₁ : IsHarmonicConjugateAtReal ℂ u v₁ x)
    (h₂ : IsHarmonicConjugateAtReal ℂ u v₂ x) :
    HasFDerivAt (fun z : ℂ => Complex.I * ((v₂ z : ℂ) - (v₁ z : ℂ)))
      (0 : ℂ →L[ℂ] ℂ) x := by
  obtain ⟨f₁, hf₁⟩ := h₁
  obtain ⟨f₂, hf₂⟩ := h₂
  have hchart_id : ∀ z : ℂ, (chartAt ℂ x).symm z = z := fun _ => rfl
  have hchart_pt : (chartAt ℂ x) x = x := rfl
  have hf₁' : HasFDerivAt
      (fun z : ℂ => (u z : ℂ) + Complex.I * (v₁ z : ℂ)) f₁ x := by
    simpa [hchart_id, hchart_pt] using hf₁
  have hf₂' : HasFDerivAt
      (fun z : ℂ => (u z : ℂ) + Complex.I * (v₂ z : ℂ)) f₂ x := by
    simpa [hchart_id, hchart_pt] using hf₂
  have hsub : HasFDerivAt
      (fun z : ℂ => Complex.I * ((v₂ z : ℂ) - (v₁ z : ℂ))) (f₂ - f₁) x := by
    refine (hf₂'.sub hf₁').congr_of_eventuallyEq
      (Filter.Eventually.of_forall fun z => ?_)
    show Complex.I * ((v₂ z : ℂ) - (v₁ z : ℂ))
        = ((u z : ℂ) + Complex.I * (v₂ z : ℂ))
          - ((u z : ℂ) + Complex.I * (v₁ z : ℂ))
    ring
  -- The composition with `reCLM` is the zero function, so the real part of
  -- the derivative vanishes identically.
  have hcomp :=
    Complex.reCLM.hasFDerivAt.comp x (hsub.restrictScalars ℝ)
  have hcomp0 : HasFDerivAt (fun _ : ℂ => (0 : ℝ))
      (Complex.reCLM.comp ((f₂ - f₁).restrictScalars ℝ)) x := by
    refine hcomp.congr_of_eventuallyEq
      (Filter.Eventually.of_forall fun z => ?_)
    show (0 : ℝ) = (Complex.I * ((v₂ z : ℂ) - (v₁ z : ℂ))).re
    simp [Complex.mul_re]
  have hD_re : Complex.reCLM.comp ((f₂ - f₁).restrictScalars ℝ) = 0 :=
    hcomp0.unique (hasFDerivAt_const (0 : ℝ) x)
  have hre : ∀ w : ℂ, ((f₂ - f₁) w).re = 0 := fun w => by
    have := ContinuousLinearMap.ext_iff.mp hD_re w
    simpa using this
  have hD0 : f₂ - f₁ = 0 := clm_eq_zero_of_re_apply_eq_zero _ hre
  rw [hD0] at hsub
  exact hsub

/-- W1a main theorem: two harmonic conjugates of the same `u` on a
preconnected open `U ⊆ ℂ` differ by a real constant.

Proof: by `conjugate_diff_hasFDerivAt_zero` the function
`g := fun z => I * (v₂ z - v₁ z)` has vanishing complex derivative at every
point of `U`, so Mathlib's `IsOpen.exists_is_const_of_fderiv_eq_zero` makes
`g` constant on `U`; the constant is read off the imaginary part.

This is the discreteness input for the B4 conjugate-germ covering space
(work items W3/W4 in `docs/perron-b4-conjugate-phase0.md`): the fiber of
local-conjugate germs over a connected conjugate ball is an `ℝ`-torsor of
constants. -/
theorem isHarmonicConjugateAtReal_sub_eq_const_on {u v₁ v₂ : ℂ → ℝ}
    {U : Set ℂ} (hU : IsOpen U) (hUc : IsPreconnected U)
    (h₁ : ∀ x ∈ U, IsHarmonicConjugateAtReal ℂ u v₁ x)
    (h₂ : ∀ x ∈ U, IsHarmonicConjugateAtReal ℂ u v₂ x) :
    ∃ c : ℝ, ∀ x ∈ U, v₂ x = v₁ x + c := by
  set g : ℂ → ℂ := fun z => Complex.I * ((v₂ z : ℂ) - (v₁ z : ℂ)) with hg
  have hder : ∀ x ∈ U, HasFDerivAt g (0 : ℂ →L[ℂ] ℂ) x := fun x hx =>
    conjugate_diff_hasFDerivAt_zero (h₁ x hx) (h₂ x hx)
  have hdiff : DifferentiableOn ℂ g U := fun x hx =>
    (hder x hx).differentiableAt.differentiableWithinAt
  have hfz : Set.EqOn (fderiv ℂ g) 0 U := fun x hx => (hder x hx).fderiv
  obtain ⟨a, ha⟩ := hU.exists_is_const_of_fderiv_eq_zero hUc hdiff hfz
  refine ⟨a.im, fun x hx => ?_⟩
  have him := congrArg Complex.im (ha x hx)
  -- `(I * ((v₂ x : ℂ) - (v₁ x : ℂ))).im = v₂ x - v₁ x`
  simp [hg, Complex.mul_im] at him
  linarith

/-- Chart independence of `IsHarmonicConjugateAtReal`: a conjugate pair at
`y` (read, per the definition, in `y`'s own chart) transfers to the chart at
any other point `x` whose source contains `y`: the pullbacks
`u ∘ (chartAt ℂ x).symm`, `v ∘ (chartAt ℂ x).symm` form a ℂ-level conjugate
pair at `(chartAt ℂ x) y`.

Proof pattern follows `dipole_compose_chart_has_conjugate`: the chart
transition `chartAt ℂ y ∘ (chartAt ℂ x).symm` is analytic at
`(chartAt ℂ x) y` (`chart_transition_contDiffOn` under `IsManifold`), the
chain rule composes the `HasFDerivAt` witnesses, and a `left_inv` germ
identity lands the stated pullback.

Direct dependency of the W3/W4 conjugate-germ covering space
(`docs/perron-b4-conjugate-phase0.md`). -/
theorem IsHarmonicConjugateAtReal.transfer_chart
    {X : Type*} [TopologicalSpace X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X]
    {u v : X → ℝ} {x y : X}
    (hy : IsHarmonicConjugateAtReal X u v y)
    (hyx : y ∈ (chartAt ℂ x).source) :
    IsHarmonicConjugateAtReal ℂ
      (u ∘ (chartAt ℂ x).symm) (v ∘ (chartAt ℂ x).symm)
      ((chartAt ℂ x) y) := by
  obtain ⟨f', hf⟩ := hy
  set z₀ : ℂ := (chartAt ℂ x) y with hz₀
  have hinv : (chartAt ℂ x).symm z₀ = y := (chartAt ℂ x).left_inv hyx
  have hz₀_t : z₀ ∈ (chartAt ℂ x).target := (chartAt ℂ x).map_source hyx
  -- The transition τ := chartAt ℂ y ∘ (chartAt ℂ x).symm is analytic at z₀.
  have hW_open : IsOpen ((chartAt ℂ x).target ∩
      (chartAt ℂ x).symm ⁻¹' (chartAt ℂ y).source) :=
    (chartAt ℂ x).continuousOn_symm.isOpen_inter_preimage
      (chartAt ℂ x).open_target (chartAt ℂ y).open_source
  have hz₀_W : z₀ ∈ (chartAt ℂ x).target ∩
      (chartAt ℂ x).symm ⁻¹' (chartAt ℂ y).source := by
    refine Set.mem_inter hz₀_t ?_
    rw [Set.mem_preimage, hinv]
    exact mem_chart_source ℂ y
  have hτ_an : AnalyticAt ℂ (chartAt ℂ y ∘ (chartAt ℂ x).symm) z₀ :=
    AnalyticOn.analyticAt (hW_open.mem_nhds hz₀_W)
      (chart_transition_contDiffOn x y).analyticOn
  have hτ := hτ_an.differentiableAt.hasFDerivAt
  -- Move the y-chart witness to the transition value τ z₀ = (chartAt ℂ y) y.
  have hτz₀ : (chartAt ℂ y ∘ (chartAt ℂ x).symm) z₀ = (chartAt ℂ y) y := by
    show chartAt ℂ y ((chartAt ℂ x).symm z₀) = (chartAt ℂ y) y
    rw [hinv]
  rw [← hτz₀] at hf
  have hcomp := hf.comp z₀ hτ
  -- Identify the composition with the x-chart pullback near z₀.
  have hnear : (fun z : ℂ =>
        (u ((chartAt ℂ y).symm ((chartAt ℂ y ∘ (chartAt ℂ x).symm) z)) : ℂ)
          + Complex.I
            * (v ((chartAt ℂ y).symm ((chartAt ℂ y ∘ (chartAt ℂ x).symm) z)) : ℂ))
      =ᶠ[nhds z₀]
      (fun z : ℂ =>
        ((u ∘ (chartAt ℂ x).symm) z : ℂ)
          + Complex.I * ((v ∘ (chartAt ℂ x).symm) z : ℂ)) := by
    filter_upwards [hW_open.mem_nhds hz₀_W] with z hz
    have hzsrc : (chartAt ℂ x).symm z ∈ (chartAt ℂ y).source := hz.2
    have hzinv : (chartAt ℂ y).symm (chartAt ℂ y ((chartAt ℂ x).symm z))
        = (chartAt ℂ x).symm z := (chartAt ℂ y).left_inv hzsrc
    show (u ((chartAt ℂ y).symm (chartAt ℂ y ((chartAt ℂ x).symm z))) : ℂ)
          + Complex.I
            * (v ((chartAt ℂ y).symm (chartAt ℂ y ((chartAt ℂ x).symm z))) : ℂ)
        = (u ((chartAt ℂ x).symm z) : ℂ)
          + Complex.I * (v ((chartAt ℂ x).symm z) : ℂ)
    rw [hzinv]
  refine ⟨f'.comp (fderiv ℂ (chartAt ℂ y ∘ (chartAt ℂ x).symm) z₀), ?_⟩
  -- Self-chart collapse on ℂ at z₀, then transport along `hnear`.
  have hchart_id : ∀ z : ℂ, (chartAt ℂ z₀).symm z = z := fun _ => rfl
  have hchart_pt : (chartAt ℂ z₀) z₀ = z₀ := rfl
  simp only [hchart_id, hchart_pt]
  exact hcomp.congr_of_eventuallyEq hnear.symm

/-- W1b main theorem: two harmonic conjugates of the same `u` on a
preconnected open `U ⊆ X` differ by a real constant, for `X` charted over ℂ
with the smooth-manifold instance.

Around each point of `U` a chart ball is chosen inside
`U ∩ (chartAt ℂ ·).source`; `IsHarmonicConjugateAtReal.transfer_chart` turns
the `X`-level hypotheses into ℂ-level conjugacy of the chart pullbacks on
that ball, the ℂ-level theorem `isHarmonicConjugateAtReal_sub_eq_const_on`
makes `v₂ - v₁` constant near the point, and Mathlib's
`eq_of_germ_isConstant_on` globalizes over the preconnected `U`.

Together with W1a this is P0 work item W1 (`docs/perron-b4-conjugate-phase0.md`):
the germ-fiber discreteness input for the W3/W4 conjugate-germ covering. -/
theorem isHarmonicConjugateAtReal_sub_eq_const_on_X
    {X : Type*} [TopologicalSpace X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X]
    {u v₁ v₂ : X → ℝ} {U : Set X}
    (hU : IsOpen U) (hUc : IsPreconnected U)
    (h₁ : ∀ x ∈ U, IsHarmonicConjugateAtReal X u v₁ x)
    (h₂ : ∀ x ∈ U, IsHarmonicConjugateAtReal X u v₂ x) :
    ∃ c : ℝ, ∀ x ∈ U, v₂ x = v₁ x + c := by
  rcases U.eq_empty_or_nonempty with rfl | ⟨x₀, hx₀⟩
  · exact ⟨0, by simp⟩
  set w : X → ℝ := fun q => v₂ q - v₁ q with hw
  -- The germ of `w` at every point of `U` is constant.
  have hgerm : ∀ p ∈ U, (↑w : Filter.Germ (nhds p) ℝ).IsConstant := by
    intro p hp
    set e := chartAt ℂ p with he
    set z₀ : ℂ := e p with hz₀
    -- An open chart-target set over `U ∩ e.source`, and a ball inside it.
    have hV_open : IsOpen (e.target ∩ e.symm ⁻¹' (U ∩ e.source)) :=
      e.continuousOn_symm.isOpen_inter_preimage e.open_target
        (hU.inter e.open_source)
    have hz₀_V : z₀ ∈ e.target ∩ e.symm ⁻¹' (U ∩ e.source) := by
      refine Set.mem_inter (e.map_source (mem_chart_source ℂ p)) ?_
      rw [Set.mem_preimage, e.left_inv (mem_chart_source ℂ p)]
      exact ⟨hp, mem_chart_source ℂ p⟩
    obtain ⟨r, hr0, hball⟩ :=
      Metric.isOpen_iff.mp hV_open z₀ hz₀_V
    -- ℂ-level conjugacy of both pullbacks at every point of the ball.
    have hball₁ : ∀ z ∈ Metric.ball z₀ r,
        IsHarmonicConjugateAtReal ℂ (u ∘ e.symm) (v₁ ∘ e.symm) z := by
      intro z hz
      have hzt : z ∈ e.target := (hball hz).1
      have hzU : e.symm z ∈ U := (hball hz).2.1
      have hzsrc : e.symm z ∈ e.source := (hball hz).2.2
      have := (h₁ (e.symm z) hzU).transfer_chart (x := p) hzsrc
      rwa [he, e.right_inv hzt] at this
    have hball₂ : ∀ z ∈ Metric.ball z₀ r,
        IsHarmonicConjugateAtReal ℂ (u ∘ e.symm) (v₂ ∘ e.symm) z := by
      intro z hz
      have hzt : z ∈ e.target := (hball hz).1
      have hzU : e.symm z ∈ U := (hball hz).2.1
      have hzsrc : e.symm z ∈ e.source := (hball hz).2.2
      have := (h₂ (e.symm z) hzU).transfer_chart (x := p) hzsrc
      rwa [he, e.right_inv hzt] at this
    obtain ⟨c, hc⟩ := isHarmonicConjugateAtReal_sub_eq_const_on
      Metric.isOpen_ball (convex_ball z₀ r).isPreconnected hball₁ hball₂
    -- Pull the constancy back to the open neighborhood `e.source ∩ e ⁻¹' ball`.
    have hN_open : IsOpen (e.source ∩ e ⁻¹' Metric.ball z₀ r) :=
      e.continuousOn.isOpen_inter_preimage e.open_source Metric.isOpen_ball
    have hpN : p ∈ e.source ∩ e ⁻¹' Metric.ball z₀ r :=
      ⟨mem_chart_source ℂ p, by
        rw [Set.mem_preimage, ← hz₀]
        exact Metric.mem_ball_self hr0⟩
    refine ⟨c, ?_⟩
    filter_upwards [hN_open.mem_nhds hpN] with q hq
    have hq_inv : e.symm (e q) = q := e.left_inv hq.1
    have := hc (e q) hq.2
    show w q = c
    rw [hw]
    have hv₂ : (v₂ ∘ e.symm) (e q) = v₂ q := by rw [Function.comp_apply, hq_inv]
    have hv₁ : (v₁ ∘ e.symm) (e q) = v₁ q := by rw [Function.comp_apply, hq_inv]
    rw [hv₂, hv₁] at this
    linarith
  -- Globalize over the preconnected `U` and read off the constant.
  refine ⟨w x₀, fun q hq => ?_⟩
  have := eq_of_germ_isConstant_on hgerm hUc hq hx₀
  simp only [hw] at this ⊢
  linarith

/-- Reverse companion of `IsHarmonicConjugateAtReal.transfer_chart`: if the
x-chart pullbacks `(u ∘ (chartAt ℂ x).symm, v ∘ (chartAt ℂ x).symm)` form a
ℂ-level conjugate pair at `(chartAt ℂ x) y` and `y ∈ (chartAt ℂ x).source`,
then `(u, v)` is a conjugate pair at `y` in `X` (read, per the definition,
in `y`'s own chart).

Proof symmetric to `transfer_chart`: the transition
`chartAt ℂ x ∘ (chartAt ℂ y).symm` is analytic at `(chartAt ℂ y) y`
(`chart_transition_contDiffOn` with the roles swapped), the chain rule
composes the witnesses, and `left_inv` germ identities collapse the double
pullback.

Used by the W2 bridge (`PerronStageConjugateBridge.lean`) to convert
ball-level conjugates produced in one fixed chart into the `X`-level
predicate at every point of the ball preimage. -/
theorem IsHarmonicConjugateAtReal.of_transfer_chart
    {X : Type*} [TopologicalSpace X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X]
    {u v : X → ℝ} {x y : X}
    (h : IsHarmonicConjugateAtReal ℂ
      (u ∘ (chartAt ℂ x).symm) (v ∘ (chartAt ℂ x).symm) ((chartAt ℂ x) y))
    (hyx : y ∈ (chartAt ℂ x).source) :
    IsHarmonicConjugateAtReal X u v y := by
  obtain ⟨g', hg⟩ := h
  set ζ₀ : ℂ := (chartAt ℂ y) y with hζ₀
  have hζinv : (chartAt ℂ y).symm ζ₀ = y :=
    (chartAt ℂ y).left_inv (mem_chart_source ℂ y)
  -- The transition τ := chartAt ℂ x ∘ (chartAt ℂ y).symm is analytic at ζ₀.
  have hW_open : IsOpen ((chartAt ℂ y).target ∩
      (chartAt ℂ y).symm ⁻¹' (chartAt ℂ x).source) :=
    (chartAt ℂ y).continuousOn_symm.isOpen_inter_preimage
      (chartAt ℂ y).open_target (chartAt ℂ x).open_source
  have hζ₀_W : ζ₀ ∈ (chartAt ℂ y).target ∩
      (chartAt ℂ y).symm ⁻¹' (chartAt ℂ x).source := by
    refine Set.mem_inter ((chartAt ℂ y).map_source (mem_chart_source ℂ y)) ?_
    rw [Set.mem_preimage, hζinv]
    exact hyx
  have hτ_an : AnalyticAt ℂ (chartAt ℂ x ∘ (chartAt ℂ y).symm) ζ₀ :=
    AnalyticOn.analyticAt (hW_open.mem_nhds hζ₀_W)
      (chart_transition_contDiffOn y x).analyticOn
  have hτ := hτ_an.differentiableAt.hasFDerivAt
  -- Move the ℂ-level witness to the transition value τ ζ₀ = (chartAt ℂ x) y.
  have hτζ₀ : (chartAt ℂ x ∘ (chartAt ℂ y).symm) ζ₀ = (chartAt ℂ x) y := by
    show chartAt ℂ x ((chartAt ℂ y).symm ζ₀) = (chartAt ℂ x) y
    rw [hζinv]
  -- Self-chart collapse on ℂ inside the hypothesis witness.
  have hchart_id : ∀ w : ℂ, (chartAt ℂ ((chartAt ℂ x) y)).symm w = w :=
    fun _ => rfl
  have hchart_pt :
      (chartAt ℂ ((chartAt ℂ x) y)) ((chartAt ℂ x) y) = (chartAt ℂ x) y := rfl
  have hg' : HasFDerivAt (fun w : ℂ =>
      ((u ∘ (chartAt ℂ x).symm) w : ℂ)
        + Complex.I * ((v ∘ (chartAt ℂ x).symm) w : ℂ))
      g' ((chartAt ℂ x ∘ (chartAt ℂ y).symm) ζ₀) := by
    rw [hτζ₀]
    simpa [hchart_id, hchart_pt] using hg
  have hcomp := hg'.comp ζ₀ hτ
  -- Identify the composition with the y-chart pullback near ζ₀.
  have hnear : (fun w : ℂ =>
        ((u ∘ (chartAt ℂ x).symm) ((chartAt ℂ x ∘ (chartAt ℂ y).symm) w) : ℂ)
          + Complex.I
            * ((v ∘ (chartAt ℂ x).symm)
                ((chartAt ℂ x ∘ (chartAt ℂ y).symm) w) : ℂ))
      =ᶠ[nhds ζ₀]
      (fun w : ℂ =>
        (u ((chartAt ℂ y).symm w) : ℂ)
          + Complex.I * (v ((chartAt ℂ y).symm w) : ℂ)) := by
    filter_upwards [hW_open.mem_nhds hζ₀_W] with w hw
    have hwsrc : (chartAt ℂ y).symm w ∈ (chartAt ℂ x).source := hw.2
    have hwinv : (chartAt ℂ x).symm (chartAt ℂ x ((chartAt ℂ y).symm w))
        = (chartAt ℂ y).symm w := (chartAt ℂ x).left_inv hwsrc
    show (u ((chartAt ℂ x).symm (chartAt ℂ x ((chartAt ℂ y).symm w))) : ℂ)
          + Complex.I
            * (v ((chartAt ℂ x).symm (chartAt ℂ x ((chartAt ℂ y).symm w))) : ℂ)
        = (u ((chartAt ℂ y).symm w) : ℂ)
          + Complex.I * (v ((chartAt ℂ y).symm w) : ℂ)
    rw [hwinv]
  exact ⟨g'.comp (fderiv ℂ (chartAt ℂ x ∘ (chartAt ℂ y).symm) ζ₀),
    hcomp.congr_of_eventuallyEq hnear.symm⟩

end JacobianChallenge.HolomorphicForms
