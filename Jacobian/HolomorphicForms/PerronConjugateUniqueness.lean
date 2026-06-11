import Mathlib.Analysis.Calculus.MeanValue
import Jacobian.HolomorphicForms.HarmonicConjugate

/-!
# Uniqueness of harmonic conjugates on preconnected opens of ℂ

B4 work item W1a (`docs/perron-b4-conjugate-phase0.md`): two harmonic
conjugates of the same `u` on a preconnected open `U ⊆ ℂ` differ by a real
constant.  This is the discreteness input for the conjugate-germ covering
space planned in W3/W4.
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

end JacobianChallenge.HolomorphicForms
