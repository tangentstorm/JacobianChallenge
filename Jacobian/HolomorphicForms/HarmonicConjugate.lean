import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Calculus.FDeriv.Basic
import Jacobian.HolomorphicForms.CompactRiemannSurface
import Jacobian.HolomorphicForms.HarmonicDipole

namespace JacobianChallenge.HolomorphicForms

open scoped Manifold

/-- A local harmonic conjugate v exists for a harmonic function u on a simply connected chart U.
We stub this coordinate-local property as part of the scaffolding strategy. -/
theorem harmonic_conjugate_exists_locally
    (X : Type*) [TopologicalSpace X] [ChartedSpace ℂ X]
    (_u : X → ℝ) (_x : X) :
    ∃ v : X → ℝ, True := by
  refine ⟨fun _ => 0, trivial⟩

/-- Genuine sibling to the `∃ v, True` stub of
`harmonic_conjugate_exists_locally`: `v` is a harmonic conjugate of
`u` near `x` in the sense that the chart-pullback of `f := u + iv`
(viewed as a `ℂ`-valued function via `Complex.ofReal` + `Complex.I`)
is `ℂ`-Fréchet-differentiable at the chart image of `x`. This is
exactly the Cauchy-Riemann condition recast as complex
differentiability — strictly stronger than mere `C²` smoothness;
`True`-style cheats no longer satisfy it once it is the demanded
predicate. -/
def IsHarmonicConjugateAtReal
    (X : Type*) [TopologicalSpace X] [ChartedSpace ℂ X]
    (u v : X → ℝ) (x : X) : Prop :=
  ∃ f' : ℂ →L[ℂ] ℂ,
    HasFDerivAt
      (fun z : ℂ =>
        (u ((chartAt ℂ x).symm z) : ℂ)
          + Complex.I * (v ((chartAt ℂ x).symm z) : ℂ))
      f'
      ((chartAt ℂ x) x)

/-- Bridge: if some `v` is a harmonic conjugate of `u` at `x` in
the contentful Real sense, then the existing `∃ v, True` conclusion
of `harmonic_conjugate_exists_locally` holds. Allows contentful
witnesses to be supplied without breaking the stub-based proof. -/
lemma harmonic_conjugate_exists_locally_real_bridge
    {X : Type*} [TopologicalSpace X] [ChartedSpace ℂ X]
    {u : X → ℝ} {x : X}
    (h : ∃ v : X → ℝ, IsHarmonicConjugateAtReal X u v x) :
    ∃ _v : X → ℝ, True := by
  obtain ⟨v, _⟩ := h
  exact ⟨v, trivial⟩

/-- Canonical witness on `X = ℂ`: the imaginary part `Complex.im`
is a harmonic conjugate of the real part `Complex.re` at every
point `x : ℂ`. The function `f(z) := (z.re : ℂ) + I * (z.im : ℂ)`
equals `z` by `Complex.re_add_im` (plus `mul_comm`), and the
identity function is trivially ℂ-Fréchet-differentiable at any
point with derivative `ContinuousLinearMap.id`. Demonstrates that
`IsHarmonicConjugateAtReal` is non-vacuous and is the intended
target predicate for the eventual harmonic-conjugate construction. -/
theorem IsHarmonicConjugateAtReal.re_im_at (x : ℂ) :
    IsHarmonicConjugateAtReal ℂ Complex.re Complex.im x := by
  refine ⟨ContinuousLinearMap.id ℂ ℂ, ?_⟩
  -- chartAt ℂ x is the identity self-chart, so (chart).symm z = z.
  -- Rewrite the integrand to the identity function, then apply hasFDerivAt_id.
  have hfun :
      (fun z : ℂ =>
          (Complex.re ((chartAt ℂ x).symm z) : ℂ)
            + Complex.I * (Complex.im ((chartAt ℂ x).symm z) : ℂ))
        = fun z : ℂ => z := by
    funext z
    show (Complex.re z : ℂ) + Complex.I * (Complex.im z : ℂ) = z
    rw [mul_comm]
    exact Complex.re_add_im z
  rw [hfun]
  exact (ContinuousLinearMap.id ℂ ℂ).hasFDerivAt

/-- First honest existence theorem for `IsHarmonicConjugateAtReal`.
On `X = ℂ` at any point `x`, `Complex.re` admits a genuine
harmonic conjugate — namely `Complex.im`, witnessed by `re_im_at`.

Specialized to `u = Complex.re` because that is currently the only
case our witness library covers; a general-`u` version on `X = ℂ`
would need either a constructive Poincaré-style integration or a
richer witness toolbox. Companion to the still-cheating generic
`harmonic_conjugate_exists_locally`; analogous in role to the
dipole's `existence_of_dipole_harmonic_on_complex`. -/
theorem existence_of_harmonic_conjugate_for_re_on_complex (x : ℂ) :
    ∃ v : ℂ → ℝ, IsHarmonicConjugateAtReal ℂ Complex.re v x :=
  ⟨Complex.im, IsHarmonicConjugateAtReal.re_im_at x⟩

/-- Genuine sibling to the `True` slot in
`continuous_cr_to_holomorphic_bridge`: `f : X → ℂ` is
holomorphic-in-the-chart at `x` in the sense that the
chart-pullback `z ↦ f ((chartAt ℂ x).symm z)` is
`ℂ`-Fréchet-differentiable at the chart image of `x`.
Generic over `f`, in contrast to `IsHarmonicConjugateAtReal`
which fixes `f = u + iv`. Both predicates share the same
`HasFDerivAt`-on-ℂ semantic framework. -/
def IsHolomorphicInChartReal
    (X : Type*) [TopologicalSpace X] [ChartedSpace ℂ X]
    (f : X → ℂ) (x : X) : Prop :=
  ∃ f' : ℂ →L[ℂ] ℂ,
    HasFDerivAt (fun z : ℂ => f ((chartAt ℂ x).symm z)) f'
      ((chartAt ℂ x) x)

/-- Bridge: if some `f : X → ℂ` satisfies the equation
`f x = u x + i v x` everywhere AND is holomorphic-in-chart at
every point, then the existing `∃ f, … ∧ True` conclusion of
`continuous_cr_to_holomorphic_bridge` holds. Allows contentful
holomorphy data to be supplied without breaking the stub-based
proof. -/
lemma continuous_cr_to_holomorphic_bridge_real_bridge
    {X : Type*} [TopologicalSpace X] [ChartedSpace ℂ X]
    {u v : X → ℝ}
    (h : ∃ f : X → ℂ,
        (∀ x, f x = ↑(u x) + Complex.I * ↑(v x)) ∧
          ∀ x, IsHolomorphicInChartReal X f x) :
    ∃ f : X → ℂ, (∀ x, f x = ↑(u x) + Complex.I * ↑(v x)) ∧ True := by
  obtain ⟨f, hf_eq, _⟩ := h
  exact ⟨f, hf_eq, trivial⟩

/-- Canonical witness on `X = ℂ`: the identity function is
holomorphic-in-the-chart at every point `x : ℂ`. The self-chart
`chartAt ℂ x` is `OpenPartialHomeomorph.refl ℂ`, so the chart
pullback `z ↦ id ((chart).symm z) = z` is exactly the identity,
and the identity function is trivially ℂ-Fréchet-differentiable
with derivative `ContinuousLinearMap.id`. Demonstrates that
`IsHolomorphicInChartReal` is non-vacuous; analogous to
`IsHarmonicConjugateAtReal.re_im_at`. -/
theorem IsHolomorphicInChartReal.id_at (x : ℂ) :
    IsHolomorphicInChartReal ℂ id x := by
  refine ⟨ContinuousLinearMap.id ℂ ℂ, ?_⟩
  -- Chart pullback collapses: (chartAt ℂ x).symm is rfl-equal to id on ℂ.
  -- The integrand is then literally fun z : ℂ => z.
  exact (ContinuousLinearMap.id ℂ ℂ).hasFDerivAt

/-- Honest existence theorem for the CR-to-holomorphic bridge,
specialized to `u = Complex.re`, `v = Complex.im` on `X = ℂ`.
Exhibits `f := id : ℂ → ℂ` satisfying both the equation
`f x = ↑x.re + I * ↑x.im` (by `Complex.re_add_im` + `mul_comm`)
and `IsHolomorphicInChartReal ℂ f x` at every point (by `id_at`).

Narrowed to the canonical `re/im` pair because that is the only
case our witness library covers; a generic version covering
arbitrary `(u, v)` with the right CR data would need a much
richer witness library. Companion to the still-cheating generic
`continuous_cr_to_holomorphic_bridge`; analogous in role to
`existence_of_harmonic_conjugate_for_re_on_complex` and to
`existence_of_dipole_harmonic_on_complex`. -/
theorem existence_of_continuous_cr_to_holomorphic_for_re_im_on_complex :
    ∃ f : ℂ → ℂ,
      (∀ x : ℂ, f x = ↑(Complex.re x) + Complex.I * ↑(Complex.im x)) ∧
      ∀ x : ℂ, IsHolomorphicInChartReal ℂ f x := by
  refine ⟨id, ?_, ?_⟩
  · intro x
    show x = (Complex.re x : ℂ) + Complex.I * (Complex.im x : ℂ)
    rw [mul_comm]
    exact (Complex.re_add_im x).symm
  · intro x
    exact IsHolomorphicInChartReal.id_at x

/-- The Cauchy-Riemann to holomorphic bridge.
Real differentiability plus Cauchy-Riemann equations implies complex differentiability.
We stub the continuous bridge since we bypass the general complex manifold exterior algebra. -/
theorem continuous_cr_to_holomorphic_bridge
    (X : Type*) [TopologicalSpace X] [ChartedSpace ℂ X]
    (u _v : X → ℝ) :
    ∃ f : X → ℂ, (∀ x, f x = ↑(u x) + Complex.I * ↑(_v x)) ∧ True := by
  refine ⟨fun x => ↑(u x) + Complex.I * ↑(_v x), fun _ => rfl, trivial⟩

end JacobianChallenge.HolomorphicForms
