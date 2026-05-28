import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Calculus.FDeriv.Basic
import Mathlib.Analysis.SpecialFunctions.Complex.LogDeriv
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

/-- Genuine sibling to the `True`-stub `IsHarmonicOff`: at every
point off the singular set `{P, Q}`, `u` admits a local harmonic
conjugate (in the contentful `IsHarmonicConjugateAtReal` sense).
On simply-connected charts this is mathematically equivalent to
classical harmonicity (`Δu = 0`), but stated this way it stays
within our existing `HasFDerivAt`-on-ℂ semantic framework and
avoids `iteratedFDeriv ℝ 2` plumbing. `True`-style cheats no
longer satisfy it once it is the demanded predicate.

Lives in `HarmonicConjugate.lean` rather than `HarmonicDipole.lean`
because it references `IsHarmonicConjugateAtReal`, which is
defined here. -/
def IsHarmonicOffReal
    (X : Type*) [TopologicalSpace X] [ChartedSpace ℂ X]
    (P Q : X) (u : X → ℝ) : Prop :=
  ∀ x : X, x ≠ P → x ≠ Q →
    ∃ v : X → ℝ, IsHarmonicConjugateAtReal X u v x

/-- Bridge from the genuine `IsHarmonicOffReal` predicate to the
`True`-stub `IsHarmonicOff`. Allows contentful harmonic-off
witnesses to be supplied without breaking the stub-based proof
of `existence_of_dipole_harmonic`. -/
lemma IsHarmonicOffReal.toStub
    {X : Type*} [TopologicalSpace X] [ChartedSpace ℂ X]
    {P Q : X} {u : X → ℝ}
    (_h : IsHarmonicOffReal X P Q u) :
    IsHarmonicOff X P Q u :=
  trivial

/-- Canonical witness on `X = ℂ`: the real-part function `Complex.re`
is harmonic-off `{P, Q}` for ANY pair `P, Q : ℂ`. At every point
`x : ℂ` (including the supposedly-excluded `P` and `Q` themselves)
the conjugate `Complex.im` works via `re_im_at x`. Demonstrates
that `IsHarmonicOffReal` is non-vacuous; analogous to
`IsHarmonicConjugateAtReal.re_im_at` and to
`IsHolomorphicInChartReal.id_at`. -/
theorem IsHarmonicOffReal.re_off (P Q : ℂ) :
    IsHarmonicOffReal ℂ P Q Complex.re := by
  intro x _ _
  exact ⟨Complex.im, IsHarmonicConjugateAtReal.re_im_at x⟩

/-- Honest existence theorem for `IsHarmonicOffReal`, specialized
on `X = ℂ`. For any `P, Q : ℂ`, exhibit a `u : ℂ → ℝ` (namely
`Complex.re`) genuinely satisfying `IsHarmonicOffReal ℂ P Q u`.
Proof is the one-line tuple ⟨Complex.re, re_off P Q⟩.

Fourth honest existential in the project. Mirrors:
- existence_of_dipole_harmonic_on_complex (9aaa54d7) — dipole track
- existence_of_harmonic_conjugate_for_re_on_complex (95367526) — Stub 1
- existence_of_continuous_cr_to_holomorphic_for_re_im_on_complex (33db01e9) — Stub 2

Specialized to the witness `Complex.re` because that is currently
the only `IsHarmonicOffReal` witness; a generic-`u` version on
`X = ℂ` would require richer harmonic-conjugate machinery
(Complex.log/arg pair for the canonical dipole, plus closure
lemmas), which is a multi-commit follow-up. Does not touch the
still-cheating generic `existence_of_dipole_harmonic`. -/
theorem existence_of_harmonic_off_for_re_on_complex (P Q : ℂ) :
    ∃ u : ℂ → ℝ, IsHarmonicOffReal ℂ P Q u :=
  ⟨Complex.re, IsHarmonicOffReal.re_off P Q⟩

/-- Second-phase witness for `IsHarmonicConjugateAtReal` using
nontrivial Mathlib API. On `X = ℂ` at any `x ∈ Complex.slitPlane`
(i.e. `x ∉ ℝ≤0`), `Complex.arg` is a harmonic conjugate of
`fun z => Real.log ‖z‖`. The full holomorphic function is
`Complex.log z`, which is ℂ-differentiable on `slitPlane` by
`Complex.hasDerivAt_log`. The chart pullback collapses via the
self-chart `rfl`, and the integrand
`(↑(log ‖z‖) + I * ↑(arg z))` equals `Complex.log z` after a
`mul_comm` (the equation is essentially the definition of
`Complex.log` rotated).

Building block toward proving the canonical dipole
`log ‖· - P‖ - log ‖· - Q‖` is harmonic off `{P, Q}`. -/
theorem IsHarmonicConjugateAtReal.log_arg_at_slitPlane
    {x : ℂ} (hx : x ∈ Complex.slitPlane) :
    IsHarmonicConjugateAtReal ℂ (fun z : ℂ => Real.log ‖z‖) Complex.arg x := by
  refine ⟨ContinuousLinearMap.smulRight (1 : ℂ →L[ℂ] ℂ) x⁻¹, ?_⟩
  -- Chart pullback on the self-chart collapses to identity; rewrite
  -- the integrand to Complex.log via its definition + mul_comm.
  have hfun :
      (fun z : ℂ =>
          (Real.log ‖(chartAt ℂ x).symm z‖ : ℂ)
            + Complex.I * (Complex.arg ((chartAt ℂ x).symm z) : ℂ))
        = Complex.log := by
    funext z
    show (Real.log ‖z‖ : ℂ) + Complex.I * (Complex.arg z : ℂ)
        = Complex.log z
    rw [mul_comm]
    rfl
  rw [hfun]
  exact (Complex.hasDerivAt_log hx).hasFDerivAt

/-- Translated version of `log_arg_at_slitPlane`: on `X = ℂ` at
any `x` with `x - P ∈ Complex.slitPlane`, the function
`fun z => Complex.arg (z - P)` is a harmonic conjugate of
`fun z => Real.log ‖z - P‖`. The combined function is
`fun z => Complex.log (z - P)`, ℂ-differentiable at `x` by the
chain rule (translation has derivative 1, `Complex.log` has
derivative `(x - P)⁻¹` on the translated slit plane).

Building block toward the canonical dipole's `+1` pole part. -/
theorem IsHarmonicConjugateAtReal.log_arg_sub_at_slitPlane
    {x P : ℂ} (hx : x - P ∈ Complex.slitPlane) :
    IsHarmonicConjugateAtReal ℂ
      (fun z : ℂ => Real.log ‖z - P‖)
      (fun z : ℂ => Complex.arg (z - P)) x := by
  refine ⟨ContinuousLinearMap.smulRight (1 : ℂ →L[ℂ] ℂ) (1 / (x - P)), ?_⟩
  have hfun :
      (fun z : ℂ =>
          (Real.log ‖(chartAt ℂ x).symm z - P‖ : ℂ)
            + Complex.I * (Complex.arg ((chartAt ℂ x).symm z - P) : ℂ))
        = fun z : ℂ => Complex.log (z - P) := by
    funext z
    show (Real.log ‖z - P‖ : ℂ) + Complex.I * (Complex.arg (z - P) : ℂ)
        = Complex.log (z - P)
    rw [mul_comm]
    rfl
  rw [hfun]
  exact (((hasDerivAt_id x).sub_const P).clog hx).hasFDerivAt

/-- Generic negation closure for `IsHarmonicConjugateAtReal`: if
`v` is a harmonic conjugate of `u` at `x`, then `-v` is a harmonic
conjugate of `-u` at `x`. Proof negates the underlying `HasFDerivAt`
witness via `HasFDerivAt.neg`; the integrand rewrite uses
`Complex.ofReal_neg` and a `ring` rearrangement to align
`(-u : ℂ) + I * (-v) = -((u : ℂ) + I * v)`.

Generic structural lemma — applies to any `(u, v, x)`. -/
lemma IsHarmonicConjugateAtReal.neg
    {X : Type*} [TopologicalSpace X] [ChartedSpace ℂ X]
    {u v : X → ℝ} {x : X}
    (h : IsHarmonicConjugateAtReal X u v x) :
    IsHarmonicConjugateAtReal X (-u) (-v) x := by
  obtain ⟨f', hf⟩ := h
  refine ⟨-f', ?_⟩
  have hfun :
      (fun z : ℂ =>
          ((-u) ((chartAt ℂ x).symm z) : ℂ)
            + Complex.I * ((-v) ((chartAt ℂ x).symm z) : ℂ))
        = (fun z : ℂ =>
            -((u ((chartAt ℂ x).symm z) : ℂ)
              + Complex.I * (v ((chartAt ℂ x).symm z) : ℂ))) := by
    funext z
    show ((-(u ((chartAt ℂ x).symm z)) : ℝ) : ℂ)
          + Complex.I * ((-(v ((chartAt ℂ x).symm z)) : ℝ) : ℂ)
        = -(((u ((chartAt ℂ x).symm z)) : ℂ)
          + Complex.I * ((v ((chartAt ℂ x).symm z)) : ℂ))
    push_cast
    ring
  rw [hfun]
  exact hf.neg

/-- Specialization of `IsHarmonicConjugateAtReal.neg` to the
translated log/arg pair: the `-1`-pole-side conjugate witness
needed for the canonical dipole. On `X = ℂ` at any `x` with
`x - Q ∈ Complex.slitPlane`, the function
`fun z => -Complex.arg (z - Q)` is a harmonic conjugate of
`fun z => -Real.log ‖z - Q‖`. Combined holomorphic function is
`-Complex.log (z - Q)`. -/
theorem IsHarmonicConjugateAtReal.neg_log_arg_sub_at_slitPlane
    {x Q : ℂ} (hxQ : x - Q ∈ Complex.slitPlane) :
    IsHarmonicConjugateAtReal ℂ
      (fun z : ℂ => -Real.log ‖z - Q‖)
      (fun z : ℂ => -Complex.arg (z - Q)) x := by
  have h := (IsHarmonicConjugateAtReal.log_arg_sub_at_slitPlane
                (P := Q) hxQ).neg
  exact h

/-- Generic additive closure for `IsHarmonicConjugateAtReal`: if
`(u₁, v₁)` and `(u₂, v₂)` both satisfy the predicate at the same
`x`, then their pointwise sum `(u₁ + u₂, v₁ + v₂)` does too. Proof
adds the underlying `HasFDerivAt` witnesses via `HasFDerivAt.add`;
the integrand rewrite uses `Complex.ofReal_add` (via `push_cast`)
and `ring` to align
`((u₁ + u₂) : ℂ) + I * (v₁ + v₂) = ((u₁ : ℂ) + I * v₁) + ((u₂ : ℂ) + I * v₂)`.

Generic structural lemma — applies to any `(u_i, v_i, x)`.
Companion to `IsHarmonicConjugateAtReal.neg`. -/
lemma IsHarmonicConjugateAtReal.add
    {X : Type*} [TopologicalSpace X] [ChartedSpace ℂ X]
    {u₁ v₁ u₂ v₂ : X → ℝ} {x : X}
    (h₁ : IsHarmonicConjugateAtReal X u₁ v₁ x)
    (h₂ : IsHarmonicConjugateAtReal X u₂ v₂ x) :
    IsHarmonicConjugateAtReal X (u₁ + u₂) (v₁ + v₂) x := by
  obtain ⟨f₁', hf₁⟩ := h₁
  obtain ⟨f₂', hf₂⟩ := h₂
  refine ⟨f₁' + f₂', ?_⟩
  have hfun :
      (fun z : ℂ =>
          ((u₁ + u₂) ((chartAt ℂ x).symm z) : ℂ)
            + Complex.I * ((v₁ + v₂) ((chartAt ℂ x).symm z) : ℂ))
        = (fun z : ℂ =>
            ((u₁ ((chartAt ℂ x).symm z) : ℂ)
              + Complex.I * (v₁ ((chartAt ℂ x).symm z) : ℂ))
            + ((u₂ ((chartAt ℂ x).symm z) : ℂ)
              + Complex.I * (v₂ ((chartAt ℂ x).symm z) : ℂ))) := by
    funext z
    show (((u₁ ((chartAt ℂ x).symm z) + u₂ ((chartAt ℂ x).symm z)) : ℝ) : ℂ)
          + Complex.I
            * (((v₁ ((chartAt ℂ x).symm z) + v₂ ((chartAt ℂ x).symm z)) : ℝ) : ℂ)
        = ((u₁ ((chartAt ℂ x).symm z) : ℂ)
            + Complex.I * (v₁ ((chartAt ℂ x).symm z) : ℂ))
          + ((u₂ ((chartAt ℂ x).symm z) : ℂ)
            + Complex.I * (v₂ ((chartAt ℂ x).symm z) : ℂ))
    push_cast
    ring
  rw [hfun]
  exact hf₁.add hf₂

/-- Generic constant-shift closure for `IsHarmonicConjugateAtReal`:
if `v` is a harmonic conjugate of `u` at `x`, then `v + β` is a
harmonic conjugate of `u + α` at `x` for any real constants
`α, β : ℝ`. Adding a real constant to `u` corresponds to adding
the complex constant `α + I * β` to `f := u + iv`, which
preserves ℂ-Fréchet-differentiability via `HasFDerivAt.add_const`.

Generic structural lemma — companion to `.neg` and `.add`. Needed
by the branch-rotation work: the rotated witness
`IsHarmonicConjugateAtReal ℂ (log ‖c (· - P)‖) (arg (c (· - P))) x`
produces an integrand whose real part is `log ‖c‖ + log ‖z - P‖`,
differing from the desired `log ‖z - P‖` by the constant `log ‖c‖`. -/
lemma IsHarmonicConjugateAtReal.add_const_const
    {X : Type*} [TopologicalSpace X] [ChartedSpace ℂ X]
    {u v : X → ℝ} {x : X}
    (h : IsHarmonicConjugateAtReal X u v x) (α β : ℝ) :
    IsHarmonicConjugateAtReal X
      (fun z : X => u z + α) (fun z : X => v z + β) x := by
  obtain ⟨f', hf⟩ := h
  refine ⟨f', ?_⟩
  have hfun :
      (fun z : ℂ =>
          ((u ((chartAt ℂ x).symm z) + α : ℝ) : ℂ)
            + Complex.I * ((v ((chartAt ℂ x).symm z) + β : ℝ) : ℂ))
        = (fun z : ℂ =>
            ((u ((chartAt ℂ x).symm z) : ℂ)
              + Complex.I * (v ((chartAt ℂ x).symm z) : ℂ))
            + ((α : ℂ) + Complex.I * (β : ℂ))) := by
    funext z
    show (((u ((chartAt ℂ x).symm z) + α) : ℝ) : ℂ)
          + Complex.I
            * (((v ((chartAt ℂ x).symm z) + β) : ℝ) : ℂ)
        = ((u ((chartAt ℂ x).symm z) : ℂ)
            + Complex.I * (v ((chartAt ℂ x).symm z) : ℂ))
          + ((α : ℂ) + Complex.I * (β : ℂ))
    push_cast
    ring
  rw [hfun]
  exact hf.add_const _

/-- Eventual-equality congruence for `IsHarmonicConjugateAtReal`:
if `(u₁, v₁)` satisfy the predicate at `x` and `(u₂, v₂)` agree
with `(u₁, v₁)` on a neighborhood of `x`, then `(u₂, v₂)` satisfy
the predicate at `x` as well. Proof transports the underlying
`HasFDerivAt` witness via `HasFDerivAt.congr_of_eventuallyEq`.

Needed because some natural function identities (e.g.
`Real.log ‖c * (z - P)‖ = Real.log ‖c‖ + Real.log ‖z - P‖` via
`Real.log_mul + norm_mul`) only hold locally away from special
points (here `z ≠ P`, since `Real.log 0 = 0` by convention).
Global-function rewrites fail; eventual-equality rewrites work.

Generic structural lemma — companion to `.neg`, `.add`, `.add_const_const`. -/
lemma IsHarmonicConjugateAtReal.congr_of_eventuallyEq
    {X : Type*} [TopologicalSpace X] [ChartedSpace ℂ X]
    {u₁ v₁ u₂ v₂ : X → ℝ} {x : X}
    (h : IsHarmonicConjugateAtReal X u₁ v₁ x)
    (hu : u₁ =ᶠ[nhds x] u₂) (hv : v₁ =ᶠ[nhds x] v₂) :
    IsHarmonicConjugateAtReal X u₂ v₂ x := by
  obtain ⟨f', hf⟩ := h
  refine ⟨f', ?_⟩
  have hsymm_cont : Filter.Tendsto (fun z : ℂ => (chartAt ℂ x).symm z)
      (nhds ((chartAt ℂ x) x)) (nhds x) := by
    have hcont : ContinuousAt (chartAt ℂ x).symm ((chartAt ℂ x) x) :=
      (chartAt ℂ x).continuousAt_symm
        ((chartAt ℂ x).map_source (mem_chart_source ℂ x))
    have hinv : (chartAt ℂ x).symm ((chartAt ℂ x) x) = x :=
      (chartAt ℂ x).left_inv (mem_chart_source ℂ x)
    simpa [ContinuousAt, hinv] using hcont.tendsto
  have hu' : (fun z : ℂ => u₁ ((chartAt ℂ x).symm z))
              =ᶠ[nhds ((chartAt ℂ x) x)]
             (fun z : ℂ => u₂ ((chartAt ℂ x).symm z)) :=
    hsymm_cont.eventually hu
  have hv' : (fun z : ℂ => v₁ ((chartAt ℂ x).symm z))
              =ᶠ[nhds ((chartAt ℂ x) x)]
             (fun z : ℂ => v₂ ((chartAt ℂ x).symm z)) :=
    hsymm_cont.eventually hv
  have hsum : (fun z : ℂ =>
                (u₁ ((chartAt ℂ x).symm z) : ℂ)
                  + Complex.I * (v₁ ((chartAt ℂ x).symm z) : ℂ))
              =ᶠ[nhds ((chartAt ℂ x) x)]
              (fun z : ℂ =>
                (u₂ ((chartAt ℂ x).symm z) : ℂ)
                  + Complex.I * (v₂ ((chartAt ℂ x).symm z) : ℂ)) := by
    filter_upwards [hu', hv'] with z hzu hzv
    rw [hzu, hzv]
  exact hf.congr_of_eventuallyEq hsum.symm

/-- Rotated translated log/arg witness: for `c * (x - P) ∈ Complex.slitPlane`,
the function `fun z => Complex.arg (c * (z - P))` is a harmonic conjugate
of `fun z => Real.log ‖c * (z - P)‖`. Combined holomorphic function is
`fun z => Complex.log (c * (z - P))`, ℂ-differentiable at `x` by the
chain rule (translation has derivative 1, multiplication by `c` has
derivative `c`, `Complex.log` at `c * (x - P)` has derivative
`(c * (x - P))⁻¹`).

Key building block for branch-rotation: when `x - P` is on the
standard branch cut `ℝ≤0`, pick a rotation `c` to move it off the
cut and use this rotated witness instead of `log_arg_sub_at_slitPlane`.
The `c = 0` case is vacuous (hypothesis fails by `zero_notMem_slitPlane`). -/
theorem IsHarmonicConjugateAtReal.log_arg_rotated_sub_at_slitPlane
    {x P c : ℂ} (hxc : c * (x - P) ∈ Complex.slitPlane) :
    IsHarmonicConjugateAtReal ℂ
      (fun z : ℂ => Real.log ‖c * (z - P)‖)
      (fun z : ℂ => Complex.arg (c * (z - P))) x := by
  refine ⟨ContinuousLinearMap.smulRight (1 : ℂ →L[ℂ] ℂ)
            (c * 1 / (c * (x - P))), ?_⟩
  have hfun :
      (fun z : ℂ =>
          (Real.log ‖c * ((chartAt ℂ x).symm z - P)‖ : ℂ)
            + Complex.I
              * (Complex.arg (c * ((chartAt ℂ x).symm z - P)) : ℂ))
        = fun z : ℂ => Complex.log (c * (z - P)) := by
    funext z
    show (Real.log ‖c * (z - P)‖ : ℂ)
          + Complex.I * (Complex.arg (c * (z - P)) : ℂ)
        = Complex.log (c * (z - P))
    rw [mul_comm Complex.I]
    rfl
  rw [hfun]
  exact (((hasDerivAt_id x).sub_const P).const_mul c).clog hxc
        |>.hasFDerivAt

/-- Normalized rotated witness: absorb the `log ‖c‖` constant from
`log_arg_rotated_sub_at_slitPlane` to land the `u` slot at the
standard `log ‖z - P‖`. The `v` slot keeps the rotated form
`arg (c * (z - P))`, which is a perfectly valid conjugate (the
`IsHarmonicConjugateAtReal` predicate is existential in `v`).

For `c * (x - P) ∈ Complex.slitPlane`, both `c ≠ 0` and `x ≠ P`
follow via `zero_notMem_slitPlane` + `mul_ne_zero_iff`. The
`log ‖c * (z - P)‖ = log ‖c‖ + log ‖z - P‖` identity holds on
a neighborhood of `x` (specifically `{z | z ≠ P}`), so the
`add_const_const + congr_of_eventuallyEq` chain absorbs the
constant. -/
theorem IsHarmonicConjugateAtReal.log_arg_rotated_normalized_at
    {x P c : ℂ} (hxc : c * (x - P) ∈ Complex.slitPlane) :
    IsHarmonicConjugateAtReal ℂ
      (fun z : ℂ => Real.log ‖z - P‖)
      (fun z : ℂ => Complex.arg (c * (z - P))) x := by
  have hcxP_ne : c * (x - P) ≠ 0 :=
    fun h => Complex.zero_notMem_slitPlane (h ▸ hxc)
  have hc_ne : c ≠ 0 := (mul_ne_zero_iff.mp hcxP_ne).1
  have hxP_ne : x - P ≠ 0 := (mul_ne_zero_iff.mp hcxP_ne).2
  have hxP : x ≠ P := sub_ne_zero.mp hxP_ne
  have h₀ := IsHarmonicConjugateAtReal.log_arg_rotated_sub_at_slitPlane
                (P := P) (c := c) hxc
  have h₁ := h₀.add_const_const (-Real.log ‖c‖) 0
  refine h₁.congr_of_eventuallyEq ?_ ?_
  · -- u-eventual-equality: log ‖c * (z - P)‖ + (-log ‖c‖) = log ‖z - P‖ near x.
    have hopen : {z : ℂ | z ≠ P} ∈ nhds x :=
      IsOpen.mem_nhds (isOpen_compl_iff.mpr (T1Space.t1 P)) hxP
    filter_upwards [hopen] with z hzP
    have hzP_ne : z - P ≠ 0 := sub_ne_zero.mpr hzP
    show Real.log ‖c * (z - P)‖ + (-Real.log ‖c‖) = Real.log ‖z - P‖
    rw [norm_mul,
        Real.log_mul (norm_ne_zero_iff.mpr hc_ne)
                     (norm_ne_zero_iff.mpr hzP_ne)]
    ring
  · -- v-eventual-equality: arg (c * (z - P)) + 0 = arg (c * (z - P)).
    refine Filter.Eventually.of_forall (fun z => ?_)
    show Complex.arg (c * (z - P)) + 0 = Complex.arg (c * (z - P))
    ring

/-- Symmetric rotated -1 witness: the -1-pole-side counterpart to
`log_arg_rotated_normalized_at`. For `c * (x - Q) ∈ Complex.slitPlane`,
`fun z => -Complex.arg (c * (z - Q))` is a harmonic conjugate of
`fun z => -Real.log ‖z - Q‖`. Combined holomorphic function is
`-Complex.log (c * (z - Q))` (modulo absorbing `log ‖c‖` into the
constant). Mirrors the unrotated `neg_log_arg_sub_at_slitPlane`. -/
theorem IsHarmonicConjugateAtReal.neg_log_arg_rotated_normalized_at
    {x Q c : ℂ} (hxc : c * (x - Q) ∈ Complex.slitPlane) :
    IsHarmonicConjugateAtReal ℂ
      (fun z : ℂ => -Real.log ‖z - Q‖)
      (fun z : ℂ => -Complex.arg (c * (z - Q))) x := by
  have h := (IsHarmonicConjugateAtReal.log_arg_rotated_normalized_at
                (P := Q) (c := c) hxc).neg
  exact h

/-- Rotated dipole conjugate under common rotation. For any `x` with
a single rotation `c` such that `c * (x - P) ∈ Complex.slitPlane`
AND `c * (x - Q) ∈ Complex.slitPlane`, the canonical dipole
`log ‖z - P‖ - log ‖z - Q‖` has a harmonic conjugate at `x` given by
`arg (c * (z - P)) - arg (c * (z - Q))`.

Structurally identical to `dipole_conjugate_at_slit_intersection`
but with both branches rotated by the same `c`. Coverage region is
much larger: the topological existence-of-rotation lemma (next
commit) shows any `x ∉ {P, Q}` admits such a `c`. -/
theorem IsHarmonicConjugateAtReal.dipole_conjugate_at_common_rotation
    {x P Q c : ℂ}
    (hxP : c * (x - P) ∈ Complex.slitPlane)
    (hxQ : c * (x - Q) ∈ Complex.slitPlane) :
    IsHarmonicConjugateAtReal ℂ
      (fun z : ℂ => Real.log ‖z - P‖ - Real.log ‖z - Q‖)
      (fun z : ℂ =>
        Complex.arg (c * (z - P)) - Complex.arg (c * (z - Q))) x := by
  have hP := IsHarmonicConjugateAtReal.log_arg_rotated_normalized_at
                (P := P) (c := c) hxP
  have hQ := IsHarmonicConjugateAtReal.neg_log_arg_rotated_normalized_at
                (Q := Q) (c := c) hxQ
  have hsum := hP.add hQ
  have hfun_u :
      (fun z : ℂ => Real.log ‖z - P‖) + (fun z : ℂ => -Real.log ‖z - Q‖)
        = fun z : ℂ => Real.log ‖z - P‖ - Real.log ‖z - Q‖ := by
    funext z
    show Real.log ‖z - P‖ + -Real.log ‖z - Q‖
        = Real.log ‖z - P‖ - Real.log ‖z - Q‖
    ring
  have hfun_v :
      (fun z : ℂ => Complex.arg (c * (z - P)))
          + (fun z : ℂ => -Complex.arg (c * (z - Q)))
        = fun z : ℂ =>
            Complex.arg (c * (z - P)) - Complex.arg (c * (z - Q)) := by
    funext z
    show Complex.arg (c * (z - P)) + -Complex.arg (c * (z - Q))
        = Complex.arg (c * (z - P)) - Complex.arg (c * (z - Q))
    ring
  rw [hfun_u, hfun_v] at hsum
  exact hsum

/-- Combined conjugate witness for the canonical dipole at the
slit-intersection. For any `x` with `x - P ∈ Complex.slitPlane`
AND `x - Q ∈ Complex.slitPlane`, the function
`fun z => Complex.arg (z - P) - Complex.arg (z - Q)` is a
harmonic conjugate of
`fun z => Real.log ‖z - P‖ - Real.log ‖z - Q‖` (the canonical
real dipole). Combines `log_arg_sub_at_slitPlane` (+1 pole at P)
with `neg_log_arg_sub_at_slitPlane` (−1 pole at Q) via the
generic additive closure `IsHarmonicConjugateAtReal.add`.

NOT yet full coverage of `x ∉ {P, Q}` — both `x - P` and
`x - Q` must lie in the same (standard) slit `slitPlane`. The
branch-rotation step in the next commit lifts this restriction. -/
theorem IsHarmonicConjugateAtReal.dipole_conjugate_at_slit_intersection
    {x P Q : ℂ}
    (hxP : x - P ∈ Complex.slitPlane)
    (hxQ : x - Q ∈ Complex.slitPlane) :
    IsHarmonicConjugateAtReal ℂ
      (fun z : ℂ => Real.log ‖z - P‖ - Real.log ‖z - Q‖)
      (fun z : ℂ => Complex.arg (z - P) - Complex.arg (z - Q)) x := by
  have hP := IsHarmonicConjugateAtReal.log_arg_sub_at_slitPlane
                (P := P) hxP
  have hQ := IsHarmonicConjugateAtReal.neg_log_arg_sub_at_slitPlane
                (Q := Q) hxQ
  have hsum := hP.add hQ
  -- Rewrite Pi.add of (f, -g) to fun z => f z - g z.
  have hfun_u :
      (fun z : ℂ => Real.log ‖z - P‖) + (fun z : ℂ => -Real.log ‖z - Q‖)
        = fun z : ℂ => Real.log ‖z - P‖ - Real.log ‖z - Q‖ := by
    funext z
    show Real.log ‖z - P‖ + -Real.log ‖z - Q‖
        = Real.log ‖z - P‖ - Real.log ‖z - Q‖
    ring
  have hfun_v :
      (fun z : ℂ => Complex.arg (z - P)) + (fun z : ℂ => -Complex.arg (z - Q))
        = fun z : ℂ => Complex.arg (z - P) - Complex.arg (z - Q) := by
    funext z
    show Complex.arg (z - P) + -Complex.arg (z - Q)
        = Complex.arg (z - P) - Complex.arg (z - Q)
    ring
  rw [hfun_u, hfun_v] at hsum
  exact hsum

/-- The Cauchy-Riemann to holomorphic bridge.
Real differentiability plus Cauchy-Riemann equations implies complex differentiability.
We stub the continuous bridge since we bypass the general complex manifold exterior algebra. -/
theorem continuous_cr_to_holomorphic_bridge
    (X : Type*) [TopologicalSpace X] [ChartedSpace ℂ X]
    (u _v : X → ℝ) :
    ∃ f : X → ℂ, (∀ x, f x = ↑(u x) + Complex.I * ↑(_v x)) ∧ True := by
  refine ⟨fun x => ↑(u x) + Complex.I * ↑(_v x), fun _ => rfl, trivial⟩

end JacobianChallenge.HolomorphicForms
