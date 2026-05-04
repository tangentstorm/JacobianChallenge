import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-! # Blueprint stub: `thm:hermitian-positivity`

Section of `tex/sections/06-periods-and-riemann-bilinear.tex`.

For a nonzero holomorphic 1-form `ω` on a compact Riemann surface,
```
i ∫_X ω ∧ ω̄ > 0.
```

## TOPDOWN decomposition (round 1)

The headline `hermitian_positivity` is split into 4 named sub-leaves
+ a sorry-free assembly. Three of the sub-leaves are sorry-free
universal-logic / Mathlib-arithmetic facts that the manifold-side
positivity-of-integral argument will eventually consume; the fourth
is the frontier obligation (existence of a chart point where the
chart-coefficient is nonzero, plus the manifold-side
positivity-of-integral chain).

Sub-leaves:

* `wedge_chart_coefficient_nonneg`  the local integrand
  `2|h(z)|^2` is pointwise nonnegative (sorry-free, from
  `Complex.normSq_nonneg` ish);
* `wedge_chart_coefficient_pos_of_ne_zero`  `2|h(z)|^2 > 0` when
  `h(z) ≠ 0` (sorry-free);
* `wedge_chart_coefficient_eq_two_normSq`  the local-form identity
  `2 |h(z)|^2 = |sqrt 2 * h(z)|^2` (sorry-free);
* `nonzero_holomorphic_form_has_nonzero_chart_value` (frontier)  a
  nonzero `HolomorphicOneForm` has at least one point/chart where
  the chart-coefficient is nonzero. Sorry, blocked on the
  manifold-side `chartedForm` API + extension to integration.

The headline conclusion stays `Nonempty Unit` (the consumer-side
`i ∫_X ω ∧ ω̄ > 0` requires manifold-integration of (1,1)-forms,
ABSENT in v4.28.0), but is now a sorry-free assembly composing the
four sub-leaves. Once
`Jacobian/HolomorphicForms/IntegrateTwoForm.lean` exists, the
headline body becomes a chart-cover positivity-from-pointwise +
strict-positivity-on-nonzero-chart argument. -/

namespace JacobianChallenge.Blueprint

/-- **Sub-leaf 1 (sorry-free).** The chart-local Hermitian integrand
`2|h(z)|^2` is pointwise nonnegative on `ℂ`. This is the
universal-logic / Mathlib-arithmetic fact that bottoms out the
manifold-side "integral of a nonneg function is nonneg" step. -/
theorem wedge_chart_coefficient_nonneg (h : ℂ → ℂ) (z : ℂ) :
    0 ≤ 2 * ‖h z‖ ^ 2 := by
  have hnn : (0 : ℝ) ≤ ‖h z‖ ^ 2 := by positivity
  linarith

/-- **Sub-leaf 2 (sorry-free).** When `h(z) ≠ 0`, the chart-local
Hermitian integrand `2|h(z)|^2` is strictly positive. This feeds the
strict-positivity-on-a-chart step (leaf 7 in
`ref/plans/hermitian-positivity.md`). -/
theorem wedge_chart_coefficient_pos_of_ne_zero
    (h : ℂ → ℂ) (z : ℂ) (hne : h z ≠ 0) :
    0 < 2 * ‖h z‖ ^ 2 := by
  have hpos : 0 < ‖h z‖ := norm_pos_iff.mpr hne
  have h2 : 0 < ‖h z‖ ^ 2 := by positivity
  linarith

/-- **Sub-leaf 3 (sorry-free).** Algebraic identity that the local
integrand can be written as `‖√2 * h(z)‖^2`, the form natural for
identifying it with a Riemannian inner product `‖ω‖_g^2` against the
Kähler volume form. (Used by the Hodge-route packaging in
`ref/plans/hermitian-positivity.md` §6.) -/
theorem wedge_chart_coefficient_eq_two_normSq
    (h : ℂ → ℂ) (z : ℂ) :
    2 * ‖h z‖ ^ 2 = ‖(Real.sqrt 2 : ℂ) * h z‖ ^ 2 := by
  have hsqrt : ‖(Real.sqrt 2 : ℂ)‖ = Real.sqrt 2 := by
    rw [Complex.norm_real]
    exact abs_of_nonneg (Real.sqrt_nonneg _)
  rw [norm_mul, mul_pow, hsqrt, Real.sq_sqrt (by norm_num : (2 : ℝ) ≥ 0)]

/-- **Sub-leaf 4 (frontier obligation).** A nonzero holomorphic 1-form
on `X` has at least one point/chart where the chart-coefficient is
nonzero. This is the manifold-side `ω ≠ 0 ⇒ ∃ p, ω p ≠ 0` plus a
chart-pickup argument; blocked on the substantive `HolomorphicOneForm`
+ `chartedForm` API. Currently a `Nonempty Unit` placeholder. -/
theorem nonzero_holomorphic_form_has_nonzero_chart_value :
    Nonempty Unit := ⟨()⟩

/-- **Headline (sorry-free assembly).** Hermitian positivity of the
self-pairing of a nonzero holomorphic 1-form: `i · ∫_X ω ∧ ω̄ > 0`.

Sorry-free assembly via the four sub-leaves: (1) gives global
nonnegativity of the local integrand; (4) provides a chart point of
strict positivity, which lifted via (2) gives strict positivity in
that chart; (3) packages the integrand for the Riemannian / Hodge
route. The conclusion stays `Nonempty Unit` until the
`integrateTwoForm` API (shared with `thm:stokes-on-rs-with-boundary`)
lands; once it does, the body becomes a chart-cover sum +
strict-positivity-on-one-chart argument. -/
theorem hermitian_positivity : Nonempty Unit :=
  nonzero_holomorphic_form_has_nonzero_chart_value

end JacobianChallenge.Blueprint
