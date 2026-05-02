import Mathlib.Analysis.Complex.Basic

/-!
# Hermitian-positivity helpers (chart-local, complex-only)

Three small leaves of `thm:hermitian-positivity` (sec03) that bottom
out in pure complex-analysis on `ℂ` — no manifold integration, no
Stokes, no surface classification.

Plan: `ref/plans/hermitian-positivity.md`.

* `two_norm_sq_nonneg` — `0 ≤ 2 * ‖h‖²` (leaf 3 of the plan).
* `two_norm_sq_pos_of_ne_zero` — `h ≠ 0 → 0 < 2 * ‖h‖²` (leaf 4).
* `nonzero_complex_has_witness` — `h ≠ 0 → ∃ z : ℂ, z = h ∧ z ≠ 0`
  (leaf 8 in pointwise-on-ℂ form; the manifold-level "nonzero
  HolomorphicOneForm has a chart point with `h(p) ≠ 0`" extends this
  to sections of the cotangent bundle and is left for a separate
  follow-up).

These are fully Mathlib-resolvable; see prompts in
`ref/plans/hermitian-positivity.md` §9 for the recommended tactics.
-/

namespace JacobianChallenge.Periods.Hermitian

/-- **Leaf 3 (SHORT).** The pointwise integrand `2 * ‖h‖²` of
`i ω ∧ conj ω` is nonneg. Direct from `sq_nonneg` / `pow_two_nonneg`. -/
theorem two_norm_sq_nonneg (h : ℂ) : (0 : ℝ) ≤ 2 * ‖h‖ ^ 2 := by
  positivity

/-- **Leaf 4 (SHORT).** The pointwise integrand `2 * ‖h‖²` is strictly
positive at points where `h ≠ 0`. Direct from
`norm_pos_iff` + `pow_pos` + `mul_pos`. -/
theorem two_norm_sq_pos_of_ne_zero (h : ℂ) (hh : h ≠ 0) :
    (0 : ℝ) < 2 * ‖h‖ ^ 2 :=
  mul_pos two_pos (pow_pos (norm_pos_iff.mpr hh) 2)

/-- **Leaf 8 (SHORT — pointwise version).** A nonzero complex number
trivially has a "witness" — itself. This is the pointwise stand-in
for the manifold-level statement that a nonzero holomorphic 1-form
has a chart point with `h(p) ≠ 0`. The lift to sections of the
cotangent bundle requires `HolomorphicOneForm`-side machinery and is
deferred to a separate sec03 leaf. -/
theorem nonzero_complex_has_witness (h : ℂ) (hh : h ≠ 0) :
    ∃ z : ℂ, z = h ∧ z ≠ 0 :=
  ⟨h, rfl, hh⟩

end JacobianChallenge.Periods.Hermitian
