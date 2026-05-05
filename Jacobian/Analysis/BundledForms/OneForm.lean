import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Calculus.ContDiff.Basic

/-!
# R9 — Chart-local complex 1-forms and the line integral

This file is the second non-placeholder layer of R9, focused on
exactly the piece the Jacobian construction actually consumes: a
**complex 1-form on a chart** of a Riemann surface, plus its
**line integral** along a smooth path.

## What is a chart-local complex 1-form?

A holomorphic 1-form on a Riemann surface, restricted to a single
holomorphic chart `U ⊆ ℂ`, has the form `f(z) dz` for a holomorphic
function `f : U → ℂ`.  We model the chart-local case by collapsing
the bundle bookkeeping: `ChartOneForm := ℂ → ℂ`, where the value
`ω z` plays the role of the coefficient of `dz`.  This is enough
to express the line integral

  `∫_γ ω = ∫₀¹ ω(γ t) · γ'(t) dt`

and the Newton–Leibniz identity, which together imply that the line
integral of an *exact* 1-form (one of the form `df`) over a closed
loop is zero — the half of "periods are well-defined modulo exact"
that this file delivers.  The other half (closed-form integration is
cycle-class invariant) reduces to Stokes/Cauchy on a chart and is
left as a future round.

## Why this design?

A bundled `Ω¹(X)` for a Riemann surface `X` would package the
chart-local data above with cocycle compatibility under chart
transitions and the `Mathlib`-level alternating-form bundle
machinery (R9-sub-A/B/C).  Since that infrastructure does not exist
in Mathlib v4.28.0, this file restricts to a single chart and
focuses on making line integration and Newton–Leibniz **real,
sorry-free** Lean theorems against Mathlib's existing
`intervalIntegral` and `deriv` APIs.
-/

namespace JacobianChallenge.Analysis.BundledForms.OneForm

open scoped Topology
open MeasureTheory intervalIntegral

/-- **Chart-local complex 1-form.**  A function `ω : ℂ → ℂ` whose
value `ω z` is the coefficient of `dz` at the point `z` in a single
holomorphic chart of a Riemann surface. -/
def ChartOneForm : Type := ℂ → ℂ

noncomputable instance : AddCommGroup ChartOneForm := by
  unfold ChartOneForm; infer_instance

noncomputable instance : Module ℂ ChartOneForm := by
  unfold ChartOneForm; infer_instance

/-! ### Round 12 — line integral along a smooth path -/

/-- **Line integral of a chart-local 1-form along a path
`γ : ℝ → ℂ`.**  Defined for `t ∈ [a, b]` by
  `∫_γ ω = ∫_a^b ω(γ t) · γ'(t) dt`.
This is the standard formula for `∫_γ f(z) dz` once the path is
parameterised. -/
noncomputable def lineIntegral
    (ω : ChartOneForm) (γ : ℝ → ℂ) (a b : ℝ) : ℂ :=
  ∫ t in a..b, ω (γ t) * deriv γ t

/-- Line integral is linear in the form. -/
theorem lineIntegral_add (ω₁ ω₂ : ChartOneForm) (γ : ℝ → ℂ) (a b : ℝ)
    (h₁ : IntervalIntegrable (fun t => ω₁ (γ t) * deriv γ t)
            MeasureTheory.volume a b)
    (h₂ : IntervalIntegrable (fun t => ω₂ (γ t) * deriv γ t)
            MeasureTheory.volume a b) :
    lineIntegral (ω₁ + ω₂) γ a b
      = lineIntegral ω₁ γ a b + lineIntegral ω₂ γ a b := by
  unfold lineIntegral
  show ∫ t in a..b, ((ω₁ + ω₂) (γ t)) * deriv γ t
    = (∫ t in a..b, ω₁ (γ t) * deriv γ t)
      + (∫ t in a..b, ω₂ (γ t) * deriv γ t)
  rw [show (fun t => ((ω₁ + ω₂) (γ t)) * deriv γ t)
        = (fun t => ω₁ (γ t) * deriv γ t)
          + (fun t => ω₂ (γ t) * deriv γ t) from by
        funext t
        show (ω₁ + ω₂) (γ t) * deriv γ t
            = ω₁ (γ t) * deriv γ t + ω₂ (γ t) * deriv γ t
        rw [show (ω₁ + ω₂) (γ t) = ω₁ (γ t) + ω₂ (γ t) from rfl]
        ring]
  exact intervalIntegral.integral_add h₁ h₂

/-! ### Round 13 — Newton–Leibniz for `df` -/

/-- **The exterior derivative of a `C¹` 0-form**, in chart-local
form: `(df)(z) = f'(z)` (the complex derivative of the underlying
function).  This is the `k = 0` exterior derivative specialised to
`E = F = ℂ` and rephrased as a complex `ChartOneForm`. -/
noncomputable def derivAsOneForm (f : ℂ → ℂ) : ChartOneForm :=
  fun z => deriv f z

/-- **Newton–Leibniz for `∫_γ df`.**  For a `C¹` function `f : ℂ → ℂ`
and any `C¹` path `γ : ℝ → ℂ` whose differential `f ∘ γ` is
integrable on `[a, b]`, the line integral of `df` along `γ` equals
the difference of endpoint values:
  `∫_γ df = f(γ b) − f(γ a)`.
This is Mathlib's fundamental theorem of calculus
(`intervalIntegral.integral_eq_sub_of_hasDerivAt`) composed with
the chain rule. -/
theorem lineIntegral_derivAsOneForm
    {f : ℂ → ℂ} {γ : ℝ → ℂ} {a b : ℝ}
    (hf : ∀ t ∈ Set.uIcc a b, HasDerivAt f (deriv f (γ t)) (γ t))
    (hγ : ∀ t ∈ Set.uIcc a b, HasDerivAt γ (deriv γ t) t)
    (h_int : IntervalIntegrable
      (fun t => deriv f (γ t) * deriv γ t)
      MeasureTheory.volume a b) :
    lineIntegral (derivAsOneForm f) γ a b = f (γ b) - f (γ a) := by
  unfold lineIntegral derivAsOneForm
  have hcomp : ∀ t ∈ Set.uIcc a b,
      HasDerivAt (f ∘ γ) (deriv f (γ t) * deriv γ t) t := fun t ht =>
    (hf t ht).comp t (hγ t ht)
  have := intervalIntegral.integral_eq_sub_of_hasDerivAt hcomp h_int
  simpa [Function.comp] using this

/-- **Round 14 corollary: closed-loop integral of an exact form vanishes.**
For a `C¹` function `f : ℂ → ℂ` and a `C¹` loop `γ` with
`γ a = γ b`, the line integral of `df` along `γ` is zero. -/
theorem lineIntegral_derivAsOneForm_loop_eq_zero
    {f : ℂ → ℂ} {γ : ℝ → ℂ} {a b : ℝ}
    (hf : ∀ t ∈ Set.uIcc a b, HasDerivAt f (deriv f (γ t)) (γ t))
    (hγ : ∀ t ∈ Set.uIcc a b, HasDerivAt γ (deriv γ t) t)
    (h_int : IntervalIntegrable
      (fun t => deriv f (γ t) * deriv γ t)
      MeasureTheory.volume a b)
    (hloop : γ a = γ b) :
    lineIntegral (derivAsOneForm f) γ a b = 0 := by
  rw [lineIntegral_derivAsOneForm hf hγ h_int, hloop, sub_self]

/-! ### Round 15 — pullback of chart-local 1-forms by smooth maps -/

/-- **Pullback of a chart-local 1-form.**  For a `C¹` map
`φ : ℂ → ℂ` and a 1-form `ω`, the pullback `φ^* ω` is given on a
chart-local model by
  `(φ^* ω)(z) = ω(φ z) · φ'(z)`.
This is the standard `f(z) dz ↦ f(φ(z)) φ'(z) dz` formula. -/
noncomputable def pullback (φ : ℂ → ℂ) (ω : ChartOneForm) : ChartOneForm :=
  fun z => ω (φ z) * deriv φ z

/-- Pullback is `ℂ`-linear in the form.  -/
theorem pullback_add (φ : ℂ → ℂ) (ω₁ ω₂ : ChartOneForm) :
    pullback φ (ω₁ + ω₂) = pullback φ ω₁ + pullback φ ω₂ := by
  funext z
  show (ω₁ + ω₂) (φ z) * deriv φ z
      = ω₁ (φ z) * deriv φ z + ω₂ (φ z) * deriv φ z
  rw [show (ω₁ + ω₂) (φ z) = ω₁ (φ z) + ω₂ (φ z) from rfl]
  ring

theorem pullback_smul (c : ℂ) (φ : ℂ → ℂ) (ω : ChartOneForm) :
    pullback φ (c • ω) = c • pullback φ ω := by
  funext z
  show (c • ω) (φ z) * deriv φ z = c * (ω (φ z) * deriv φ z)
  rw [show (c • ω) (φ z) = c * ω (φ z) from rfl]
  ring

/-- **Change-of-variables for the line integral.**  The integral of
`ω` along `φ ∘ γ` equals the integral of `φ^* ω` along `γ`, provided
`γ` and `φ` are differentiable in the right sense.  This is the
standard substitution rule. -/
theorem lineIntegral_pullback
    {φ : ℂ → ℂ} {ω : ChartOneForm} {γ : ℝ → ℂ} {a b : ℝ}
    (hφ : ∀ t ∈ Set.uIcc a b, HasDerivAt φ (deriv φ (γ t)) (γ t))
    (hγ : ∀ t ∈ Set.uIcc a b, HasDerivAt γ (deriv γ t) t) :
    lineIntegral ω (φ ∘ γ) a b = lineIntegral (pullback φ ω) γ a b := by
  unfold lineIntegral pullback
  refine intervalIntegral.integral_congr (fun t ht => ?_)
  have hcomp : HasDerivAt (φ ∘ γ) (deriv φ (γ t) * deriv γ t) t :=
    (hφ t ht).comp t (hγ t ht)
  have h_eq : deriv (φ ∘ γ) t = deriv φ (γ t) * deriv γ t := hcomp.deriv
  show ω (φ (γ t)) * deriv (φ ∘ γ) t
    = ω (φ (γ t)) * deriv φ (γ t) * deriv γ t
  rw [h_eq]
  ring

/-! ### Round 16 — additivity of the line integral over path concatenation -/

/-- **Additivity of the line integral over a midpoint split.**
For `a ≤ b ≤ c` (or any choice in which both sub-integrands are
integrable on the respective intervals), the line integral over
`[a, c]` is the sum of the integrals over `[a, b]` and `[b, c]`.
This is the path-concatenation identity needed for splitting a
loop into two arcs. -/
theorem lineIntegral_concat
    (ω : ChartOneForm) (γ : ℝ → ℂ) (a b c : ℝ)
    (h₁ : IntervalIntegrable (fun t => ω (γ t) * deriv γ t)
            MeasureTheory.volume a b)
    (h₂ : IntervalIntegrable (fun t => ω (γ t) * deriv γ t)
            MeasureTheory.volume b c) :
    lineIntegral ω γ a c
      = lineIntegral ω γ a b + lineIntegral ω γ b c := by
  unfold lineIntegral
  exact (intervalIntegral.integral_add_adjacent_intervals h₁ h₂).symm

/-! ### Round 17 — holomorphic 1-form predicate -/

/-- **Holomorphic 1-form (chart-local).**  A `ChartOneForm` `ω` is
holomorphic on a set `s ⊆ ℂ` when its underlying coefficient
function `z ↦ ω z` is differentiable in the complex sense at every
`z ∈ s`.  This is the chart-local restriction of the global notion
``ω is a holomorphic 1-form on a Riemann surface'': in a holomorphic
chart, `ω = f(z) dz` is holomorphic iff its `f` is. -/
def IsHolomorphicOn (ω : ChartOneForm) (s : Set ℂ) : Prop :=
  ∀ z ∈ s, DifferentiableAt ℂ ω z

/-- **The exterior derivative of a holomorphic 0-form is a
holomorphic 1-form.**  If `f : ℂ → ℂ` is `C²` (hence its complex
derivative is itself differentiable) on a set `s`, then `df`
is holomorphic on `s`. -/
theorem isHolomorphicOn_derivAsOneForm
    {f : ℂ → ℂ} {s : Set ℂ}
    (hf : ∀ z ∈ s, DifferentiableAt ℂ (deriv f) z) :
    IsHolomorphicOn (derivAsOneForm f) s := by
  intro z hz
  exact hf z hz

/-! ### Round 18 — concrete example: `∫_γ dz = γ(b) − γ(a)` -/

/-- **`dz` as the exterior derivative of the identity function.**
The chart-local 1-form `dz` is `derivAsOneForm (fun z => z)`, i.e.
the constant function `z ↦ 1`. -/
theorem derivAsOneForm_id : derivAsOneForm (fun z : ℂ => z)
    = (fun _ : ℂ => (1 : ℂ)) := by
  funext z
  show deriv (fun z : ℂ => z) z = 1
  simp

/-- **Worked example: `∫_γ dz = γ(b) − γ(a)`.**  Plugging `f = id`
into Newton–Leibniz reduces a `dz` integral to the endpoint
difference of the path, irrespective of the path's shape — the
simplest non-trivial Cauchy/Stokes-style identity. -/
theorem lineIntegral_dz_eq_endpoint_diff
    {γ : ℝ → ℂ} {a b : ℝ}
    (hγ : ∀ t ∈ Set.uIcc a b, HasDerivAt γ (deriv γ t) t)
    (h_int : IntervalIntegrable (fun t => deriv γ t)
              MeasureTheory.volume a b) :
    lineIntegral (fun _ : ℂ => (1 : ℂ)) γ a b = γ b - γ a := by
  have h := lineIntegral_derivAsOneForm
    (f := fun z : ℂ => z) (γ := γ) (a := a) (b := b)
    (fun t ht => by
      have hid : HasDerivAt (fun z : ℂ => z) 1 (γ t) := hasDerivAt_id _
      have hderiv : deriv (fun z : ℂ => z) (γ t) = 1 := by simp
      rw [hderiv]; exact hid)
    hγ
    (by
      have hderiv : (fun t : ℝ => deriv (fun z : ℂ => z) (γ t) * deriv γ t)
                  = fun t => deriv γ t := by
        funext t; simp
      rw [hderiv]; exact h_int)
  rw [derivAsOneForm_id] at h
  exact h

end JacobianChallenge.Analysis.BundledForms.OneForm
