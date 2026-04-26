import Jacobian.HolomorphicForms.Defs

/-!
# Chart-local transport of a holomorphic 1-form

Queue D scaffolding. To integrate a `HolomorphicOneForm E X` along a
path that lives inside a single chart `c : OpenPartialHomeomorph X E`,
we first transport `ω` to a 1-form `chartedForm c ω : E → E →L[ℂ] ℂ`
on the model space `E`. Then Mathlib's `curveIntegral` applies to a
path in `E`.

`chartedForm` is defined pointwise: at `e : E`, evaluate `ω` at the
corresponding manifold point `c.symm e`. The fiber type
`CotangentSpace E X (c.symm e) = TangentSpace I (c.symm e) →L[ℂ] ℂ`
reduces to `E →L[ℂ] ℂ` because `TangentSpace I _ = E` by
trivialization in `Mathlib.Geometry.Manifold.MFDeriv.Defs`.

This is the chart-local building block used by the eventual
`PathIntegralChart` definition.

**Known correctness gap.** The current definition is *not* the
genuine chart pullback of a 1-form. A proper chart pullback would be

```text
chartedForm c ω e v = ω.toFun (c.symm e) (D(c.symm)_e v)
```

— i.e., the value of `ω` at the manifold point `c.symm e`, applied
to the chart-derivative `D(c.symm)` of the input tangent vector
`v`. The current code drops the `D(c.symm)_e` factor, which Lean
accepts only because Mathlib's `TangentSpace` trivialization makes
this type-check. The integral defined from this transport agrees
with the true integral only when chart transitions are translations
(zero derivative correction), which is the torus case but not the
general Riemann-surface case. Fixing this is a queued task.
-/

namespace JacobianChallenge.Periods

open JacobianChallenge.HolomorphicForms

/-- Transport a holomorphic 1-form on `X` to a 1-form on the model
space `E`, by pulling back through a chart's `symm`. The result is
defined globally on `E`; it agrees with the genuine pullback only on
`c.target` (outside, the value depends on `c.symm`'s out-of-source
behavior, which is junk). -/
noncomputable def chartedForm
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    {X : Type*} [TopologicalSpace X] [ChartedSpace E X]
    [IsManifold (modelWithCornersSelf ℂ E) (⊤ : WithTop ℕ∞) X]
    (c : OpenPartialHomeomorph X E)
    (ω : HolomorphicOneForm E X) :
    E → E →L[ℂ] ℂ :=
  fun e => ω.toFun (c.symm e)

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  {X : Type*} [TopologicalSpace X] [ChartedSpace E X]
  [IsManifold (modelWithCornersSelf ℂ E) (⊤ : WithTop ℕ∞) X]

@[simp] theorem chartedForm_apply
    (c : OpenPartialHomeomorph X E) (ω : HolomorphicOneForm E X) (e : E) :
    chartedForm c ω e = ω.toFun (c.symm e) := rfl

/-- The chart-transport of the zero `HolomorphicOneForm` is the zero
1-form on the model space. -/
@[simp] theorem chartedForm_zero
    (c : OpenPartialHomeomorph X E) :
    chartedForm c (0 : HolomorphicOneForm E X) = 0 := by
  funext e
  show ((0 : HolomorphicOneForm E X) : ∀ x, _) (c.symm e) = 0
  rw [ContMDiffSection.coe_zero]
  rfl

end JacobianChallenge.Periods
