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

end JacobianChallenge.Periods
