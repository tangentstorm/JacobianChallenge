import Mathlib.Geometry.Manifold.VectorBundle.Tangent
import Mathlib.Analysis.Complex.Basic
import Mathlib.Geometry.Manifold.ContMDiff.NormedSpace

/-!
# Local ℂ-field bridge for `TangentSpace 𝓘(ℂ, ℂ) z`

`TangentSpace 𝓘(ℂ, ℂ) z` is definitionally equal to `ℂ`, but the
underlying `def` is **not reducible**, so instance synthesis does not
transport `ℂ`'s field structure (`Inv`, `Field`, `CommRing`, ...) to
`TangentSpace 𝓘(ℂ, ℂ) z` automatically.

`Jacobian/TraceDegree/TraceDefinition.lean` already provides the
`NormedAddCommGroup` and `NormedSpace ℂ` scoped instances (the bare
minimum for the `IsIso` predicate on `mfderiv 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) f x`).

This file adds the **field-structure** synthesis needed by the ramified
trace-form argument (`ramifiedKfoldSum_locally_bounded` in
`HolomorphicForms/TraceSpec.lean`), where one needs to invert `mfderiv`
factors and compose `cotangentPushforward` post-multiplications in
chart coordinates. Without these, Lean cannot synthesise `a⁻¹` for
`a : TangentSpace 𝓘(ℂ, ℂ) z`, even though the underlying type is `ℂ`.

All instances are scoped to `JacobianChallenge.HolomorphicForms` (and
named `private`-style with a clear `tangentSpace_complex_` prefix) so
they cannot leak into the global namespace.

Strategy: every instance is `inferInstanceAs (_ ℂ)`, transported across
the definitional equality `TangentSpace 𝓘(ℂ, ℂ) z = ℂ`.

This is **Milestone 1** of the worker-3 (jc3) branch-point trace-bound
project (see `.sci/plan.md`). Milestone 2 (the roots-of-unity
cancellation bound) uses these instances directly.
-/

namespace JacobianChallenge.HolomorphicForms

open scoped Manifold

/-! ### Ring / field-structure scoped instances on `TangentSpace 𝓘(ℂ, ℂ) z`. -/

noncomputable scoped instance tangentSpace_complex_inv
    {Z : Type*} [TopologicalSpace Z] [ChartedSpace ℂ Z] (z : Z) :
    Inv (TangentSpace 𝓘(ℂ, ℂ) z) :=
  inferInstanceAs (Inv ℂ)

noncomputable scoped instance tangentSpace_complex_commRing
    {Z : Type*} [TopologicalSpace Z] [ChartedSpace ℂ Z] (z : Z) :
    CommRing (TangentSpace 𝓘(ℂ, ℂ) z) :=
  inferInstanceAs (CommRing ℂ)

noncomputable scoped instance tangentSpace_complex_field
    {Z : Type*} [TopologicalSpace Z] [ChartedSpace ℂ Z] (z : Z) :
    Field (TangentSpace 𝓘(ℂ, ℂ) z) :=
  inferInstanceAs (Field ℂ)

/-! ### Explicit transport across the definitional equality. -/

/--
**Definitional bridge.** The tangent space of `ℂ` (modelled on itself)
at any point of a `ChartedSpace ℂ Z` is the type `ℂ`. This lemma exposes
the equality at the type level — it is `rfl`, but stating it lets
downstream proofs explicitly invoke it (e.g. for `show`/`change`
gymnastics around CLM types).
-/
theorem tangentSpace_complex_eq_complex
    {Z : Type*} [TopologicalSpace Z] [ChartedSpace ℂ Z] (z : Z) :
    TangentSpace 𝓘(ℂ, ℂ) z = ℂ := rfl

/--
**Linear-equiv transport.** `TangentSpace 𝓘(ℂ, ℂ) z ≃ₗ[ℂ] ℂ`, given by
the identity at the underlying-type level. This is `LinearEquiv.refl ℂ ℂ`
under the definitional equality — useful as a named witness for explicit
transports in the kfold-cancellation argument.
-/
noncomputable def tangentSpaceComplexEquiv
    {Z : Type*} [TopologicalSpace Z] [ChartedSpace ℂ Z] (z : Z) :
    TangentSpace 𝓘(ℂ, ℂ) z ≃ₗ[ℂ] ℂ :=
  LinearEquiv.refl ℂ ℂ

@[simp]
theorem tangentSpaceComplexEquiv_apply
    {Z : Type*} [TopologicalSpace Z] [ChartedSpace ℂ Z] (z : Z)
    (v : TangentSpace 𝓘(ℂ, ℂ) z) :
    tangentSpaceComplexEquiv z v = v := rfl

@[simp]
theorem tangentSpaceComplexEquiv_symm_apply
    {Z : Type*} [TopologicalSpace Z] [ChartedSpace ℂ Z] (z : Z)
    (w : ℂ) :
    (tangentSpaceComplexEquiv z).symm w = w := rfl

end JacobianChallenge.HolomorphicForms
