import Jacobian.ComplexTorus.ChartedSpace
import Jacobian.ComplexTorus.IsManifold
import Jacobian.ComplexTorus.LieAddGroup

/-!
# ULift transport of the complex torus manifold structure

`Jacobian/Solution.lean` defines `Jacobian X` as a `ULift` of a complex
torus quotient (so it lives in the right universe). The complex torus
quotient already carries a `ChartedSpace`, `IsManifold`, and
`LieAddGroup` structure (from `Jacobian.ComplexTorus.{ChartedSpace,
IsManifold, LieAddGroup}`); this file transports those structures along
the homeomorphism `Homeomorph.ulift : ULift M ≃ₜ M`.

These three instances are the named bottom-up obligations pointed to by
the top-down refinement of the `ChartedSpace`, `IsManifold`, and
`LieAddGroup` instances on `Jacobian X` in `Solution.lean`. They are
generic in the carrier `V` rather than specialised to the period quotient
because the transport itself does not depend on the specific lattice.

Bottom-up: the `ChartedSpace` transport requires composing each
quotient chart with `Homeomorph.ulift`. The `IsManifold` transport
requires showing that the resulting chart transitions remain analytic
(automatic, since `Homeomorph.ulift` and its inverse are continuous and
do not change the analytic-structure side). The `LieAddGroup` transport
requires that addition on `ULift` is `ContMDiff` — direct from the
`AddCommGroup` instance on `ULift` and analyticity of `+` and `-` on
`quotient V Λ`.
-/

namespace JacobianChallenge.ComplexTorus

open scoped Manifold

universe u

/-- ULift transport of the complex torus charted-space structure.

Top-down obligation: pointed to by `Jacobian/Solution.lean` for the
`ChartedSpace` instance on `Jacobian X`. -/
noncomputable instance complexTorusULift_chartedSpace
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V]
    [FiniteDimensional ℂ V] (Λ : FullComplexLattice V) :
    ChartedSpace V (ULift.{u} (quotient V Λ)) := sorry

/-- ULift transport of the complex torus manifold structure.

Top-down obligation: pointed to by `Jacobian/Solution.lean` for the
`IsManifold` instance on `Jacobian X`. -/
noncomputable instance complexTorusULift_isManifold
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V]
    [FiniteDimensional ℂ V] (Λ : FullComplexLattice V) :
    IsManifold (modelWithCornersSelf ℂ V) (⊤ : WithTop ℕ∞)
      (ULift.{u} (quotient V Λ)) := sorry

/-- ULift transport of the complex torus Lie-add-group structure.

Top-down obligation: pointed to by `Jacobian/Solution.lean` for the
`LieAddGroup` instance on `Jacobian X`. -/
noncomputable instance complexTorusULift_lieAddGroup
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V]
    [FiniteDimensional ℂ V] (Λ : FullComplexLattice V) :
    LieAddGroup (modelWithCornersSelf ℂ V) (⊤ : WithTop ℕ∞)
      (ULift.{u} (quotient V Λ)) := sorry

end JacobianChallenge.ComplexTorus
