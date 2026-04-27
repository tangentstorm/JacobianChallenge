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

/-- The map `ULift.up : quotient V Λ → ULift (quotient V Λ)` is `ContMDiff`
of every degree.

Top-down obligation: pointed to by `Jacobian/Solution.lean` for the
`ofCurve_contMDiff` lemma (composed with `analyticOfCurve_contMDiff`).
Bottom-up: a chart-target identity through `Homeomorph.ulift`. -/
lemma contMDiff_uLift_up
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V]
    [FiniteDimensional ℂ V] {Λ : FullComplexLattice V}
    {n : WithTop ℕ∞} :
    ContMDiff (modelWithCornersSelf ℂ V) (modelWithCornersSelf ℂ V) n
      (ULift.up : quotient V Λ → ULift.{u} (quotient V Λ)) := sorry

/-- `ULift.down : ULift M → M` is `ContMDiff` of every degree, for the
ULift transports of any complex torus quotient. Companion to
`contMDiff_uLift_up`. -/
lemma contMDiff_uLift_down
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V]
    [FiniteDimensional ℂ V] {Λ : FullComplexLattice V}
    {n : WithTop ℕ∞} :
    ContMDiff (modelWithCornersSelf ℂ V) (modelWithCornersSelf ℂ V) n
      (ULift.down : ULift.{u} (quotient V Λ) → quotient V Λ) := sorry

/-- Lift a continuous additive group homomorphism from the analytic
carriers up to their `ULift` versions.

Pure assembly — composes `ULift.up` and `ULift.down` (both continuous)
with the underlying hom; no sorry of its own. -/
noncomputable def ULiftContinuousAddMonoidHom
    {A B : Type*} [AddMonoid A] [AddMonoid B]
    [TopologicalSpace A] [TopologicalSpace B]
    (φ : A →ₜ+ B) : ULift.{u} A →ₜ+ ULift.{u} B where
  toFun a := ULift.up (φ a.down)
  map_zero' := by
    show ULift.up (φ (0 : ULift.{u} A).down) = (0 : ULift.{u} B)
    simp [map_zero]
    rfl
  map_add' a b := by
    show ULift.up (φ (a + b).down) = ULift.up (φ a.down) + ULift.up (φ b.down)
    simp [map_add]
    rfl
  continuous_toFun :=
    continuous_uliftUp.comp (φ.continuous.comp continuous_uliftDown)

end JacobianChallenge.ComplexTorus
