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

/-- Transporting both charts in a transition along a homeomorphism does not
change the transition, up to source-equivalence. Pure assembly from
Mathlib's `OpenPartialHomeomorph.symm_trans_self` plus standard
re-association. -/
lemma homeomorph_transOpenPartialHomeomorph_transition_eqOnSource
    {A B C : Type*} [TopologicalSpace A] [TopologicalSpace B] [TopologicalSpace C]
    (e : A ≃ₜ B) (c c' : OpenPartialHomeomorph B C) :
    (e.transOpenPartialHomeomorph c).symm ≫ₕ e.transOpenPartialHomeomorph c' ≈
      c.symm ≫ₕ c' := by
  rw [Homeomorph.transOpenPartialHomeomorph_eq_trans,
      Homeomorph.transOpenPartialHomeomorph_eq_trans,
      OpenPartialHomeomorph.trans_symm_eq_symm_trans_symm,
      OpenPartialHomeomorph.trans_assoc,
      ← OpenPartialHomeomorph.trans_assoc e.toOpenPartialHomeomorph.symm
        e.toOpenPartialHomeomorph c']
  refine OpenPartialHomeomorph.EqOnSource.trans' (Setoid.refl _) ?_
  refine Setoid.trans
    (OpenPartialHomeomorph.EqOnSource.trans'
      e.toOpenPartialHomeomorph.symm_trans_self (Setoid.refl c')) ?_
  simp only [Homeomorph.toOpenPartialHomeomorph_target,
    OpenPartialHomeomorph.ofSet_univ_eq_refl, OpenPartialHomeomorph.refl_trans]
  exact OpenPartialHomeomorph.eqOnSource_refl c'

/-- The complex-torus chart at a `ULift`ed quotient point, transported
through `Homeomorph.ulift`. -/
noncomputable def complexTorusULiftChartAt
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V]
    (Λ : FullComplexLattice V) (q : ULift.{u} (quotient V Λ)) :
    OpenPartialHomeomorph (ULift.{u} (quotient V Λ)) V :=
  (Homeomorph.ulift : ULift.{u} (quotient V Λ) ≃ₜ quotient V Λ).transOpenPartialHomeomorph
    (chartAtPoint Λ q.down)

/-- ULift transport of the complex torus charted-space structure.

Top-down obligation: pointed to by `Jacobian/Solution.lean` for the
`ChartedSpace` instance on `Jacobian X`. -/
noncomputable instance complexTorusULift_chartedSpace
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V]
    [FiniteDimensional ℂ V] (Λ : FullComplexLattice V) :
    ChartedSpace V (ULift.{u} (quotient V Λ)) where
  atlas := Set.range (complexTorusULiftChartAt Λ)
  chartAt := complexTorusULiftChartAt Λ
  mem_chart_source q := by
    change q.down ∈ (chartAtPoint Λ q.down).source
    exact mem_chartAtPoint_source Λ q.down
  chart_mem_atlas q := ⟨q, rfl⟩

/-- The transition between two `ULift`-transported quotient charts agrees,
on its source, with the corresponding transition between the underlying
quotient charts.

Top-down obligation. Bottom-up: reassociate the `OpenPartialHomeomorph`
composition and cancel
`Homeomorph.ulift.toOpenPartialHomeomorph.symm ≫ₕ
Homeomorph.ulift.toOpenPartialHomeomorph`. -/
lemma complexTorusULift_transition_eqOnSource
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V]
    (Λ : FullComplexLattice V)
    (q q' : ULift.{u} (quotient V Λ)) :
    (complexTorusULiftChartAt Λ q).symm ≫ₕ complexTorusULiftChartAt Λ q' ≈
      (chartAtPoint Λ q.down).symm ≫ₕ chartAtPoint Λ q'.down := by
  exact homeomorph_transOpenPartialHomeomorph_transition_eqOnSource
    (Homeomorph.ulift : ULift.{u} (quotient V Λ) ≃ₜ quotient V Λ)
    (chartAtPoint Λ q.down) (chartAtPoint Λ q'.down)

/-- ULift transport of the complex torus `HasGroupoid` structure.

Pure assembly from `complexTorusULift_transition_eqOnSource` and the
underlying quotient manifold transition theorem. -/
noncomputable instance complexTorusULift_hasGroupoid
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V]
    [FiniteDimensional ℂ V] (Λ : FullComplexLattice V) :
    HasGroupoid (ULift.{u} (quotient V Λ))
      (contDiffGroupoid (⊤ : WithTop ℕ∞) (modelWithCornersSelf ℂ V)) := by
  refine ⟨?_⟩
  rintro e e' ⟨q, rfl⟩ ⟨q', rfl⟩
  exact (contDiffGroupoid (⊤ : WithTop ℕ∞) (modelWithCornersSelf ℂ V)).mem_of_eqOnSource
    ((contDiffGroupoid (⊤ : WithTop ℕ∞) (modelWithCornersSelf ℂ V)).compatible
      (chart_mem_atlas V q.down) (chart_mem_atlas V q'.down))
    (complexTorusULift_transition_eqOnSource Λ q q')

/-- ULift transport of the complex torus manifold structure.

Top-down obligation: pointed to by `Jacobian/Solution.lean` for the
`IsManifold` instance on `Jacobian X`. -/
noncomputable instance complexTorusULift_isManifold
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V]
    [FiniteDimensional ℂ V] (Λ : FullComplexLattice V) :
    IsManifold (modelWithCornersSelf ℂ V) (⊤ : WithTop ℕ∞)
      (ULift.{u} (quotient V Λ)) where

/-- ULift transport of the complex torus Lie-add-group structure.

Top-down obligation: pointed to by `Jacobian/Solution.lean` for the
`LieAddGroup` instance on `Jacobian X`. -/
noncomputable instance complexTorusULift_contMDiffAdd
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V]
    [FiniteDimensional ℂ V] (Λ : FullComplexLattice V) :
    ContMDiffAdd (modelWithCornersSelf ℂ V) (⊤ : WithTop ℕ∞)
      (ULift.{u} (quotient V Λ)) := sorry

/-- Negation on the `ULift`ed quotient is analytic for the transported
complex-torus manifold structure.

Top-down obligation. Bottom-up: compose `ULift.down`, quotient negation,
and `ULift.up`, using `contMDiff_quotient_neg` and the smoothness of the
ULift equivalence. -/
lemma complexTorusULift_contMDiff_neg
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V]
    [FiniteDimensional ℂ V] (Λ : FullComplexLattice V) :
    ContMDiff (modelWithCornersSelf ℂ V) (modelWithCornersSelf ℂ V)
      (⊤ : WithTop ℕ∞) (fun a : ULift.{u} (quotient V Λ) => -a) := sorry

noncomputable instance complexTorusULift_lieAddGroup
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V]
    [FiniteDimensional ℂ V] (Λ : FullComplexLattice V) :
    LieAddGroup (modelWithCornersSelf ℂ V) (⊤ : WithTop ℕ∞)
      (ULift.{u} (quotient V Λ)) where
  contMDiff_neg := complexTorusULift_contMDiff_neg Λ

/-- The quotient-to-ULift direction of the `Homeomorph.ulift` equivalence is
analytic for the transported chart structure.

Top-down obligation. Bottom-up: in the transported charts this map is the
identity on the model space. -/
lemma complexTorusULift_contMDiff_up
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V]
    [FiniteDimensional ℂ V] (Λ : FullComplexLattice V)
    {n : WithTop ℕ∞} :
    ContMDiff (modelWithCornersSelf ℂ V) (modelWithCornersSelf ℂ V) n
      (ULift.up : quotient V Λ → ULift.{u} (quotient V Λ)) := sorry

/-- The ULift-to-quotient direction of the `Homeomorph.ulift` equivalence is
analytic for the transported chart structure.

Top-down obligation. Bottom-up: companion to
`complexTorusULift_contMDiff_up`; in transported charts this map is the
identity on the model space. -/
lemma complexTorusULift_contMDiff_down
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V]
    [FiniteDimensional ℂ V] (Λ : FullComplexLattice V)
    {n : WithTop ℕ∞} :
    ContMDiff (modelWithCornersSelf ℂ V) (modelWithCornersSelf ℂ V) n
      (ULift.down : ULift.{u} (quotient V Λ) → quotient V Λ) := sorry

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
      (ULift.up : quotient V Λ → ULift.{u} (quotient V Λ)) :=
  complexTorusULift_contMDiff_up Λ

/-- `ULift.down : ULift M → M` is `ContMDiff` of every degree, for the
ULift transports of any complex torus quotient. Companion to
`contMDiff_uLift_up`. -/
lemma contMDiff_uLift_down
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V]
    [FiniteDimensional ℂ V] {Λ : FullComplexLattice V}
    {n : WithTop ℕ∞} :
    ContMDiff (modelWithCornersSelf ℂ V) (modelWithCornersSelf ℂ V) n
      (ULift.down : ULift.{u} (quotient V Λ) → quotient V Λ) :=
  complexTorusULift_contMDiff_down Λ

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
