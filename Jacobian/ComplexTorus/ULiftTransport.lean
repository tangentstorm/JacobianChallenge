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

/-- The chart on `ULift (quotient V Λ)` at `ULift.up x` applied to `ULift.up y`
unfolds to applying the underlying chart on `quotient V Λ` at `x` to `y`.

Pure unfolding of `complexTorusULiftChartAt`. -/
lemma complexTorusULiftChartAt_up_apply_up
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V]
    (Λ : FullComplexLattice V) (x y : quotient V Λ) :
    complexTorusULiftChartAt Λ (ULift.up x) (ULift.up y) =
      chartAtPoint Λ x y := rfl

/-- The inverse of the chart on `ULift (quotient V Λ)` at `ULift.up x` applied
to a vector `v : V` produces `ULift.up` of the underlying chart's inverse. -/
lemma complexTorusULiftChartAt_up_symm_apply
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V]
    (Λ : FullComplexLattice V) (x : quotient V Λ) (v : V) :
    (complexTorusULiftChartAt Λ (ULift.up x)).symm v =
      ULift.up ((chartAtPoint Λ x).symm v) := rfl

/-- The quotient-to-ULift direction of the `Homeomorph.ulift` equivalence is
analytic for the transported chart structure.

Top-down obligation. Bottom-up: in the transported charts this map is the
identity on the model space. -/
lemma complexTorusULift_contMDiff_up
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V]
    [FiniteDimensional ℂ V] (Λ : FullComplexLattice V)
    {n : WithTop ℕ∞} :
    ContMDiff (modelWithCornersSelf ℂ V) (modelWithCornersSelf ℂ V) n
      (ULift.up : quotient V Λ → ULift.{u} (quotient V Λ)) := by
  intro x
  -- We use `contMDiffAt_iff_of_mem_source` with source-chart at `x` and
  -- target-chart at `ULift.up x`. With the self-model, the model is the
  -- identity, so the chart-pulled-back map reduces to
  -- `chartAtPoint Λ x ∘ (chartAtPoint Λ x).symm`, which is the identity on
  -- `(chartAtPoint Λ x).target`, an open neighborhood of
  -- `extChartAt _ x x = chartAtPoint Λ x x`.
  have hx_src : x ∈ (chartAt V x).source := mem_chart_source V x
  have hux_src : (ULift.up x : ULift.{u} (quotient V Λ)) ∈
      (chartAt V (ULift.up x : ULift.{u} (quotient V Λ))).source :=
    mem_chart_source V (ULift.up x : ULift.{u} (quotient V Λ))
  rw [contMDiffAt_iff_of_mem_source (x := x) (y := (ULift.up x : ULift.{u} (quotient V Λ)))
    hx_src hux_src]
  refine ⟨continuous_uliftUp.continuousAt, ?_⟩
  -- The composition equals `id` on the chart's target.
  set chart : OpenPartialHomeomorph (quotient V Λ) V := chartAt V x with chart_def
  have htgt_open : IsOpen chart.target := chart.open_target
  have hxchart : chart x ∈ chart.target := chart.map_source hx_src
  -- The chart-pulled-back composition.
  set f : V → V := fun v =>
    (chartAt V (ULift.up x : ULift.{u} (quotient V Λ))) (ULift.up (chart.symm v)) with f_def
  -- On `chart.target`, `f = id`.
  have hf_eq_on : ∀ v ∈ chart.target, f v = v := by
    intro v hv
    show (chartAt V (ULift.up x : ULift.{u} (quotient V Λ)))
        (ULift.up (chart.symm v)) = v
    -- chartAt V (ULift.up x) = complexTorusULiftChartAt Λ (ULift.up x).
    -- Applied to ULift.up (chart.symm v), it equals chartAtPoint Λ x (chart.symm v).
    -- chart = chartAtPoint Λ x, so chart (chart.symm v) = v on chart.target.
    change complexTorusULiftChartAt Λ (ULift.up x) (ULift.up (chart.symm v)) = v
    rw [complexTorusULiftChartAt_up_apply_up]
    change chart (chart.symm v) = v
    exact chart.right_inv hv
  -- Convert `ContDiffWithinAt` of `id` at `chart x` within `univ` to `f`.
  have hid : ContDiffWithinAt ℂ n (id : V → V) (Set.range (modelWithCornersSelf ℂ V))
      (extChartAt (modelWithCornersSelf ℂ V) x x) :=
    contDiffWithinAt_id
  -- f and id agree on the chart's target, which is a neighborhood of chart x.
  have htgt_mem : chart.target ∈ nhds (chart x) := htgt_open.mem_nhds hxchart
  have hee : f =ᶠ[nhds (chart x)] (id : V → V) := by
    refine Filter.eventuallyEq_iff_exists_mem.mpr ⟨chart.target, htgt_mem, ?_⟩
    intro v hv
    exact hf_eq_on v hv
  -- Translate from `nhds` to `nhdsWithin`.
  have hee' : f =ᶠ[nhdsWithin
      (extChartAt (modelWithCornersSelf ℂ V) x x)
      (Set.range (modelWithCornersSelf ℂ V))] id := by
    have : (extChartAt (modelWithCornersSelf ℂ V) x) x = chart x := rfl
    rw [this]
    exact hee.filter_mono nhdsWithin_le_nhds
  have hfx : f (chart x) = id (chart x) := hf_eq_on (chart x) hxchart
  have : ContDiffWithinAt ℂ n f (Set.range (modelWithCornersSelf ℂ V))
      (extChartAt (modelWithCornersSelf ℂ V) x x) :=
    hid.congr_of_eventuallyEq hee' hfx
  -- Match the goal shape.
  convert this using 1

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
      (ULift.down : ULift.{u} (quotient V Λ) → quotient V Λ) := by
  intro q
  have hq_src : q ∈ (chartAt V q).source := mem_chart_source V q
  have hdq_src : q.down ∈ (chartAt V q.down).source := mem_chart_source V q.down
  rw [contMDiffAt_iff_of_mem_source (x := q) (y := q.down) hq_src hdq_src]
  refine ⟨continuous_uliftDown.continuousAt, ?_⟩
  -- Use the underlying chart on `quotient V Λ` at `q.down`.
  set chart : OpenPartialHomeomorph (quotient V Λ) V := chartAt V q.down with chart_def
  have htgt_open : IsOpen chart.target := chart.open_target
  have hxchart : chart q.down ∈ chart.target := chart.map_source hdq_src
  set f : V → V := fun v =>
    chart ((chartAt V q).symm v).down with f_def
  -- (chartAt V q).symm v = ULift.up (chart.symm v).
  have hf_eq : f = fun v => chart (chart.symm v) := by
    funext v
    show chart ((chartAt V q).symm v).down = chart (chart.symm v)
    -- chartAt V q is `complexTorusULiftChartAt Λ q`, whose symm sends v
    -- to `ULift.up ((chartAtPoint Λ q.down).symm v)`. The `.down` of that
    -- is `(chartAtPoint Λ q.down).symm v = chart.symm v`.
    rfl
  -- On chart.target, chart (chart.symm v) = v.
  have hf_eq_on : ∀ v ∈ chart.target, f v = v := by
    intro v hv
    rw [hf_eq]
    exact chart.right_inv hv
  -- The chart at q sends q to the same model-space value as chart at q.down.
  -- (chartAt V q) q = complexTorusULiftChartAt Λ q q = chartAtPoint Λ q.down q.down.
  have hchart_q : (extChartAt (modelWithCornersSelf ℂ V) q) q = chart q.down := rfl
  have hid : ContDiffWithinAt ℂ n (id : V → V)
      (Set.range (modelWithCornersSelf ℂ V))
      (extChartAt (modelWithCornersSelf ℂ V) q q) := contDiffWithinAt_id
  have htgt_mem : chart.target ∈ nhds (chart q.down) := htgt_open.mem_nhds hxchart
  have hee : f =ᶠ[nhds (chart q.down)] (id : V → V) := by
    refine Filter.eventuallyEq_iff_exists_mem.mpr ⟨chart.target, htgt_mem, ?_⟩
    intro v hv
    exact hf_eq_on v hv
  have hee' : f =ᶠ[nhdsWithin
      (extChartAt (modelWithCornersSelf ℂ V) q q)
      (Set.range (modelWithCornersSelf ℂ V))] id := by
    rw [hchart_q]
    exact hee.filter_mono nhdsWithin_le_nhds
  have hfx : f ((extChartAt (modelWithCornersSelf ℂ V) q) q) =
      id ((extChartAt (modelWithCornersSelf ℂ V) q) q) := by
    rw [hchart_q]
    exact hf_eq_on (chart q.down) hxchart
  have : ContDiffWithinAt ℂ n f
      (Set.range (modelWithCornersSelf ℂ V))
      (extChartAt (modelWithCornersSelf ℂ V) q q) :=
    hid.congr_of_eventuallyEq hee' hfx
  convert this using 1

/-- Addition on the `ULift`ed quotient is analytic for the transported
complex-torus manifold structure.

Top-down obligation. Bottom-up: compose `ULift.down` on both inputs,
use smooth addition on the quotient, and compose with `ULift.up`. -/
lemma complexTorusULift_contMDiff_add
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V]
    [FiniteDimensional ℂ V] (Λ : FullComplexLattice V) :
    ContMDiff ((modelWithCornersSelf ℂ V).prod (modelWithCornersSelf ℂ V))
      (modelWithCornersSelf ℂ V) (⊤ : WithTop ℕ∞)
      (fun p : ULift.{u} (quotient V Λ) × ULift.{u} (quotient V Λ) => p.1 + p.2) := by
  have hdown :
      ContMDiff ((modelWithCornersSelf ℂ V).prod (modelWithCornersSelf ℂ V))
        ((modelWithCornersSelf ℂ V).prod (modelWithCornersSelf ℂ V))
        (⊤ : WithTop ℕ∞)
        (fun p : ULift.{u} (quotient V Λ) × ULift.{u} (quotient V Λ) =>
          (p.1.down, p.2.down)) :=
    ((complexTorusULift_contMDiff_down Λ).comp contMDiff_fst).prodMk
      ((complexTorusULift_contMDiff_down Λ).comp contMDiff_snd)
  have h : (fun p : ULift.{u} (quotient V Λ) × ULift.{u} (quotient V Λ) => p.1 + p.2) =
      (ULift.up : quotient V Λ → ULift.{u} (quotient V Λ)) ∘
      (fun p : quotient V Λ × quotient V Λ => p.1 + p.2) ∘
      (fun p : ULift.{u} (quotient V Λ) × ULift.{u} (quotient V Λ) =>
        (p.1.down, p.2.down)) := by
    funext p
    rfl
  rw [h]
  exact (complexTorusULift_contMDiff_up Λ).comp
    ((contMDiff_quotient_add Λ).comp hdown)

noncomputable instance complexTorusULift_contMDiffAdd
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V]
    [FiniteDimensional ℂ V] (Λ : FullComplexLattice V) :
    ContMDiffAdd (modelWithCornersSelf ℂ V) (⊤ : WithTop ℕ∞)
      (ULift.{u} (quotient V Λ)) where
  contMDiff_add := complexTorusULift_contMDiff_add Λ

/-- Negation on the `ULift`ed quotient is analytic for the transported
complex-torus manifold structure.

Pure assembly: `(-a) = ULift.up (-a.down)` definitionally, so
negation on `ULift` factors as
`ULift.up ∘ (Neg.neg : quotient V Λ → quotient V Λ) ∘ ULift.down`,
each piece being smooth. -/
lemma complexTorusULift_contMDiff_neg
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V]
    [FiniteDimensional ℂ V] (Λ : FullComplexLattice V) :
    ContMDiff (modelWithCornersSelf ℂ V) (modelWithCornersSelf ℂ V)
      (⊤ : WithTop ℕ∞) (fun a : ULift.{u} (quotient V Λ) => -a) := by
  have h : (fun a : ULift.{u} (quotient V Λ) => -a) =
      (ULift.up : quotient V Λ → ULift.{u} (quotient V Λ)) ∘
      (fun a : quotient V Λ => -a) ∘
      (ULift.down : ULift.{u} (quotient V Λ) → quotient V Λ) := by
    funext a
    rfl
  rw [h]
  exact (complexTorusULift_contMDiff_up Λ).comp
    ((contMDiff_quotient_neg Λ).comp (complexTorusULift_contMDiff_down Λ))

/-- ULift transport of the complex torus Lie-add-group structure.

Top-down obligation: pointed to by `Jacobian/Solution.lean` for the
`LieAddGroup` instance on `Jacobian X`. -/
noncomputable instance complexTorusULift_lieAddGroup
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V]
    [FiniteDimensional ℂ V] (Λ : FullComplexLattice V) :
    LieAddGroup (modelWithCornersSelf ℂ V) (⊤ : WithTop ℕ∞)
      (ULift.{u} (quotient V Λ)) where
  contMDiff_neg := complexTorusULift_contMDiff_neg Λ

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
