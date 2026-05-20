import Jacobian.HolomorphicForms.MeromorphicFunction
import Jacobian.HolomorphicForms.HolomorphicMap
import Jacobian.HolomorphicForms.OnePointCxIsManifold
import Jacobian.HolomorphicForms.LocalMappingThm
import Jacobian.Blueprint.Sec02.WeightedFiberCardConst
import Jacobian.Periods.TrivializationContinuousLinearMapAt

/-! Production API promoted from blueprint: `def:meromorphic-to-cp1` in
`tex/sections/01-compact-riemann-surfaces.tex`.

The associated map `f̂ : X → ℂ ∪ {∞}` to the Riemann sphere from a nonzero
meromorphic function. -/

namespace JacobianChallenge.HolomorphicForms

open scoped Manifold OnePoint Topology
open JacobianChallenge.HolomorphicForms

/-- The associated map to `OnePoint ℂ` (the Riemann sphere) from a
meromorphic function: simply the underlying set function `f.toFun`. -/
noncomputable def meromorphicToCp1
    (X : Type*) [TopologicalSpace X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X]
    [JacobianChallenge.Periods.StableChartAt ℂ X]
    (f : MeromorphicFunctionType X) : X → OnePoint ℂ :=
  f.toFun

/-- Continuity of the CP¹ lift of a meromorphic function.

Body: `meromorphicToCp1 X f := f.toFun`, and `f.toFun_continuous` is the
relevant `Continuous` field of the `MeromorphicFunctionType` structure.

Used by `liftToCp1_branchedCoverData` (sub-leaf 2 of
`thm:principal-degree-zero`) to feed
`Sec02/BranchedDegree.lean` leaf 8
(`branchedCoverData_of_nonconstant_holomorphic`). -/
theorem liftToCp1_continuous
    (X : Type*) [TopologicalSpace X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X]
    [JacobianChallenge.Periods.StableChartAt ℂ X]
    (f : MeromorphicFunctionType X) (_hholo : True) :
    Continuous (meromorphicToCp1 X f) :=
  f.toFun_continuous

/-- Chart-local holomorphicity of the CP¹ lift of a meromorphic function.

This is the direct analytic bridge from the meromorphic-germ field
`f.isMeromorphic` to the project-local holomorphic-map predicate:
in every source chart and the corresponding finite/infinite chart on
`OnePoint ℂ`, the chart-local presentation is analytic. -/
theorem liftToCp1_holomorphicAt_finite
    (X : Type*) [TopologicalSpace X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X]
    [JacobianChallenge.Periods.StableChartAt ℂ X]
    (f : MeromorphicFunctionType X) (_hholo : True)
    (p : X) {z : ℂ} (_hp : meromorphicToCp1 X f p = (z : OnePoint ℂ)) :
    IsHolomorphicAt (meromorphicToCp1 X f) p := by
  apply_rules [ MeromorphicAt.analyticAt ];
  · have h_eq : ∀ᶠ t in nhds (chartAt ℂ p p), chartLocalAt (meromorphicToCp1 X f) p t = (f.toFun (chartAt ℂ p |>.symm t)).getD 0 := by
      have h_eq : ∀ᶠ t in nhds (chartAt ℂ p p), (chartAt ℂ p).symm t ∈ f.toFun ⁻¹' Set.range (OnePoint.some : ℂ → OnePoint ℂ) := by
        have h_eq : ContinuousAt (fun t => f.toFun (chartAt ℂ p |>.symm t)) (chartAt ℂ p p) := by
          refine' ContinuousAt.comp _ _;
          · exact f.toFun_continuous.continuousAt;
          · exact ( chartAt ℂ p ).symm.continuousAt ( by simp +decide );
        have h_eq : ∀ᶠ t in nhds (chartAt ℂ p p), f.toFun (chartAt ℂ p |>.symm t) ≠ OnePoint.infty := by
          convert h_eq.eventually_ne _;
          convert _hp.symm ▸ OnePoint.coe_ne_infty z;
          exact ( chartAt ℂ p ).left_inv ( by simp +decide );
        filter_upwards [ h_eq ] with t ht using by cases h : f.toFun ( chartAt ℂ p |>.symm t ) <;> tauto;
      filter_upwards [ h_eq ] with t ht;
      cases h : f.toFun ( chartAt ℂ p |>.symm t ) <;> simp_all +decide [ chartLocalAt ];
      simp_all +decide [ meromorphicToCp1 ];
      simp +decide [ chartAt ];
      simp +decide [ ChartedSpace.chartAt ];
      simp +decide [ HolomorphicForms.identityChart ];
      simp +decide [ Topology.IsOpenEmbedding.toOpenPartialHomeomorph ];
      simp +decide [ Function.invFunOn ];
      rfl;
    apply_rules [ MeromorphicAt.congr ];
    convert f.isMeromorphic p using 1;
    any_goals exact eventuallyEq_nhdsWithin_of_eqOn fun ⦃x⦄ => congrFun rfl;
    filter_upwards [ h_eq.filter_mono nhdsWithin_le_nhds ] with t ht using ht.symm;
  · apply_rules [ ContinuousAt.comp, continuousAt_id ];
    any_goals exact continuousAt_id;
    · convert ( chartAt ℂ ( meromorphicToCp1 X f p ) ).continuousAt _;
      aesop;
    · refine' ContinuousAt.comp _ _;
      · convert f.toFun_continuous.continuousAt using 1;
      · exact ( chartAt ℂ p ).symm.continuousAt ( by simp +decide )

/-- Chart-local holomorphicity of the CP¹ lift at a pole.

In the target inversion chart, this is analyticity of the reciprocal
local branch of the meromorphic projection. -/
theorem liftToCp1_holomorphicAt_infty
    (X : Type*) [TopologicalSpace X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X]
    [JacobianChallenge.Periods.StableChartAt ℂ X]
    (f : MeromorphicFunctionType X) (_hholo : True)
    (p : X) (_hp : meromorphicToCp1 X f p = (∞ : OnePoint ℂ)) :
    IsHolomorphicAt (meromorphicToCp1 X f) p := by
  apply_rules [ MeromorphicAt.analyticAt ];
  · have h_meromorphic : MeromorphicAt (fun t => (f.toFun ((chartAt ℂ p).symm t)).getD 0) (chartAt ℂ p p) := by
      convert f.isMeromorphic p;
    convert h_meromorphic.inv using 1;
    ext t; simp [chartLocalAt, meromorphicToCp1];
    cases h : f.toFun ( ( chartAt ℂ p ).symm t ) <;> simp_all +decide [ meromorphicToCp1 ];
    · unfold Option.getD; aesop;
    · exact Complex.ext rfl rfl;
  · refine' ContinuousAt.comp _ _;
    · convert ( chartAt ℂ ( meromorphicToCp1 X f p ) ).continuousAt using 1;
      aesop;
    · refine' ContinuousAt.comp _ _;
      · convert f.toFun_continuous.continuousAt using 1;
      · exact ( chartAt ℂ p ).symm.continuousAt ( by simp +decide )

/-- Chart-local holomorphicity of the CP¹ lift of a meromorphic function.

This is now a case split on the target value: finite values use
`liftToCp1_holomorphicAt_finite`; poles use
`liftToCp1_holomorphicAt_infty`. -/
theorem liftToCp1_holomorphicAt
    (X : Type*) [TopologicalSpace X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X]
    [JacobianChallenge.Periods.StableChartAt ℂ X]
    (f : MeromorphicFunctionType X) (_hholo : True) :
    ∀ p, IsHolomorphicAt (meromorphicToCp1 X f) p := by
  intro p
  cases hval : meromorphicToCp1 X f p with
  | infty =>
      exact liftToCp1_holomorphicAt_infty X f _hholo p hval
  | coe z =>
      exact liftToCp1_holomorphicAt_finite X f _hholo p hval

/-- Local `k`-fold normal form/counting for the CP¹ lift.

### Why this is a frontier sorry

This is the local mapping theorem (`z ↦ z^k` normal form) for the CP¹ lift,
in both the finite chart and the infinity chart on `OnePoint ℂ`. A real
proof has to:

* split on whether `meromorphicToCp1 X f x` is finite or `∞`;
* in the finite chart, reduce to the local analytic map for the finite lift
  of `f` and apply `AnalyticLocalMapping.analytic_local_mapping_theorem`;
* in the infinity chart, reduce to the reciprocal local branch and apply
  the same local mapping theorem to `f.toFun⁻¹`;
* prove compatibility of `mapAnalyticOrderAt (meromorphicToCp1 X f)` with the
  finite/infinity chart normal forms — i.e., that the chart-local order at
  `x` matches the multiplicity from the local mapping theorem;
* identify the produced `Finset` with the actual local fiber, not an
  arbitrary witness.

The current `MeromorphicFunctionType` exposes local meromorphicity of the
raw map but no chart-local normal form, no finite-local-fiber data, and no
ramification/order compatibility lemma. The missing infrastructure is a
sharper local-analytic API for meromorphic germs on Riemann surfaces. Until
that exists this theorem cannot be discharged honestly. -/
theorem liftToCp1_local_kfold_ramified
    (X : Type*) [TopologicalSpace X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X]
    [JacobianChallenge.Periods.StableChartAt ℂ X]
    (f : MeromorphicFunctionType X) (_hholo : True) :
    ∀ [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X]
      [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) (OnePoint ℂ)]
      {x : X} {k : ℕ}, 0 < k →
      mapAnalyticOrderAt (meromorphicToCp1 X f) x = k →
      ∃ U : Set X, IsOpen U ∧ x ∈ U ∧
      ∃ V : Set (OnePoint ℂ), IsOpen V ∧ meromorphicToCp1 X f x ∈ V ∧
      ∀ y ∈ V, y ≠ meromorphicToCp1 X f x →
      ∃ s : Finset X, s.card = k ∧ ↑s ⊆ U ∧
        (∀ x' ∈ s, meromorphicToCp1 X f x' = y ∧
          mapAnalyticOrderAt (meromorphicToCp1 X f) x' = 1) ∧
        (∀ x' ∈ U, meromorphicToCp1 X f x' = y → x' ∈ s) := by
  -- Frontier: local mapping theorem for meromorphic CP¹ lifts. Do not
  -- fabricate a `Finset` witness — the `s` here must be the actual local
  -- fiber produced by the local analytic mapping theorem.
  sorry

/-- Local conservation of the weighted fibre count for the CP¹ lift.

### Why this is a frontier sorry

Weighted-fiber conservation (the degree theorem for branched covers) is the
*global* statement that the weighted fiber sum is locally constant on the
target. A real proof needs:

* the local k-fold ramification data from `liftToCp1_local_kfold_ramified`
  to get neighborhoods on which fiber multiplicities sum to the local
  degree;
* compactness/properness to cover the fiber over `y₀` by finitely many such
  neighborhoods;
* a disjoint-union argument showing that nearby fibers decompose as a
  disjoint union of the local fiber witnesses;
* the sum of `mapAnalyticOrderAt` over that disjoint union, plus the
  ramification/order compatibility from the local mapping theorem.

The `finite_fiber` hypothesis here is only finite support data; it does
not by itself give weighted conservation. The `_hholo : True` carries no
analytic content. Discharging this honestly requires the local-mapping
infrastructure above and a properness argument for the CP¹ lift, neither
of which is currently in the codebase. -/
theorem liftToCp1_weightedFiberSum_eventually_eq
    (X : Type*) [TopologicalSpace X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X]
    [JacobianChallenge.Periods.StableChartAt ℂ X]
    (f : MeromorphicFunctionType X) (_hholo : True) :
    ∀ [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X]
      [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) (OnePoint ℂ)]
      [CompactSpace X] [T2Space X] [PreconnectedSpace X] [T2Space (OnePoint ℂ)],
      (¬ ∃ y₀ : OnePoint ℂ, ∀ x, meromorphicToCp1 X f x = y₀) →
      (finite_fiber : ∀ y : OnePoint ℂ, ((meromorphicToCp1 X f) ⁻¹' {y}).Finite) →
      ∀ y₀ : OnePoint ℂ, ∀ᶠ y in 𝓝 y₀,
        ((finite_fiber y).toFinset).sum
          (mapAnalyticOrderAt (meromorphicToCp1 X f)) =
        ((finite_fiber y₀).toFinset).sum
          (mapAnalyticOrderAt (meromorphicToCp1 X f)) := by
  -- Frontier: weighted-fiber conservation = branched-cover degree principle.
  -- Do not force `mapAnalyticOrderAt` to be constant or ignore ramification —
  -- both would silently weaken the statement.
  sorry

/-- Basic holomorphicity of the CP¹ lift of a meromorphic function. -/
theorem liftToCp1_isHolomorphicBasic
    (X : Type*) [TopologicalSpace X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X]
    [JacobianChallenge.Periods.StableChartAt ℂ X]
    (f : MeromorphicFunctionType X) (hholo : True) :
    JacobianChallenge.HolomorphicForms.IsHolomorphicBasic
      (meromorphicToCp1 X f) := by
  exact
    { continuous := liftToCp1_continuous X f hholo
      holomorphicAt := liftToCp1_holomorphicAt X f hholo }

/-- Local k-fold ramification data for the CP¹ lift, kept separate from
basic holomorphicity. -/
theorem liftToCp1_hasLocalKfoldRamification
    (X : Type*) [TopologicalSpace X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X]
    [JacobianChallenge.Periods.StableChartAt ℂ X]
    (f : MeromorphicFunctionType X) (hholo : True) :
    JacobianChallenge.HolomorphicForms.HasLocalKfoldRamification
      (meromorphicToCp1 X f) := by
  exact
    { local_kfold_ramified := liftToCp1_local_kfold_ramified X f hholo }

/-- Holomorphicity of the CP¹ lift of a meromorphic function.

This is the analytic content needed by sub-leaf 2 of
`thm:principal-degree-zero`: after constructing the set-level map
`meromorphicToCp1 X f := f.toFun`, one must prove it is holomorphic in
the project-local sense used by the branched-cover constructor.

Compatibility wrapper assembling the older `IsHolomorphic` package from
the now-separated basic and local-kfold route data. -/
theorem liftToCp1_isHolomorphic
    (X : Type*) [TopologicalSpace X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X]
    [JacobianChallenge.Periods.StableChartAt ℂ X]
    (f : MeromorphicFunctionType X) (hholo : True) :
    JacobianChallenge.HolomorphicForms.IsHolomorphic
      (meromorphicToCp1 X f) := by
  exact IsHolomorphic.of_basic
    (liftToCp1_isHolomorphicBasic X f hholo)
    (liftToCp1_hasLocalKfoldRamification X f hholo)

/-- Weighted-fiber conservation for the CP¹ lift, kept separate from
basic/local holomorphicity. -/
theorem liftToCp1_hasWeightedFiberConservation
    (X : Type*) [TopologicalSpace X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X]
    [JacobianChallenge.Periods.StableChartAt ℂ X]
    (f : MeromorphicFunctionType X) (hholo : True) :
    JacobianChallenge.HolomorphicForms.HasWeightedFiberConservation
      (meromorphicToCp1 X f) := by
  exact
    {
      weightedFiberSum_eventually_eq :=
        liftToCp1_weightedFiberSum_eventually_eq X f hholo }

end JacobianChallenge.HolomorphicForms
