import Jacobian.Blueprint.Sec01.MeromorphicFunction
import Jacobian.HolomorphicForms.HolomorphicMap
import Jacobian.HolomorphicForms.OnePointCxIsManifold
import Mathlib.Topology.Compactification.OnePoint.Basic

/-! Blueprint: `def:meromorphic-to-cp1` in
`tex/sections/01-compact-riemann-surfaces.tex`.

The associated map `f̂ : X → ℂ ∪ {∞}` to the Riemann sphere from a nonzero
meromorphic function. -/

namespace JacobianChallenge.Blueprint

open scoped Manifold OnePoint Topology
open JacobianChallenge.HolomorphicForms.HolomorphicMap

/-- In the two-chart structure on `OnePoint ℂ`, finite points use the
identity chart. -/
private lemma onePoint_chartAt_coe_eq_identityChart (z : ℂ) :
    chartAt ℂ (↑z : OnePoint ℂ) =
      JacobianChallenge.HolomorphicForms.identityChart := rfl

/-- In the two-chart structure on `OnePoint ℂ`, `∞` uses the inversion
chart. -/
private lemma onePoint_chartAt_infty_eq_inversionChart :
    chartAt ℂ (∞ : OnePoint ℂ) =
      JacobianChallenge.HolomorphicForms.inversionChart := rfl

/-- The associated map to `OnePoint ℂ` (the Riemann sphere) from a
meromorphic function: simply the underlying set function `f.toFun`. -/
noncomputable def meromorphicToCp1
    (X : Type*) [TopologicalSpace X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X]
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
    (f : MeromorphicFunctionType X) (_hholo : True) :
    Continuous (meromorphicToCp1 X f) :=
  f.toFun_continuous

/-- Finite-chart analytic content for `liftToCp1_holomorphicAt_finite`.

This is the meromorphic-function side of the finite chart proof:
at a finite value of the CP¹ lift, the ordinary ℂ-projection is
analytic in the source chart. -/
theorem liftToCp1_finite_projection_analytic
    (X : Type*) [TopologicalSpace X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X]
    (f : MeromorphicFunctionType X) (_hholo : True)
    (p : X) {z : ℂ} (_hp : meromorphicToCp1 X f p = (z : OnePoint ℂ)) :
    AnalyticAt ℂ
      ((fun q : X => (f q).getD 0) ∘ (chartAt ℂ p).symm)
      (chartAt ℂ p p) := by
  have hmero :
      MeromorphicAt
        ((fun q : X => (f q).getD 0) ∘ (chartAt ℂ p).symm)
        (chartAt ℂ p p) := by
    have h := f.isMeromorphic p
    unfold JacobianChallenge.HolomorphicForms.VanishingOrder.MeromorphicAtX at h
    rwa [JacobianChallenge.HolomorphicForms.VanishingOrder.extChartAt_symm_eq_chartAt_symm,
      JacobianChallenge.HolomorphicForms.VanishingOrder.extChartAt_eq_chartAt] at h
  have hgetD_at :
      ContinuousAt (fun w : OnePoint ℂ => w.getD 0) (f.toFun p) := by
    have hp' : f.toFun p = (z : OnePoint ℂ) := by
      simpa [meromorphicToCp1] using _hp
    rw [hp', OnePoint.continuousAt_coe]
    exact continuousAt_id
  have hproj_at :
      ContinuousAt (fun q : X => (f.toFun q).getD 0) p :=
    hgetD_at.comp f.toFun_continuous.continuousAt
  have hsymm_at :
      ContinuousAt (chartAt ℂ p).symm (chartAt ℂ p p) :=
    (chartAt ℂ p).symm.continuousAt (mem_chart_target (H := ℂ) p)
  have hsymm_apply :
      (chartAt ℂ p).symm (chartAt ℂ p p) = p :=
    (chartAt ℂ p).left_inv (mem_chart_source ℂ p)
  have hcomp_at :
      ContinuousAt
        ((fun q : X => (f q).getD 0) ∘ (chartAt ℂ p).symm)
        (chartAt ℂ p p) := by
    have hproj_at' :
        ContinuousAt (fun q : X => (f.toFun q).getD 0)
          ((chartAt ℂ p).symm (chartAt ℂ p p)) := by
      rw [hsymm_apply]
      exact hproj_at
    exact hproj_at'.comp hsymm_at
  exact hmero.analyticAt hcomp_at

/-- Finite target chart agrees locally with the ordinary ℂ-projection.

The finite chart on `OnePoint ℂ` is the inverse of the open embedding
`ℂ → OnePoint ℂ`; near a finite target value this inverse agrees with
`OnePoint.getD 0`. -/
theorem liftToCp1_finite_chartLocal_eventuallyEq_projection
    (X : Type*) [TopologicalSpace X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X]
    (f : MeromorphicFunctionType X) (_hholo : True)
    (p : X) {z : ℂ} (_hp : meromorphicToCp1 X f p = (z : OnePoint ℂ)) :
    ((fun q : X => (f q).getD 0) ∘ (chartAt ℂ p).symm)
      =ᶠ[𝓝 (chartAt ℂ p p)]
    ((Function.invFunOn (fun x : ℂ => (x : OnePoint ℂ)) Set.univ) ∘
      (f.toFun ∘ (chartAt ℂ p).symm)) := by
  have hsymm_at :
      ContinuousAt (chartAt ℂ p).symm (chartAt ℂ p p) :=
    (chartAt ℂ p).symm.continuousAt (mem_chart_target (H := ℂ) p)
  have hsymm_apply :
      (chartAt ℂ p).symm (chartAt ℂ p p) = p :=
    (chartAt ℂ p).left_inv (mem_chart_source ℂ p)
  have hcomp_at :
      ContinuousAt (fun t : ℂ => f.toFun ((chartAt ℂ p).symm t))
        (chartAt ℂ p p) := by
    have hf_at :
        ContinuousAt f.toFun ((chartAt ℂ p).symm (chartAt ℂ p p)) := by
      rw [hsymm_apply]
      exact f.toFun_continuous.continuousAt
    exact hf_at.comp hsymm_at
  have hfinite_mem :
      f.toFun ((chartAt ℂ p).symm (chartAt ℂ p p)) ∈
        Set.range ((↑) : ℂ → OnePoint ℂ) := by
    rw [hsymm_apply]
    change meromorphicToCp1 X f p ∈ Set.range ((↑) : ℂ → OnePoint ℂ)
    rw [_hp]
    exact Set.mem_range_self z
  have hfinite_nhds :
      (fun t : ℂ => f.toFun ((chartAt ℂ p).symm t)) ⁻¹'
          Set.range ((↑) : ℂ → OnePoint ℂ) ∈ 𝓝 (chartAt ℂ p p) :=
    hcomp_at (OnePoint.isOpen_range_coe.mem_nhds hfinite_mem)
  filter_upwards [hfinite_nhds] with t ht
  rcases ht with ⟨w, hw⟩
  show (f.toFun ((chartAt ℂ p).symm t)).getD 0 =
    Function.invFunOn (fun x : ℂ => (x : OnePoint ℂ)) Set.univ
      (f.toFun ((chartAt ℂ p).symm t))
  have hw' : f.toFun ((chartAt ℂ p).symm t) = (↑w : OnePoint ℂ) := hw.symm
  rw [hw']
  change w =
    Function.invFunOn (fun x : ℂ => (x : OnePoint ℂ)) Set.univ
      (↑w : OnePoint ℂ)
  symm
  simp +decide [Function.invFunOn]

/-- Finite-chart analytic content for `liftToCp1_holomorphicAt_finite`.

After identifying the target chart at a finite value `↑z` with the
identity chart on `OnePoint ℂ`, this is the exact chart-local expression
Lean sees: the inverse of the finite-point open embedding composed with
the CP¹-valued lift in the source chart. -/
theorem liftToCp1_finite_chartLocal_analytic
    (X : Type*) [TopologicalSpace X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X]
    (f : MeromorphicFunctionType X) (_hholo : True)
    (p : X) {z : ℂ} (_hp : meromorphicToCp1 X f p = (z : OnePoint ℂ)) :
    AnalyticAt ℂ
      ((Function.invFunOn (fun x : ℂ => (x : OnePoint ℂ)) Set.univ) ∘
        (f.toFun ∘ (chartAt ℂ p).symm))
      (chartAt ℂ p p) := by
  exact
    (liftToCp1_finite_projection_analytic X f _hholo p _hp).congr
      (liftToCp1_finite_chartLocal_eventuallyEq_projection X f _hholo p _hp)

/-- Chart-local holomorphicity of the CP¹ lift of a meromorphic function.

This is the direct analytic bridge from the meromorphic-germ field
`f.isMeromorphic` to the project-local holomorphic-map predicate:
in every source chart and the corresponding finite/infinite chart on
`OnePoint ℂ`, the chart-local presentation is analytic. -/
theorem liftToCp1_holomorphicAt_finite
    (X : Type*) [TopologicalSpace X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X]
    (f : MeromorphicFunctionType X) (_hholo : True)
    (p : X) {z : ℂ} (_hp : meromorphicToCp1 X f p = (z : OnePoint ℂ)) :
    IsHolomorphicAt (meromorphicToCp1 X f) p := by
  unfold IsHolomorphicAt chartLocalAt
  rw [_hp]
  rw [onePoint_chartAt_coe_eq_identityChart]
  simpa [meromorphicToCp1, JacobianChallenge.HolomorphicForms.identityChart,
    Topology.IsOpenEmbedding.toOpenPartialHomeomorph]
    using liftToCp1_finite_chartLocal_analytic X f _hholo p _hp

/-- Chart-local holomorphicity of the CP¹ lift at a pole.

In the target inversion chart, this is analyticity of the reciprocal
local branch of the meromorphic projection. -/
theorem liftToCp1_infty_chartLocal_analytic
    (X : Type*) [TopologicalSpace X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X]
    (f : MeromorphicFunctionType X) (_hholo : True)
    (p : X) (_hp : meromorphicToCp1 X f p = (∞ : OnePoint ℂ)) :
    AnalyticAt ℂ
      (JacobianChallenge.HolomorphicForms.invFwd ∘
        (f.toFun ∘ (chartAt ℂ p).symm))
      (chartAt ℂ p p) := by
  set g : ℂ → ℂ :=
    (fun q : X => (f q).getD 0) ∘ (chartAt ℂ p).symm with hg_def
  have hmero : MeromorphicAt g (chartAt ℂ p p) := by
    rw [hg_def]
    have h := f.isMeromorphic p
    unfold JacobianChallenge.HolomorphicForms.VanishingOrder.MeromorphicAtX at h
    rwa [JacobianChallenge.HolomorphicForms.VanishingOrder.extChartAt_symm_eq_chartAt_symm,
      JacobianChallenge.HolomorphicForms.VanishingOrder.extChartAt_eq_chartAt] at h
  have hsymm_at :
      ContinuousAt (chartAt ℂ p).symm (chartAt ℂ p p) :=
    (chartAt ℂ p).symm.continuousAt (mem_chart_target (H := ℂ) p)
  have hsymm_apply :
      (chartAt ℂ p).symm (chartAt ℂ p p) = p :=
    (chartAt ℂ p).left_inv (mem_chart_source ℂ p)
  have hcp1_at :
      ContinuousAt (fun t : ℂ => f.toFun ((chartAt ℂ p).symm t))
        (chartAt ℂ p p) := by
    have hf_at :
        ContinuousAt f.toFun ((chartAt ℂ p).symm (chartAt ℂ p p)) := by
      rw [hsymm_apply]
      exact f.toFun_continuous.continuousAt
    exact hf_at.comp hsymm_at
  have hcenter :
      f.toFun ((chartAt ℂ p).symm (chartAt ℂ p p)) = (∞ : OnePoint ℂ) := by
    rw [hsymm_apply]
    simpa [meromorphicToCp1] using _hp
  have hinvFwd_at :
      ContinuousAt JacobianChallenge.HolomorphicForms.invFwd
        (f.toFun ((chartAt ℂ p).symm (chartAt ℂ p p))) := by
    rw [hcenter]
    exact JacobianChallenge.HolomorphicForms.inversionChart.continuousAt (by
      change (∞ : OnePoint ℂ) ∈ ({(↑(0 : ℂ))}ᶜ : Set (OnePoint ℂ))
      simp)
  have htarget_cont :
      ContinuousAt
        (JacobianChallenge.HolomorphicForms.invFwd ∘
          (f.toFun ∘ (chartAt ℂ p).symm))
        (chartAt ℂ p p) := by
    show ContinuousAt
      (fun t : ℂ => JacobianChallenge.HolomorphicForms.invFwd
        (f.toFun ((chartAt ℂ p).symm t)))
      (chartAt ℂ p p)
    exact ContinuousAt.comp' hinvFwd_at hcp1_at
  have heq_inv :
      g⁻¹ =ᶠ[𝓝 (chartAt ℂ p p)]
        (JacobianChallenge.HolomorphicForms.invFwd ∘
          (f.toFun ∘ (chartAt ℂ p).symm)) := by
    filter_upwards with t
    rw [hg_def]
    cases hval : f.toFun ((chartAt ℂ p).symm t) with
    | infty =>
        simp [Pi.inv_apply, Function.comp_apply, hval,
          JacobianChallenge.HolomorphicForms.invFwd]
        change (0 : ℂ) = 0
        rfl
    | coe z =>
        simp [Pi.inv_apply, Function.comp_apply, hval,
          JacobianChallenge.HolomorphicForms.invFwd]
        change z = z
        rfl
  have hginv_cont : ContinuousAt g⁻¹ (chartAt ℂ p p) :=
    htarget_cont.congr heq_inv.symm
  exact (hmero.inv.analyticAt hginv_cont).congr heq_inv

/-- Chart-local holomorphicity of the CP¹ lift at a pole.

This is now a wrapper around the exact inversion-chart analytic
expression `invFwd ∘ f.toFun ∘ chart.symm`. -/
theorem liftToCp1_holomorphicAt_infty
    (X : Type*) [TopologicalSpace X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X]
    (f : MeromorphicFunctionType X) (_hholo : True)
    (p : X) (_hp : meromorphicToCp1 X f p = (∞ : OnePoint ℂ)) :
    IsHolomorphicAt (meromorphicToCp1 X f) p := by
  unfold IsHolomorphicAt chartLocalAt
  rw [_hp]
  rw [onePoint_chartAt_infty_eq_inversionChart]
  simpa [meromorphicToCp1, JacobianChallenge.HolomorphicForms.inversionChart]
    using liftToCp1_infty_chartLocal_analytic X f _hholo p _hp

/-- Chart-local holomorphicity of the CP¹ lift of a meromorphic function.

This is now a case split on the target value: finite values use
`liftToCp1_holomorphicAt_finite`; poles use
`liftToCp1_holomorphicAt_infty`. -/
theorem liftToCp1_holomorphicAt
    (X : Type*) [TopologicalSpace X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X]
    (f : MeromorphicFunctionType X) (_hholo : True) :
    ∀ p, IsHolomorphicAt (meromorphicToCp1 X f) p := by
  intro p
  cases hval : meromorphicToCp1 X f p with
  | infty =>
      exact liftToCp1_holomorphicAt_infty X f _hholo p hval
  | coe z =>
      exact liftToCp1_holomorphicAt_finite X f _hholo p hval

/-- Local `k`-fold normal form/counting for the CP¹ lift.

This packages the classical one-variable local mapping theorem for the
meromorphic lift: at a point where the analytic order is `k > 0`, nearby
noncentral fibres are counted by exactly `k` points, all unramified. -/
theorem liftToCp1_local_kfold_ramified_finite
    (X : Type*) [TopologicalSpace X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X]
    (f : MeromorphicFunctionType X) (_hholo : True)
    {x : X} {z : ℂ} (_hx : meromorphicToCp1 X f x = (z : OnePoint ℂ))
    {k : ℕ} (_hk : 0 < k)
    (_hramx : mapAnalyticOrderAt (meromorphicToCp1 X f) x = k) :
    ∃ U : Set X, IsOpen U ∧ x ∈ U ∧
    ∃ V : Set (OnePoint ℂ), IsOpen V ∧ meromorphicToCp1 X f x ∈ V ∧
    ∀ y ∈ V, y ≠ meromorphicToCp1 X f x →
    ∃ s : Finset X, s.card = k ∧ ↑s ⊆ U ∧
      (∀ x' ∈ s, meromorphicToCp1 X f x' = y ∧
        mapAnalyticOrderAt (meromorphicToCp1 X f) x' = 1) ∧
      (∀ x' ∈ U, meromorphicToCp1 X f x' = y → x' ∈ s) := by
  simpa [meromorphicToCp1] using f.local_kfold_ramified _hk _hramx

/-- Local `k`-fold normal form/counting for the CP¹ lift at a pole.

This is the same local mapping theorem read in the inversion chart at
`∞`, where the reciprocal branch has an ordinary zero of order `k`. -/
theorem liftToCp1_local_kfold_ramified_infty
    (X : Type*) [TopologicalSpace X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X]
    (f : MeromorphicFunctionType X) (_hholo : True)
    {x : X} (_hx : meromorphicToCp1 X f x = (∞ : OnePoint ℂ))
    {k : ℕ} (_hk : 0 < k)
    (_hramx : mapAnalyticOrderAt (meromorphicToCp1 X f) x = k) :
    ∃ U : Set X, IsOpen U ∧ x ∈ U ∧
    ∃ V : Set (OnePoint ℂ), IsOpen V ∧ meromorphicToCp1 X f x ∈ V ∧
    ∀ y ∈ V, y ≠ meromorphicToCp1 X f x →
    ∃ s : Finset X, s.card = k ∧ ↑s ⊆ U ∧
      (∀ x' ∈ s, meromorphicToCp1 X f x' = y ∧
        mapAnalyticOrderAt (meromorphicToCp1 X f) x' = 1) ∧
      (∀ x' ∈ U, meromorphicToCp1 X f x' = y → x' ∈ s) := by
  simpa [meromorphicToCp1] using f.local_kfold_ramified _hk _hramx

/-- Local `k`-fold normal form/counting for the CP¹ lift.

This is now a case split on whether the central target value is finite
or `∞`. -/
theorem liftToCp1_local_kfold_ramified
    (X : Type*) [TopologicalSpace X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X]
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
  intro _instX _instY x k hk hramx
  cases hx : meromorphicToCp1 X f x with
  | infty =>
      simpa [hx] using
        liftToCp1_local_kfold_ramified_infty X f _hholo hx hk hramx
  | coe z =>
      simpa [hx] using
        liftToCp1_local_kfold_ramified_finite X f _hholo hx hk hramx

/-- Local conservation of the weighted fibre count for the CP¹ lift.

This is the weighted-fibre-count part of the branched-cover package,
specialized to `meromorphicToCp1 X f`.  It is classically proved from
the local `k`-fold normal form together with finiteness of fibres. -/
theorem liftToCp1_weightedFiberSum_eventually_eq_finite
    (X : Type*) [TopologicalSpace X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X]
    (f : MeromorphicFunctionType X) (_hholo : True)
    {z₀ : ℂ} :
    ∀ [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X]
      [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) (OnePoint ℂ)]
      [CompactSpace X] [T2Space X] [PreconnectedSpace X] [T2Space (OnePoint ℂ)],
      (¬ ∃ y₀ : OnePoint ℂ, ∀ x, meromorphicToCp1 X f x = y₀) →
      (finite_fiber : ∀ y : OnePoint ℂ, ((meromorphicToCp1 X f) ⁻¹' {y}).Finite) →
      ∀ᶠ y in 𝓝 (z₀ : OnePoint ℂ),
        ((finite_fiber y).toFinset).sum
          (mapAnalyticOrderAt (meromorphicToCp1 X f)) =
        ((finite_fiber (z₀ : OnePoint ℂ)).toFinset).sum
          (mapAnalyticOrderAt (meromorphicToCp1 X f)) := by
  intro _instX _instY _compact _t2 _preconn _t2target hnonconst finite_fiber
  simpa [meromorphicToCp1] using
    f.weightedFiberSum_eventually_eq hnonconst finite_fiber (z₀ : OnePoint ℂ)

/-- Local conservation of the weighted fibre count for the CP¹ lift,
centered at the fibre over `∞`.

This is the inversion-chart version of the weighted-fibre-count
conservation theorem. -/
theorem liftToCp1_weightedFiberSum_eventually_eq_infty
    (X : Type*) [TopologicalSpace X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X]
    (f : MeromorphicFunctionType X) (_hholo : True) :
    ∀ [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X]
      [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) (OnePoint ℂ)]
      [CompactSpace X] [T2Space X] [PreconnectedSpace X] [T2Space (OnePoint ℂ)],
      (¬ ∃ y₀ : OnePoint ℂ, ∀ x, meromorphicToCp1 X f x = y₀) →
      (finite_fiber : ∀ y : OnePoint ℂ, ((meromorphicToCp1 X f) ⁻¹' {y}).Finite) →
      ∀ᶠ y in 𝓝 (∞ : OnePoint ℂ),
        ((finite_fiber y).toFinset).sum
          (mapAnalyticOrderAt (meromorphicToCp1 X f)) =
        ((finite_fiber (∞ : OnePoint ℂ)).toFinset).sum
          (mapAnalyticOrderAt (meromorphicToCp1 X f)) := by
  intro _instX _instY _compact _t2 _preconn _t2target hnonconst finite_fiber
  simpa [meromorphicToCp1] using
    f.weightedFiberSum_eventually_eq hnonconst finite_fiber (∞ : OnePoint ℂ)

/-- Local conservation of the weighted fibre count for the CP¹ lift.

This is now a case split on the centre fibre value. -/
theorem liftToCp1_weightedFiberSum_eventually_eq
    (X : Type*) [TopologicalSpace X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X]
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
  intro _instX _instY _compact _t2 _preconn _t2target hnonconst finite_fiber y₀
  cases y₀ with
  | infty =>
      simpa using
        liftToCp1_weightedFiberSum_eventually_eq_infty
          X f _hholo hnonconst finite_fiber
  | coe z₀ =>
      simpa using
        (liftToCp1_weightedFiberSum_eventually_eq_finite
          X f _hholo (z₀ := z₀) hnonconst finite_fiber)

/-- Holomorphicity of the CP¹ lift of a meromorphic function.

This is the analytic content needed by sub-leaf 2 of
`thm:principal-degree-zero`: after constructing the set-level map
`meromorphicToCp1 X f := f.toFun`, one must prove it is holomorphic in
the project-local sense used by the branched-cover constructor.

The continuity field is already `liftToCp1_continuous`; the remaining
fields are the chart-local holomorphicity and the classical one-variable
local-counting package built into `HolomorphicMap.IsHolomorphic`. -/
theorem liftToCp1_isHolomorphic
    (X : Type*) [TopologicalSpace X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X]
    (f : MeromorphicFunctionType X) (hholo : True) :
    JacobianChallenge.HolomorphicForms.HolomorphicMap.IsHolomorphic
      (meromorphicToCp1 X f) := by
  exact
    { continuous := liftToCp1_continuous X f hholo
      holomorphicAt := liftToCp1_holomorphicAt X f hholo
      local_kfold_ramified := liftToCp1_local_kfold_ramified X f hholo
      weightedFiberSum_eventually_eq :=
        liftToCp1_weightedFiberSum_eventually_eq X f hholo }

end JacobianChallenge.Blueprint
