import Jacobian.HolomorphicForms.MeromorphicDegree
import Jacobian.HolomorphicForms.MeromorphicToCp1
import Jacobian.HolomorphicForms.OnePointCxIsManifold
import Jacobian.HolomorphicForms.HolomorphicCompactConstant
import Jacobian.Blueprint.Sec02.BranchedDegreeFromHolomorphic
import Jacobian.Periods.TrivializationContinuousLinearMapAt

/-!
# Bridging `MeromorphicMapToSphere` to branched-cover data

This module bridges a `MeromorphicMapToSphere X` equipped with explicit
`AnalyticData` to the holomorphic-map / branched-cover machinery of
`HolomorphicForms/HolomorphicMap.lean` and
`Blueprint/Sec02/BranchedDegreeFromHolomorphic.lean`.

### Semantic interface boundary

A previous iteration of this file declared two generic structural-axiom
sorries claiming that the analytic content "the canonical finite lift is
`MeromorphicAtX`" and "at a simple pole the chart-local order is `1`"
could be derived from `MeromorphicMapToSphere + PoleModulusData`. Neither
is derivable — `PoleModulusData` is a modulus-divergence witness, not an
analytic one, and the structure's `toFiniteFun_mdifferentiable` field is
*vacuous* in the presence of any pole.

The actual abstraction boundary is **`MeromorphicMapToSphere.AnalyticData`**
(defined in `Meromorphic.lean`): a record whose fields are *exactly* the
chart-local Laurent / order content that production constructors of a
`MeromorphicMapToSphere` (Riemann-Roch witness, dipole, etc.) must
supply by construction. With `AnalyticData` in hand, the
`MeromorphicFunctionType` / `liftToCp1_*` infrastructure of
`MeromorphicToCp1.lean` and the analytic constructor
`branchedCoverData_of_nonconstant_holomorphic` of
`Sec02/BranchedDegreeFromHolomorphic.lean` discharge everything else.
-/

namespace JacobianChallenge.HolomorphicForms

open scoped Manifold OnePoint Topology ContDiff
open JacobianChallenge.HolomorphicForms

variable {X : Type*} [TopologicalSpace X] [T2Space X] [CompactSpace X]
  [ConnectedSpace X] [ChartedSpace ℂ X]
  [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X]
  [JacobianChallenge.Periods.StableChartAt ℂ X]

/-! ### Thin projections from `AnalyticData` -/

omit [T2Space X] [CompactSpace X] [ConnectedSpace X]
  [JacobianChallenge.Periods.StableChartAt ℂ X] in
/--
Projection from `AnalyticData`: the canonical finite lift is
`MeromorphicAtX` at every point.
-/
theorem MeromorphicMapToSphere.meromorphicAt_getD_of_analyticData
    (f : MeromorphicMapToSphere X) (han : f.AnalyticData) :
    ∀ p : X, JacobianChallenge.HolomorphicForms.VanishingOrder.MeromorphicAtX
      (fun q => (f.toMap q).getD 0) p :=
  han.meromorphic_getD

omit [T2Space X] [CompactSpace X] [ConnectedSpace X]
  [JacobianChallenge.Periods.StableChartAt ℂ X] in
/--
Projection from `AnalyticData`: at a simple pole, the chart-local
analytic order is `1`.
-/
theorem MeromorphicMapToSphere.mapAnalyticOrderAt_toMap_eq_one_of_analyticData
    (f : MeromorphicMapToSphere X) (han : f.AnalyticData) (P : X)
    (hpole : f.poles = Divisor.point P) :
    JacobianChallenge.HolomorphicForms.mapAnalyticOrderAt f.toMap P = 1 :=
  han.simple_pole_order_one P hpole

/-! ### Packaging a `MeromorphicMapToSphere` with analytic data as a `MeromorphicFunctionType` -/

omit [T2Space X] [CompactSpace X] [ConnectedSpace X] in
/--
Package a `MeromorphicMapToSphere` plus explicit `AnalyticData` as a
`MeromorphicFunctionType`, so that the `liftToCp1_*` infrastructure of
`MeromorphicToCp1.lean` can be applied to its underlying map.

The packaging is purely structural: the `AnalyticData` fields exactly
match the `MeromorphicFunctionType` fields.
-/
noncomputable def MeromorphicMapToSphere.toMeromorphicFunctionType
    (f : MeromorphicMapToSphere X) (han : f.AnalyticData) :
    MeromorphicFunctionType X where
  toFun := f.toMap
  toFun_continuous := han.continuous_toMap
  isMeromorphic := han.meromorphic_getD

omit [T2Space X] [CompactSpace X] [ConnectedSpace X]
  [JacobianChallenge.Periods.StableChartAt ℂ X] in
@[simp] theorem MeromorphicMapToSphere.toMeromorphicFunctionType_toFun
    (f : MeromorphicMapToSphere X) (han : f.AnalyticData) :
    (f.toMeromorphicFunctionType han).toFun = f.toMap := rfl

omit [T2Space X] [CompactSpace X] [ConnectedSpace X] in
@[simp] theorem MeromorphicMapToSphere.meromorphicToCp1_toMeromorphicFunctionType
    (f : MeromorphicMapToSphere X) (han : f.AnalyticData) :
    meromorphicToCp1 X (f.toMeromorphicFunctionType han) = f.toMap := rfl

omit [T2Space X] [CompactSpace X] [ConnectedSpace X] in
/-- The CP¹ lift of `f.toMap` is complex-smooth in the manifold sense. -/
theorem MeromorphicMapToSphere.contMDiff_toMap_of_analyticData
    (f : MeromorphicMapToSphere X) (han : f.AnalyticData) :
    ContMDiff (modelWithCornersSelf ℂ ℂ) (modelWithCornersSelf ℂ ℂ)
      (⊤ : WithTop ℕ∞) f.toMap := by
  have h := liftToCp1_contMDiff X (f.toMeromorphicFunctionType han)
  simpa using h

omit [T2Space X] [CompactSpace X] [ConnectedSpace X] in
/--
The underlying map of a `MeromorphicMapToSphere` is `IsHolomorphic`
in the project-local sense, given explicit `AnalyticData`.
-/
theorem MeromorphicMapToSphere.isHolomorphic_toMap_of_analyticData
    (f : MeromorphicMapToSphere X) (han : f.AnalyticData) :
    JacobianChallenge.HolomorphicForms.IsHolomorphic f.toMap := by
  have h := liftToCp1_isHolomorphic X (f.toMeromorphicFunctionType han) True.intro
  simpa using h

omit [T2Space X] [CompactSpace X] [ConnectedSpace X] in
/--
Weighted-fiber conservation for `f.toMap`, given explicit
`AnalyticData`.
-/
theorem MeromorphicMapToSphere.hasWeightedFiberConservation_toMap_of_analyticData
    (f : MeromorphicMapToSphere X) (han : f.AnalyticData) :
    JacobianChallenge.HolomorphicForms.HasWeightedFiberConservation f.toMap := by
  have h := liftToCp1_hasWeightedFiberConservation X
    (f.toMeromorphicFunctionType han) True.intro
  simpa using h

omit [T2Space X] [CompactSpace X] [ConnectedSpace X]
  [JacobianChallenge.Periods.StableChartAt ℂ X] in
/--
The fiber `f.toMap ⁻¹' {∞}` of a continuous meromorphic map whose
pole divisor is `[P]` is exactly the singleton `{P}`.
-/
theorem MeromorphicMapToSphere.preimage_infty_eq_singleton_of_poleDivisor_point
    (f : MeromorphicMapToSphere X) (P : X)
    (hpole : f.poles = Divisor.point P) :
    f.toMap ⁻¹' {(OnePoint.infty : OnePoint ℂ)} = {P} := by
  classical
  ext x
  constructor
  · intro hx
    have hxinfty : f.toMap x = (OnePoint.infty : OnePoint ℂ) := hx
    by_contra hne
    have hne' : x ≠ P := hne
    have hzero : (Divisor.point P : Divisor X) x = 0 :=
      Divisor.point_apply_ne hne'
    have hzero' : f.poleDivisor x = 0 := by
      change f.poles x = 0
      rw [hpole]; exact hzero
    exact f.toMap_ne_infty_of_poleDivisor_zero x hzero' hxinfty
  · intro hxP
    have hx : x = P := hxP
    show f.toMap x = (OnePoint.infty : OnePoint ℂ)
    refine f.toMap_eq_infty_of_poleDivisor_pos x ?_
    have h : f.poleDivisor x = (Divisor.point P : Divisor X) x := by
      change f.poles x = _
      rw [hpole]
    rw [h, hx, Divisor.point_apply_self]
    decide

/-! ### Branched-cover-data assembly from `AnalyticData` -/

/--
Given a `MeromorphicMapToSphere f` on a compact connected complex
1-manifold which is nonconstant, has a simple pole at `P`, and carries
explicit `AnalyticData`, the map `f.toMap` packages as a
`BranchedCoverData X (OnePoint ℂ) f.toMap` whose branched degree is
`f.poleDivisor.degree.toNat = 1`.

* `isHolomorphic_toMap_of_analyticData` (above; uses the analytic
  adapter projection from `AnalyticData`).
* `hasWeightedFiberConservation_toMap_of_analyticData` (above; same).
* `branchedCoverData_of_nonconstant_holomorphic` (in
  `Sec02/BranchedDegreeFromHolomorphic.lean`).
* `branchedDegree_eq_weightedFiberCard` over `∞` (in
  `BranchedCover.lean`).
* `preimage_infty_eq_singleton_of_poleDivisor_point` (above).
* `AnalyticData.simple_pole_order_one` (projection; supplies the
  simple-pole order-one content).
-/
theorem MeromorphicMapToSphere.branchedCoverDataOfPoleDegree_of_simple_pole
    (f : MeromorphicMapToSphere X) (P : X)
    (hnc : f.Nonconstant)
    (hpole : f.poles = Divisor.point P)
    (han : f.AnalyticData) :
    f.BranchedCoverDataOfPoleDegree := by
  classical
  refine ⟨?_⟩
  intro _hcont
  -- Step A. Holomorphicity and weighted-fiber conservation for f.toMap.
  have hfHol : JacobianChallenge.HolomorphicForms.IsHolomorphic f.toMap :=
    f.isHolomorphic_toMap_of_analyticData han
  have hWeighted :
      JacobianChallenge.HolomorphicForms.HasWeightedFiberConservation f.toMap :=
    f.hasWeightedFiberConservation_toMap_of_analyticData han
  -- Step B. Unfold the nonconstancy hypothesis.
  have hnc' : ¬ ∃ y₀ : OnePoint ℂ, ∀ x : X, f.toMap x = y₀ := by
    intro h; exact hnc h
  -- Step C. Build the BranchedCoverData via the analytic constructor.
  set hbc :
      JacobianChallenge.HolomorphicForms.BranchedCoverData X (OnePoint ℂ) f.toMap :=
    JacobianChallenge.Blueprint.branchedCoverData_of_nonconstant_holomorphic
      hfHol hWeighted hnc' with hbc_def
  refine ⟨hbc, ?_⟩
  -- Step D. Compute branchedDegree.
  rw [JacobianChallenge.HolomorphicForms.branchedDegree_eq_weightedFiberCard hbc
      (OnePoint.infty : OnePoint ℂ)]
  -- Identify the fiber over ∞ with {P}.
  have hfib_eq : f.toMap ⁻¹' {(OnePoint.infty : OnePoint ℂ)} = ({P} : Set X) :=
    f.preimage_infty_eq_singleton_of_poleDivisor_point P hpole
  have hfib_finite :
      hbc.finite_fiber (OnePoint.infty : OnePoint ℂ) =
        (by exact hfib_eq ▸ Set.finite_singleton P :
          (f.toMap ⁻¹' {(OnePoint.infty : OnePoint ℂ)}).Finite) := by
    apply Subsingleton.elim
  show ((hbc.finite_fiber (OnePoint.infty : OnePoint ℂ)).toFinset).sum
        hbc.ramificationIndex = f.poleDivisor.degree.toNat
  have hto : (hbc.finite_fiber (OnePoint.infty : OnePoint ℂ)).toFinset = {P} := by
    rw [hfib_finite]
    rw [show (hfib_eq ▸ Set.finite_singleton P :
                (f.toMap ⁻¹' {(OnePoint.infty : OnePoint ℂ)}).Finite).toFinset =
              (Set.finite_singleton P).toFinset from by
      ext x
      simp [hfib_eq]]
    ext x
    simp
  rw [hto]
  rw [Finset.sum_singleton]
  -- ramificationIndex of the analytic constructor is mapAnalyticOrderAt.
  have hcompat :
      hbc.RamificationIndexCompatible :=
    JacobianChallenge.Blueprint.branchedCoverData_of_nonconstant_holomorphic_compatible
      hfHol hWeighted hnc'
  have hrami :
      hbc.ramificationIndex P =
        JacobianChallenge.HolomorphicForms.mapAnalyticOrderAt f.toMap P :=
    hcompat P (hfHol.holomorphicAt P)
  rw [hrami, han.simple_pole_order_one P hpole]
  -- f.poleDivisor.degree.toNat = (Divisor.point P).degree.toNat = 1.
  have h1 : Divisor.degree f.poleDivisor = 1 := by
    change Divisor.degree f.poles = 1
    rw [hpole]; exact Divisor.degree_point P
  rw [h1]; rfl

/-!
### Concrete simple-pole-to-sphere data and constructor

The production interface for a concrete fixed-pole meromorphic-map-to-sphere
is `SimplePoleToSphereData`. Its fields are the local analytic inputs
actually needed to construct a one-pole map: a concrete
piecewise-defined `toMap`, a global finite lift, continuity of `toMap`
into `OnePoint ℂ`, meromorphicity of the lift, simple-pole order data,
and modulus divergence at the pole.
-/

/--
**Concrete simple-pole production input.**

This record carries the local analytic content that a concrete
fixed-pole meromorphic-map-to-sphere is actually built from:

* `finiteLift : X → ℂ` — a global complex-valued function;
* `toMap : X → OnePoint ℂ` — the map to the Riemann sphere;
* `toMap_at_pole` / `toMap_off_pole` — `toMap` is `∞` exactly at `P`
  and `(finiteLift x : OnePoint ℂ)` elsewhere;
* `continuous_toMap` — continuity of `toMap` (this packages the
  removable-singularity / properness step into a hypothesis);
* `meromorphic_finiteLift` — the finite lift is meromorphic at every
  point in the manifold sense;
* `simple_pole_order` — at `P`, the chart-local analytic order of
  `toMap` (read in the inversion chart on `OnePoint ℂ`) is `1`;
* `pole_modulus` — `‖finiteLift x‖ → ∞` along the punctured
  neighborhood of `P`.

Branch-cover data is *not* part of this record; it is a proved
consequence of these fields plus the surrounding manifold structure.

We separate the `toMap` description into two equations
(`toMap_at_pole`, `toMap_off_pole`) rather than a single piecewise
`if` to avoid pulling in `DecidableEq X` typeclass requirements.
-/
structure SimplePoleToSphereData
    (X : Type*) [TopologicalSpace X] [T2Space X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X]
    [JacobianChallenge.Periods.StableChartAt ℂ X]
    (P : X) where
  /--
A global complex-valued lift, defined on all of `X` (the value at
  `P` is arbitrary; only off-`P` values matter for `toMap`).
-/
  finiteLift : X → ℂ
  /-- The map to the Riemann sphere. -/
  toMap : X → OnePoint ℂ
  /-- At `P`, `toMap` is `∞`. -/
  toMap_at_pole : toMap P = OnePoint.infty
  /-- Off `P`, `toMap` is the canonical complex coordinate of `finiteLift`. -/
  toMap_off_pole : ∀ x : X, x ≠ P → toMap x = ((finiteLift x : ℂ) : OnePoint ℂ)
  /-- Global continuity of `toMap` into `OnePoint ℂ`. -/
  continuous_toMap : Continuous toMap
  /--
The finite lift is meromorphic at every point of `X` (in the
  manifold sense).
-/
  meromorphic_finiteLift :
    ∀ p : X,
      JacobianChallenge.HolomorphicForms.VanishingOrder.MeromorphicAtX
        finiteLift p
  /-- At `P`, the chart-local analytic order of `toMap` is `1`. -/
  simple_pole_order :
    JacobianChallenge.HolomorphicForms.mapAnalyticOrderAt toMap P = 1
  /-- `‖finiteLift x‖ → ∞` as `x → P` in the punctured neighborhood. -/
  pole_modulus :
    Filter.Tendsto (fun x => ‖finiteLift x‖) (nhdsWithin P {P}ᶜ) Filter.atTop

namespace SimplePoleToSphereData

/-- Off the pole, `toMap` takes finite values. -/
theorem toMap_ne_infty_off_pole {X : Type*} [TopologicalSpace X] [T2Space X]
    [ChartedSpace ℂ X] [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X]
    [JacobianChallenge.Periods.StableChartAt ℂ X]
    {P : X} (d : SimplePoleToSphereData X P) {x : X}
    (hx : x ≠ P) : d.toMap x ≠ (OnePoint.infty : OnePoint ℂ) := by
  rw [d.toMap_off_pole x hx]
  exact OnePoint.coe_ne_infty _

/-- Off the pole, `(d.toMap x).getD 0 = d.finiteLift x`. -/
theorem getD_toMap_off_pole {X : Type*} [TopologicalSpace X] [T2Space X]
    [ChartedSpace ℂ X] [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X]
    [JacobianChallenge.Periods.StableChartAt ℂ X]
    {P : X} (d : SimplePoleToSphereData X P) {x : X}
    (hx : x ≠ P) : (d.toMap x).getD 0 = d.finiteLift x := by
  rw [d.toMap_off_pole x hx]
  rfl

end SimplePoleToSphereData

section OnePointExtend

variable {Y : Type*}

/--
Canonical one-point extension of `F : Y → ℂ` to `OnePoint ℂ`,
sending `P` to `∞` and any other point `x` to `((F x : ℂ) : OnePoint ℂ)`.

Classical decidability of `x = P` is used so that no `DecidableEq Y`
typeclass is required at the call site.
-/
noncomputable def onePointExtend (F : Y → ℂ) (P : Y) : Y → OnePoint ℂ := by
  classical
  exact fun x => if x = P then OnePoint.infty else ((F x : ℂ) : OnePoint ℂ)

@[simp] theorem onePointExtend_at (F : Y → ℂ) (P : Y) :
    onePointExtend F P P = OnePoint.infty := by
  classical
  simp [onePointExtend]

theorem onePointExtend_off {F : Y → ℂ} {P x : Y} (hx : x ≠ P) :
    onePointExtend F P x = ((F x : ℂ) : OnePoint ℂ) := by
  classical
  simp [onePointExtend, hx]

end OnePointExtend

/--
**Complex principal-part predicate.**

A predicate on a function `F : X → ℂ` and a point `P : X` saying that
`F` carries the full complex simple-pole behavior at `P` needed to
build a `SimplePoleToSphereData`:

* `meromorphic_everywhere` — `F` is meromorphic at every point of `X`
  (in the manifold sense);
* `continuous_extension` — the one-point extension
  `onePointExtend F P` is continuous;
* `orderAt_pole` — the chart-local analytic order of the extension at
  `P` (read in the inversion chart on `OnePoint ℂ`) is `1`;
* `modulus_tendsto` — `‖F x‖ → ∞` along the punctured neighborhood of
  `P`.

This is a `structure` (not a `Prop`) because the order-one and
modulus-divergence statements would otherwise need their own dedicated
proof terms; bundling them into one record is cleaner and matches the
shape of `SimplePoleToSphereData`.
-/
structure HasComplexSimplePolePrincipalPart (F : X → ℂ) (P : X) : Prop where
  meromorphic_everywhere :
    ∀ p : X,
      JacobianChallenge.HolomorphicForms.VanishingOrder.MeromorphicAtX F p
  continuous_extension : Continuous (onePointExtend F P)
  orderAt_pole :
    JacobianChallenge.HolomorphicForms.mapAnalyticOrderAt (onePointExtend F P) P = 1
  modulus_tendsto :
    Filter.Tendsto (fun x => ‖F x‖) (nhdsWithin P {P}ᶜ) Filter.atTop

/--
Given a complex function `F` with complex simple-pole principal part
at `P`, package it as a concrete `SimplePoleToSphereData X P` with
`finiteLift := F` and `toMap := onePointExtend F P`. All fields are
filled directly from the predicate fields.
-/
noncomputable def SimplePoleToSphereData.of_complexPrincipalPart
    (F : X → ℂ) (P : X) (hF : HasComplexSimplePolePrincipalPart F P) :
    SimplePoleToSphereData X P where
  finiteLift := F
  toMap := onePointExtend F P
  toMap_at_pole := onePointExtend_at F P
  toMap_off_pole := fun _x hx => onePointExtend_off hx
  continuous_toMap := hF.continuous_extension
  meromorphic_finiteLift := hF.meromorphic_everywhere
  simple_pole_order := hF.orderAt_pole
  pole_modulus := hF.modulus_tendsto

omit [CompactSpace X] [ConnectedSpace X] in

theorem singlePoleAnalyticData_of_simplePoleToSphereData
    (P : X) (d : SimplePoleToSphereData X P) :
    Nonempty (SinglePoleMeromorphicAnalyticData (X := X) P) := by
  classical
  -- Build the underlying MeromorphicMapToSphere.
  refine ⟨{
    map :=
      { toMap := d.toMap
        locally_meromorphic := True
        zeroDivisor := 0
        poleDivisor := Divisor.point P
        principalDivisor := -Divisor.point P
        principalDivisor_eq := by simp
        poleDivisor_nonneg := fun x => Divisor.effective_point P x
        zero_or_pole_eq_zero := fun _ => Or.inl rfl
        toMap_ne_infty_of_poleDivisor_zero := ?_
        continuousOn_ne_infty := ?_
        toFiniteFun_mdifferentiable := ?_
        toMap_eq_infty_of_poleDivisor_pos := ?_ }
    poleDivisor_eq := rfl
    nonconstant := ?_
    poleModulusData := ?_
    analyticData := ?_ }⟩
  -- `toMap_ne_infty_of_poleDivisor_zero`: poleDivisor x = 0 ⇒ x ≠ P ⇒ toMap x ≠ ∞.
  · intro x hx
    have hxP : x ≠ P := by
      intro hxeq
      have : (Divisor.point P : Divisor X) x = 1 := by
        rw [hxeq]; exact Divisor.point_apply_self P
      rw [this] at hx
      exact one_ne_zero hx
    exact d.toMap_ne_infty_off_pole hxP
  -- `continuousOn_ne_infty`: restriction of d.continuous_toMap to the non-infty set.
  · exact d.continuous_toMap.continuousOn
  -- `toFiniteFun_mdifferentiable`: vacuous because no global lift `g` exists
  -- satisfying d.toMap = ((g · : ℂ) : OnePoint ℂ) (since d.toMap P = ∞).
  · intro g hg
    exfalso
    have h := congrFun hg P
    rw [d.toMap_at_pole] at h
    exact OnePoint.infty_ne_coe (g P) h
  -- `toMap_eq_infty_of_poleDivisor_pos`: at P, toMap = ∞.
  · intro x hx
    have hxP : x = P := by
      by_contra hxne
      have : (Divisor.point P : Divisor X) x = 0 := Divisor.point_apply_ne hxne
      rw [this] at hx; exact (lt_irrefl _) hx
    subst hxP
    exact d.toMap_at_pole
  -- `nonconstant`: pick Q ≠ P; d.toMap Q ≠ d.toMap P = ∞.
  · -- The compact connected Riemann surface has Nonempty X (because P : X), so
    -- there is at least one other point.
    haveI : Nonempty X := ⟨P⟩
    obtain ⟨a, b, hab⟩ := exists_two_distinct_points_of_chartedSpaceComplex (X := X)
    -- One of a, b is different from P.
    intro ⟨c, hc⟩
    -- Both a and b map to c, but at least one of them differs from P (since a ≠ b
    -- and equality with P can hold for at most one of them).
    by_cases haP : a = P
    · -- Then b ≠ P (since a = P and a ≠ b).
      have hbP : b ≠ P := by intro hbP; exact hab (haP.trans hbP.symm)
      have hcP : c = OnePoint.infty := by
        rw [← hc a]
        change d.toMap a = OnePoint.infty
        rw [haP]; exact d.toMap_at_pole
      have hb : d.toMap b = c := hc b
      rw [hcP] at hb
      exact d.toMap_ne_infty_off_pole hbP hb
    · -- a ≠ P; d.toMap a is finite but d.toMap P = ∞.
      have hcP : c = OnePoint.infty := by
        rw [← hc P]
        exact d.toMap_at_pole
      have ha : d.toMap a = c := hc a
      rw [hcP] at ha
      exact d.toMap_ne_infty_off_pole haP ha
  -- `PoleModulusData`: provide the finite lift d.finiteLift with modulus divergence.
  · refine ⟨?_⟩
    intro Q hQ
    -- Only Q = P has positive poleDivisor for our chosen poleDivisor := Divisor.point P.
    have hQP : Q = P := by
      by_contra hne
      have : (Divisor.point P : Divisor X) Q = 0 := Divisor.point_apply_ne hne
      change (Divisor.point P : Divisor X) Q > 0 at hQ
      rw [this] at hQ; exact (lt_irrefl _) hQ
    subst hQP
    refine ⟨d.finiteLift, ?_, d.pole_modulus⟩
    intro x hx
    have hxP : x ≠ Q := by
      intro hxQ
      rw [hxQ, Divisor.point_apply_self] at hx
      exact one_ne_zero hx
    exact d.toMap_off_pole x hxP
  -- `AnalyticData`: three fields.
  · refine
      { continuous_toMap := d.continuous_toMap
        meromorphic_getD := ?_
        simple_pole_order_one := ?_ }
    · -- `meromorphic_getD`: (d.toMap q).getD 0 is MeromorphicAtX at every p.
      -- The two functions `(d.toMap ·).getD 0` and `d.finiteLift` agree on `{P}ᶜ`.
      -- Pulled through the chart, this agreement is eventual in `𝓝[≠] (chart p p)`.
      intro p
      have hmer := d.meromorphic_finiteLift p
      unfold JacobianChallenge.HolomorphicForms.VanishingOrder.MeromorphicAtX at hmer ⊢
      refine hmer.congr ?_
      -- Show: (fun q => (d.toMap q).getD 0) ∘ (extChartAt I p).symm
      --   =ᶠ[𝓝[≠] (extChartAt I p p)]
      --   d.finiteLift ∘ (extChartAt I p).symm
      -- They differ at most at the point t such that (extChartAt I p).symm t = P.
      -- Use the continuity-based argument: on the open set
      -- `(extChartAt I p).symm ⁻¹' {P}ᶜ`, the functions agree, and this set is a
      -- punctured neighborhood of `extChartAt I p p` (it is open and contains all
      -- points whose chart-inverse is not P; the chart inverse equals p at the
      -- center, and p = P or p ≠ P).
      rw [show ⇑(extChartAt 𝓘(ℂ) p) = chartAt ℂ p from
        JacobianChallenge.HolomorphicForms.VanishingOrder.extChartAt_eq_chartAt p]
      rw [show ⇑(extChartAt 𝓘(ℂ) p).symm = (chartAt ℂ p).symm from
        JacobianChallenge.HolomorphicForms.VanishingOrder.extChartAt_symm_eq_chartAt_symm p]
      -- The chart `(chartAt ℂ p)` has open source containing `p`. Its inverse
      -- maps target to source. We use that the chart is bijective on (source, target).
      -- The set `(chartAt ℂ p).target ∩ {t | (chartAt ℂ p).symm t ≠ P}` is open
      -- and contains `chartAt ℂ p p` if `p ≠ P`, or its complement of one point
      -- if `p = P`.
      -- Show: ∀ᶠ t in 𝓝[≠] (chartAt ℂ p p),
      --   (d.finiteLift ∘ (chartAt ℂ p).symm) t = ((·.getD 0) ∘ d.toMap ∘ (chartAt ℂ p).symm) t
      show (d.finiteLift ∘ (chartAt ℂ p).symm)
          =ᶠ[𝓝[≠] (chartAt ℂ p p)] (fun q => (d.toMap q).getD 0) ∘ (chartAt ℂ p).symm
      by_cases hpP : p = P
      · -- p = P case: punctured nbhd argument via chart target.
        -- After `subst hpP`, the variable `P` is replaced by `p` (Lean 4 default).
        subst hpP
        rw [Filter.EventuallyEq, eventually_nhdsWithin_iff]
        have htarget : (chartAt ℂ p).target ∈ 𝓝 (chartAt ℂ p p) :=
          (chartAt ℂ p).open_target.mem_nhds
            ((chartAt ℂ p).map_source (mem_chart_source ℂ p))
        filter_upwards [htarget] with t ht ht_ne
        have ht_ne' : t ≠ chartAt ℂ p p := by
          intro heq
          apply ht_ne
          show t ∈ ({chartAt ℂ p p} : Set ℂ)
          rw [heq]
          exact Set.mem_singleton _
        have hsymm_ne : (chartAt ℂ p).symm t ≠ p := by
          intro heq
          have h1 : (chartAt ℂ p) ((chartAt ℂ p).symm t) = t :=
            (chartAt ℂ p).right_inv ht
          rw [heq] at h1
          exact ht_ne' h1.symm
        exact (d.getD_toMap_off_pole hsymm_ne).symm
      · -- p ≠ P case: full-nbhd continuity argument.
        have h_sym_eq :
            (chartAt ℂ p).symm (chartAt ℂ p p) = p :=
          (chartAt ℂ p).left_inv (mem_chart_source ℂ p)
        have h_cont : ContinuousAt (chartAt ℂ p).symm (chartAt ℂ p p) := by
          have hsrc : chartAt ℂ p p ∈ (chartAt ℂ p).target :=
            (chartAt ℂ p).map_source (mem_chart_source ℂ p)
          exact (chartAt ℂ p).continuousAt_symm hsrc
        have hP_compl_nhd_p : ({P}ᶜ : Set X) ∈ 𝓝 p :=
          isOpen_compl_singleton.mem_nhds hpP
        have hP_compl_nhd_sym : ({P}ᶜ : Set X) ∈ 𝓝 ((chartAt ℂ p).symm (chartAt ℂ p p)) := by
          rw [h_sym_eq]; exact hP_compl_nhd_p
        have h_nhd : ∀ᶠ t in 𝓝 (chartAt ℂ p p),
            (chartAt ℂ p).symm t ∈ ({P}ᶜ : Set X) :=
          h_cont.preimage_mem_nhds hP_compl_nhd_sym
        rw [Filter.EventuallyEq]
        refine Filter.Eventually.filter_mono nhdsWithin_le_nhds ?_
        filter_upwards [h_nhd] with t htne
        exact (d.getD_toMap_off_pole htne).symm
    · -- `simple_pole_order_one`: given hpole, P' = P, then use d.simple_pole_order.
      intro P' hpole
      have hpoint : (Divisor.point P : Divisor X) = Divisor.point P' := by
        -- hpole : (constructedMap).poles = Divisor.point P'
        -- unfold poles → poleDivisor (definitional via dot notation)
        have hpoles : (Divisor.point P : Divisor X) = Divisor.point P' := hpole
        exact hpoles
      have hP'P : P' = P :=
        (Finsupp.single_left_injective (M := ℤ) (α := X)
          (one_ne_zero) hpoint).symm
      subst hP'P
      exact d.simple_pole_order

/-! ### Genus-zero fixed-pole route-data assemblies -/

/--
For a given `MeromorphicMapToSphere f` with prescribed simple pole at
`P`, nonconstancy, and **explicit `AnalyticData`**, the
branched-cover-data structure follows from
`branchedCoverDataOfPoleDegree_of_simple_pole`.

This is the per-`f` theorem with concrete hypotheses: the analytic
content comes in as `han : f.AnalyticData`, not as the impossible
"derive analyticity from `PoleModulusData`" claim previously held
here.

Note: `_h` (analytic-genus-zero) and `_hmem` (Riemann-Roch membership)
are accepted but unused; they are kept in the signature so callers
that came through the genus-zero pipeline can pass them without
reshaping. The branched-cover content depends only on `(hnc, hpole,
han)`.
-/
theorem genusZero_fixedPole_branchedCoverDataOfPoleDegree
    (X : Type*) [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X]
    [JacobianChallenge.Periods.StableChartAt ℂ X]
    [FiniteDimensionalHolomorphicOneForms ℂ X]
    (P : X) (_h : analyticGenus ℂ X = 0)
    (f : MeromorphicMapToSphere X)
    (hnc : f.Nonconstant)
    (_hmem : f.MemRiemannRochSpace (Divisor.point P))
    (hpole : f.poles = Divisor.point P)
    (han : f.AnalyticData) :
    f.BranchedCoverDataOfPoleDegree :=
  f.branchedCoverDataOfPoleDegree_of_simple_pole P hnc hpole han

/-! ### Riemann-Roch analytic-route conditional bridge -/

omit [T2Space X] [CompactSpace X] [ConnectedSpace X] in
/--
**Helper: the canonical one-point extension of the finite lift
agrees with the original `f.toMap`.**

For a `MeromorphicMapToSphere f` whose pole divisor is `Divisor.point P`,
the canonical finite lift `(f.toMap ·).getD 0` extended back to `OnePoint ℂ`
via `onePointExtend ... P` recovers `f.toMap`:

* at `P`, both sides equal `∞` (left by definition of `onePointExtend`,
  right by `toMap_pole_eq_infty_of_poleDivisor_point`);
* off `P`, `f.toMap x = some z` for some `z` (by
  `toMap_ne_infty_off_pole`), so `getD 0` recovers `z` and the
  coercion `((z : ℂ) : OnePoint ℂ) = some z = f.toMap x`.
-/
theorem onePointExtend_getD_eq_toMap_of_pole
    (f : MeromorphicMapToSphere X) (P : X)
    (hpole : f.poles = Divisor.point P) :
    onePointExtend (fun x => (f.toMap x).getD 0) P = f.toMap := by
  classical
  funext x
  by_cases hx : x = P
  · rw [hx, onePointExtend_at]
    exact (f.toMap_pole_eq_infty_of_poleDivisor_point P hpole).symm
  · rw [onePointExtend_off hx]
    have hne : f.toMap x ≠ (OnePoint.infty : OnePoint ℂ) :=
      f.toMap_ne_infty_off_pole P hpole x hx
    rcases hfx : f.toMap x with _ | z
    · exact (hne hfx).elim
    · rfl

/--
Given a `MeromorphicMapToSphere f` with simple pole at `P`
(`f.poles = Divisor.point P`), per-point chart-local `AnalyticData`,
and modulus-divergence `PoleModulusData`, the canonical finite lift
`F := fun x => (f.toMap x).getD 0` carries the four fields of
`HasComplexSimplePolePrincipalPart F P`:
-/
theorem complexPrincipalPart_of_meromorphicMap_analyticData
    {X : Type*} [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X]
    [JacobianChallenge.Periods.StableChartAt ℂ X]
    (P : X) (f : MeromorphicMapToSphere X)
    (hpole : f.poles = Divisor.point P)
    (han : f.AnalyticData)
    (hmod : f.PoleModulusData) :
    HasComplexSimplePolePrincipalPart (fun x => (f.toMap x).getD 0) P := by
  classical
  -- Helper: identify the one-point extension with `f.toMap`.
  have hext : onePointExtend (fun x => (f.toMap x).getD 0) P = f.toMap :=
    onePointExtend_getD_eq_toMap_of_pole f P hpole
  refine
    { meromorphic_everywhere := han.meromorphic_getD
      continuous_extension := ?_
      orderAt_pole := ?_
      modulus_tendsto := ?_ }
  · -- Continuity of the extension follows from continuity of `f.toMap`
    -- and the identification `hext`.
    rw [hext]
    exact han.continuous_toMap
  · -- The chart-local analytic order at `P` of the extension equals the
    -- order of `f.toMap` at `P`, which is `1` by `simple_pole_order_one`.
    rw [hext]
    exact han.simple_pole_order_one P hpole
  · -- Modulus divergence comes from `PoleModulusData` applied at the
    -- single positive-pole point `P`.
    -- Step 1: extract the finite-modulus lift from `hmod`.
    have hposP : 0 < f.poleDivisor P := by
      have hh : f.poleDivisor P = (Divisor.point P : Divisor X) P := by
        change f.poles P = (Divisor.point P : Divisor X) P
        rw [hpole]
      rw [hh, Divisor.point_apply_self]
      decide
    obtain ⟨g, hg_eq, hg_div⟩ := hmod.exists_modulus_atTop_at_pole P hposP
    -- Step 2: off `P`, `(f.toMap x).getD 0 = g x`.
    -- So `‖(f.toMap x).getD 0‖ = ‖g x‖` eventually in `nhdsWithin P {P}ᶜ`.
    refine (hg_div.congr' ?_)
    filter_upwards [self_mem_nhdsWithin] with x hx
    -- `hx : x ∈ {P}ᶜ`, i.e. `x ≠ P`. Then `f.poleDivisor x = 0`.
    have hxP : x ≠ P := hx
    have hxpoleZero : f.poleDivisor x = 0 := by
      have hh : f.poleDivisor x = (Divisor.point P : Divisor X) x := by
        change f.poles x = (Divisor.point P : Divisor X) x
        rw [hpole]
      rw [hh, Divisor.point_apply_ne hxP]
    -- `hg_eq` gives `f.toMap x = ((g x : ℂ) : OnePoint ℂ)`.
    have hfx : f.toMap x = ((g x : ℂ) : OnePoint ℂ) := hg_eq x hxpoleZero
    -- Hence `(f.toMap x).getD 0 = g x`, so the norms agree.
    show ‖g x‖ = ‖(f.toMap x).getD 0‖
    rw [hfx]; rfl

/-!
### Production analytic Riemann-Roch witness

The current divisor-level Riemann-Roch route (e.g. the assembly
`genusZero_fixedPole_meromorphicData_nonempty`, which under the hood
selects `singlePoleMeromorphicMap P`) is correct only for
divisor/topology-level claims: the underlying map is the bump-cutoff
scaffold, whose canonical finite lift is *not* meromorphic everywhere
and whose chart-local order at `P` is not the analytic order-one of a
production simple pole. The actual analytic content of Riemann-Roch — an
actual meromorphic function with prescribed simple pole *and* the
chart-local Laurent / order data — is collected by the records below.

These records are intentionally *distinct* from
`GenusZeroPointRiemannRochElement` (defined in `RiemannRoch.lean`).
The latter is the divisor/topology-level RR witness that the existing
scaffold can populate; the records below are the analytic-level
witnesses that the scaffold cannot actually populate.

The records form a small hierarchy:
-/

/--
**Concrete simple-pole Riemann-Roch section (smallest analytic witness).**

The bare local analytic data an actual genus-zero Riemann-Roch fixed-pole
section provides:

* `finiteLift : X → ℂ` — the meromorphic function on `X` with a simple
  pole at `P`, presented as a complex-valued function (defined on all of
  `X`; the value at `P` is irrelevant).
* `hasPrincipalPart : HasComplexSimplePolePrincipalPart finiteLift P` —
  the analytic content that says `finiteLift` is meromorphic at every
  point, that the canonical one-point extension is globally continuous
  on `OnePoint ℂ`, that the chart-local order of the extension at `P`
  is `1`, and that the modulus diverges at `P`.
-/
structure SimplePoleRRSection
    (X : Type*) [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X]
    [JacobianChallenge.Periods.StableChartAt ℂ X]
    (P : X) where
  /--
The complex-valued meromorphic function with a simple pole
  at `P` — the Riemann-Roch section.
-/
  finiteLift : X → ℂ
  /--
The chart-local analytic principal-part data: meromorphic
  everywhere, the one-point extension is continuous on `OnePoint ℂ`,
  chart-local order one at `P`, and modulus divergence at `P`.
-/
  hasPrincipalPart : HasComplexSimplePolePrincipalPart finiteLift P

namespace SimplePoleRRSection

variable {X : Type*} [TopologicalSpace X] [T2Space X] [CompactSpace X]
  [ChartedSpace ℂ X]
  [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X]
  [JacobianChallenge.Periods.StableChartAt ℂ X]

/--
Composes `SimplePoleToSphereData.of_complexPrincipalPart` with the
record's `hasPrincipalPart` field. The resulting `toMap` is
`onePointExtend s.finiteLift P` and the resulting `finiteLift` is
`s.finiteLift`.
-/
noncomputable def toSimplePoleToSphereData
    {P : X} (s : SimplePoleRRSection X P) :
    SimplePoleToSphereData X P :=
  SimplePoleToSphereData.of_complexPrincipalPart s.finiteLift P s.hasPrincipalPart

end SimplePoleRRSection

/--
**Production analytic Riemann-Roch fixed-pole witness (older record).**

The production output of an actual genus-zero analytic Riemann-Roch
theorem on a compact connected Riemann surface: a meromorphic map to
the sphere with pole divisor exactly `[P]` (`poleDivisor_eq`),
nonconstant (`nonconstant`), in the Riemann-Roch space `L([P])`
(`mem_L_point`), and — crucially — equipped with the chart-local
analytic content (`analyticData`) and modulus-divergence
(`poleModulusData`) that the bump-cutoff scaffold *cannot* actually
provide.
-/
structure GenusZeroFixedPoleAnalyticRRWitness
    (X : Type*) [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X]
    [JacobianChallenge.Periods.StableChartAt ℂ X]
    [FiniteDimensionalHolomorphicOneForms ℂ X]
    (P : X) where
  /-- The concrete meromorphic-map-to-sphere with a simple pole at `P`. -/
  map : MeromorphicMapToSphere X
  /-- The pole divisor is exactly `[P]`. -/
  poleDivisor_eq : map.poles = Divisor.point P
  /-- The map is nonconstant. -/
  nonconstant : map.Nonconstant
  /-- The map lies in the Riemann-Roch space `L([P])`. -/
  mem_L_point : map.MemRiemannRochSpace (Divisor.point P)
  /--
The chart-local analytic content: meromorphicity of the canonical
  finite lift everywhere, global continuity to `OnePoint ℂ`, and
  order-one at the simple pole. This field is the actual analytic
  content of Riemann-Roch that the bump-cutoff scaffold cannot supply.
-/
  analyticData : map.AnalyticData
  /-- Modulus-divergence at the pole. -/
  poleModulusData : map.PoleModulusData

namespace SimplePoleRRSection

variable {X : Type*} [TopologicalSpace X] [T2Space X] [CompactSpace X]
  [ConnectedSpace X] [ChartedSpace ℂ X]
  [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X]
  [JacobianChallenge.Periods.StableChartAt ℂ X]
  [FiniteDimensionalHolomorphicOneForms ℂ X]

omit [ConnectedSpace X] [FiniteDimensionalHolomorphicOneForms ℂ X] in

theorem toSinglePoleMeromorphicAnalyticData
    {P : X} (s : SimplePoleRRSection X P) :
    Nonempty (SinglePoleMeromorphicAnalyticData (X := X) P) :=
  singlePoleAnalyticData_of_simplePoleToSphereData (X := X) P s.toSimplePoleToSphereData

/--
Projects out the full bundle: the underlying `MeromorphicMapToSphere`,
its pole divisor equation, nonconstancy, `AnalyticData`, and
`PoleModulusData` come from the inline simple-pole assembly, mirroring
`singlePoleAnalyticData_of_simplePoleToSphereData` but exposing
`zeroDivisor := 0` so that
`MemRiemannRochSpace (Divisor.point P)` is direct: `(f) + [P] =
zeroDivisor - poleDivisor + [P] = 0 - [P] + [P] = 0 ≥ 0`.
-/
noncomputable def toGenusZeroFixedPoleAnalyticRRWitness
    {P : X} (s : SimplePoleRRSection X P) :
    GenusZeroFixedPoleAnalyticRRWitness X P := by
  classical
  let d : SimplePoleToSphereData X P := s.toSimplePoleToSphereData
  -- Build the analytic data record manually (paralleling
  -- `singlePoleAnalyticData_of_simplePoleToSphereData`) so that
  -- `zeroDivisor := 0` is in scope and the `MemRiemannRochSpace` field
  -- follows from a direct divisor calculation.
  refine
    { map :=
        { toMap := d.toMap
          locally_meromorphic := True
          zeroDivisor := 0
          poleDivisor := Divisor.point P
          principalDivisor := -Divisor.point P
          principalDivisor_eq := by simp
          poleDivisor_nonneg := fun x => Divisor.effective_point P x
          zero_or_pole_eq_zero := fun _ => Or.inl rfl
          toMap_ne_infty_of_poleDivisor_zero := ?_
          continuousOn_ne_infty := ?_
          toFiniteFun_mdifferentiable := ?_
          toMap_eq_infty_of_poleDivisor_pos := ?_ }
      poleDivisor_eq := rfl
      nonconstant := ?_
      mem_L_point := ?_
      analyticData := ?_
      poleModulusData := ?_ }
  -- `toMap_ne_infty_of_poleDivisor_zero`.
  · intro x hx
    have hxP : x ≠ P := by
      intro hxeq
      have h1 : (Divisor.point P : Divisor X) x = 1 := by
        rw [hxeq]; exact Divisor.point_apply_self P
      rw [h1] at hx
      exact one_ne_zero hx
    exact d.toMap_ne_infty_off_pole hxP
  -- `continuousOn_ne_infty`.
  · exact d.continuous_toMap.continuousOn
  -- `toFiniteFun_mdifferentiable`: vacuous, no global lift `g` exists.
  · intro g hg
    exfalso
    have h := congrFun hg P
    rw [d.toMap_at_pole] at h
    exact OnePoint.infty_ne_coe (g P) h
  -- `toMap_eq_infty_of_poleDivisor_pos`.
  · intro x hx
    have hxP : x = P := by
      by_contra hxne
      have h0 : (Divisor.point P : Divisor X) x = 0 := Divisor.point_apply_ne hxne
      rw [h0] at hx; exact (lt_irrefl _) hx
    subst hxP
    exact d.toMap_at_pole
  -- `nonconstant`. Same proof as in `singlePoleAnalyticData_of_simplePoleToSphereData`.
  · haveI : Nonempty X := ⟨P⟩
    obtain ⟨a, b, hab⟩ := exists_two_distinct_points_of_chartedSpaceComplex (X := X)
    intro ⟨c, hc⟩
    by_cases haP : a = P
    · have hbP : b ≠ P := by intro hbP; exact hab (haP.trans hbP.symm)
      have hcP : c = OnePoint.infty := by
        rw [← hc a]
        change d.toMap a = OnePoint.infty
        rw [haP]; exact d.toMap_at_pole
      have hb : d.toMap b = c := hc b
      rw [hcP] at hb
      exact d.toMap_ne_infty_off_pole hbP hb
    · have hcP : c = OnePoint.infty := by
        rw [← hc P]
        exact d.toMap_at_pole
      have ha : d.toMap a = c := hc a
      rw [hcP] at ha
      exact d.toMap_ne_infty_off_pole haP ha
  -- `mem_L_point`: `(f) + Divisor.point P = zeroDivisor - poleDivisor + Divisor.point P
  -- = 0 - Divisor.point P + Divisor.point P = 0 ≥ 0`.
  · unfold MeromorphicMapToSphere.MemRiemannRochSpace
    -- principal = zeroDivisor - poleDivisor = 0 - Divisor.point P = -Divisor.point P
    -- principal + Divisor.point P = 0
    show Divisor.Effective (-Divisor.point P + Divisor.point P)
    have : -Divisor.point P + (Divisor.point P : Divisor X) = 0 := by abel
    rw [this]
    exact Divisor.effective_zero
  -- `analyticData`: continuous_toMap, meromorphic_getD, simple_pole_order_one.
  · refine
      { continuous_toMap := d.continuous_toMap
        meromorphic_getD := ?_
        simple_pole_order_one := ?_ }
    · intro p
      have hmer := d.meromorphic_finiteLift p
      unfold JacobianChallenge.HolomorphicForms.VanishingOrder.MeromorphicAtX at hmer ⊢
      refine hmer.congr ?_
      rw [show ⇑(extChartAt 𝓘(ℂ) p) = chartAt ℂ p from
        JacobianChallenge.HolomorphicForms.VanishingOrder.extChartAt_eq_chartAt p]
      rw [show ⇑(extChartAt 𝓘(ℂ) p).symm = (chartAt ℂ p).symm from
        JacobianChallenge.HolomorphicForms.VanishingOrder.extChartAt_symm_eq_chartAt_symm p]
      show (d.finiteLift ∘ (chartAt ℂ p).symm)
          =ᶠ[𝓝[≠] (chartAt ℂ p p)] (fun q => (d.toMap q).getD 0) ∘ (chartAt ℂ p).symm
      by_cases hpP : p = P
      · subst hpP
        rw [Filter.EventuallyEq, eventually_nhdsWithin_iff]
        have htarget : (chartAt ℂ p).target ∈ 𝓝 (chartAt ℂ p p) :=
          (chartAt ℂ p).open_target.mem_nhds
            ((chartAt ℂ p).map_source (mem_chart_source ℂ p))
        filter_upwards [htarget] with t ht ht_ne
        have ht_ne' : t ≠ chartAt ℂ p p := by
          intro heq
          apply ht_ne
          show t ∈ ({chartAt ℂ p p} : Set ℂ)
          rw [heq]
          exact Set.mem_singleton _
        have hsymm_ne : (chartAt ℂ p).symm t ≠ p := by
          intro heq
          have h1 : (chartAt ℂ p) ((chartAt ℂ p).symm t) = t :=
            (chartAt ℂ p).right_inv ht
          rw [heq] at h1
          exact ht_ne' h1.symm
        exact (d.getD_toMap_off_pole hsymm_ne).symm
      · have h_sym_eq :
            (chartAt ℂ p).symm (chartAt ℂ p p) = p :=
          (chartAt ℂ p).left_inv (mem_chart_source ℂ p)
        have h_cont : ContinuousAt (chartAt ℂ p).symm (chartAt ℂ p p) := by
          have hsrc : chartAt ℂ p p ∈ (chartAt ℂ p).target :=
            (chartAt ℂ p).map_source (mem_chart_source ℂ p)
          exact (chartAt ℂ p).continuousAt_symm hsrc
        have hP_compl_nhd_p : ({P}ᶜ : Set X) ∈ 𝓝 p :=
          isOpen_compl_singleton.mem_nhds hpP
        have hP_compl_nhd_sym : ({P}ᶜ : Set X) ∈ 𝓝 ((chartAt ℂ p).symm (chartAt ℂ p p)) := by
          rw [h_sym_eq]; exact hP_compl_nhd_p
        have h_nhd : ∀ᶠ t in 𝓝 (chartAt ℂ p p),
            (chartAt ℂ p).symm t ∈ ({P}ᶜ : Set X) :=
          h_cont.preimage_mem_nhds hP_compl_nhd_sym
        rw [Filter.EventuallyEq]
        refine Filter.Eventually.filter_mono nhdsWithin_le_nhds ?_
        filter_upwards [h_nhd] with t htne
        exact (d.getD_toMap_off_pole htne).symm
    · intro P' hpole
      have hpoint : (Divisor.point P : Divisor X) = Divisor.point P' := by
        have hpoles : (Divisor.point P : Divisor X) = Divisor.point P' := hpole
        exact hpoles
      have hP'P : P' = P :=
        (Finsupp.single_left_injective (M := ℤ) (α := X)
          (one_ne_zero) hpoint).symm
      subst hP'P
      exact d.simple_pole_order
  -- `poleModulusData`. Same proof as in the constructor.
  · refine ⟨?_⟩
    intro Q hQ
    have hQP : Q = P := by
      by_contra hne
      have h0 : (Divisor.point P : Divisor X) Q = 0 := Divisor.point_apply_ne hne
      change (Divisor.point P : Divisor X) Q > 0 at hQ
      rw [h0] at hQ; exact (lt_irrefl _) hQ
    subst hQP
    refine ⟨d.finiteLift, ?_, d.pole_modulus⟩
    intro x hx
    have hxP : x ≠ Q := by
      intro hxQ
      rw [hxQ, Divisor.point_apply_self] at hx
      exact one_ne_zero hx
    exact d.toMap_off_pole x hxP

end SimplePoleRRSection

/-!
### Section-level Riemann-Roch record with explicit local order data

The record `SimplePoleRRSection X P` (above) bundles a function
`finiteLift : X → ℂ` with the analytic predicate
`HasComplexSimplePolePrincipalPart` — but the four predicate fields are
*deduced* analytic content, not the section-level divisor/order data
that genus-zero Riemann-Roch directly produces.

The record `RiemannRochSectionAtPoint X P` below carries the
strictly-richer section-level local data:

This is **not** a rename of `SimplePoleRRSection`: the
`orderAt_P_eq_neg_one` and `noPoleOff_P` fields expose actual divisor
content (`(finiteLift) = -[P] + zeros`), which a section produced by
Riemann-Roch carries by construction and which `SimplePoleRRSection`
does not encode.
-/

/--
**Section-level Riemann-Roch input with explicit local order
data.**

The local data of a section `f ∈ L(P)` with simple pole at `P`:

The `orderAt_P_eq_neg_one` and `noPoleOff_P` fields are the
section-level local divisor data that genus-zero Riemann-Roch
*directly* provides — they are what distinguishes a real RR section
from an arbitrary "function with a simple pole" predicate witness.
-/
structure RiemannRochSectionAtPoint
    (X : Type*) [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X]
    [JacobianChallenge.Periods.StableChartAt ℂ X]
    (P : X) where
  /-- The Riemann-Roch section as a complex-valued function. -/
  finiteLift : X → ℂ
  /-- The section is meromorphic at every point of `X`. -/
  meromorphic_everywhere :
    ∀ p : X,
      JacobianChallenge.HolomorphicForms.VanishingOrder.MeromorphicAtX finiteLift p
  /--
Off the prescribed pole, the section has nonnegative chart-local
  vanishing order — i.e. no poles outside `P`. This is the divisor
  bound `(finiteLift) ≥ -[P]` at every point `p ≠ P`.
-/
  noPoleOff_P :
    ∀ p : X, p ≠ P →
      0 ≤ JacobianChallenge.HolomorphicForms.VanishingOrder.orderAt p finiteLift
  /--
At `P`, the section has chart-local vanishing order exactly `-1`
  — a simple pole.
-/
  orderAt_P_eq_neg_one :
    JacobianChallenge.HolomorphicForms.VanishingOrder.orderAt P finiteLift = (-1 : ℤ)
  /-- The one-point extension is continuous on `OnePoint ℂ`. -/
  continuous_extension : Continuous (onePointExtend finiteLift P)
  /--
The chart-local analytic order of the one-point extension at `P`
  (read in the inversion chart on `OnePoint ℂ`) is `1`.
-/
  orderAt_pole_in_extension :
    JacobianChallenge.HolomorphicForms.mapAnalyticOrderAt
      (onePointExtend finiteLift P) P = 1
  /-- The modulus of the section diverges at `P`. -/
  modulus_tendsto :
    Filter.Tendsto (fun x => ‖finiteLift x‖) (nhdsWithin P {P}ᶜ) Filter.atTop

namespace RiemannRochSectionAtPoint

variable {X : Type*} [TopologicalSpace X] [T2Space X] [CompactSpace X]
  [ChartedSpace ℂ X]
  [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X]
  [JacobianChallenge.Periods.StableChartAt ℂ X]

/--
Each field of `HasComplexSimplePolePrincipalPart` is supplied by the
corresponding field of `RiemannRochSectionAtPoint`:

* `meromorphic_everywhere` — directly the section record field.
* `continuous_extension` — directly.
* `orderAt_pole` — directly the `orderAt_pole_in_extension` field.
* `modulus_tendsto` — directly.

This conversion does **not** use `orderAt_P_eq_neg_one` or `noPoleOff_P`
— those are section-level local order data that the
`HasComplexSimplePolePrincipalPart` predicate does not need to expose.
They remain in the section record as evidence that the witness is a
production Riemann-Roch section, not just a function with a simple-pole
principal part.
-/
theorem hasComplexSimplePolePrincipalPart
    {P : X} (s : RiemannRochSectionAtPoint X P) :
    HasComplexSimplePolePrincipalPart s.finiteLift P where
  meromorphic_everywhere := s.meromorphic_everywhere
  continuous_extension := s.continuous_extension
  orderAt_pole := s.orderAt_pole_in_extension
  modulus_tendsto := s.modulus_tendsto

/--
Drops the section-level order/divisor data (`orderAt_P_eq_neg_one`,
`noPoleOff_P`, `meromorphic_everywhere` as a separate field) and
returns only the `finiteLift` + `HasComplexSimplePolePrincipalPart`
bundle. The principal-part predicate is supplied by
`hasComplexSimplePolePrincipalPart`.
-/
def toSimplePoleRRSection
    {P : X} (s : RiemannRochSectionAtPoint X P) :
    SimplePoleRRSection X P where
  finiteLift := s.finiteLift
  hasPrincipalPart := s.hasComplexSimplePolePrincipalPart

end RiemannRochSectionAtPoint

/-!
### Pure-RR section layer (`PointRiemannRochSection`)

The record `PointRiemannRochSection X P` exposes *only* the algebraic
content of an element of `L(P)` outside the constants: meromorphic
everywhere, divisor bound `(f) ≥ -[P]`, and not constant. It contains
no one-point-extension data, no chart-local order at `P` claim, no
modulus-divergence data, and no analytic-extension fields. Those are
local consequences of the algebraic data, isolated as separate provider
lemmas below.

The Riemann-Roch provider `genusZero_pointRRSection_outside_constants_exists`
asks for the algebraic input only. The order-extraction lemma
`PointRiemannRochSection.orderAt_P_eq_neg_one` deduces
`orderAt P f = -1` from the algebraic data plus the compact-Liouville
provider `meromorphic_no_poles_constant`. The conversion
`PointRiemannRochSection.toRiemannRochSectionAtPoint` deduces the
analytic-extension fields from the local-Laurent providers
(`continuous_onePointExtend_of_meromorphic_order_neg_one`,
`mapAnalyticOrderAt_onePointExtend_of_order_neg_one`,
`tendsto_norm_atTop_of_order_neg_one`).
-/

/--
**Pure-RR section: an element of `L(P)` outside constants.**

The minimal algebraic data of a Riemann-Roch section at a single point
`P`: a complex-valued function on `X` that is meromorphic everywhere,
holomorphic off `P`, has divisor bound `(f) ≥ -[P]` at `P`, and is not
constant.

No one-point-extension data, no analytic order at `P` claim, and no
modulus-divergence data — those are local consequences, isolated in the
provider lemmas below.
-/
structure PointRiemannRochSection
    (X : Type*) [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X]
    [JacobianChallenge.Periods.StableChartAt ℂ X]
    (P : X) where
  /-- The section as a complex-valued function. -/
  finiteLift : X → ℂ
  /-- Meromorphic at every point of `X`. -/
  meromorphic_everywhere :
    ∀ p : X,
      JacobianChallenge.HolomorphicForms.VanishingOrder.MeromorphicAtX finiteLift p
  /--
Off the prescribed pole, the literal point values of `finiteLift` agree
  with their removable holomorphic germs, so the finite lift is continuous.
-/
  finiteLift_continuous_off_P :
    ∀ p : X, p ≠ P → ContinuousAt finiteLift p
  /-- Divisor bound at `P`: `orderAt P finiteLift ≥ -1`. -/
  order_ge_neg_one_at_P :
    ((-1 : ℤ) : WithTop ℤ) ≤
      JacobianChallenge.HolomorphicForms.VanishingOrder.orderAt P finiteLift
  /-- No poles off `P`: `orderAt p finiteLift ≥ 0` for `p ≠ P`. -/
  noPoleOff_P :
    ∀ p : X, p ≠ P →
      (0 : WithTop ℤ) ≤
        JacobianChallenge.HolomorphicForms.VanishingOrder.orderAt p finiteLift
  /--
The germ of `finiteLift` at `P` is not constant on a punctured
  neighborhood. Equivalent (for meromorphic functions) to "the order at
  `P` is not `0` or `⊤`", i.e. there is a real singularity or zero at
  `P`. The weakest condition that is still satisfied by an element of
  `L(P)` with a true simple pole at `P` and ruled out by a literal
  constant.
-/
  outside_constants :
    ¬ ∃ c : ℂ, ∀ᶠ z in 𝓝[≠] P, finiteLift z = c

/-!
### Local analytic providers

The four lemmas below isolate the *purely local* facts about a
meromorphic function with prescribed chart-local order at one pole.
They feed the conversion `PointRiemannRochSection.toRiemannRochSectionAtPoint`.
-/

/--
**Provider (removable no-poles representative).** A meromorphic
complex-valued function whose chart-local order is nonnegative at every
point has a global holomorphic representative with the same punctured
germ at every point.

This is the local removable-singularity step in chart-holomorphic form:
it supplies a continuous representative with analytic chart-local
germs, but does not yet package the result as manifold-level
`ContMDiff`.
-/
theorem meromorphic_no_poles_holomorphic_representative
    {X : Type*} [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X]
    [JacobianChallenge.Periods.StableChartAt ℂ X]
    (F : X → ℂ)
    (hmer : ∀ p : X,
      JacobianChallenge.HolomorphicForms.VanishingOrder.MeromorphicAtX F p)
    (horders : ∀ p : X,
      (0 : WithTop ℤ) ≤
        JacobianChallenge.HolomorphicForms.VanishingOrder.orderAt p F) :
    ∃ G : X → ℂ,
      Continuous G ∧
      (∀ p : X, JacobianChallenge.HolomorphicForms.IsHolomorphicAt G p) ∧
      ∀ p : X, F =ᶠ[𝓝[≠] p] G := by
  sorry

/--
**Provider (removable no-poles representative, `ContMDiff` form).**
A meromorphic complex-valued function whose chart-local order is
nonnegative at every point has a global complex-smooth representative
with the same punctured germ at every point.

This packages `meromorphic_no_poles_holomorphic_representative` through
the existing chart-holomorphic plus continuity bridge
`ContMDiff.of_isHolomorphic_and_continuous`.
-/
theorem meromorphic_no_poles_contMDiff_representative
    {X : Type*} [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X]
    [JacobianChallenge.Periods.StableChartAt ℂ X]
    (F : X → ℂ)
    (hmer : ∀ p : X,
      JacobianChallenge.HolomorphicForms.VanishingOrder.MeromorphicAtX F p)
    (horders : ∀ p : X,
      (0 : WithTop ℤ) ≤
        JacobianChallenge.HolomorphicForms.VanishingOrder.orderAt p F) :
    ∃ G : X → ℂ,
      ContMDiff (modelWithCornersSelf ℂ ℂ) (modelWithCornersSelf ℂ ℂ)
        (⊤ : WithTop ℕ∞) G ∧
      ∀ p : X, F =ᶠ[𝓝[≠] p] G := by
  obtain ⟨G, hG_cont, hG_holo, hFG⟩ :=
    meromorphic_no_poles_holomorphic_representative F hmer horders
  exact ⟨G, ContMDiff.of_isHolomorphic_and_continuous hG_holo hG_cont, hFG⟩

/--
**Provider (compact Liouville, germ form).** A meromorphic function
on a compact connected charted space with no poles anywhere agrees,
locally on a punctured neighborhood of every point, with a single
global constant.

The conclusion is stated in germ form: the value of `F` at any single
point is not constrained by `MeromorphicAtX F p` (which only constrains
the punctured-neighborhood germ), so the literal global equality
`F = fun _ ↦ c` is in general false. The germ-form conclusion is the
strongest true statement: `F` agrees with some constant `c` on a
punctured neighborhood of every point of `X`.
-/
theorem meromorphic_no_poles_constant
    {X : Type*} [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X]
    [JacobianChallenge.Periods.StableChartAt ℂ X]
    (F : X → ℂ)
    (hmer : ∀ p : X,
      JacobianChallenge.HolomorphicForms.VanishingOrder.MeromorphicAtX F p)
    (horders : ∀ p : X,
      (0 : WithTop ℤ) ≤
        JacobianChallenge.HolomorphicForms.VanishingOrder.orderAt p F) :
    ∃ c : ℂ, ∀ p : X, ∀ᶠ z in 𝓝[≠] p, F z = c := by
  obtain ⟨G, hG_hol, hFG⟩ :=
    meromorphic_no_poles_contMDiff_representative F hmer horders
  obtain ⟨c, hGc⟩ := holomorphic_compact_connected_constant X G hG_hol
  refine ⟨c, ?_⟩
  intro p
  filter_upwards [hFG p] with z hz
  exact hz.trans (hGc z)

/--
**Provider (local Laurent → chart-order one for the extension).**
If `F` has chart-local meromorphic order `-1` at `P`, then the
one-point extension `onePointExtend F P`, read in the inversion chart
on `OnePoint ℂ`, has chart-local analytic order `1` at `P`.

Proof idea: the inversion-chart pullback of `onePointExtend F P` at `P`
is `1 / (F ∘ chart.symm)`, and order `-1` on `F` becomes order `1` on
the reciprocal (the leading Laurent coefficient cancels, leaving a
holomorphic function vanishing to first order).
-/
theorem mapAnalyticOrderAt_onePointExtend_of_order_neg_one
    {X : Type*} [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X]
    [JacobianChallenge.Periods.StableChartAt ℂ X]
    (F : X → ℂ) (P : X)
    (hmer : ∀ p : X,
      JacobianChallenge.HolomorphicForms.VanishingOrder.MeromorphicAtX F p)
    (horder :
      JacobianChallenge.HolomorphicForms.VanishingOrder.orderAt P F =
        ((-1 : ℤ) : WithTop ℤ)) :
    JacobianChallenge.HolomorphicForms.mapAnalyticOrderAt
      (onePointExtend F P) P = 1 := by
  set e := chartAt ℂ P with he_def
  set z₀ : ℂ := e P with hz₀_def
  set f : ℂ → ℂ := F ∘ e.symm with hf_def
  set g : ℂ → ℂ :=
    fun t =>
      JacobianChallenge.HolomorphicForms.chartLocalAt (onePointExtend F P) P t -
        JacobianChallenge.HolomorphicForms.chartLocalAt (onePointExtend F P) P z₀
    with hg_def
  have _hmer_at_P := hmer P
  have hP_source : P ∈ e.source := by
    rw [he_def]
    exact mem_chart_source ℂ P
  have hP_target : z₀ ∈ e.target := by
    rw [hz₀_def]
    exact e.map_source hP_source
  have hOrd_f :
      meromorphicOrderAt f z₀ = ((-1 : ℤ) : WithTop ℤ) := by
    have h1 :
        JacobianChallenge.HolomorphicForms.VanishingOrder.orderAt P F =
          meromorphicOrderAt (F ∘ (chartAt ℂ P).symm) (chartAt ℂ P P) :=
      JacobianChallenge.HolomorphicForms.VanishingOrder.orderAt_eq_chartAt P F
    rw [h1] at horder
    simpa [hf_def, he_def, hz₀_def] using horder
  have hg_center : g z₀ = 0 := by
    simp [hg_def]
  have hchart_center :
      JacobianChallenge.HolomorphicForms.chartLocalAt (onePointExtend F P) P z₀ = 0 := by
    have hsymm : e.symm z₀ = P := by
      rw [hz₀_def]
      exact e.left_inv hP_source
    calc
      JacobianChallenge.HolomorphicForms.chartLocalAt (onePointExtend F P) P z₀ =
          chartAt ℂ (onePointExtend F P P) (onePointExtend F P (e.symm z₀)) := by
            simp [JacobianChallenge.HolomorphicForms.chartLocalAt, Function.comp_def,
              he_def, hz₀_def]
      _ = chartAt ℂ (OnePoint.infty : OnePoint ℂ) (OnePoint.infty : OnePoint ℂ) := by
            rw [hsymm, onePointExtend_at]
      _ = 0 := by
            change inversionChart (OnePoint.infty : OnePoint ℂ) = 0
            rfl
  have hg_eventually_inv :
      g =ᶠ[𝓝[≠] z₀] f⁻¹ := by
    rw [Filter.EventuallyEq, eventually_nhdsWithin_iff]
    filter_upwards [e.open_target.mem_nhds hP_target] with t ht ht_ne
    have ht_ne' : t ≠ z₀ := by
      intro htz
      exact ht_ne (by simp [htz])
    have hsymm_ne : e.symm t ≠ P := by
      intro hsymm
      have ht_eq : e (e.symm t) = t := e.right_inv ht
      have hz_eq : e P = z₀ := hz₀_def
      rw [hsymm, hz_eq] at ht_eq
      exact ht_ne' ht_eq.symm
    have htarget_chart :
        chartAt ℂ (onePointExtend F P P) = inversionChart := by
      rw [onePointExtend_at]
      rfl
    have hlocal_t :
        JacobianChallenge.HolomorphicForms.chartLocalAt (onePointExtend F P) P t =
          (f t)⁻¹ := by
      calc
        JacobianChallenge.HolomorphicForms.chartLocalAt (onePointExtend F P) P t =
            chartAt ℂ (onePointExtend F P P) (onePointExtend F P (e.symm t)) := by
              simp [JacobianChallenge.HolomorphicForms.chartLocalAt, Function.comp_def,
                he_def]
        _ = inversionChart (onePointExtend F P (e.symm t)) := by
              rw [htarget_chart]
        _ = inversionChart (((F (e.symm t) : ℂ) : OnePoint ℂ)) := by
              rw [onePointExtend_off hsymm_ne]
        _ = (f t)⁻¹ := by
              change invFwd (((F (e.symm t) : ℂ) : OnePoint ℂ)) = (f t)⁻¹
              simp [hf_def]
    calc
      g t =
          JacobianChallenge.HolomorphicForms.chartLocalAt (onePointExtend F P) P t -
            JacobianChallenge.HolomorphicForms.chartLocalAt (onePointExtend F P) P z₀ := by
            simp [hg_def]
      _ = (f t)⁻¹ := by
            rw [hlocal_t, hchart_center]
            simp
      _ = (f⁻¹) t := rfl
  have hOrd_g : meromorphicOrderAt g z₀ = ((1 : ℤ) : WithTop ℤ) := by
    calc
      meromorphicOrderAt g z₀ = meromorphicOrderAt (f⁻¹) z₀ :=
        meromorphicOrderAt_congr hg_eventually_inv
      _ = -meromorphicOrderAt f z₀ := meromorphicOrderAt_inv
      _ = ((1 : ℤ) : WithTop ℤ) := by
        rw [hOrd_f]
        norm_num
  have hAnalytic_g : AnalyticAt ℂ g z₀ := by
    have hpos : (0 : WithTop ℤ) < meromorphicOrderAt g z₀ := by
      rw [hOrd_g]
      norm_num
    exact AnalyticAt.of_meromorphicOrderAt_pos hpos hg_center
  have hAnalyticOrder_g : analyticOrderAt g z₀ = (1 : ℕ∞) := by
    have hcompat := hAnalytic_g.meromorphicOrderAt_eq
    rw [hOrd_g] at hcompat
    cases horder_an : analyticOrderAt g z₀ with
    | top =>
        simp [horder_an] at hcompat
    | coe n =>
        have hn : (n : WithTop ℤ) = ((1 : ℤ) : WithTop ℤ) := by
          simpa [horder_an] using hcompat.symm
        have hn_nat : n = 1 := by
          exact_mod_cast (WithTop.coe_inj.mp hn)
        simp [hn_nat]
  unfold JacobianChallenge.HolomorphicForms.mapAnalyticOrderAt
  rw [← hg_def, ← he_def, ← hz₀_def]
  rw [show analyticOrderNatAt g z₀ = 1 by
    rw [analyticOrderNatAt, hAnalyticOrder_g]
    rfl]

/--
**Provider (local Laurent → modulus divergence).** If `F` has
chart-local order `-1` at `P`, then `‖F x‖ → ∞` as `x → P` through
`{P}ᶜ`.

Proof idea: order `-1` gives a chart-local Laurent expansion
`F ∘ chart.symm = c₋₁ · z⁻¹ + holomorphic` with `c₋₁ ≠ 0`. The norm of
this diverges to infinity as `z → 0`, and the chart is a homeomorphism
near `P`, so divergence transfers along `nhdsWithin P {P}ᶜ`.
-/
theorem tendsto_norm_atTop_of_order_neg_one
    {X : Type*} [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X]
    [JacobianChallenge.Periods.StableChartAt ℂ X]
    (F : X → ℂ) (P : X)
    (_hmer : ∀ p : X,
      JacobianChallenge.HolomorphicForms.VanishingOrder.MeromorphicAtX F p)
    (horder :
      JacobianChallenge.HolomorphicForms.VanishingOrder.orderAt P F =
        ((-1 : ℤ) : WithTop ℤ)) :
    Filter.Tendsto (fun x => ‖F x‖) (nhdsWithin P {P}ᶜ) Filter.atTop := by
  set e := chartAt ℂ P with he_def
  -- Step 1: meromorphic order of the chart pullback at `e P` equals `-1 < 0`.
  have hP_source : P ∈ e.source := mem_chart_source ℂ P
  have hP_target : e P ∈ e.target := e.map_source hP_source
  have hOrd_pullback :
      meromorphicOrderAt (F ∘ e.symm) (e P) = ((-1 : ℤ) : WithTop ℤ) := by
    have h1 :
        JacobianChallenge.HolomorphicForms.VanishingOrder.orderAt P F =
          meromorphicOrderAt (F ∘ e.symm) (e P) :=
      JacobianChallenge.HolomorphicForms.VanishingOrder.orderAt_eq_chartAt P F
    rw [h1] at horder
    exact horder
  have hNeg : meromorphicOrderAt (F ∘ e.symm) (e P) < (0 : WithTop ℤ) := by
    rw [hOrd_pullback]
    decide
  -- Step 2: the chart pullback tends to infinity in norm at `e P`.
  have hTendsto_pullback :
      Filter.Tendsto (fun w => ‖(F ∘ e.symm) w‖) (nhdsWithin (e P) {e P}ᶜ)
        Filter.atTop := by
    have h := tendsto_cobounded_of_meromorphicOrderAt_neg
      (f := F ∘ e.symm) (x := e P) hNeg
    rwa [← tendsto_norm_atTop_iff_cobounded] at h
  -- Step 3: `e` sends `nhdsWithin P {P}ᶜ` into `nhdsWithin (e P) {e P}ᶜ`.
  have hChart_tendsto :
      Filter.Tendsto (fun x => e x) (nhdsWithin P {P}ᶜ) (nhdsWithin (e P) {e P}ᶜ) := by
    rw [tendsto_nhdsWithin_iff]
    refine ⟨?_, ?_⟩
    · -- continuity gives `Tendsto e (𝓝 P) (𝓝 (e P))`; restrict to `nhdsWithin`.
      have hcont : Filter.Tendsto e (𝓝 P) (𝓝 (e P)) :=
        (e.continuousAt hP_source).tendsto
      exact hcont.mono_left nhdsWithin_le_nhds
    · -- on a neighborhood of `P` (the chart source), `e x = e P ↔ x = P`.
      have hsrc_nhd : e.source ∈ nhdsWithin P {P}ᶜ :=
        mem_nhdsWithin_of_mem_nhds (e.open_source.mem_nhds hP_source)
      filter_upwards [hsrc_nhd, self_mem_nhdsWithin] with x hx_src hx_ne
      -- hx_ne : x ∈ {P}ᶜ, i.e., x ≠ P; hx_src : x ∈ e.source
      have hxP : x ≠ P := hx_ne
      intro hex
      -- hex : e x = e P; since `e` is injective on its source, `x = P`.
      apply hxP
      have hinj := e.injOn hx_src hP_source hex
      exact hinj
  -- Step 4: compose; use that `(F ∘ e.symm) (e x) = F x` on `e.source`.
  have hComp_tendsto :
      Filter.Tendsto (fun x => ‖(F ∘ e.symm) (e x)‖) (nhdsWithin P {P}ᶜ)
        Filter.atTop :=
    hTendsto_pullback.comp hChart_tendsto
  -- Step 5: rewrite using `e.symm (e x) = x` on the chart source.
  refine hComp_tendsto.congr' ?_
  have hsrc_nhd : e.source ∈ nhdsWithin P {P}ᶜ :=
    mem_nhdsWithin_of_mem_nhds (e.open_source.mem_nhds hP_source)
  filter_upwards [hsrc_nhd] with x hx_src
  show ‖(F ∘ e.symm) (e x)‖ = ‖F x‖
  congr 1
  show F (e.symm (e x)) = F x
  rw [e.left_inv hx_src]

/--
**Provider (local Laurent plus honest off-pole values → continuous extension).**
If `F` is meromorphic everywhere on `X`, has no poles off `P`, is
literally continuous off `P`, and has chart-local order `-1` at `P`,
then the one-point extension `onePointExtend F P` is continuous on `X`.
-/
theorem continuous_onePointExtend_of_meromorphic_order_neg_one
    {X : Type*} [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X]
    [JacobianChallenge.Periods.StableChartAt ℂ X]
    (F : X → ℂ) (P : X)
    (hmer : ∀ p : X,
      JacobianChallenge.HolomorphicForms.VanishingOrder.MeromorphicAtX F p)
    (_hnoPoleOff : ∀ p : X, p ≠ P →
      (0 : WithTop ℤ) ≤
        JacobianChallenge.HolomorphicForms.VanishingOrder.orderAt p F)
    (hcontOff : ∀ p : X, p ≠ P → ContinuousAt F p)
    (horder :
      JacobianChallenge.HolomorphicForms.VanishingOrder.orderAt P F =
        ((-1 : ℤ) : WithTop ℤ)) :
    Continuous (onePointExtend F P) := by
  rw [continuous_iff_continuousAt]
  intro x
  by_cases hxP : x = P
  · rw [hxP]
    have hpunctured :
        Filter.Tendsto (onePointExtend F P) (nhdsWithin P {P}ᶜ)
          (nhds (OnePoint.infty : OnePoint ℂ)) := by
      refine (OnePoint.tendsto_infty_of_modulus_diverges P F
        (tendsto_norm_atTop_of_order_neg_one F P hmer horder)).congr' ?_
      filter_upwards [self_mem_nhdsWithin] with y hy
      exact (onePointExtend_off (F := F) (P := P) hy).symm
    have hdecomp : nhds P = nhdsWithin P {P} ⊔ nhdsWithin P {P}ᶜ :=
      nhds_eq_nhdsWithin_sup_nhdsWithin P (by simp)
    rw [ContinuousAt, onePointExtend_at, hdecomp, Filter.tendsto_sup]
    refine ⟨?_, hpunctured⟩
    rw [nhdsWithin_singleton]
    simpa [onePointExtend_at] using tendsto_pure_nhds (onePointExtend F P) P
  · have hcoe :
        ContinuousAt (fun x : X => ((F x : ℂ) : OnePoint ℂ)) x :=
      OnePoint.continuous_coe.continuousAt.comp (hcontOff x hxP)
    refine hcoe.congr_of_eventuallyEq ?_
    have hne_nhds : {P}ᶜ ∈ 𝓝 x :=
      isClosed_singleton.isOpen_compl.mem_nhds hxP
    filter_upwards [hne_nhds] with y hy
    exact onePointExtend_off (F := F) (P := P) hy

namespace PointRiemannRochSection

variable {X : Type*} [TopologicalSpace X] [T2Space X] [CompactSpace X]
  [ChartedSpace ℂ X]
  [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X]
  [JacobianChallenge.Periods.StableChartAt ℂ X]

/--
Proof: by `order_ge_neg_one_at_P` and `noPoleOff_P`, every chart-local
order is nonnegative except possibly at `P`, where it is at least `-1`.
If the order at `P` were also nonnegative, `meromorphic_no_poles_constant`
would force `finiteLift` to agree with a single constant on a
punctured neighborhood of every point — in particular on a punctured
neighborhood of `P` — contradicting `outside_constants`. Hence the
order at `P` is exactly `-1`.
-/
theorem orderAt_P_eq_neg_one
    [ConnectedSpace X]
    {P : X} (s : PointRiemannRochSection X P) :
    JacobianChallenge.HolomorphicForms.VanishingOrder.orderAt P s.finiteLift =
      ((-1 : ℤ) : WithTop ℤ) := by
  -- Case analysis on whether the order at `P` is `≥ 0`.
  by_cases hP : (0 : WithTop ℤ) ≤
      JacobianChallenge.HolomorphicForms.VanishingOrder.orderAt P s.finiteLift
  · -- All orders are nonneg, so `finiteLift` has a constant germ at `P`
    -- (and everywhere) by compact Liouville.
    exfalso
    have horders : ∀ p : X,
        (0 : WithTop ℤ) ≤
          JacobianChallenge.HolomorphicForms.VanishingOrder.orderAt p s.finiteLift := by
      intro p
      by_cases hpP : p = P
      · subst hpP; exact hP
      · exact s.noPoleOff_P p hpP
    obtain ⟨c, hc⟩ :=
      meromorphic_no_poles_constant s.finiteLift s.meromorphic_everywhere horders
    -- Specialize the global germ-equality at `P`.
    exact s.outside_constants ⟨c, hc P⟩
  · -- Order at `P` is `< 0` and `≥ -1`, so equals `-1`.
    push_neg at hP
    -- `hP : orderAt P s.finiteLift < 0`
    -- Combined with `order_ge_neg_one_at_P : -1 ≤ orderAt P s.finiteLift`,
    -- and the fact that the order is in `WithTop ℤ`.
    have hge : ((-1 : ℤ) : WithTop ℤ) ≤
        JacobianChallenge.HolomorphicForms.VanishingOrder.orderAt P s.finiteLift :=
      s.order_ge_neg_one_at_P
    -- Show `orderAt P s.finiteLift ≤ -1`.
    have hlt : JacobianChallenge.HolomorphicForms.VanishingOrder.orderAt P s.finiteLift
        < (0 : WithTop ℤ) := hP
    -- In `WithTop ℤ`, `x < 0` is equivalent to `x ≤ -1` since `x ≥ -1`.
    -- Conclude antisymmetry.
    apply le_antisymm _ hge
    -- Show `orderAt P s.finiteLift ≤ -1`.
    -- Since `orderAt P s.finiteLift ≥ -1` and `< 0`, and values are integers in `WithTop ℤ`,
    -- the only possibility is `= -1`.
    cases hOrd : JacobianChallenge.HolomorphicForms.VanishingOrder.orderAt P s.finiteLift with
    | top =>
      -- top ≤ -1 is false unless top = -1, contradicting hlt
      simp [hOrd] at hlt
    | coe n =>
      -- n is an integer; from hge, -1 ≤ n; from hlt, n < 0.  So n = -1.
      rw [hOrd] at hge hlt
      have hge' : (-1 : ℤ) ≤ n := by exact_mod_cast hge
      have hlt' : n < (0 : ℤ) := by exact_mod_cast hlt
      interval_cases n
      simp

/--
The three additional fields needed by `RiemannRochSectionAtPoint`
(continuous extension, chart-order one for the extension, and modulus
divergence) are supplied by the three local-Laurent providers above,
each applied with the chart-local order `-1` extracted by
`orderAt_P_eq_neg_one`.
-/
noncomputable def toRiemannRochSectionAtPoint
    [ConnectedSpace X]
    {P : X} (s : PointRiemannRochSection X P) :
    RiemannRochSectionAtPoint X P where
  finiteLift := s.finiteLift
  meromorphic_everywhere := s.meromorphic_everywhere
  noPoleOff_P := s.noPoleOff_P
  orderAt_P_eq_neg_one := s.orderAt_P_eq_neg_one
  continuous_extension :=
    continuous_onePointExtend_of_meromorphic_order_neg_one
      s.finiteLift P s.meromorphic_everywhere s.noPoleOff_P
      s.finiteLift_continuous_off_P s.orderAt_P_eq_neg_one
  orderAt_pole_in_extension :=
    mapAnalyticOrderAt_onePointExtend_of_order_neg_one
      s.finiteLift P s.meromorphic_everywhere s.orderAt_P_eq_neg_one
  modulus_tendsto :=
    tendsto_norm_atTop_of_order_neg_one
      s.finiteLift P s.meromorphic_everywhere s.orderAt_P_eq_neg_one

end PointRiemannRochSection



/--
Intended proof: genus-zero Riemann-Roch gives `dim L(P) = 2`. The
constants embed into `L(P)` with dimension `1`. Choose any element
outside the constants; membership in `L(P)` is exactly the algebraic
divisor bound `(f) ≥ -[P]`.

This is the *exact* RR provider for the genus-zero simple-pole route.
It contains no one-point-extension data, no chart-local analytic order
claim, and no modulus data — only the algebraic content of
"nonconstant element of `L(P)`". The local-analytic consequences are
isolated as separate providers and consumed by
`PointRiemannRochSection.toRiemannRochSectionAtPoint`.
-/
theorem genusZero_pointRRSection_outside_constants_exists
    (X : Type*) [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X]
    [JacobianChallenge.Periods.StableChartAt ℂ X]
    [FiniteDimensionalHolomorphicOneForms ℂ X]
    (P : X) (h : analyticGenus ℂ X = 0) :
    Nonempty (PointRiemannRochSection X P) := by
  sorry


theorem genusZero_fixedPole_rrSection_nonempty
    (X : Type*) [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X]
    [JacobianChallenge.Periods.StableChartAt ℂ X]
    [FiniteDimensionalHolomorphicOneForms ℂ X]
    (P : X) (h : analyticGenus ℂ X = 0) :
    Nonempty (RiemannRochSectionAtPoint X P) := by
  obtain ⟨s⟩ := genusZero_pointRRSection_outside_constants_exists X P h
  exact ⟨s.toRiemannRochSectionAtPoint⟩


theorem genusZero_fixedPole_simplePoleRRSection_nonempty
    (X : Type*) [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X]
    [JacobianChallenge.Periods.StableChartAt ℂ X]
    [FiniteDimensionalHolomorphicOneForms ℂ X]
    (P : X) (h : analyticGenus ℂ X = 0) :
    Nonempty (SimplePoleRRSection X P) := by
  obtain ⟨s⟩ := genusZero_fixedPole_rrSection_nonempty X P h
  exact ⟨s.toSimplePoleRRSection⟩


theorem genusZero_fixedPole_analyticRRWitness_nonempty
    (X : Type*) [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X]
    [JacobianChallenge.Periods.StableChartAt ℂ X]
    [FiniteDimensionalHolomorphicOneForms ℂ X]
    (P : X) (h : analyticGenus ℂ X = 0) :
    Nonempty (GenusZeroFixedPoleAnalyticRRWitness X P) := by
  obtain ⟨s⟩ := genusZero_fixedPole_simplePoleRRSection_nonempty X P h
  exact ⟨s.toGenusZeroFixedPoleAnalyticRRWitness⟩

/--
* a meromorphic-map-to-sphere `f` with `f.poles = Divisor.point P`;
* the per-point chart-local `f.AnalyticData` (meromorphicity of the
  canonical finite lift at every point, global continuity, and
  order-one at the simple pole);
* the modulus-divergence `f.PoleModulusData`.
-/
theorem genusZero_fixedPole_rr_analyticData_nonempty
    (X : Type*) [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X]
    [JacobianChallenge.Periods.StableChartAt ℂ X]
    [FiniteDimensionalHolomorphicOneForms ℂ X]
    (P : X) (h : analyticGenus ℂ X = 0) :
    ∃ f : MeromorphicMapToSphere X,
      f.poles = Divisor.point P ∧ f.AnalyticData ∧ f.PoleModulusData := by
  obtain ⟨w⟩ := genusZero_fixedPole_analyticRRWitness_nonempty X P h
  exact ⟨w.map, w.poleDivisor_eq, w.analyticData, w.poleModulusData⟩


theorem genusZero_fixedPole_complexPrincipalPart_nonempty
    (X : Type*) [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X]
    [JacobianChallenge.Periods.StableChartAt ℂ X]
    [FiniteDimensionalHolomorphicOneForms ℂ X]
    (P : X) (h : analyticGenus ℂ X = 0) :
    ∃ F : X → ℂ, HasComplexSimplePolePrincipalPart F P := by
  obtain ⟨f, hpole, han, hmod⟩ :=
    genusZero_fixedPole_rr_analyticData_nonempty X P h
  exact ⟨fun x => (f.toMap x).getD 0,
    complexPrincipalPart_of_meromorphicMap_analyticData P f hpole han hmod⟩


theorem genusZero_fixedPole_simplePoleToSphereData_nonempty
    (X : Type*) [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X]
    [JacobianChallenge.Periods.StableChartAt ℂ X]
    [FiniteDimensionalHolomorphicOneForms ℂ X]
    (P : X) (h : analyticGenus ℂ X = 0) :
    Nonempty (SimplePoleToSphereData X P) := by
  obtain ⟨F, hF⟩ := genusZero_fixedPole_complexPrincipalPart_nonempty X P h
  exact ⟨SimplePoleToSphereData.of_complexPrincipalPart F P hF⟩


theorem genusZero_fixedPole_analyticRouteData_nonempty
    (X : Type*) [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X]
    [JacobianChallenge.Periods.StableChartAt ℂ X]
    [FiniteDimensionalHolomorphicOneForms ℂ X]
    (P : X) (h : analyticGenus ℂ X = 0) :
    Nonempty (SinglePoleMeromorphicAnalyticData (X := X) P) := by
  obtain ⟨d⟩ := genusZero_fixedPole_simplePoleToSphereData_nonempty X P h
  exact singlePoleAnalyticData_of_simplePoleToSphereData (X := X) P d


theorem genusZero_fixedPole_singlePoleRouteData_nonempty
    (X : Type*) [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X]
    [JacobianChallenge.Periods.StableChartAt ℂ X]
    [FiniteDimensionalHolomorphicOneForms ℂ X]
    (P : X) (h : analyticGenus ℂ X = 0) :
    Nonempty (SinglePoleMeromorphicMapData (X := X) P) := by
  obtain ⟨route⟩ := genusZero_fixedPole_analyticRouteData_nonempty X P h
  have hbranch : route.map.BranchedCoverDataOfPoleDegree :=
    route.map.branchedCoverDataOfPoleDegree_of_simple_pole P
      route.nonconstant route.poleDivisor_eq route.analyticData
  exact ⟨{
    map := route.map
    poleDivisor_eq := route.poleDivisor_eq
    nonconstant := route.nonconstant
    poleModulusData := route.poleModulusData
    analyticData := route.analyticData
    branchedCoverDataOfPoleDegree := hbranch }⟩

/--
**Fixed-pole route-data assembly wrapper.**

This is the entry point used by `GenusZeroClassification.lean`.
-/
theorem genusZero_fixedPole_meromorphicData_with_routeData_nonempty
    (X : Type*) [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X]
    [JacobianChallenge.Periods.StableChartAt ℂ X]
    [FiniteDimensionalHolomorphicOneForms ℂ X]
    (P : X) (h : analyticGenus ℂ X = 0) :
    Nonempty
      { data : GenusZeroFixedPoleMeromorphicData X P h //
        data.meromorphicMap.PoleModulusData ∧
        data.meromorphicMap.BranchedCoverDataOfPoleDegree } := by
  obtain ⟨route⟩ := genusZero_fixedPole_singlePoleRouteData_nonempty X P h
  let data : GenusZeroFixedPoleMeromorphicData X P h :=
    { meromorphicMap := route.map
      poleDivisor_eq_point := route.poleDivisor_eq }
  exact ⟨⟨data, route.poleModulusData, route.branchedCoverDataOfPoleDegree⟩⟩

end JacobianChallenge.HolomorphicForms
