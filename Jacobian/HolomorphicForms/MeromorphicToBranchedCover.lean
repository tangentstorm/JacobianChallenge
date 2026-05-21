import Jacobian.HolomorphicForms.MeromorphicDegree
import Jacobian.HolomorphicForms.MeromorphicToCp1
import Jacobian.HolomorphicForms.OnePointCxIsManifold
import Jacobian.Blueprint.Sec02.BranchedDegreeFromHolomorphic
import Jacobian.Periods.TrivializationContinuousLinearMapAt

/-!
# Bridging `MeromorphicMapToSphere` to branched-cover data

This module bridges a `MeromorphicMapToSphere X` equipped with explicit
`AnalyticData` to the holomorphic-map / branched-cover machinery of
`HolomorphicForms/HolomorphicMap.lean` and
`Blueprint/Sec02/BranchedDegreeFromHolomorphic.lean`.

### Honest interface boundary

A previous iteration of this file declared two generic structural-axiom
sorries claiming that the analytic content "the canonical finite lift is
`MeromorphicAtX`" and "at a simple pole the chart-local order is `1`"
could be derived from `MeromorphicMapToSphere + PoleModulusData`. Neither
is derivable — `PoleModulusData` is a modulus-divergence witness, not an
analytic one, and the structure's `toFiniteFun_mdifferentiable` field is
*vacuous* in the presence of any pole.

The honest abstraction boundary is **`MeromorphicMapToSphere.AnalyticData`**
(defined in `Meromorphic.lean`): a record whose fields are *exactly* the
chart-local Laurent / order content that production constructors of a
`MeromorphicMapToSphere` (Riemann-Roch witness, dipole, etc.) must
supply by construction. With `AnalyticData` in hand, the
`MeromorphicFunctionType` / `liftToCp1_*` infrastructure of
`MeromorphicToCp1.lean` and the analytic constructor
`branchedCoverData_of_nonconstant_holomorphic` of
`Sec02/BranchedDegreeFromHolomorphic.lean` discharge everything else.

The genuine remaining project frontier — the *production Riemann-Roch
analytic route-data theorem* — is now isolated in
`genusZero_fixedPole_analyticRouteData_nonempty` below, which says
"genus-zero Riemann-Roch supplies a fixed-pole meromorphic map together
with the needed `AnalyticData`". That is the precise mathematical content
still missing; it is not an arbitrary-map abstract claim. -/

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
/-- Projection from `AnalyticData`: the canonical finite lift is
`MeromorphicAtX` at every point. -/
theorem MeromorphicMapToSphere.meromorphicAt_getD_of_analyticData
    (f : MeromorphicMapToSphere X) (han : f.AnalyticData) :
    ∀ p : X, JacobianChallenge.HolomorphicForms.VanishingOrder.MeromorphicAtX
      (fun q => (f.toMap q).getD 0) p :=
  han.meromorphic_getD

omit [T2Space X] [CompactSpace X] [ConnectedSpace X]
  [JacobianChallenge.Periods.StableChartAt ℂ X] in
/-- Projection from `AnalyticData`: at a simple pole, the chart-local
analytic order is `1`. -/
theorem MeromorphicMapToSphere.mapAnalyticOrderAt_toMap_eq_one_of_analyticData
    (f : MeromorphicMapToSphere X) (han : f.AnalyticData) (P : X)
    (hpole : f.poles = Divisor.point P) :
    JacobianChallenge.HolomorphicForms.mapAnalyticOrderAt f.toMap P = 1 :=
  han.simple_pole_order_one P hpole

/-! ### Packaging a `MeromorphicMapToSphere` with analytic data as a `MeromorphicFunctionType` -/

omit [T2Space X] [CompactSpace X] [ConnectedSpace X] in
/-- Package a `MeromorphicMapToSphere` plus explicit `AnalyticData` as a
`MeromorphicFunctionType`, so that the `liftToCp1_*` infrastructure of
`MeromorphicToCp1.lean` can be applied to its underlying map.

The packaging is purely structural: the `AnalyticData` fields exactly
match the `MeromorphicFunctionType` fields. -/
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
/-- The underlying map of a `MeromorphicMapToSphere` is `IsHolomorphic`
in the project-local sense, given explicit `AnalyticData`. -/
theorem MeromorphicMapToSphere.isHolomorphic_toMap_of_analyticData
    (f : MeromorphicMapToSphere X) (han : f.AnalyticData) :
    JacobianChallenge.HolomorphicForms.IsHolomorphic f.toMap := by
  have h := liftToCp1_isHolomorphic X (f.toMeromorphicFunctionType han) True.intro
  simpa using h

omit [T2Space X] [CompactSpace X] [ConnectedSpace X] in
/-- Weighted-fiber conservation for `f.toMap`, given explicit
`AnalyticData`. -/
theorem MeromorphicMapToSphere.hasWeightedFiberConservation_toMap_of_analyticData
    (f : MeromorphicMapToSphere X) (han : f.AnalyticData) :
    JacobianChallenge.HolomorphicForms.HasWeightedFiberConservation f.toMap := by
  have h := liftToCp1_hasWeightedFiberConservation X
    (f.toMeromorphicFunctionType han) True.intro
  simpa using h

omit [T2Space X] [CompactSpace X] [ConnectedSpace X]
  [JacobianChallenge.Periods.StableChartAt ℂ X] in
/-- The fiber `f.toMap ⁻¹' {∞}` of a continuous meromorphic map whose
pole divisor is `[P]` is exactly the singleton `{P}`.

Sorry-free: routes through `toMap_eq_infty_of_poleDivisor_pos` (P maps
to ∞) and `toMap_ne_infty_of_poleDivisor_zero` (other points don't). -/
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

/-- **Production: branched-cover data of pole degree (sorry-free).**

Given a `MeromorphicMapToSphere f` on a compact connected complex
1-manifold which is nonconstant, has a simple pole at `P`, and carries
explicit `AnalyticData`, the map `f.toMap` packages as a
`BranchedCoverData X (OnePoint ℂ) f.toMap` whose branched degree is
`f.poleDivisor.degree.toNat = 1`.

The proof is a sorry-free assembly from:

* `isHolomorphic_toMap_of_analyticData` (above; uses the analytic
  adapter projection from `AnalyticData`).
* `hasWeightedFiberConservation_toMap_of_analyticData` (above; same).
* `branchedCoverData_of_nonconstant_holomorphic` (in
  `Sec02/BranchedDegreeFromHolomorphic.lean`).
* `branchedDegree_eq_weightedFiberCard` over `∞` (in
  `BranchedCover.lean`).
* `preimage_infty_eq_singleton_of_poleDivisor_point` (above).
* `AnalyticData.simple_pole_order_one` (projection; supplies the
  simple-pole order-one content). -/
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

/-! ### Concrete simple-pole-to-sphere data and constructor

The production interface for an honest fixed-pole meromorphic-map-to-sphere
is `SimplePoleToSphereData`. Its fields are the local analytic inputs
genuinely needed to construct an honest one-pole map: a concrete
piecewise-defined `toMap`, a global finite lift, continuity of `toMap`
into `OnePoint ℂ`, meromorphicity of the lift, simple-pole order data,
and modulus divergence at the pole.

The constructor `singlePoleAnalyticData_of_simplePoleToSphereData`
turns such a record into a `SinglePoleMeromorphicAnalyticData` — a
sorry-free assembly. The remaining production frontier is then the
single existence theorem
`genusZero_fixedPole_simplePoleToSphereData_nonempty` that says
"genus zero supplies a concrete simple-pole record". -/

/-- **Concrete simple-pole production input.**

This record carries the local analytic content that an honest
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
`if` to avoid pulling in `DecidableEq X` typeclass requirements. -/
structure SimplePoleToSphereData
    (X : Type*) [TopologicalSpace X] [T2Space X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X]
    [JacobianChallenge.Periods.StableChartAt ℂ X]
    (P : X) where
  /-- A global complex-valued lift, defined on all of `X` (the value at
  `P` is arbitrary; only off-`P` values matter for `toMap`). -/
  finiteLift : X → ℂ
  /-- The map to the Riemann sphere. -/
  toMap : X → OnePoint ℂ
  /-- At `P`, `toMap` is `∞`. -/
  toMap_at_pole : toMap P = OnePoint.infty
  /-- Off `P`, `toMap` is the canonical complex coordinate of `finiteLift`. -/
  toMap_off_pole : ∀ x : X, x ≠ P → toMap x = ((finiteLift x : ℂ) : OnePoint ℂ)
  /-- Global continuity of `toMap` into `OnePoint ℂ`. -/
  continuous_toMap : Continuous toMap
  /-- The finite lift is meromorphic at every point of `X` (in the
  manifold sense). -/
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

/-- Canonical one-point extension of `F : Y → ℂ` to `OnePoint ℂ`,
sending `P` to `∞` and any other point `x` to `((F x : ℂ) : OnePoint ℂ)`.

Classical decidability of `x = P` is used so that no `DecidableEq Y`
typeclass is required at the call site. -/
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

/-- **Complex principal-part predicate.**

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
shape of `SimplePoleToSphereData`. -/
structure HasComplexSimplePolePrincipalPart (F : X → ℂ) (P : X) : Prop where
  meromorphic_everywhere :
    ∀ p : X,
      JacobianChallenge.HolomorphicForms.VanishingOrder.MeromorphicAtX F p
  continuous_extension : Continuous (onePointExtend F P)
  orderAt_pole :
    JacobianChallenge.HolomorphicForms.mapAnalyticOrderAt (onePointExtend F P) P = 1
  modulus_tendsto :
    Filter.Tendsto (fun x => ‖F x‖) (nhdsWithin P {P}ᶜ) Filter.atTop

/-- **Sorry-free bridge: `SimplePoleToSphereData` from
`HasComplexSimplePolePrincipalPart`.**

Given a complex function `F` with complex simple-pole principal part
at `P`, package it as a concrete `SimplePoleToSphereData X P` with
`finiteLift := F` and `toMap := onePointExtend F P`. All fields are
filled directly from the predicate fields. -/
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
/-- **Sorry-free constructor: build a `SinglePoleMeromorphicAnalyticData` from
a `SimplePoleToSphereData`.**

Given a concrete simple-pole record `d : SimplePoleToSphereData X P`,
constructs an honest `MeromorphicMapToSphere` whose pole divisor is
`Divisor.point P` together with `PoleModulusData` and
`AnalyticData`. All structure-level fields are discharged from the
record's fields with no sorry.

This is the constructor that replaces the previous broad
"genus-zero gives all analytic data at once" sorry — the analytic
content now comes through this *concrete*, locally-checkable
interface. -/
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

/-! ### Genus-zero fixed-pole route-data assemblies

The remaining sorry has been narrowed to the *smallest* honest
production frontier:
`genusZero_fixedPole_simplePoleToSphereData_nonempty`, which supplies
*only* the concrete simple-pole input data
(`SimplePoleToSphereData`). Branch data is **not** part of this sorry
— it is a proved consequence below, filled sorry-free via
`MeromorphicMapToSphere.branchedCoverDataOfPoleDegree_of_simple_pole`.

This separation matches the goal: the only remaining direct sorry in
this cluster is the honest existence frontier of a real concrete
simple-pole meromorphic map. -/

/-- **Branched-cover-data assembly for the genus-zero fixed-pole route
(sorry-free, takes explicit `AnalyticData`).**

For a given `MeromorphicMapToSphere f` with prescribed simple pole at
`P`, nonconstancy, and **explicit `AnalyticData`**, the
branched-cover-data structure follows from
`branchedCoverDataOfPoleDegree_of_simple_pole`.

This is the per-`f` theorem with honest hypotheses: the analytic
content comes in as `han : f.AnalyticData`, not as the impossible
"derive analyticity from `PoleModulusData`" claim previously held
here.

Note: `_h` (analytic-genus-zero) and `_hmem` (Riemann-Roch membership)
are accepted but unused; they are kept in the signature so callers
that came through the genus-zero pipeline can pass them without
reshaping. The branched-cover content depends only on `(hnc, hpole,
han)`. -/
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

/-- **Production-frontier existence (sorry): a complex function with simple-pole
principal part in genus zero.**

The remaining genuine analytic / Riemann-Roch obligation: in genus zero,
for every prescribed pole point `P`, there exists a complex function
`F : X → ℂ` with simple-pole principal part at `P`. The required
fields (meromorphicity, continuity of the one-point extension,
order-one in the inversion chart, modulus divergence) are *exactly* the
chart-local Laurent / order content a production PDE-dipole construction
or a divisor-Riemann-Roch construction would output.

This is the strictly-smallest mathematically standard frontier in the
genus-zero meromorphic-route cluster: building a real meromorphic
function with the prescribed simple pole. Once such an `F` is in hand,
the full route data follows sorry-free through the bridge below. -/
theorem genusZero_fixedPole_complexPrincipalPart_nonempty
    (X : Type*) [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X]
    [JacobianChallenge.Periods.StableChartAt ℂ X]
    [FiniteDimensionalHolomorphicOneForms ℂ X]
    (P : X) (h : analyticGenus ℂ X = 0) :
    ∃ F : X → ℂ, HasComplexSimplePolePrincipalPart F P := by
  sorry

/-- **Sorry-free existence of `SimplePoleToSphereData` from the
complex-principal-part frontier.**

Discharged by composing the strictly-smaller existence theorem
`genusZero_fixedPole_complexPrincipalPart_nonempty` with the
sorry-free bridge `SimplePoleToSphereData.of_complexPrincipalPart`. -/
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

/-- **Analytic route data, sorry-free assembly.**

Builds `SinglePoleMeromorphicAnalyticData` from the smaller existence
frontier `genusZero_fixedPole_simplePoleToSphereData_nonempty` via the
sorry-free constructor `singlePoleAnalyticData_of_simplePoleToSphereData`.

The sorry has moved entirely to the existence frontier — this theorem
is sorry-free. -/
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

/-- **Full route-data package (sorry-free).**

Builds the full `SinglePoleMeromorphicMapData P` from the smaller
production frontier `genusZero_fixedPole_analyticRouteData_nonempty`
by filling the `branchedCoverDataOfPoleDegree` field via the
sorry-free assembly
`MeromorphicMapToSphere.branchedCoverDataOfPoleDegree_of_simple_pole`.

The sorry has moved entirely to the smaller analytic frontier — this
theorem is sorry-free. -/
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

/-- **Fixed-pole route-data assembly wrapper.**

Sorry-free assembly: unwraps a `SinglePoleMeromorphicMapData P` produced
by the production frontier `genusZero_fixedPole_singlePoleRouteData_nonempty`,
repackages its `map` field as a `GenusZeroFixedPoleMeromorphicData X P h`,
and exposes the bundled `PoleModulusData` and `BranchedCoverDataOfPoleDegree`
as a subtype.

This is the entry point used by `GenusZeroClassification.lean`. -/
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
