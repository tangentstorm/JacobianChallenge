import Jacobian.AbelJacobi.AnalyticOfCurveBasis
import Jacobian.TraceDegree.PushforwardBasis
import Jacobian.TraceDegree.PiecewiseC1Instance
import Jacobian.ComplexTorus.OfClm
import Jacobian.ComplexTorus.MkSmooth
import Jacobian.HolomorphicForms.HolomorphicMap
import Jacobian.Blueprint.Sec02.BranchedDegreeFromHolomorphic

set_option linter.unusedSectionVars false

/-!
# Analytic pullback on the basis-aligned carrier

The basis-aligned analytic Jacobian `BasisAnalyticJacobian X` (defined in
`Jacobian/AbelJacobi/AnalyticOfCurveBasis.lean`) is a complex torus
quotient. A holomorphic map `f : X → Y` of compact Riemann surfaces
induces a pullback `f* : BasisAnalyticJacobian Y → BasisAnalyticJacobian X`
through the dual of the form pullback, descended through the period
quotient.

This module exposes the pullback as a small set of named obligations
that the top-down refinement of `Solution.pullback` (and its
functoriality lemmas) delegates to. Following the project's preference
for *small* named obligations:

* `analyticPullback f hf` — the pullback as a continuous additive
  homomorphism on the basis-aligned carrier (data, `opaque`);
* `analyticPullback_id` — pullback along the identity map is the
  identity (named sorry);
* `analyticPullback_comp` — pullback distributes over composition,
  contravariantly (named sorry);
* `analyticPullback_contMDiff` — the pullback is holomorphic (named
  sorry).

Bottom-up content: each is the descent through periods of the
corresponding identity on `(Fin g_Y → ℂ) →L[ℂ] (Fin g_X → ℂ)` linear
maps (the dual of holomorphic-form pullback in basis coordinates).
-/

namespace JacobianChallenge.TraceDegree

open scoped ContDiff Manifold
open JacobianChallenge.HolomorphicForms JacobianChallenge.Periods
open JacobianChallenge.AbelJacobi
open JacobianChallenge.ComplexTorus
open JacobianChallenge.HolomorphicForms.HolomorphicMap

open Classical

variable {X : Type} [TopologicalSpace X] [T2Space X] [CompactSpace X]
  [ConnectedSpace X] [ChartedSpace ℂ X]
  [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X]
  [StableChartAt ℂ X]
variable {Y : Type} [TopologicalSpace Y] [T2Space Y] [CompactSpace Y]
  [ConnectedSpace Y] [ChartedSpace ℂ Y]
  [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) Y]
  [StableChartAt ℂ Y]
variable {Z : Type} [TopologicalSpace Z] [T2Space Z] [CompactSpace Z]
  [ConnectedSpace Z] [ChartedSpace ℂ Z]
  [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) Z]
  [StableChartAt ℂ Z]

/-- The basis-coordinate form pullback as a `ℂ`-linear map.
Sorry-free: use the `holomorphicTraceCoord` from `PushforwardBasis.lean`. -/
noncomputable def pullbackTraceLiftLinearMap
    (f : X → Y) (hf : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω f) :
    (Fin (analyticGenus ℂ Y) → ℂ) →ₗ[ℂ] (Fin (analyticGenus ℂ X) → ℂ) :=
  holomorphicTraceCoord f hf

/-- The basis-coordinate form pullback as a continuous `ℂ`-linear map.
Upgrade via finite-dimensional auto-continuity. Sorry-free. -/
noncomputable def pullbackTraceLiftCLM
    (f : X → Y) (hf : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω f) :
    (Fin (analyticGenus ℂ Y) → ℂ) →L[ℂ] (Fin (analyticGenus ℂ X) → ℂ) :=
  LinearMap.toContinuousLinearMap (pullbackTraceLiftLinearMap f hf)

/-- **Transfer functional obligation.** For every cycle `σ` on `Y`, the
linear functional on `H⁰(X, Ω¹)` obtained by applying the pullback
trace lift to the period vector of `σ` and pulling back through the
basis-aligned dual equivalence lies in the period subgroup of `X`.

Mathematically, this asserts the existence of a *transfer map* on
cycles: there is a cycle `γ` on `X` such that for every holomorphic
1-form `ω` on `X`,
`∫_γ ω = ∑ⱼ (∫_σ ηⱼ) · (i-th coordinate of f*(ηⱼ))`,
where `ηⱼ` are the chosen basis forms on `Y` and `f*` is the
holomorphic-form pullback.

This is the genuine Mathlib gap: constructing the transfer (wrong-way)
map `f^! : H₁(Y, ℤ) → H₁(X, ℤ)` for a branched cover `f : X → Y`,
and proving the naturality `∫_{f^!(σ)} ω = ∫_σ f_*(ω)` where `f_*`
is the trace on forms. -/
theorem transfer_functional_mem_periodSubgroup
    (f : X → Y) (hf : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω f)
    (σ : IntegralOneCycle Y) :
    (holomorphicOneFormDualEquiv ℂ X).symm
      (pullbackTraceLiftCLM f hf
        (holomorphicOneFormDualEquiv ℂ Y (periodPairing ℂ Y σ)))
    ∈ periodSubgroup ℂ X := by
  sorry

/-- Raw geometric obligation: the form pullback preserves the period
subgroup (in the contravariant direction).

This is the dual of `pushforwardTraceLift_preserves_lattice_raw`.
Mathematically, it relies on the naturality of integration via the
transfer map (pullback on cycles): `∫_{f*σ} η = ∫_σ f_* η`.

The proof decomposes into:
1. Membership witness: `transfer_functional_mem_periodSubgroup`
   (the genuine geometric content — transfer maps for branched covers).
2. Algebraic assembly: the pullback trace lift applied to a period
   vector equals the basis-aligned dual equiv applied to the transfer
   functional. -/
theorem pullbackTraceLift_preserves_lattice_raw
    (f : X → Y) (hf : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω f) :
    ∀ v ∈ (periodFullComplexLattice Y).subgroup,
      pullbackTraceLiftCLM f hf v ∈ (periodFullComplexLattice X).subgroup := by
  intro v hv
  -- Unfold to the concrete representative.
  show pullbackTraceLiftCLM f hf v ∈ basisAlignedPeriodSubgroupConcrete X
  -- Extract the witness functional φ from membership in the Y-side subgroup.
  have hv' : v ∈ basisAlignedPeriodSubgroupConcrete Y := hv
  rw [mem_basisAlignedPeriodSubgroupConcrete_iff] at hv'
  obtain ⟨φ, hφ_mem, hφ_eq⟩ := hv'
  -- φ is in the range of periodPairing; extract a cycle σ.
  change φ ∈ (periodPairing ℂ Y).range at hφ_mem
  rw [AddMonoidHom.mem_range] at hφ_mem
  obtain ⟨σ, hσ⟩ := hφ_mem
  -- Rewrite v in terms of φ and σ.
  rw [← hφ_eq, ← hσ]
  -- Define ψ as the pulled-back functional.
  set ψ := (holomorphicOneFormDualEquiv ℂ X).symm
    (pullbackTraceLiftCLM f hf
      (holomorphicOneFormDualEquiv ℂ Y (periodPairing ℂ Y σ))) with hψ_def
  -- ψ ∈ periodSubgroup ℂ X by the transfer obligation.
  have hψ_mem : ψ ∈ periodSubgroup ℂ X :=
    transfer_functional_mem_periodSubgroup f hf σ
  -- The image of ψ under the dual equiv equals the target vector.
  have hψ_eq : holomorphicOneFormDualEquiv ℂ X ψ =
      pullbackTraceLiftCLM f hf
        (holomorphicOneFormDualEquiv ℂ Y (periodPairing ℂ Y σ)) := by
    rw [hψ_def]
    exact (holomorphicOneFormDualEquiv ℂ X).apply_symm_apply _
  -- Conclude membership.
  rw [← hψ_eq]
  exact holomorphicOneFormDualEquiv_mem_basisAlignedPeriodSubgroupConcrete X hψ_mem

/-- The analytic pullback induced by a holomorphic map of compact
Riemann surfaces, on the basis-aligned carrier.

Concrete (non-opaque) descent of `pullbackTraceLiftCLM` through
the period quotient via `ComplexTorus.mapClm`, using
`pullbackTraceLift_preserves_lattice_raw` for the lattice
preservation hypothesis. The continuity of the descent comes from
`mapClm_continuous`; the smoothness companion
`analyticPullback_contMDiff_raw` remains a (named) sorry —
quotient-of-manifold smoothness is the genuine geometric content. -/
noncomputable def analyticPullback (f : X → Y)
    (hf : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω f) :
    BasisAnalyticJacobian Y →ₜ+ BasisAnalyticJacobian X where
  toFun := mapClm (pullbackTraceLiftCLM f hf) (pullbackTraceLift_preserves_lattice_raw f hf)
  map_zero' := (mapClm _ _).map_zero
  map_add' := (mapClm _ _).map_add
  continuous_toFun := mapClm_continuous (pullbackTraceLiftCLM f hf) (pullbackTraceLift_preserves_lattice_raw f hf)

/-- Raw obligation: the descended map is holomorphic.

Sorry-free: chart-glue smoothness, mirroring the pattern in
`Jacobian/ComplexTorus/AddSmooth.lean`. At any `q`, take the chart
`chart := chartAt _ q`. On `chart.source`, the descent
`analyticPullback = mapClm pullbackTraceLiftCLM` equals
`mk_X ∘ pullbackTraceLiftCLM ∘ chart.toFun`, a composition of
smooth maps:
* `chart.toFun` is `ContMDiffOn` on `chart.source` (`contMDiffOn_chart`);
* `pullbackTraceLiftCLM` is a continuous linear map between
  finite-dim spaces, hence `ContMDiff` (`ContinuousLinearMap.contMDiff`);
* `mk X _` is `ContMDiff` (`contMDiff_mk`).

The equation on `chart.source` uses `chart.left_inv'` plus
`mapClm`'s definition (`map_mk`). -/
theorem analyticPullback_contMDiff_raw
    (f : X → Y) (hf : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω f) :
    ContMDiff (modelWithCornersSelf ℂ (Fin (analyticGenus ℂ Y) → ℂ))
      (modelWithCornersSelf ℂ (Fin (analyticGenus ℂ X) → ℂ)) ω
      (analyticPullback f hf) := by
  intro q
  set chartY :=
    chartAt (Fin (analyticGenus ℂ Y) → ℂ) q with chartY_def
  have hsrc : q ∈ chartY.source := mem_chart_source _ q
  have hOpen : IsOpen chartY.source := chartY.open_source
  have hMem : chartY.source ∈ nhds q := hOpen.mem_nhds hsrc
  -- chart.toFun is ContMDiffOn on chart.source.
  have hChart :
      ContMDiffOn (modelWithCornersSelf ℂ (Fin (analyticGenus ℂ Y) → ℂ))
        (modelWithCornersSelf ℂ (Fin (analyticGenus ℂ Y) → ℂ))
        (⊤ : WithTop ℕ∞) chartY chartY.source :=
    contMDiffOn_chart
  -- pullbackTraceLiftCLM is ContMDiff (continuous linear map).
  have hCLM :
      ContMDiff (modelWithCornersSelf ℂ (Fin (analyticGenus ℂ Y) → ℂ))
        (modelWithCornersSelf ℂ (Fin (analyticGenus ℂ X) → ℂ))
        (⊤ : WithTop ℕ∞)
        (pullbackTraceLiftCLM f hf) :=
    (pullbackTraceLiftCLM f hf).contMDiff
  -- mk X is ContMDiff.
  have hMk :
      ContMDiff (modelWithCornersSelf ℂ (Fin (analyticGenus ℂ X) → ℂ))
        (modelWithCornersSelf ℂ (Fin (analyticGenus ℂ X) → ℂ))
        (⊤ : WithTop ℕ∞)
        (ComplexTorus.mk (Fin (analyticGenus ℂ X) → ℂ)
          (periodFullComplexLattice X)) :=
    ComplexTorus.contMDiff_mk (periodFullComplexLattice X)
  -- Compose to get the auxiliary smooth function on chart.source.
  have hComp :
      ContMDiffOn (modelWithCornersSelf ℂ (Fin (analyticGenus ℂ Y) → ℂ))
        (modelWithCornersSelf ℂ (Fin (analyticGenus ℂ X) → ℂ))
        (⊤ : WithTop ℕ∞)
        (fun q' => ComplexTorus.mk _ (periodFullComplexLattice X)
          (pullbackTraceLiftCLM f hf (chartY q')))
        chartY.source :=
    (hMk.comp hCLM).comp_contMDiffOn hChart
  -- On chart.source, analyticPullback equals the auxiliary.
  have hEq : ∀ q' ∈ chartY.source,
      analyticPullback f hf q' =
        ComplexTorus.mk _ (periodFullComplexLattice X)
          (pullbackTraceLiftCLM f hf (chartY q')) := by
    intro q' hq'
    have hLeft : ComplexTorus.mk _ (periodFullComplexLattice Y)
        (chartY q') = q' := chartY.left_inv' hq'
    -- Rewrite q' on the LHS as mk (chartY q'), then invoke
    -- descent compatibility.
    conv_lhs => rw [← hLeft]
    -- analyticPullback (mk v) = mk (pullbackTraceLiftCLM v)
    rfl
  -- ContMDiffOn on chart.source → ContMDiffAt at q.
  have hOn :
      ContMDiffOn (modelWithCornersSelf ℂ (Fin (analyticGenus ℂ Y) → ℂ))
        (modelWithCornersSelf ℂ (Fin (analyticGenus ℂ X) → ℂ))
        (⊤ : WithTop ℕ∞)
        (analyticPullback f hf) chartY.source := by
    refine hComp.congr ?_
    intro q' hq'
    exact hEq q' hq'
  exact hOn.contMDiffAt hMem

/-- Bundle carrying the analytic pullback together with its
covering-space representative `basisDualPullback` and the descent
compatibility axiom `mk_eq`.

The `analyticPullback` field is the bundled `→ₜ+` hom on the
basis-aligned carrier; the `basisDualPullback` field is the additive
hom on the covering space; `mk_eq` is the defining property linking
the two: `analyticPullback (mk v) = mk (basisDualPullback v)`.

Bottom-up: concretising `basisDualPullback` requires the dual of the
basis-aligned form-pullback; `analyticPullback` is then its descent
through the period quotient (using period-preservation), and `mk_eq`
is automatic from the descent. -/
structure BasisAnalyticPullbackBundle
    (X : Type) [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X]
    [StableChartAt ℂ X]
    (Y : Type) [TopologicalSpace Y] [T2Space Y] [CompactSpace Y]
    [ConnectedSpace Y] [ChartedSpace ℂ Y]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) Y]
    [StableChartAt ℂ Y]
    (_f : X → Y) (_hf : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω _f) where
  /-- The pullback as a continuous additive group homomorphism on the
  basis-aligned carrier. -/
  analyticPullback : BasisAnalyticJacobian Y →ₜ+ BasisAnalyticJacobian X
  /-- The dual form-pullback on the covering space. -/
  basisDualPullback : (Fin (analyticGenus ℂ Y) → ℂ) →+ (Fin (analyticGenus ℂ X) → ℂ)
  /-- Descent compatibility: the bundled pullback acts on the period
  quotient as the descended dual form-pullback. -/
  mk_eq : ∀ v : Fin (analyticGenus ℂ Y) → ℂ,
    analyticPullback (QuotientAddGroup.mk v) =
      QuotientAddGroup.mk (basisDualPullback v)
  /-- The bundled pullback is smooth as a manifold map. -/
  contMDiff_pull :
    ContMDiff (modelWithCornersSelf ℂ (Fin (analyticGenus ℂ Y) → ℂ))
      (modelWithCornersSelf ℂ (Fin (analyticGenus ℂ X) → ℂ)) ω analyticPullback
  /-- The (analytic) degree of `f`. Used in the trace-pullback identity
  (anti-hack #4). -/
  degree : ℕ
  /-- Trace-pullback identity (anti-hack #4):
  `pushf (pullback Q) = degree • Q` for every `Q`. -/
  trace_pullback_spec : ∀ Q : BasisAnalyticJacobian Y,
    analyticPushforward _f _hf (analyticPullback Q) = degree • Q

noncomputable instance (f : X → Y) (hf : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω f) :
    Inhabited (BasisAnalyticPullbackBundle X Y f hf) :=
  ⟨{ analyticPullback := 0
     basisDualPullback := 0
     mk_eq := fun _ => rfl
     contMDiff_pull := contMDiff_const
     degree := 0
     trace_pullback_spec := fun Q => by
       -- pull = 0 here, so pull Q = 0, and pushf 0 = 0 = 0 • Q.
       show (analyticPushforward f hf) (0 : BasisAnalyticJacobian X) =
         (0 : ℕ) • Q
       rw [map_zero, zero_smul] }⟩

/-- The bundled analytic pullback (data + descent axiom). Concretely
realized by descent through the period quotient. -/
noncomputable def basisAnalyticPullbackBundle (f : X → Y)
    (hf : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω f) :
    BasisAnalyticPullbackBundle X Y f hf :=
  { analyticPullback := analyticPullback f hf
    basisDualPullback := (pullbackTraceLiftLinearMap f hf).toAddMonoidHom
    mk_eq := fun v => rfl
    contMDiff_pull := analyticPullback_contMDiff_raw f hf
    degree :=
      if h : ∃ y₀, ∀ x, f x = y₀ then 0
      else
        have hf_holo : IsHolomorphic f := isHolomorphic_of_contMDiff hf
        JacobianChallenge.HolomorphicForms.branchedDegree
          (JacobianChallenge.Blueprint.branchedCoverData_of_nonconstant_holomorphic
            hf_holo h)
    trace_pullback_spec := fun _ => sorry }

/-- The analytic pullback is holomorphic.

Sorry-free extraction from `basisAnalyticPullbackBundle.contMDiff_pull`. -/
lemma analyticPullback_contMDiff (f : X → Y) (hf : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω f) :
    ContMDiff (modelWithCornersSelf ℂ (Fin (analyticGenus ℂ Y) → ℂ))
      (modelWithCornersSelf ℂ (Fin (analyticGenus ℂ X) → ℂ)) ω
      (analyticPullback f hf) :=
  (basisAnalyticPullbackBundle f hf).contMDiff_pull

/-! ### Deeper companions for contravariant functoriality

The `analyticPullback` is the descent through the period
quotient of a linear map on the covering space — the dual of the
basis-aligned form-pullback. The two specs below capture that
relationship:

* `basisDualPullback` — the additive group homomorphism on the
  covering space;
* `analyticPullback_mk_eq` — descent compatibility (rfl);
* `basisDualPullback_comp` — form-pullback contravariance (rfl).
-/

/-- The dual of the basis-aligned form-pullback, as an additive group
homomorphism on the covering space
`Fin (analyticGenus ℂ Y) → ℂ → Fin (analyticGenus ℂ X) → ℂ`.

Extracted from `basisAnalyticPullbackBundle`. -/
noncomputable def basisDualPullback (f : X → Y)
    (hf : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω f) :
    (Fin (analyticGenus ℂ Y) → ℂ) →+ (Fin (analyticGenus ℂ X) → ℂ) :=
  (basisAnalyticPullbackBundle f hf).basisDualPullback

/-! ### Bundle-primitive split (mirrors PushforwardBasis pattern)

The `basisAnalyticPullbackBundle f hf` is now a concrete (non-opaque)
definition built from `pullbackFormsMap`. This resolves the structural
blocker where Lean had no intrinsic propositional relationship between
the dual pullbacks for `f`, `g`, and `g ∘ f`.
-/

/-! ### Round 1 (2026-05-05) — split the HEq diamond sorries

The two diamond sorries
`basisAnalyticPullbackBundle_id_dualPullback` and
`basisAnalyticPullbackBundle_comp_dualPullback` cannot be discharged
without a concrete (non-opaque) realisation of the per-(f, hf)
bundle. We split each into:

* `basisAnalyticPullbackBundle_eq_pullbackFormsMap` — bridge from the
  bundle's `basisDualPullback` field to a *named* covering-space
  dual-pullback function `pullbackFormsMap` (currently both are
  opaque-realised; bridge is itself a sorry);
* `pullbackFormsMap_id` — identity functoriality of the bridge map;
* `pullbackFormsMap_comp` — composition functoriality.

Each is the same Mathlib gap (concrete dual of basis-aligned form
pullback) but stated as a separate, smaller named obligation. -/

/-- **Stage A leaf (round 2, concretised).** Concrete dual of the
basis-aligned form pullback, defined as `holomorphicTraceCoord f hf`
(the basis-coordinate representation of the holomorphic-1-form
pullback `f^* : H⁰(Y, Ω¹) → H⁰(X, Ω¹)`) coerced to a `→+`.

This concretisation collapses both `pullbackFormsMap_id_eq_id` and
`pullbackFormsMap_comp_eq` to sorry-free assemblies, riding on the
sorry-free `holomorphicTraceCoord_id` and `holomorphicTraceCoord_comp`
in `PushforwardBasis.lean`. The `basisAnalyticPullbackBundle_eq_pullbackFormsMap`
bridge remains a (single) sorry because `basisAnalyticPullbackBundle`
itself is still `noncomputable opaque` — concretising the bundle
requires lattice preservation for `holomorphicTraceCoord`, which is
genuinely Mathlib-gap-bound (Stokes naturality on the pullback side,
analogous to the pushforward-side `pushforwardTraceLift_preserves_lattice_raw`). -/
noncomputable def pullbackFormsMap
    (X' Y' : Type) [TopologicalSpace X'] [T2Space X']
    [CompactSpace X'] [ConnectedSpace X'] [ChartedSpace ℂ X']
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X']
    [TopologicalSpace Y'] [T2Space Y'] [CompactSpace Y']
    [ConnectedSpace Y'] [ChartedSpace ℂ Y']
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) Y']
    (f : X' → Y') (hf : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω f) :
    (Fin (analyticGenus ℂ Y') → ℂ) →+ (Fin (analyticGenus ℂ X') → ℂ) :=
  (holomorphicTraceCoord f hf).toAddMonoidHom

/-! #### Pdp-chain decomposition (Round 2, 2026-05-05)

The single sorry on `basisAnalyticPullbackBundle_eq_pullbackFormsMap`
is decomposed via the `pdp-r1 … pdp-r17` chain documented in
`tex/sections/12-classical-analysis-gaps.tex`. Each helper below is
the Lean shadow of a chain step. -/

/-- **Pass pdp.1 (matrix of the basis-aligned form-pullback).** The
basis-aligned form pullback as a `ℂ`-linear map between the chosen-
basis coordinate vector spaces. Not yet realised concretely: depends
on `Module.Basis.equivFun` (pdp.14) applied to chosen bases of
`H⁰(X, Ω¹)` and `H⁰(Y, Ω¹)`. See TeX label `lem:pdp-r1`. -/
noncomputable def basisAlignedFormPullbackMatrix
    (f : X → Y) (hf : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω f) :
    (Fin (analyticGenus ℂ Y) → ℂ) →ₗ[ℂ] (Fin (analyticGenus ℂ X) → ℂ) :=
  holomorphicTraceCoord f hf

/-- **Pass pdp.2 + pdp.3 (transposed matrix is the dual map).**
The dual of the basis-aligned form pullback, viewed as a map of
covering spaces, is the transpose of `basisAlignedFormPullbackMatrix`.
We package this as: `pullbackFormsMap` agrees with the underlying
`AddMonoidHom` of `basisAlignedFormPullbackMatrix`. See TeX label
`lem:pdp-r3`. -/
theorem pullbackFormsMap_eq_matrix_AddHom
    (f : X → Y) (hf : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω f) :
    pullbackFormsMap X Y f hf =
      (basisAlignedFormPullbackMatrix f hf).toAddMonoidHom :=
  rfl


/-- **Pass pdp.4 + pdp.5 + pdp.7 (concrete bundle by descent).** The
concrete `basisAnalyticPullbackBundle f hf` agrees, on its
`basisDualPullback` field, with the underlying `AddMonoidHom` of
`basisAlignedFormPullbackMatrix f hf`. Bottom-up: descent through the
period quotient via `QuotientAddGroup.lift` produces the bundled
pullback, and its `basisDualPullback` field is exactly the matrix of
the basis-aligned form pullback by construction. See TeX labels
`lem:pdp-r4`, `lem:pdp-r5`, `lem:pdp-r7`. -/
theorem basisAnalyticPullbackBundle_dualPullback_eq_matrix_AddHom
    (f : X → Y) (hf : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω f) :
    (basisAnalyticPullbackBundle f hf).basisDualPullback =
      (basisAlignedFormPullbackMatrix f hf).toAddMonoidHom :=
  rfl

/-- **Stage A leaf (round 2, bridge).** The bundle's
`basisDualPullback` agrees with the named `pullbackFormsMap`.

**Round 2 sorry-free assembly via the pdp chain.** Combine the bundle
descent identification (`pdp-r4`,
`basisAnalyticPullbackBundle_dualPullback_eq_matrix_AddHom`) with the
`pullbackFormsMap` matrix identification (`pdp-r3`,
`pullbackFormsMap_eq_matrix_AddHom`). Both sides equal
`(basisAlignedFormPullbackMatrix f hf).toAddMonoidHom`, hence equal each
other. -/
theorem basisAnalyticPullbackBundle_eq_pullbackFormsMap
    (f : X → Y) (hf : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω f) :
    (basisAnalyticPullbackBundle f hf).basisDualPullback =
      pullbackFormsMap X Y f hf := by
  rw [basisAnalyticPullbackBundle_dualPullback_eq_matrix_AddHom f hf,
      pullbackFormsMap_eq_matrix_AddHom f hf]

/-- Identity functoriality of `pullbackFormsMap`: the dual of form-pullback
along `id` is the identity additive group homomorphism on the basis-aligned
covering space. Sorry-free via `holomorphicTraceCoord_id`. -/
theorem pullbackFormsMap_id_eq_id :
    pullbackFormsMap X X id contMDiff_id =
      AddMonoidHom.id (Fin (analyticGenus ℂ X) → ℂ) := by
  unfold pullbackFormsMap
  rw [holomorphicTraceCoord_id]
  rfl

/-- Composition (contravariant) functoriality of `pullbackFormsMap`.
Sorry-free via `holomorphicTraceCoord_comp`. -/
theorem pullbackFormsMap_comp_eq
    (f : X → Y) (hf : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω f)
    (g : Y → Z) (hg : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω g) :
    pullbackFormsMap X Z (g ∘ f) (hg.comp hf) =
      (pullbackFormsMap X Y f hf).comp (pullbackFormsMap Y Z g hg) := by
  unfold pullbackFormsMap
  rw [holomorphicTraceCoord_comp f hf g hg]
  rfl

/-- Bundle-level axiom: the `basisDualPullback` field of the bundle
selected at `(X, X, id, contMDiff_id)` is the identity additive group
homomorphism on the covering space.

**Round 1 sorry-free assembly.** Compose
`basisAnalyticPullbackBundle_eq_pullbackFormsMap` (the bridge sorry)
with `pullbackFormsMap_id_eq_id` (the identity-functoriality sorry). -/
theorem basisAnalyticPullbackBundle_id_dualPullback :
    (basisAnalyticPullbackBundle (X := X) (Y := X) id contMDiff_id).basisDualPullback =
      AddMonoidHom.id (Fin (analyticGenus ℂ X) → ℂ) := by
  rw [basisAnalyticPullbackBundle_eq_pullbackFormsMap (X := X) (Y := X)
      id contMDiff_id,
    pullbackFormsMap_id_eq_id (X := X)]

/-- The dual form-pullback along `id` is the identity additive group
homomorphism. Sorry-free: extracts the bundle-level axiom via `unfold`. -/
theorem basisDualPullback_id :
    basisDualPullback (X := X) (Y := X) id contMDiff_id =
      AddMonoidHom.id (Fin (analyticGenus ℂ X) → ℂ) := by
  unfold basisDualPullback
  exact basisAnalyticPullbackBundle_id_dualPullback

/-- Pointwise form of `basisDualPullback_id`: the dual form-pullback
along `id` is pointwise the identity on the covering space.

Sorry-free assembly via `basisDualPullback_id`. -/
theorem basisDualPullback_id_apply (v : Fin (analyticGenus ℂ X) → ℂ) :
    basisDualPullback (X := X) (Y := X) id contMDiff_id v = v := by
  rw [basisDualPullback_id]
  rfl

/-- Descent compatibility: `analyticPullback` acts on the period
quotient as the descended `basisDualPullback`.

Sorry-free extraction from `basisAnalyticPullbackBundle.mk_eq`. -/
theorem analyticPullback_mk_eq
    (f : X → Y) (hf : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω f)
    (v : Fin (analyticGenus ℂ Y) → ℂ) :
    analyticPullback f hf (QuotientAddGroup.mk v) =
      QuotientAddGroup.mk (basisDualPullback f hf v) :=
  (basisAnalyticPullbackBundle f hf).mk_eq v

/--
Contravariant functoriality of the dual form-pullback on the
covering space: `basisDualPullback (g ∘ f) = basisDualPullback f ∘ basisDualPullback g`.

Bottom-up content: the dual of form-pullback reverses composition.
This is the lifting of `pullbackFormsFun_comp_apply` to the
basis-aligned linear maps, then dualization.

### Blocker analysis (integrated from Aristotle ad278fcd)

**Goal.** Show that the covering-space dual pullback for `g ∘ f`
equals the composition of dual pullbacks for `f` and `g`
(contravariantly), at each covering-space vector.

**Root cause: three independent opaques.** The three
`basisDualPullback` values appearing in this equation originate
from three distinct opaque values:
`basisAnalyticPullbackBundle (g ∘ f) (hg.comp hf)`,
`basisAnalyticPullbackBundle f hf`, and
`basisAnalyticPullbackBundle g hg`. Each `opaque` is selected
independently by `Classical.choice` from the `Inhabited` witness
(which uses `basisDualPullback := 0`), so Lean has no propositional
relationship between the three covering-space lifts.

**Why `mk_eq` is insufficient.** The `mk_eq` field of
`BasisAnalyticPullbackBundle` only gives quotient-level descent
compatibility, yielding congruence modulo the period lattice — not
the exact covering-space equality required.

**Why a composition bundle does not resolve it.** Same cross-instance
opacity issue as `pushforwardTraceLift_comp_spec_apply_at`: a comp
bundle cannot constrain the per-`(f, hf)` opaques, since
`basisDualPullback f hf` is defined directly from
`basisAnalyticPullbackBundle f hf`.

**Mathlib API required to land this:** concrete pullback of
holomorphic 1-forms `f* : H⁰(Y, Ω¹) → H⁰(X, Ω¹)`, contravariant
functoriality `(g ∘ f)* = f* ∘ g*`, basis-coordinate matrix
representation. All absent in v4.28.0.

**Structural change required:** replace the per-`(f, hf)` opaque
bundle with a concrete (non-opaque) definition built from
`pullbackFormsMap`. This is the exact dual of the blocker on
`pushforwardTraceLift_comp_spec_apply_at`.

#### Bundle-primitive split (mirrors PushforwardBasis pattern)

The composition obligation is now isolated as a single
`AddMonoidHom`-equality at the bundle field level
(`basisAnalyticPullbackBundle_comp_dualPullback` below), with the
top-level `basisDualPullback_comp_top` and the per-vector
`basisDualPullback_comp` as sorry-free assemblies. This matches the
PushforwardBasis pattern (`basisAnalyticPushforwardBundle_comp_traceLift`
+ `pushforwardTraceLift_comp` + `_comp_spec_apply_at`). -/
theorem basisAnalyticPullbackBundle_comp_dualPullback
    (f : X → Y) (hf : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω f)
    (g : Y → Z) (hg : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω g) :
    (basisAnalyticPullbackBundle (g ∘ f) (hg.comp hf)).basisDualPullback =
      ((basisAnalyticPullbackBundle f hf).basisDualPullback).comp
        (basisAnalyticPullbackBundle g hg).basisDualPullback := by
  -- Round 1 sorry-free assembly: route through the structural bridge.
  rw [basisAnalyticPullbackBundle_eq_pullbackFormsMap (g ∘ f) (hg.comp hf),
      basisAnalyticPullbackBundle_eq_pullbackFormsMap f hf,
      basisAnalyticPullbackBundle_eq_pullbackFormsMap g hg,
      pullbackFormsMap_comp_eq f hf g hg]

/-- Top-level contravariant functoriality of the dual form-pullback:
`(g ∘ f)* = f* ∘ g*` as an additive group homomorphism on the covering
space. Sorry-free: extracts the bundle-level axiom via `unfold`. -/
theorem basisDualPullback_comp_top
    (f : X → Y) (hf : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω f)
    (g : Y → Z) (hg : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω g) :
    basisDualPullback (g ∘ f) (hg.comp hf) =
      (basisDualPullback f hf).comp (basisDualPullback g hg) := by
  unfold basisDualPullback
  exact basisAnalyticPullbackBundle_comp_dualPullback f hf g hg

/-- Pointwise form: `basisDualPullback (g ∘ f) v = basisDualPullback f
(basisDualPullback g v)`. Sorry-free assembly via
`basisDualPullback_comp_top` + `AddMonoidHom.comp_apply`. -/
theorem basisDualPullback_comp
    (f : X → Y) (hf : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω f)
    (g : Y → Z) (hg : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω g)
    (v : Fin (analyticGenus ℂ Z) → ℂ) :
    basisDualPullback (g ∘ f) (hg.comp hf) v =
      basisDualPullback f hf (basisDualPullback g hg v) := by
  rw [basisDualPullback_comp_top f hf g hg, AddMonoidHom.comp_apply]

/-- Companion spec for `analyticPullback_comp_apply`: pullback of forms is
contravariantly functorial, and descent preserves composition.

**Proof.** Assembly from the deeper companions `analyticPullback_mk_eq`
and `basisDualPullback_comp`. Every element of the quotient is
`⟦v⟧` for some covering-space vector `v`; rewrite both sides using
descent compatibility, then apply the covering-space composition law. -/
theorem analyticPullback_comp_spec
    (f : X → Y) (hf : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω f)
    (g : Y → Z) (hg : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω g)
    (P : BasisAnalyticJacobian Z) :
    analyticPullback (g ∘ f) (hg.comp hf) P =
      analyticPullback f hf (analyticPullback g hg P) := by
  induction P using QuotientAddGroup.induction_on with
  | H v =>
    rw [analyticPullback_mk_eq (g ∘ f) (hg.comp hf) v]
    rw [analyticPullback_mk_eq g hg v]
    rw [analyticPullback_mk_eq f hf (basisDualPullback g hg v)]
    rw [basisDualPullback_comp f hf g hg v]

/-- Pullback distributes contravariantly over composition.

Pure assembly of `analyticPullback_comp_spec`. -/
lemma analyticPullback_comp_apply
    (f : X → Y) (hf : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω f)
    (g : Y → Z) (hg : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω g)
    (P : BasisAnalyticJacobian Z) :
    analyticPullback (g ∘ f) (hg.comp hf) P =
      analyticPullback f hf (analyticPullback g hg P) :=
  analyticPullback_comp_spec f hf g hg P

/-- Companion spec: pullback along the identity map equals the identity
homomorphism (as a `ContinuousAddMonoidHom`).

**Proof.** Assembly from the deeper companions `analyticPullback_mk_eq`
(descent compatibility) and `basisDualPullback_id` (covering-space
identity functoriality). On each `mk v`, rewrite via descent and
identify the dual pullback as the identity. -/
theorem analyticPullback_id_spec :
    analyticPullback (X := X) (Y := X) id contMDiff_id =
      ContinuousAddMonoidHom.id (BasisAnalyticJacobian X) := by
  ext P
  induction P using QuotientAddGroup.induction_on with
  | H v =>
    rw [analyticPullback_mk_eq id contMDiff_id v, basisDualPullback_id]
    rfl

/-- Pullback along the identity is the identity.

Assembly from `analyticPullback_id_spec`. -/
lemma analyticPullback_id_apply (P : BasisAnalyticJacobian X) :
    analyticPullback (X := X) (Y := X) id contMDiff_id P = P := by
  rw [analyticPullback_id_spec]
  rfl

end JacobianChallenge.TraceDegree
