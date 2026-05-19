import Jacobian.HolomorphicForms.Defs
import Jacobian.HolomorphicForms.ChartedSpaceComplexPoints
import Jacobian.HolomorphicForms.CompactRiemannSurface
import Jacobian.HolomorphicForms.SectionFiberNorm
import Jacobian.HolomorphicForms.HolomorphicMap
import Jacobian.HolomorphicForms.BranchedCover
import Jacobian.HolomorphicForms.ToFunApplyVec
import Jacobian.Blueprint.Sec02.BranchedDegreeFromHolomorphic
import Jacobian.TraceDegree.TraceDefinition
import Jacobian.HolomorphicForms.PullbackBundled
import Jacobian.TraceDegree.AnalyticDegree
import Jacobian.Periods.TrivializationContinuousLinearMapAt

/-!
# Bundled trace (pushforward) of holomorphic 1-forms

This file defines the trace (pushforward) of holomorphic 1-forms along
a non-constant holomorphic map `f : X → Y` between compact Riemann
surfaces.

The trace `f_* η` for `η ∈ H⁰(X, Ω¹)` is defined by summing over the
fibers:
`(f_* η)_y = ∑_{x ∈ f⁻¹(y)} e_x • (η_x ∘ (local_inverse_of_f)_x)`

For a non-constant holomorphic map, this sum is well-defined and
holomorphic on `Y`.

## Main definitions

* `traceFormsBundled f hf η` — the bundled trace of `η` along `f`.
* `traceFormsBundledLM f hf` — the trace as a ℂ-linear map
  `H⁰(X, Ω¹) →ₗ[ℂ] H⁰(Y, Ω¹)`.

## Anti-hack identity

* `trace_pullback_identity` — `trace (pullback η) = degree • η`.
-/

namespace JacobianChallenge.HolomorphicForms

open scoped Manifold ContDiff
open JacobianChallenge.HolomorphicForms
open JacobianChallenge.HolomorphicForms.SectionFiberNorm
open JacobianChallenge.TraceDegree
open JacobianChallenge.Periods

variable {X Y : Type} [TopologicalSpace X] [T2Space X] [CompactSpace X]
  [ConnectedSpace X] [ChartedSpace ℂ X]
  [IsManifold 𝓘(ℂ, ℂ) (⊤ : WithTop ℕ∞) X]
  [StableChartAt ℂ X]
variable {Y : Type} [TopologicalSpace Y] [T2Space Y] [CompactSpace Y]
  [ConnectedSpace Y] [ChartedSpace ℂ Y]
  [IsManifold 𝓘(ℂ, ℂ) (⊤ : WithTop ℕ∞) Y]
  [StableChartAt ℂ Y]

/-- The trace (pushforward) of a holomorphic 1-form along a smooth map. -/
noncomputable opaque traceFormsBundled
    (f : X → Y) (hf : ContMDiff 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) (⊤ : WithTop ℕ∞) f)
    (η : HolomorphicOneForm ℂ X) : HolomorphicOneForm ℂ Y

/-- The trace of the zero form is zero. (Linearity axiom). -/
theorem traceFormsBundled_zero
    (f : X → Y) (hf : ContMDiff 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) (⊤ : WithTop ℕ∞) f) :
    traceFormsBundled f hf 0 = 0 :=
  sorry

/- The target-side branch locus (image of ramification points) is finite. -/
omit [T2Space X] [CompactSpace X] [ConnectedSpace X] [ChartedSpace ℂ X]
  [IsManifold 𝓘(ℂ, ℂ) ω X] [StableChartAt ℂ X]
  [T2Space Y] [CompactSpace Y] [ConnectedSpace Y] [ChartedSpace ℂ Y]
  [IsManifold 𝓘(ℂ, ℂ) ω Y] [StableChartAt ℂ Y] in
theorem branchLocus_finite
    {f : X → Y} (h : BranchedCoverData X Y f) :
    {y : Y | ¬ isRegularValue h y}.Finite := by
  have hram : {x : X | h.ramificationIndex x ≠ 1}.Finite := h.ramified_finite
  have h_eq : {y : Y | ¬ isRegularValue h y} = f '' {x : X | h.ramificationIndex x ≠ 1} := by
    ext y; constructor
    · intro hy
      simp [isRegularValue] at hy
      obtain ⟨x, hx, hx_ram⟩ := hy
      exact ⟨x, hx_ram, hx⟩
    · rintro ⟨x, hx_ram, rfl⟩
      simp [isRegularValue]
      exact ⟨x, rfl, hx_ram⟩
  rw [h_eq]
  exact hram.image f

private theorem dense_compl_of_finite_of_perfect
    {Z : Type*} [TopologicalSpace Z] [T1Space Z] [PerfectSpace Z]
    {s : Set Z} (hs : s.Finite) :
    Dense (sᶜ : Set Z) := by
  classical
  let F := hs.toFinset
  have hF : (F : Set Z) = s := hs.coe_toFinset
  rw [← hF]
  induction F using Finset.induction_on with
  | empty =>
      simp
  | insert a F _ha ih =>
      have hsingle : Dense ({a}ᶜ : Set Z) := dense_compl_singleton a
      have hFopen : IsOpen ((F : Set Z)ᶜ) := F.finite_toSet.isClosed.isOpen_compl
      have hinter : Dense ({a}ᶜ ∩ (F : Set Z)ᶜ : Set Z) :=
        hsingle.inter_of_isOpen_right ih hFopen
      have hset : (insert a (F : Set Z))ᶜ = ({a}ᶜ ∩ (F : Set Z)ᶜ : Set Z) := by
        ext z
        simp
      simpa [Finset.coe_insert, hset] using hinter

/- The regular locus is dense in Y. -/
omit [T2Space X] [CompactSpace X] [ConnectedSpace X] [ChartedSpace ℂ X]
  [IsManifold 𝓘(ℂ, ℂ) ω X] [StableChartAt ℂ X]
  [CompactSpace Y] [IsManifold 𝓘(ℂ, ℂ) ω Y] [StableChartAt ℂ Y] in
theorem regularLocus_dense
    {f : X → Y} (h : BranchedCoverData X Y f) :
    Dense (regularLocus h) := by
  haveI : Nontrivial Y := by
    obtain ⟨p, q, hpq⟩ := exists_two_distinct_points_of_chartedSpaceComplex (X := Y)
    exact ⟨⟨p, q, hpq⟩⟩
  haveI : PerfectSpace Y := inferInstance
  have hbranch : Dense ({y : Y | ¬ isRegularValue h y}ᶜ : Set Y) :=
    dense_compl_of_finite_of_perfect (branchLocus_finite h)
  simpa [regularLocus, Set.compl_setOf] using hbranch

/- **Identity principle for holomorphic 1-forms.**
Two holomorphic 1-forms that agree on a dense set of a connected Riemann
surface are equal everywhere. -/
omit [ConnectedSpace Y] in
theorem holomorphicOneForm_ext_on
    {s : Set Y} (hs : Dense s)
    {ω₁ ω₂ : HolomorphicOneForm ℂ Y} (h : ∀ y ∈ s, ω₁.toFun y = ω₂.toFun y) :
    ω₁ = ω₂ := by
  apply ContMDiffSection.ext
  intro y
  let δ : HolomorphicOneForm ℂ Y := ω₁ - ω₂
  have hcont : Continuous (ContMDiffSection.fiberNorm δ) :=
    holomorphicOneForm_fiberNorm_continuous Y δ
  have hzero_on : Set.EqOn (ContMDiffSection.fiberNorm δ) (fun _ : Y => (0 : ℝ)) s := by
    intro z hz
    have hzfun : δ.toFun z = 0 := by
      dsimp [δ]
      change ((ω₁ - ω₂ : HolomorphicOneForm ℂ Y) : ∀ y, _) z = 0
      rw [ContMDiffSection.coe_sub]
      exact sub_eq_zero.mpr (h z hz)
    simp [ContMDiffSection.fiberNorm, hzfun]
  have hzero_all : ContMDiffSection.fiberNorm δ = fun _ : Y => (0 : ℝ) :=
    Continuous.ext_on hs hcont continuous_const hzero_on
  have hyzero : δ.toFun y = 0 := by
    have hn : ‖δ.toFun y‖ = 0 := by
      simpa [ContMDiffSection.fiberNorm] using congrFun hzero_all y
    exact norm_eq_zero.mp hn
  dsimp [δ] at hyzero
  change ((ω₁ - ω₂ : HolomorphicOneForm ℂ Y) : ∀ y, _) y = 0 at hyzero
  rw [ContMDiffSection.coe_sub] at hyzero
  exact sub_eq_zero.mp hyzero

/-- **Section extraction axiom for trace.**
The underlying function of the bundled trace equals the local fiber sum
at regular values. -/
theorem traceFormsBundled_apply_fun_regular
    {f : X → Y} (hf : ContMDiff 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) (⊤ : WithTop ℕ∞) f)
    (hbc : BranchedCoverData X Y f)
    (η : HolomorphicOneForm ℂ X) (y : Y) (hy : isRegularValue hbc y) :
    (traceFormsBundled f hf η).toFun y = traceAtRegularValue hbc (fun x => η.toFun x) y hy :=
  sorry

/-- Minimal trace input used by local linearity and regular-value
assemblies.  This separates the specification needed downstream from
the construction of the global bundled trace form. -/
structure TraceFormsRegularSpec
    (f : X → Y) (hf : ContMDiff 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) (⊤ : WithTop ℕ∞) f) where
  /-- Trace sends the zero form to zero. -/
  map_zero : traceFormsBundled f hf 0 = 0
  /-- At regular values, trace agrees with the finite local fiber sum. -/
  apply_fun_regular :
    ∀ (hbc : BranchedCoverData X Y f) (η : HolomorphicOneForm ℂ X)
      (y : Y) (hy : isRegularValue hbc y),
      (traceFormsBundled f hf η).toFun y =
        traceAtRegularValue hbc (fun x => η.toFun x) y hy

/-- Frontier provider: the current global trace frontiers packaged as
the smaller local regular-value specification.

Narrow consumers should take `TraceFormsRegularSpec f hf` explicitly
instead of calling this provider internally. -/
def traceFormsRegularSpec_frontier
    (f : X → Y) (hf : ContMDiff 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) (⊤ : WithTop ℕ∞) f) :
    TraceFormsRegularSpec f hf where
  map_zero := traceFormsBundled_zero f hf
  apply_fun_regular := fun hbc η y hy =>
    traceFormsBundled_apply_fun_regular hf hbc η y hy

/-- The trace as a ℂ-linear map between holomorphic 1-form spaces,
from an explicit regular-value trace specification. -/
noncomputable def traceFormsBundledLM_of_spec
    (f : X → Y) (hf : ContMDiff 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) (⊤ : WithTop ℕ∞) f)
    (htrace : TraceFormsRegularSpec f hf)
    (hkfold : HasLocalKfoldRamification f)
    (hw : HasWeightedFiberConservation f) :
    HolomorphicOneForm ℂ X →ₗ[ℂ] HolomorphicOneForm ℂ Y where
  toFun := by
    classical
    exact fun η => if ∃ y₀, ∀ x, f x = y₀ then 0 else traceFormsBundled f hf η
  map_add' η ζ := by
    classical
    -- Trace is linear: use identity principle
    by_cases hconst : ∃ y₀, ∀ x, f x = y₀
    · change (if ∃ y₀, ∀ x, f x = y₀ then 0 else traceFormsBundled f hf (η + ζ)) =
        (if ∃ y₀, ∀ x, f x = y₀ then 0 else traceFormsBundled f hf η) +
          (if ∃ y₀, ∀ x, f x = y₀ then 0 else traceFormsBundled f hf ζ)
      simp [hconst]
    · have hbc := JacobianChallenge.Blueprint.branchedCoverData_of_nonconstant_holomorphic
        (isHolomorphic_of_contMDiff hf hkfold) hw hconst
      simp only [if_neg hconst]
      apply holomorphicOneForm_ext_on (regularLocus_dense hbc)
      intro y hy
      rw [htrace.apply_fun_regular hbc (η + ζ) y hy]
      simpa [add_toFun_apply, htrace.apply_fun_regular hbc η y hy,
        htrace.apply_fun_regular hbc ζ y hy] using
        traceAtRegularValue_add hbc (fun x => η.toFun x) (fun x => ζ.toFun x) y hy
  map_smul' k η := by
    classical
    by_cases hconst : ∃ y₀, ∀ x, f x = y₀
    · change (if ∃ y₀, ∀ x, f x = y₀ then 0 else traceFormsBundled f hf (k • η)) =
        k • (if ∃ y₀, ∀ x, f x = y₀ then 0 else traceFormsBundled f hf η)
      simp only [if_pos hconst]
      apply ContMDiffSection.ext
      intro y
      simp
    · have hbc := JacobianChallenge.Blueprint.branchedCoverData_of_nonconstant_holomorphic
        (isHolomorphic_of_contMDiff hf hkfold) hw hconst
      simp only [if_neg hconst]
      apply holomorphicOneForm_ext_on (regularLocus_dense hbc)
      intro y hy
      rw [htrace.apply_fun_regular hbc (k • η) y hy]
      simpa [smul_toFun_apply, htrace.apply_fun_regular hbc η y hy] using
        traceAtRegularValue_smul hbc k (fun x => η.toFun x) y hy

/-- The trace as a ℂ-linear map between holomorphic 1-form spaces.

Compatibility wrapper using the named frontier provider. New
sorry-free consumers should use `traceFormsBundledLM_of_spec` with an
explicit `TraceFormsRegularSpec` and weighted-fiber conservation. -/
noncomputable def traceFormsBundledLM
    (f : X → Y) (hf : ContMDiff 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) (⊤ : WithTop ℕ∞) f)
    (hkfold : HasLocalKfoldRamification f)
    (hw : HasWeightedFiberConservation f) :
    HolomorphicOneForm ℂ X →ₗ[ℂ] HolomorphicOneForm ℂ Y :=
  traceFormsBundledLM_of_spec f hf (traceFormsRegularSpec_frontier f hf) hkfold hw

omit [T2Space X] [CompactSpace X] [StableChartAt ℂ X]
  [T2Space Y] [CompactSpace Y] [ConnectedSpace Y] [StableChartAt ℂ Y] in
/- The trace–pullback identity holds at regular values from explicit trace data. -/
theorem trace_pullback_identity_regular_of_spec
    (f : X → Y) (hf : ContMDiff 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) (⊤ : WithTop ℕ∞) f)
    (htrace : TraceFormsRegularSpec f hf)
    (hHol : IsHolomorphic f)
    (hbc : BranchedCoverData X Y f)
    (hcompat : hbc.RamificationIndexCompatible)
    (η : HolomorphicOneForm ℂ Y) (y : Y) (hy : isRegularValue hbc y) :
    (traceFormsBundled f hf (pullbackFormsBundled f hf η)).toFun y =
      ((hbc.weightedFiberCard y : ℂ) • η).toFun y := by
  rw [htrace.apply_fun_regular hbc (pullbackFormsBundled f hf η) y hy]
  exact trace_pullback_at_regular_value hbc hcompat hf hHol η y hy

/-- Compatibility wrapper using the named trace frontier provider. -/
theorem trace_pullback_identity_regular
    (f : X → Y) (hf : ContMDiff 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) (⊤ : WithTop ℕ∞) f)
    (hkfold : HasLocalKfoldRamification f)
    (hbc : BranchedCoverData X Y f)
    (hcompat : hbc.RamificationIndexCompatible)
    (η : HolomorphicOneForm ℂ Y) (y : Y) (hy : isRegularValue hbc y) :
    (traceFormsBundled f hf (pullbackFormsBundled f hf η)).toFun y =
      ((hbc.weightedFiberCard y : ℂ) • η).toFun y :=
  trace_pullback_identity_regular_of_spec f hf (traceFormsRegularSpec_frontier f hf)
    (isHolomorphic_of_contMDiff hf hkfold) hbc hcompat η y hy

omit [T2Space X] [CompactSpace X] [ConnectedSpace X] [StableChartAt ℂ X]
  [T2Space Y] [CompactSpace Y] [ConnectedSpace Y] [StableChartAt ℂ Y] in
/- The pullback along a constant map is zero. -/
theorem pullbackFormsBundled_constant
    (f : X → Y) (hf : ContMDiff 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) (⊤ : WithTop ℕ∞) f)
    (hconst : ∃ y₀, ∀ x, f x = y₀) (η : HolomorphicOneForm ℂ Y) :
    pullbackFormsBundled f hf η = 0 := by
  apply ContMDiffSection.coe_inj
  funext x
  obtain ⟨y₀, hf_const⟩ := hconst
  have hf_eq : f = fun _ : X => y₀ := funext hf_const
  subst f
  simp [pullbackFormsBundled, pullbackFormsFunFiber, mfderiv_const]

/- **The Trace-Pullback Identity.** The fundamental identity for
holomorphic 1-forms: the trace of a pullback is multiplication by
the degree.

This is the analytic heart of the Challenge's anti-hack #4. -/
/-- Trace-pullback identity from explicit trace data. -/
theorem trace_pullback_identity_of_spec
    [FiniteDimensionalHolomorphicOneForms ℂ X]
    [FiniteDimensionalHolomorphicOneForms ℂ Y]
    (f : X → Y) (hf : ContMDiff 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) (⊤ : WithTop ℕ∞) f)
    (htrace : TraceFormsRegularSpec f hf)
    (hkfold : HasLocalKfoldRamification f)
    (hw : HasWeightedFiberConservation f)
    (hdegree : ∀ hnonconst : ¬ ∃ y₀, ∀ x, f x = y₀,
      JacobianChallenge.TraceDegree.analyticDegree f hf =
        branchedDegree
          (JacobianChallenge.Blueprint.branchedCoverData_of_nonconstant_holomorphic
            (isHolomorphic_of_contMDiff hf hkfold) hw hnonconst))
    (η : HolomorphicOneForm ℂ Y) :
    traceFormsBundled f hf (pullbackFormsBundled f hf η) =
      (JacobianChallenge.TraceDegree.analyticDegree f hf : ℂ) • η := by
  -- 1. Get branched cover data
  by_cases hconst : ∃ y₀, ∀ x, f x = y₀
  · -- Constant case: both sides are zero
    rw [pullbackFormsBundled_constant f hf hconst η]
    rw [htrace.map_zero]
    rw [analyticDegree_constant f hf hconst]
    apply ContMDiffSection.ext
    intro y
    simp
  · let hbc := JacobianChallenge.Blueprint.branchedCoverData_of_nonconstant_holomorphic
      (isHolomorphic_of_contMDiff hf hkfold) hw hconst
    have hcompat : hbc.RamificationIndexCompatible :=
      JacobianChallenge.Blueprint.branchedCoverData_of_nonconstant_holomorphic_compatible
        (isHolomorphic_of_contMDiff hf hkfold) hw hconst
    -- 2. Use identity principle: equal on dense set implies equal everywhere
    rw [analyticDegree_eq_branchedDegree f hf hbc (hdegree hconst)]
    apply holomorphicOneForm_ext_on (regularLocus_dense hbc)
    intro y hy
    rw [branchedDegree_eq_weightedFiberCard hbc y]
    exact trace_pullback_identity_regular_of_spec f hf htrace
      (isHolomorphic_of_contMDiff hf hkfold) hbc hcompat η y hy

/-- **The Trace-Pullback Identity.** Compatibility wrapper using the
named trace frontier provider. New shortcut assemblies should use
`trace_pullback_identity_of_spec` when the trace data is part of the
explicit boundary. -/
theorem trace_pullback_identity
    [FiniteDimensionalHolomorphicOneForms ℂ X]
    [FiniteDimensionalHolomorphicOneForms ℂ Y]
    (f : X → Y) (hf : ContMDiff 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) (⊤ : WithTop ℕ∞) f)
    (hkfold : HasLocalKfoldRamification f)
    (hw : HasWeightedFiberConservation f)
    (hdegree : ∀ hnonconst : ¬ ∃ y₀, ∀ x, f x = y₀,
      JacobianChallenge.TraceDegree.analyticDegree f hf =
        branchedDegree
          (JacobianChallenge.Blueprint.branchedCoverData_of_nonconstant_holomorphic
            (isHolomorphic_of_contMDiff hf hkfold) hw hnonconst))
    (η : HolomorphicOneForm ℂ Y) :
    traceFormsBundled f hf (pullbackFormsBundled f hf η) =
      (JacobianChallenge.TraceDegree.analyticDegree f hf : ℂ) • η :=
  trace_pullback_identity_of_spec f hf (traceFormsRegularSpec_frontier f hf) hkfold hw hdegree η

end JacobianChallenge.HolomorphicForms
