import Jacobian.HolomorphicForms.TraceSpec
import Jacobian.HolomorphicForms.HolomorphicMap
import Jacobian.Blueprint.Sec02.BranchedDegreeFromHolomorphic
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

/-- Frontier provider: the current global trace frontiers packaged as
the smaller local regular-value specification.

Narrow consumers should take `TraceFormsRegularSpec f hf` explicitly
instead of calling this provider internally. -/
def traceFormsRegularSpec_frontier
    [FiniteDimensionalHolomorphicOneForms ℂ X]
    [FiniteDimensionalHolomorphicOneForms ℂ Y]
    (f : X → Y) (hf : ContMDiff 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) (⊤ : WithTop ℕ∞) f) :
    TraceFormsRegularSpec f hf :=
  (JacobianChallenge.TraceDegree.analyticTraceDegreeSpec_frontier f hf).trace_regular

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
    [FiniteDimensionalHolomorphicOneForms ℂ X]
    [FiniteDimensionalHolomorphicOneForms ℂ Y]
    (f : X → Y) (hf : ContMDiff 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) (⊤ : WithTop ℕ∞) f)
    (hkfold : HasLocalKfoldRamification f)
    (hw : HasWeightedFiberConservation f) :
    HolomorphicOneForm ℂ X →ₗ[ℂ] HolomorphicOneForm ℂ Y :=
  traceFormsBundledLM_of_spec f hf (traceFormsRegularSpec_frontier f hf) hkfold hw

omit [T2Space X] [CompactSpace X] [StableChartAt ℂ X]
  [CompactSpace Y] [StableChartAt ℂ Y] in
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
    [FiniteDimensionalHolomorphicOneForms ℂ X]
    [FiniteDimensionalHolomorphicOneForms ℂ Y]
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
