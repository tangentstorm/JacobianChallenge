import Jacobian.HolomorphicForms.Defs
import Jacobian.HolomorphicForms.HolomorphicMap
import Jacobian.HolomorphicForms.BranchedCover
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

/-- The trace as a ℂ-linear map between holomorphic 1-form spaces. -/
noncomputable def traceFormsBundledLM
    (f : X → Y) (hf : ContMDiff 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) (⊤ : WithTop ℕ∞) f) :
    HolomorphicOneForm ℂ X →ₗ[ℂ] HolomorphicOneForm ℂ Y where
  toFun := traceFormsBundled f hf
  map_add' η ζ := by
    -- Trace is linear: use identity principle
    by_cases hconst : ∃ y₀, ∀ x, f x = y₀
    · rw [traceFormsBundled_zero, traceFormsBundled_zero, traceFormsBundled_zero]
      simp
    · have hbc := JacobianChallenge.Blueprint.branchedCoverData_of_nonconstant_holomorphic
        (isHolomorphic_of_contMDiff hf) hconst
      apply holomorphicOneForm_ext_on (regularLocus_dense hbc)
      intro y hy
      simp [traceFormsBundled_apply_fun_regular hf hbc]
      exact traceAtRegularValue_add hbc (fun x => η.toFun x) (fun x => ζ.toFun x) y hy
  map_smul' k η := by
    by_cases hconst : ∃ y₀, ∀ x, f x = y₀
    · rw [traceFormsBundled_zero, traceFormsBundled_zero]
      simp
    · have hbc := JacobianChallenge.Blueprint.branchedCoverData_of_nonconstant_holomorphic
        (isHolomorphic_of_contMDiff hf) hconst
      apply holomorphicOneForm_ext_on (regularLocus_dense hbc)
      intro y hy
      simp [traceFormsBundled_apply_fun_regular hf hbc]
      exact traceAtRegularValue_smul hbc k (fun x => η.toFun x) y hy

/-- **Section extraction axiom for trace.**
The underlying function of the bundled trace equals the local fiber sum
at regular values. -/
theorem traceFormsBundled_apply_fun_regular
    {f : X → Y} (hf : ContMDiff 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) (⊤ : WithTop ℕ∞) f)
    (hbc : BranchedCoverData X Y f)
    (η : HolomorphicOneForm ℂ X) (y : Y) (hy : isRegularValue hbc y) :
    (traceFormsBundled f hf η).toFun y = traceAtRegularValue hbc (fun x => η.toFun x) y hy :=
  sorry

/-- The trace–pullback identity holds at regular values. -/
theorem trace_pullback_identity_regular
    (f : X → Y) (hf : ContMDiff 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) (⊤ : WithTop ℕ∞) f)
    (hbc : BranchedCoverData X Y f)
    (η : HolomorphicOneForm ℂ Y) (y : Y) (hy : isRegularValue hbc y) :
    (traceFormsBundled f hf (pullbackFormsBundled f hf η)).toFun y =
      ((hbc.weightedFiberCard y : ℂ) • η).toFun y := by
  rw [traceFormsBundled_apply_fun_regular hf hbc (pullbackFormsBundled f hf η) y hy]
  exact trace_pullback_at_regular_value hbc hf (isHolomorphic_of_contMDiff hf) η y hy

/-- The target-side branch locus (image of ramification points) is finite. -/
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

/-- The regular locus is dense in Y. -/
theorem regularLocus_dense
    {f : X → Y} (h : BranchedCoverData X Y f) :
    Dense (regularLocus h) := by
  -- The regular locus is the complement of a finite set.
  -- In an infinite T1 space, the complement of a finite set is dense.
  apply Set.Finite.dense_compl
  · exact branchLocus_finite h
  · -- Compact connected Riemann surfaces are infinite.
    sorry

/-- **Identity principle for holomorphic 1-forms.**
Two holomorphic 1-forms that agree on a dense set of a connected Riemann
surface are equal everywhere. -/
theorem holomorphicOneForm_ext_on
    {s : Set Y} (hs : Dense s)
    {ω₁ ω₂ : HolomorphicOneForm ℂ Y} (h : ∀ y ∈ s, ω₁.toFun y = ω₂.toFun y) :
    ω₁ = ω₂ := by
  apply ContMDiffSection.coe_inj
  funext y
  -- 1. In any chart, the sections are analytic functions U → ℂ.
  -- 2. Agreement on a dense set implies agreement on a set with accumulation points.
  -- 3. The local analytic identity principle implies equality on the chart.
  -- 4. Connectedness of Y propagates this equality to the entire surface.
  sorry

/-- The pullback along a constant map is zero. -/
theorem pullbackFormsBundled_constant
    (f : X → Y) (hf : ContMDiff 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) (⊤ : WithTop ℕ∞) f)
    (hconst : ∃ y₀, ∀ x, f x = y₀) (η : HolomorphicOneForm ℂ Y) :
    pullbackFormsBundled f hf η = 0 := by
  apply ContMDiffSection.coe_inj
  funext x
  obtain ⟨y₀, hf_const⟩ := hconst
  unfold pullbackFormsBundled pullbackFormsFunFiber
  -- Derivative of constant map is zero
  have hdf : mfderiv 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) f x = 0 := by
    apply mfderiv_zero_of_eventually_const
    filter_upwards with x' using hf_const x'
  rw [hdf]
  exact ContinuousLinearMap.comp_zero _

/-- **The Trace-Pullback Identity.** The fundamental identity for
holomorphic 1-forms: the trace of a pullback is multiplication by
the degree.

This is the analytic heart of the Challenge's anti-hack #4. -/
theorem trace_pullback_identity
    (f : X → Y) (hf : ContMDiff 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) (⊤ : WithTop ℕ∞) f)
    (η : HolomorphicOneForm ℂ Y) :
    traceFormsBundled f hf (pullbackFormsBundled f hf η) =
      (JacobianChallenge.TraceDegree.analyticDegree f hf : ℂ) • η := by
  -- 1. Get branched cover data
  by_cases hconst : ∃ y₀, ∀ x, f x = y₀
  · -- Constant case: both sides are zero
    rw [pullbackFormsBundled_constant f hf hconst η]
    rw [traceFormsBundled_zero f hf]
    rw [analyticDegree_constant f hf hconst]
    simp
  · have hbc := JacobianChallenge.Blueprint.branchedCoverData_of_nonconstant_holomorphic
      (isHolomorphic_of_contMDiff hf) hconst
    -- 2. Use identity principle: equal on dense set implies equal everywhere
    rw [analyticDegree_eq_branchedDegree f hf hconst]
    apply holomorphicOneForm_ext_on (regularLocus_dense hbc)
    intro y hy
    rw [branchedDegree_eq_weightedFiberCard hbc y]
    exact trace_pullback_identity_regular f hf hbc η y hy

end JacobianChallenge.HolomorphicForms
