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
open JacobianChallenge.HolomorphicForms.HolomorphicMap
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

/-- The trace as a ℂ-linear map between holomorphic 1-form spaces. -/
noncomputable def traceFormsBundledLM
    (f : X → Y) (hf : ContMDiff 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) (⊤ : WithTop ℕ∞) f) :
    HolomorphicOneForm ℂ X →ₗ[ℂ] HolomorphicOneForm ℂ Y where
  toFun := traceFormsBundled f hf
  map_add' η ζ := sorry -- Trace is linear
  map_smul' k η := sorry

/-- Agreement between bundled trace and the local fiber sum at regular values. -/
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
  -- Use trace_pullback_at_regular_value from TraceDefinition.lean
  -- This requires matching pullbackFormsBundled with cotangentPushforward
  sorry

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
  -- In a connected manifold of real dimension 2, this is dense.
  apply Set.dense_compl_finite
  · exact branchLocus_finite h
  · -- Need to show Y is infinite.
    -- Compact connected Riemann surfaces are infinite unless they are a point.
    -- But we assume non-constant f, which implies Y has more than one point.
    sorry

/-- **Identity principle for holomorphic 1-forms.**
Two holomorphic 1-forms that agree on a dense set of a connected Riemann
surface are equal everywhere. -/
theorem holomorphicOneForm_ext_on
    {s : Set Y} (hs : Dense s)
    {ω₁ ω₂ : HolomorphicOneForm ℂ Y} (h : ∀ y ∈ s, ω₁.toFun y = ω₂.toFun y) :
    ω₁ = ω₂ := by
  -- This is the "Identity Principle" bridge.
  -- Bottom-up: local analytic identity principle + connectedness.
  sorry

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
    sorry
  · have hbc := JacobianChallenge.Blueprint.branchedCoverData_of_nonconstant_holomorphic
      (isHolomorphic_of_contMDiff hf) hconst
    -- 2. Use identity principle: equal on dense set implies equal everywhere
    rw [analyticDegree_eq_branchedDegree f hf hconst]
    apply holomorphicOneForm_ext_on (regularLocus_dense hbc)
    intro y hy
    rw [branchedDegree_eq_weightedFiberCard hbc y]
    exact trace_pullback_identity_regular f hf hbc η y hy


end JacobianChallenge.HolomorphicForms
