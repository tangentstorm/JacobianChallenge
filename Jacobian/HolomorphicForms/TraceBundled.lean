import Jacobian.HolomorphicForms.Defs
import Jacobian.HolomorphicForms.HolomorphicMap
import Jacobian.HolomorphicForms.BranchedCover
import Jacobian.Blueprint.Sec02.BranchedDegreeFromHolomorphic

/-!
# Bundled trace (pushforward) of holomorphic 1-forms

This file defines the trace (pushforward) of holomorphic 1-forms along
a non-constant holomorphic map `f : X → Y` between compact Riemann
surfaces.

The trace `f_* ω` for `ω ∈ H⁰(X, Ω¹)` is defined by summing over the
fibers:
`(f_* ω)_y = ∑_{x ∈ f⁻¹(y)} e_x • (ω_x ∘ (local_inverse_of_f)_x)`

For a non-constant holomorphic map, this sum is well-defined and
holomorphic on `Y`.

## Main definitions

* `traceFormsBundled f hf ω` — the bundled trace of `ω` along `f`.
* `traceFormsBundledLM f hf` — the trace as a ℂ-linear map
  `H⁰(X, Ω¹) →ₗ[ℂ] H⁰(Y, Ω¹)`.

## Anti-hack identity

* `trace_pullback_identity` — `trace (pullback η) = degree • η`.
-/

namespace JacobianChallenge.HolomorphicForms

open scoped Manifold ContDiff
open JacobianChallenge.HolomorphicForms.HolomorphicMap

variable {X Y : Type*} [TopologicalSpace X] [T2Space X] [CompactSpace X]
  [ConnectedSpace X] [ChartedSpace ℂ X]
  [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X]
variable [TopologicalSpace Y] [T2Space Y] [CompactSpace Y]
  [ConnectedSpace Y] [ChartedSpace ℂ Y]
  [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) Y]

/-- The trace (pushforward) of a holomorphic 1-form along a smooth map.

For now, we keep this as an **opaque** declaration, as the fiber-sum
construction requires significant local analytic machinery (local normal
form, extension across branch locus).

Bottom-up: once `BranchedCoverData` is fully connected to the analytic
order, the trace is constructed as a fiber sum. -/
opaque traceFormsBundled
    (f : X → Y) (hf : ContMDiff 𝓘(ℂ) 𝓘(ℂ) (⊤ : WithTop ℕ∞) f)
    (ω : HolomorphicOneForm ℂ X) : HolomorphicOneForm ℂ Y

/-- The trace as a ℂ-linear map between holomorphic 1-form spaces. -/
noncomputable def traceFormsBundledLM
    (f : X → Y) (hf : ContMDiff 𝓘(ℂ) 𝓘(ℂ) (⊤ : WithTop ℕ∞) f) :
    HolomorphicOneForm ℂ X →ₗ[ℂ] HolomorphicOneForm ℂ Y where
  toFun := traceFormsBundled f hf
  map_add' η ζ := sorry -- Trace is linear
  map_smul' k η := sorry

/-- **The Trace-Pullback Identity.** The fundamental identity for
holomorphic 1-forms: the trace of a pullback is multiplication by
the degree.

This is the analytic heart of the Challenge's anti-hack #4. -/
theorem trace_pullback_identity
    (f : X → Y) (hf : ContMDiff 𝓘(ℂ) 𝓘(ℂ) (⊤ : WithTop ℕ∞) f)
    (η : HolomorphicOneForm ℂ Y) :
    traceFormsBundled f hf (pullbackFormsBundled f hf η) =
      (JacobianChallenge.TraceDegree.analyticDegree f hf : ℂ) • η :=
  sorry

end JacobianChallenge.HolomorphicForms
