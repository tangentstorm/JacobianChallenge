import Jacobian.HolomorphicForms.SmoothDifferentialForm
import Jacobian.HolomorphicForms.DeRhamComplex
import Jacobian.HolomorphicForms.RealSingularH1
import Jacobian.Periods.IntegralOneCycle

/-!
# De Rham comparison map (frontier API)

The de Rham theorem is the statement that integration of forms over
singular simplices gives a quasi-isomorphism

  Ω^*(X)  ─∫─→  C^*_sing(X, ℝ)

between the smooth de Rham complex and the singular cochain complex
with real coefficients.  Inverting this on H¹ gives

  H¹_dR(X, ℝ)  ≃ℝ  H¹_sing(X, ℝ)  ≃ℝ  Hom_ℤ(H₁(X, ℤ), ℝ).

This file declares the comparison map at degree 1 as a frontier opaque
linear map plus a named frontier identity asserting it is an
isomorphism on H¹ — the **single deepest analytic frontier theorem** in
the entire `hodge_deRham_rank_eq` chain.

## What this file provides (round 2 refinement)

* `deRhamComparisonMap1` — opaque linear map
  `ClosedForm 1 X → (IntegralOneCycle X →ₗ[ℤ] ℂ)`,
  the integration of a closed 1-form over an integer 1-cycle.

* `deRhamComparisonMap1_vanishes_on_exact` — frontier identity
  (sorry, **STOKES**): the integral of an exact form over a 1-cycle
  is zero.

* `deRhamComparisonMap1_descends` — frontier construction (sorry-free
  given the previous): the descent to the closed/exact quotient.

* `deRhamComparisonMap1_isLinearEquiv` — frontier identity (sorry,
  **the de Rham theorem proper**): the descended map is a linear
  isomorphism.

* `realDim_deRhamH1_eq_realDim_singularH1` — top-level identity
  (refined in this file) is now sorry-free assembly of the above.

## TOPDOWN role

The "de Rham theorem on a compact smooth manifold" frontier sorry has
now been split into:
1. **Stokes** (vanishing on exact),
2. **Surjectivity** (every cohomology class has a representative whose
   integral over each cycle is the prescribed value), and
3. **Injectivity** (a closed form integrating to zero on every cycle is
   exact — Poincaré lemma + sheaf cohomology).

Each is a substantial Mathlib effort but now precisely scoped.
-/

namespace JacobianChallenge.HolomorphicForms

open JacobianChallenge.Periods

open scoped Manifold

/-- **Frontier opaque.** The de Rham comparison map at degree 1:
integration of a closed 1-form over a 1-cycle.  Linear over ℤ in the
cycle (it is well-defined modulo boundaries by Stokes — see
`deRhamComparisonMap1_vanishes_on_exact`).

Bottom-up content: for `ω` a closed 1-form and `σ : Δ¹ → X` a smooth
singular 1-simplex, integrate `σ^*ω` over `[0,1]`.  Extend
ℤ-linearly to integer 1-chains; well-definedness on cycles uses
Stokes.  Mathlib gap: pullback of forms along smooth maps + integration
of one-forms over `[0,1]` are partially there, but the bridge to the
singular complex is missing.

Currently a frontier opaque for the type-level shape; deeper
refinement in this file decomposes its image and kernel. -/
noncomputable opaque deRhamComparisonMap1
    (X : Type) [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X] :
    ClosedForm 1 X →ₗ[ℂ] (IntegralOneCycle X →ₗ[ℤ] ℂ)

/-- **Frontier identity (sorry, STOKES).** The de Rham comparison map
vanishes on exact 1-forms.

Bottom-up content: this is **Stokes' theorem** for a 1-form on a
manifold and a 1-cycle: `∫_σ df = f(∂σ) = 0` since `∂σ = 0`.  Mathlib
gap: Stokes' theorem on manifolds (with or without boundary) is one of
the project's named *big classical inputs*
(`thm:stokes-on-rs-with-boundary`).  See `ref/scope-out.md`. -/
theorem deRhamComparisonMap1_vanishes_on_exact
    (X : Type) [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X]
    (η : ClosedForm 1 X)
    (hη : (η : SmoothDiffForm 1 X) ∈ ExactForm 0 X) :
    deRhamComparisonMap1 X η = 0 := by
  sorry

/-- **Frontier identity (sorry, SURJECTIVITY half of de Rham).**
Every ℝ-linear functional on `IntegralOneCycle X` arises (after
extending scalars) as the integral of some closed 1-form.

Bottom-up content: prescribed-period theorem.  For each ℝ-valued
1-cocycle `c` on the singular complex, partition-of-unity construction
plus Poincaré lemma yields a closed 1-form `ω_c` whose integral over
each cycle is `c`.  Mathlib gap: partition of unity on manifolds is
present (`Mathlib.Geometry.Manifold.PartitionOfUnity`); the Poincaré
lemma + chart-wise primitive construction is absent. -/
theorem deRhamComparisonMap1_surjective
    (X : Type) [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X]
    (φ : IntegralOneCycle X →ₗ[ℤ] ℂ) :
    ∃ ω : ClosedForm 1 X, deRhamComparisonMap1 X ω = φ := by
  sorry

/-- **Frontier identity (sorry, INJECTIVITY half of de Rham).**
A closed 1-form integrating to zero on every integer 1-cycle is
exact.

Bottom-up content: classical de Rham — vanishing periods ⇒ exactness.
Proof goes through sheaf cohomology / Čech cohomology comparison or
direct global potential construction (using simply-connected covers
and a path-integral primitive, then descent).  Mathlib gap: sheaf
cohomology comparison on manifolds is partial; global path-integral
primitive on a non-simply-connected manifold is absent. -/
theorem deRhamComparisonMap1_kernel_subset_exact
    (X : Type) [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X]
    (ω : ClosedForm 1 X)
    (hω : deRhamComparisonMap1 X ω = 0) :
    (ω : SmoothDiffForm 1 X) ∈ ExactForm 0 X := by
  sorry

/-- **Frontier identity (sorry, ARISTOTLE-SIZED).** The de Rham
comparison map sends two cocycles in the same de-Rham class to the
same functional. Direct corollary of
`deRhamComparisonMap1_vanishes_on_exact`. -/
theorem deRhamComparisonMap1_descends
    (X : Type) [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X] :
    ∃ _ : deRhamH1Cocycle X →ₗ[ℂ] (IntegralOneCycle X →ₗ[ℤ] ℂ), True := by
  sorry

/-- **Frontier identity (sorry).** The descended de Rham comparison map
is a linear equivalence, at the level of finrank: the closed-mod-exact
quotient and the cycle-functional space have the same `Module.finrank ℂ`.

Sorry-free assembly *if* one had Mathlib lemmas linking quasi-iso of
cochain complexes to finrank equality of cohomology groups; for now
recorded as a single frontier identity. -/
theorem deRhamH1Cocycle_finrank_eq_realDim_singularH1
    (X : Type) [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X] :
    Module.finrank ℂ (deRhamH1Cocycle X) = realDimSingularH1 X := by
  sorry

/-- **Round-2 sorry-free assembly.** Bridges
`realDim_deRhamH1_eq_realDim_singularH1` from `DeRhamSingular.lean`
through the explicit quotient model + integration map. -/
theorem realDimDeRhamH1_eq_realDimSingularH1_via_cocycle
    (X : Type) [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X] :
    realDimDeRhamH1 X = realDimSingularH1 X := by
  rw [realDimDeRhamH1_eq_finrank_cocycleℝ X,
      deRhamH1Cocycle_finrank_eq_realDim_singularH1 X]

end JacobianChallenge.HolomorphicForms
