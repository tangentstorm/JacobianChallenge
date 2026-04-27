import Jacobian.HolomorphicForms.Defs
import Mathlib.Geometry.Manifold.VectorBundle.SmoothSection
import Mathlib.Topology.ContinuousMap.Compact
import Mathlib.Topology.UniformSpace.UniformConvergenceTopology

/-!
# Reconnaissance: topology on `ContMDiffSection` for the Riemann-Roch route

This is a recon stub for the next-up Mathlib infrastructure piece flagged
by Aristotle's `compactRiemannSurface_finiteDimensionalHolomorphicOneForms`
survey (in `CompactRiemannSurface.lean`):

> Step (a): Define the topology of uniform convergence on compact sets
> for `ContMDiffSection`, and upgrade it to a Banach space structure
> when the base manifold is `CompactSpace`.

This file is **not** part of the public API. Like the existing
`Jacobian/ComplexTorus/{Manifold,ZLattice,Discreteness}Recon.lean` and
`Jacobian/HolomorphicForms/Recon.lean` files, it is name-discovery and
strategy-documentation. It contains no production declarations and is
not re-exported by any umbrella.

The eventual goal is to discharge
`compactRiemannSurface_finiteDimensionalHolomorphicOneForms` via Riesz's
theorem on the function space of holomorphic 1-forms (a.k.a. holomorphic
sections of the cotangent bundle) on a compact connected Riemann surface.

## What Aristotle should fill in

(NOT YET FILLED; this stub is the input to a recon packet.)

1. **What Mathlib v4.28.0 has**: enumerate the existing topology /
   norm / function-space / uniform-convergence machinery in Mathlib
   that is most relevant for `ContMDiffSection`. In particular:
   - `ContinuousMap.Compact` (compact-open topology, Banach structure
     on `C(X, Y)` for compact `X`).
   - `UniformConvergenceOn` / `UniformConvergence` topology
     constructors.
   - `BoundedContinuousFunction` and its NormedSpace instance.
   - Existing topology / norm / Banach instances (or lack thereof) on
     `ContMDiffSection`.
   - Sup-norm / Banach instances on smooth sections of a vector bundle.

2. **What Mathlib v4.28.0 does NOT have** (likely list):
   - A `TopologicalSpace` instance for `ContMDiffSection I F n V`
     (general bundles).
   - A `NormedAddCommGroup` / `NormedSpace` instance for
     `ContMDiffSection` over a compact base.
   - Banach completeness for `ContMDiffSection` over compact base
     manifolds.
   - Cauchy estimates for holomorphic functions on chart balls
     transferred up to sections.

3. **Design plan for filling the gap**:
   - How to define the sup-norm on `ContMDiffSection I F ⊤ V` when
     the base is compact (likely via the underlying `ContinuousMap`
     coercion and `ContinuousMap.normedAddCommGroupSup` or similar).
   - How to upgrade to a Banach space structure (via
     `Metric.completeSpace_of_isClosed` / `IsClosed.completeSpace` —
     find the right Mathlib lemma).
   - Explicit Mathlib lemmas the proof will cite.

4. **Dependency graph**: which Mathlib files / theorems would be
   imported and in what order. Goal: a TODO list a future implementation
   packet can pick up directly.

## Status

`opaque` recon — Aristotle to fill in. Once filled, the resulting
strategy doc should make the topology-on-`ContMDiffSection`
implementation packet (and follow-up Montel + Riesz packets) clear-cut.
-/

namespace JacobianChallenge.HolomorphicForms.SectionTopologyRecon

-- Aristotle to fill in: see file docstring.

end JacobianChallenge.HolomorphicForms.SectionTopologyRecon
