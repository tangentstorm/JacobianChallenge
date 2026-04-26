import Mathlib.Geometry.Manifold.MFDeriv.Basic
import Mathlib.Geometry.Manifold.VectorBundle.SmoothSection
import Mathlib.Geometry.Manifold.VectorBundle.Tangent

/-!
# Reconnaissance: holomorphic 1-forms on a complex manifold

Queue C kickoff. This is a reconnaissance document for the
`HolomorphicOneForm X` definition needed by `Jacobian/Challenge.lean`
through the placeholder `JacobianChallenge.HolomorphicForms.HolomorphicOneForm`
in `StatementBank.lean`.

This file is **not** part of the public API. It is name-discovery and
strategy-documentation, similar in role to the earlier `ComplexTorus/*Recon.lean`
files. It contains no production declarations and is not re-exported
by any umbrella.

## What Mathlib v4.28.0 has

* `TangentBundle I M` — `Geometry/Manifold/VectorBundle/Tangent.lean`.
  The total space; fiber at each point is the model space `E`.
* `TangentSpace I x = E` — by trivialization. `Geometry/Manifold/MFDeriv/Defs.lean`
  uses this to type derivatives.
* `mfderiv I I' f x : TangentSpace I x →L[𝕜] TangentSpace I' (f x)`
  — the manifold derivative as a continuous linear map.
* `MDifferentiable I I' f` and pointwise/within variants.
* `ContMDiff` (the analytic-with-respect-to-the-complex-model version
  is what we have been using throughout `ComplexTorus/`).
* `ContMDiffSection I F n V` (`Geometry/Manifold/VectorBundle/SmoothSection.lean`)
  — bundled `C^n` sections of a vector bundle. `AddCommGroup` and
  `Module` instances available.
* `ContinuousLinearMap.Bundle` machinery — for forming `Bundle.continuousLinearMap`,
  the bundle of continuous linear maps between two vector bundles.

## What Mathlib v4.28.0 does NOT have

* No `CotangentBundle` or `CotangentSpace`. There is a TODO comment in
  `Geometry/Manifold/ContMDiffMFDeriv.lean:230` mentioning this.
* No `MDifferentialForm`, `SmoothOneForm`, `HolomorphicOneForm`.
* No manifold-level exterior derivative.
* No finite-dimensionality of holomorphic global sections on a compact
  manifold (would need Riemann–Roch / Hodge / Serre duality).

## Design choices for `HolomorphicOneForm X`

The challenge needs:
1. A type `HolomorphicOneForm X` with `AddCommGroup` and `Module ℂ`
   structure;
2. `analyticGenus X = Module.finrank ℂ (HolomorphicOneForm X)`;
3. `genus_eq_analyticGenus` and `analyticGenus_eq_zero_iff_homeomorphic_sphere`.

For (1) and (2), we have two viable approaches:

### Approach A: bundle-of-continuous-linear-maps + `ContMDiffSection`

Define the cotangent bundle as
`Bundle.continuousLinearMap ℂ (TangentBundle 𝓘(ℂ, E) X) (Bundle.Trivial X ℂ)`
(or similar), then take `ContMDiffSection` with `n = ⊤`. This is the
"morally correct" definition and inherits `AddCommGroup` / `Module ℂ`
for free from `ContMDiffSection`.

* Pros: aligns with mathlib bundle infrastructure; smoothness handled
  automatically; AddCommGroup/Module follow.
* Cons: building the cotangent bundle from `Bundle.continuousLinearMap`
  is non-trivial. Transition functions on the linear-map bundle are
  by inverse-transpose of the tangent transition, and the analytic
  transformation rule for 1-forms must be threaded through the bundle
  glue.

### Approach B: chart-coherent sections by hand

Define `HolomorphicOneForm X` directly as a structure containing
* a function `ω : Π x : X, TangentSpace 𝓘(ℂ, E) x →L[ℂ] ℂ`,
* an analytic-coherence hypothesis: in each chart, the chart-coordinate
  representation of `ω` (a function `chart.target → E →L[ℂ] ℂ`) is
  `ContDiff ℂ ω`.

`AddCommGroup` and `Module ℂ` are provable directly from pointwise
operations and the linearity of the analytic-coherence hypothesis under
those operations.

* Pros: avoids the bundle scaffolding; a small, self-contained
  definition.
* Cons: re-derives smoothness API that already exists for
  `ContMDiffSection`; the "analytic coherence under chart changes"
  needs its own glue lemma.

### Recommendation

Start with **Approach B** as a self-contained scaffold to unblock the
genus / `analyticGenus` definitions. If/when the bundle infrastructure
is needed for finer integration / pullback theorems, migrate to
Approach A in a separate refactor.

## First Aristotle-sized packets (when queue unblocks)

1. Define `HolomorphicOneForm X` per Approach B. Allowed write scope:
   `Jacobian/HolomorphicForms/Defs.lean`. Forbidden files:
   `Jacobian/Challenge.lean`, `Jacobian/WorkPackets/StatementBank.lean`.
2. Prove `AddCommGroup (HolomorphicOneForm X)` (pointwise add).
3. Prove `Module ℂ (HolomorphicOneForm X)`.
4. Update `JacobianChallenge.HolomorphicForms.HolomorphicOneForm` in
   `StatementBank.lean` from the `:= ℂ` placeholder to the new type.
5. State `FiniteDimensionalHolomorphicOneForms X` as a class wrapping
   `Module.Finite ℂ (HolomorphicOneForm X)`. The proof is deferred —
   it is the single largest missing analytic ingredient.

## Anti-hack considerations

`HolomorphicOneForm X` must be defined so that the trivial answer
`HolomorphicOneForm X := PUnit` is not viable. Approach B's
chart-coherence hypothesis is non-vacuous: there are non-zero
holomorphic 1-forms on a torus (e.g. `dz` pulled back via the chart),
so the dimension must be at least 1 for the simplest non-trivial
example. Confirming this concretely on `V ⧸ Λ.subgroup` is itself a
non-trivial check that should land before claiming
`genus_eq_analyticGenus` for that example.
-/

namespace JacobianChallenge.HolomorphicForms

/-- Reconnaissance marker. This file intentionally contains no public
declarations beyond this token, which exists to make the module
non-empty for the build system. -/
def reconStub : Unit := ()

end JacobianChallenge.HolomorphicForms
