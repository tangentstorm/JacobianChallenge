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
* an analytic-coherence hypothesis enforcing that under chart
  transitions, the local representation transforms by the
  inverse-transpose of the transition's `mfderiv`.

`AddCommGroup` and `Module ℂ` are provable directly from pointwise
operations.

* Pros: avoids the bundle scaffolding; a small, self-contained
  definition.
* Cons: hand-rolled cotangent transformation rule under chart
  changes; nontrivial to state correctly.

### A note on a tempting wrong simplification

The most-naive form of Approach B —

```text
HolomorphicOneForm X := { ω : X → (E →L[ℂ] ℂ) // ContMDiff … ω }
```

— **does not give the right answer in general**. Without the
inverse-transpose transformation rule under chart changes, the
"smooth function `X → E*`" view is chart-dependent. Concretely:
under the trivialization `TangentSpace I x = E`, two different
charts trivialize the same tangent space differently, and the
naive subtype identifies all those trivializations.

Worked example: for `Riemann sphere`, the genus is 0 and there are
no nonzero global holomorphic 1-forms; but global holomorphic
functions `X → ℂ` (i.e., the naive subtype with `E = ℂ`,
`E →L[ℂ] ℂ = ℂ`) form a 1-dimensional ℂ-space (the constants).
The naive definition would compute `analyticGenus(sphere) = 1`,
contradicting the genus-zero requirement.

For `V ⧸ Λ.subgroup` the chart transitions are translations whose
`mfderiv` is the identity, so the inverse-transpose is also the
identity and the naive subtype happens to agree with the correct
answer. Coincidence — do not generalize.

### Recommendation (revised)

Approach B's substantive content is the cotangent transformation
rule, so once we write that down honestly we're effectively building
the cotangent bundle by hand. **Approach A (Mathlib's
`Bundle.continuousLinearMap` + `ContMDiffSection`) is the cleaner
target.**

Concretely:
1. Build `CotangentBundle X := Bundle.continuousLinearMap ℂ
   (TangentBundle 𝓘(ℂ, E) X) (Bundle.Trivial X ℂ)` (or the equivalent;
   the bundle exists in `Topology/VectorBundle/Hom.lean`).
2. `HolomorphicOneForm X := Cₛ^⊤⟮𝓘(ℂ, E); E →L[ℂ] ℂ, CotangentBundle X⟯`.
3. Pull `AddCommGroup` and `Module ℂ` from
   `ContMDiffSection.module`.

This requires showing `CotangentBundle` is a `VectorBundle` over
`X` with fiber `E →L[ℂ] ℂ`, which Mathlib's `Hom.lean` already
provides scaffolding for once both `TangentBundle` and the trivial
`X × ℂ` bundle are recognized as `VectorBundle`s — both are
already instances.

## First Aristotle-sized packets (when queue unblocks)

1. **`Jacobian/HolomorphicForms/CotangentBundle.lean`** — assemble
   `CotangentBundle X` via `Bundle.continuousLinearMap`. Likely
   ~30 lines: bundle declaration, `VectorBundle` instance derivation
   from existing `TangentBundle` + `Bundle.Trivial` instances. Allowed
   write scope: only that file.
2. **`Jacobian/HolomorphicForms/Defs.lean`** — define
   `HolomorphicOneForm X := Cₛ^⊤⟮𝓘(ℂ, E); E →L[ℂ] ℂ, CotangentBundle X⟯`,
   plus the type abbreviation for use in `StatementBank`.
3. **`Jacobian/HolomorphicForms/AddCommGroup.lean`** — derive
   `AddCommGroup` from `ContMDiffSection.addCommGroup` (one-liner).
4. **`Jacobian/HolomorphicForms/Module.lean`** — derive `Module ℂ`
   similarly (one-liner).
5. **Update `JacobianChallenge.HolomorphicForms.HolomorphicOneForm`** in
   `StatementBank.lean` from the `:= ℂ` placeholder to the real type.
6. State `FiniteDimensionalHolomorphicOneForms X` as a class wrapping
   `Module.Finite ℂ (HolomorphicOneForm X)`. The proof is deferred —
   it is the single largest missing analytic ingredient.

## Anti-hack considerations

`HolomorphicOneForm X := PUnit` is not viable because of the
`genus_eq_analyticGenus` and `analyticGenus_eq_zero_iff_homeomorphic_sphere`
constraints in `Challenge.lean`. The cotangent-bundle definition
naturally avoids over-counting (which the naive Approach B would
suffer from on the Riemann sphere — see "tempting wrong simplification"
above).

Confirming nonzero holomorphic 1-forms on `V ⧸ Λ.subgroup` (`g = 1`
yielding a 1-dim space spanned by `dz`) is the cleanest first
sanity check after the type and module structure land.
-/

namespace JacobianChallenge.HolomorphicForms

/-- Reconnaissance marker. This file intentionally contains no public
declarations beyond this token, which exists to make the module
non-empty for the build system. -/
def reconStub : Unit := ()

end JacobianChallenge.HolomorphicForms
