import Jacobian.HolomorphicForms

/-!
# Reconnaissance: trace, degree, pushforward, pullback

Queue G kickoff. This is a name-discovery and design document for
the trace/degree/pullback/pushforward machinery needed by
`Jacobian/Challenge.lean`'s `Jacobian.pullback`, `Jacobian.pushforward`,
`ContMDiff.degree`, and the `pushforward_pullback` anti-hack theorem.

Like the earlier `*/Recon.lean` files, this contains no production
declarations beyond a stub token; it is not re-exported.

## Phase context

Queue C provides `HolomorphicOneForm E X` and its module structure.
The pullback/trace/degree apparatus operates on these:

```text
pullbackForms f hf : HolomorphicOneForm E Y →ₗ[ℂ] HolomorphicOneForm E X
traceForms    f hf : HolomorphicOneForm E X →ₗ[ℂ] HolomorphicOneForm E Y
analyticDegree f hf : ℕ
```

The fundamental identity (`trace_pullback_forms`):

```text
traceForms f hf (pullbackForms f hf η) = (analyticDegree f hf : ℂ) • η
```

This is the analytic engine that supports
`pushforward_pullback : pushforward (pullback P) = degree • P`,
the strongest of the four anti-hack theorems for the multiplicative
structure on the Jacobian.

## What Mathlib v4.28.0 has

* `mfderiv I I' f x : TangentSpace I x →L[ℂ] TangentSpace I' (f x)` —
  the manifold derivative.
* `MDifferentiable`, `ContMDiff` (for analyticity in our `n = ⊤` case).
* Composition lemmas (`ContMDiff.comp`, `ContMDiffAt.comp`).
* `LinearMap` API for the chain-rule-style pullback.

## What Mathlib v4.28.0 does NOT have

* No `pullbackForms` for differential forms on manifolds (depends on
  the cotangent bundle, which Mathlib lacks; we built ours via
  `Bundle.continuousLinearMap` in `HolomorphicForms/CotangentBundle`).
* No `traceForms` (the fiber-trace of forms along a finite covering
  map is bespoke geometric content).
* No `analyticDegree` (degree of a holomorphic map of compact
  Riemann surfaces; Mathlib has `ContMDiff.degree` as a public API
  hook in `Challenge.lean` but no concrete construction).

## Design choices

### Pullback (`pullbackForms`)

Given `f : X → Y` smooth and `η : HolomorphicOneForm E Y`, define
`pullbackForms f hf η : HolomorphicOneForm E X` by
`(f^*η)_x = η_{f x} ∘ mfderiv I I f x` — the cotangent transports
contravariantly via the differential. Concretely as a section:

```text
(pullbackForms f hf η).toFun x =
  (η.toFun (f x)).comp (mfderiv I I f x)
```

This is the chain-rule formula in the cotangent bundle. The
linearity in `η` is automatic; `ContMDiffSection` membership of the
result needs `ContMDiff` of `mfderiv f` (provided by the
`ContMDiff.mfderiv` API in Mathlib for `n + 1 ≤ ⊤`).

### Trace (`traceForms`)

The trace of a form `ω : HolomorphicOneForm E X` along a holomorphic
covering map `f : X → Y` (with finite fibers): for each `y : Y`,
sum `ω` over the fibers:

```text
(traceForms f hf ω).toFun y = ∑ x ∈ f⁻¹(y), ω.toFun x ∘ (mfderiv f x)⁻¹
```

This requires fiber-finiteness (degree theory) and a careful local
description (fibers are discrete, the sum is locally constant in
`y`). For Riemann surfaces, the degree is `analyticDegree f hf`.

### Degree (`analyticDegree`)

For a non-constant holomorphic map of compact Riemann surfaces,
`analyticDegree f hf` is the cardinality of a generic fiber. The
classical definition: `degree f = #f⁻¹(y)` for any `y` not in the
critical values. Equivalently: the degree of the map on top
cohomology, or the trace identity itself.

For the bridge to `ContMDiff.degree` (the Challenge-side hook), we
expect `ContMDiff.degree = analyticDegree`. Establishing this
equality is `degree_eq_analyticDegree`.

## Major gaps

* **`mfderiv` of holomorphic maps as a section of `Hom(TX, f^*TY)`.**
  Mathlib's `mfderiv` is pointwise; making it into a smooth section
  of the relevant bundle is an extra packaging step.
* **Fiber finiteness and degree.** The classical proof uses
  properness of `f` and the discreteness of fibers (zeros of the
  Jacobian). Mathlib has neither in this generality.
* **Riemann–Hurwitz / degree formula.** Not strictly needed for the
  challenge, but useful for sanity checks.

## First Aristotle-sized packets (when queue unblocks)

1. **`Jacobian/TraceDegree/Pullback.lean`** — `pullbackForms f hf η`
   defined via `mfderiv` composition. Linearity in `η` for free.
   `ContMDiff` of the result is the substantive piece.
2. **`Jacobian/TraceDegree/Pullback_module.lean`** — show
   `pullbackForms f hf` is a `LinearMap` (it is, by construction;
   wrap as `→ₗ[ℂ]`).
3. **`Jacobian/TraceDegree/Trace.lean`** — define `traceForms` for
   finite-fiber maps. Heavy: needs degree theory.
4. **`Jacobian/TraceDegree/Degree.lean`** — `analyticDegree` and
   bridge to `ContMDiff.degree`.
5. **`Jacobian/TraceDegree/TracePullback.lean`** — the trace-pullback
   identity. Substantive proof.
6. **`Jacobian/TraceDegree/PushforwardPullback.lean`** — the anti-hack
   theorem `pushforward_pullback = degree • id` (descends from the
   trace-pullback identity through the period quotient).

## Anti-hack considerations

`pushforward_pullback : pushforward (pullback P) = degree • P` is
the strongest multiplicative anti-hack theorem. It rules out
trivial choices like `pushforward = id`, `pullback = id`,
`degree = 0` simultaneously. With the trace-pullback identity in
place at the form level, the descent through the Jacobian quotient
is straightforward; without it, the result is essentially a free
parameter.

## Recommendation

Until `mfderiv`-as-section is wrapped and the cotangent bundle is
fully usable, this layer is in design state. Pullback (packet 1) is
the cleanest first concrete step; trace and degree are substantially
heavier and depend on degree-theoretic results not currently in
Mathlib.
-/

namespace JacobianChallenge.TraceDegree

/-- Reconnaissance marker. This file intentionally contains no public
declarations beyond this token, which exists to make the module
non-empty for the build system. -/
def reconStub : Unit := ()

end JacobianChallenge.TraceDegree
