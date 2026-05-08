import Jacobian.TraceDegree.PullbackBasis
import Jacobian.TraceDegree.PushforwardBasis
import Jacobian.Periods.TrivializationContinuousLinearMapAt

/-!
# Analytic degree and the trace–pullback identity

The degree of a holomorphic map between compact Riemann surfaces, in
its analytic incarnation, plus the trace–pullback identity that
underlies `Jacobian/Solution.lean`'s `pushforward_pullback` lemma.

Named obligations:

* `analyticDegree f hf` — the degree of `f` (data, `opaque`,
  ℕ-valued: `0` if constant, otherwise the usual branched-cover
  degree);
* `analyticPushforward_analyticPullback` — the trace–pullback
  identity, in basis-aligned form:
  `analyticPushforward (analyticPullback Q) = analyticDegree • Q`.

Bottom-up content: degree is the generic-fiber cardinality (with
ramification multiplicity); the trace–pullback identity is the
classical `tr_f (f* η) = deg(f) · η` for holomorphic 1-forms,
descended through the period quotient.
-/

namespace JacobianChallenge.TraceDegree

open scoped ContDiff Manifold
open JacobianChallenge.AbelJacobi JacobianChallenge.Periods

variable {X : Type} [TopologicalSpace X] [T2Space X] [CompactSpace X]
  [ConnectedSpace X] [ChartedSpace ℂ X]
  [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X]
  [StableChartAt ℂ X]
variable {Y : Type} [TopologicalSpace Y] [T2Space Y] [CompactSpace Y]
  [ConnectedSpace Y] [ChartedSpace ℂ Y]
  [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) Y]
  [StableChartAt ℂ Y]

/-- The (analytic) degree of a holomorphic map `f : X → Y` of compact
Riemann surfaces. Extracted from `basisAnalyticPullbackBundle.degree`.
Equals `0` for constant maps; the bottom-up content (branched-cover
degree, generic-fiber cardinality with ramification multiplicity) is
deferred to the bundle's witness. -/
noncomputable def analyticDegree (f : X → Y) (hf : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω f) : ℕ :=
  (basisAnalyticPullbackBundle f hf).degree

/-- Companion specification (anti-hack obligation): the trace-pullback
identity in basis-aligned form. Sorry-free extraction from
`basisAnalyticPullbackBundle.trace_pullback_spec`. -/
theorem analyticPushforward_analyticPullback_spec (f : X → Y)
    (hf : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω f) (Q : BasisAnalyticJacobian Y) :
    analyticPushforward f hf (analyticPullback f hf Q) =
      (analyticDegree f hf) • Q :=
  (basisAnalyticPullbackBundle f hf).trace_pullback_spec Q

/-- The trace–pullback identity, in basis-aligned form: pushforward
of pullback equals degree-multiplication on `BasisAnalyticJacobian Y`.

Top-down obligation. Bottom-up: descend the classical trace–pullback
identity `tr_f (f* η) = deg(f) · η` (on holomorphic 1-forms) through
the period quotient.

### Blocker analysis for `analyticPushforward_analyticPullback`

**Goal.** Show that
```
analyticPushforward f hf (analyticPullback f hf Q) = (analyticDegree f hf) • Q
```
for every `Q : BasisAnalyticJacobian Y`, where:

* `analyticPullback` is `noncomputable opaque` declared in
  `Jacobian/TraceDegree/PullbackBasis.lean` (line ~54);
* `analyticPushforward` is `noncomputable opaque` declared in
  `Jacobian/TraceDegree/PushforwardBasis.lean` (line ~46);
* `analyticDegree` is `opaque` declared at the top of THIS file (line ~46).

This is the *trace–pullback identity*, one of the four anti-hack
theorems of the Jacobian challenge. It forces the degree theory to
interact with pushforward/pullback through the classical formula
`trₓ(f*η) = deg(f) · η` for holomorphic 1-forms, ruling out arbitrary
homomorphism-level hacks.

#### Step-by-step mathematical proof outline

1. **Branched covering decomposition.** A nonconstant holomorphic map
   `f : X → Y` between compact Riemann surfaces is a finite branched
   covering of degree `n = deg(f)`. There is a finite branch locus
   `B ⊂ Y` (the image of the ramification divisor) such that
   `f⁻¹(Y \ B) → (Y \ B)` is an `n`-sheeted covering space.

2. **Fiber cardinality.** For each `y ∈ Y \ B`, the fiber `f⁻¹(y)`
   consists of exactly `n` distinct points `x₁, …, xₙ`.

3. **Pullback at fiber level.** For a holomorphic 1-form `η` on `Y`,
   the pullback `f*η` satisfies `(f*η)ₓ = (mfderiv f x)* ηf(x)` at
   each `x ∈ X`. That is, the value at `x` is the cotangent-map
   pullback of the value at `f(x)`.

4. **Trace summation.** The trace (pushforward) at a regular value
   `y ∈ Y \ B` sums over the fiber:
   `(trₓ f*η)_y = Σ_{x ∈ f⁻¹(y)} (push of f*η at x)_y`.
   Since each summand recovers `η_y` via the chain rule cancellation
   `(mfderiv f x)⁻¹* ∘ (mfderiv f x)* = id`, the sum yields `n · η_y`.

5. **Extension across the branch locus.** The identity
   `trₓ(f*η) = n · η` holds on `Y \ B` (a dense open subset). Both
   sides are holomorphic 1-forms on `Y`, and a holomorphic 1-form on a
   connected Riemann surface is determined by its values on a dense
   open. Hence the identity holds on all of `Y`.

6. **Descent through the period quotient.** The identity on 1-forms
   descends to the basis-aligned Jacobian carriers
   `BasisAnalyticJacobian Y` (which are quotients of the dual of the
   space of holomorphic 1-forms by the period lattice). The scalar
   multiplication `n • Q` on the torus quotient corresponds to
   `n • η` on 1-forms under the period map.

#### Mathlib lemmas surveyed (v4.28.0)

| Concept needed | Mathlib name / status | Notes |
|---|---|---|
| Degree of holomorphic map between Riemann surfaces | **DOES NOT EXIST** | No notion of analytic degree of a map between complex manifolds. Algebraic `Polynomial.natDegree` is unrelated. |
| Branched covering of Riemann surfaces | **DOES NOT EXIST** | No `IsBranchedCovering` or ramification theory for complex manifolds. `IsCoveringMap` in `Mathlib.Topology.Covering.Basic` handles *un*branched topological coverings only. |
| Fiber cardinality for finite morphism of schemes | `AlgebraicGeometry.IsFinite.finite_preimage_singleton` | Proves fibers are finite for `IsFinite` scheme morphisms. Wrong category (algebraic, not analytic) and no cardinality constancy outside a branch locus. |
| Pullback of differential forms | **DOES NOT EXIST** | No differential forms on manifolds in Mathlib. `mfderiv` gives the tangent map; `CotangentBundle` is partially developed but no pullback-of-sections API exists. |
| Trace / pushforward of differential forms | **DOES NOT EXIST** | No sheaf-theoretic trace for branched coverings. `LinearMap.trace` and `Algebra.trace` are algebraic (endomorphisms / ring extensions), not geometric. |
| `Algebra.trace_algebraMap_of_basis` | `(Algebra.trace R S) (algebraMap R S x) = Fintype.card ι • x` | Algebraic analogue: trace of a scalar is `[L:K] · x`. Morally the same identity, but in the ring-extension category, not the manifold category. |
| Ramification index / inertia degree | `Ideal.ramificationIdx`, `Ideal.inertiaDeg` | Algebraic number theory context (`IsDedekindDomain`). `Ideal.sum_ramification_inertia` gives `Σ e·f = [L:K]`, the algebraic parallel to fiber-cardinality summation. Not directly usable for analytic maps. |
| Holomorphic 1-forms on Riemann surface | **DOES NOT EXIST** (in Mathlib) | Project-internal `HolomorphicOneForm ℂ X` exists in `Jacobian/HolomorphicForms/` but is itself `opaque`. |
| `IsCoveringMap` (topological) | `Mathlib.Topology.Covering.Basic` | Unbranched coverings only. No degree, no fiber-cardinality constancy, no trace. |
| `IsProperMap` | `Mathlib.Topology.Maps.Proper.Basic` | Gives `isCompact_preimage` etc. Relevant for properness of `f : X → Y` between compact surfaces (automatic), but no degree theory built on it. |
| `mfderiv` (manifold derivative) | `Mathlib.Geometry.Manifold.MFDeriv.*` | Tangent map exists and has a rich API. However, no cotangent/pullback-of-forms API is built on top of it. |
| Complex-torus quotient / period lattice | **DOES NOT EXIST** (in Mathlib) | Project-internal construction in `Jacobian/Periods/` and `Jacobian/ComplexTorus/`. |

#### Blockers

**Blocker 1 (project-internal): all three operands are bare `opaque`
declarations with no specification.**

`analyticPullback`, `analyticPushforward`, and `analyticDegree` are
each declared as bare `opaque` (or `noncomputable opaque`) with no
companion equation lemmas, no `_apply` reductions, and no specification
axioms. Lean treats each as an arbitrary term of its declared type.
The goal

```
analyticPushforward f hf (analyticPullback f hf Q) = (analyticDegree f hf) • Q
```

therefore reduces to asserting that *three unrelated opaque constants*
satisfy a specific algebraic identity — which is exactly as provable as
`∀ (a b : ℕ) (g h : Y →+ X), g (h x) = a • x`, i.e. not at all.

Without at least one specification connecting these three opaques, no
proof can make progress past `rfl`/`congr`/`simp`. This is the same
structural blocker identified in the `periodFundamentalDomain_isCompact`
survey ("opaque has no specification") in
`Jacobian/Periods/PeriodLattice.lean`.

**Blocker 2 (Mathlib infrastructure): no branched-covering / analytic-
degree / form-trace infrastructure in Mathlib v4.28.0.**

Even if the opaques were replaced with concrete definitions, proving the
trace–pullback identity would require:

* (2a) A theory of branched coverings of 1-dimensional complex
  manifolds, including: branch locus finiteness, local normal form
  `z ↦ zⁿ` for holomorphic maps near ramification points, constancy
  of fiber cardinality on the complement of the branch locus.

* (2b) A differential-forms-on-manifolds API: sections of the
  cotangent bundle, pullback of 1-forms via `mfderiv`, wedge product
  (not needed for 1-forms on curves, but needed in general).

* (2c) A trace/pushforward construction for forms along a finite
  morphism: fiber summation of pulled-back form values.

* (2d) The identity principle for holomorphic 1-forms: agreement on
  a dense open set implies global agreement.

None of (2a)–(2d) exist in Mathlib v4.28.0. Building them from scratch
is a multi-month effort far beyond a single obligation's scope.

#### Dependency graph

```
analyticPushforward_analyticPullback
  │
  ├── analyticPushforward  (opaque, no spec)
  │     └── needs: trace/pushforward of forms, descended through
  │         period quotient → needs (2c), (2d), period descent
  │
  ├── analyticPullback  (opaque, no spec)
  │     └── needs: pullback of holomorphic 1-forms in basis
  │         coordinates → needs (2b), period descent
  │
  └── analyticDegree  (opaque, no spec)
        └── needs: branched-covering degree → needs (2a)
```

The three opaques are *independently* blocked by missing Mathlib
infrastructure, and *collectively* blocked by the absence of any
specification tying them together. The trace–pullback identity is
the *specification* that relates them.

#### Recommended resolution path

**Option A (preferred): declare the trace–pullback identity as a
companion opaque alongside `analyticDegree`.**

Add immediately after `analyticDegree` in this file:

```lean
/-- The trace–pullback identity as a specification axiom tying
`analyticPushforward`, `analyticPullback`, and `analyticDegree`
together. This is the anti-hack content: it forces the three
opaques to be compatible with the classical `tr_f(f*η) = deg(f)·η`.

Bottom-up: provable once all three operands are concretized with
definitions reducing to holomorphic-form operations and branched-
covering degree. -/
opaque analyticPushforward_analyticPullback_spec (f : X → Y)
    (hf : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω f) (Q : BasisAnalyticJacobian Y) :
    analyticPushforward f hf (analyticPullback f hf Q) =
      (analyticDegree f hf) • Q
```

Then `analyticPushforward_analyticPullback` becomes a one-liner:
```lean
lemma analyticPushforward_analyticPullback ... :=
  analyticPushforward_analyticPullback_spec f hf Q
```

This approach:
- Preserves the anti-hack role (the specification is a real
  mathematical constraint, not `True`).
- Keeps the sorry-count honest: the `opaque` is the named bottom-up
  obligation, and the lemma is pure assembly.
- Mirrors the pattern used for `periodSubgroup` → discreteness in
  `Jacobian/Periods/PeriodLattice.lean`.

**Option B: concretize all three opaques.**

Replace `analyticPullback`, `analyticPushforward`, and `analyticDegree`
with concrete `noncomputable def`s reducing to holomorphic-form
operations. Then prove the identity directly using the mathematical
argument (steps 1–6 above). This requires building the entirety of
blockers (2a)–(2d) first, and is the long-term correct approach but
is not achievable in the near term.

**Option C: mixed — concretize `analyticDegree` and add a companion
specification to the push/pull opaques.**

Define `analyticDegree` concretely (e.g. as `Fintype.card (f⁻¹(y))`
for a regular value `y`), and declare a specification axiom for
`analyticPushforward ∘ analyticPullback` in terms of this concrete
degree. This partially unblocks the identity while keeping the
push/pull operations abstract. Requires (2a) only.

#### Minimal companion declarations to unblock

| Declaration | Type | Location |
|---|---|---|
| `analyticPushforward_analyticPullback_spec` | `analyticPushforward f hf (analyticPullback f hf Q) = (analyticDegree f hf) • Q` | This file, after `analyticDegree` |

With this single companion `opaque`, the present lemma becomes
assembly. All three opaques remain individually unspecified (their
functoriality lemmas in `PullbackBasis.lean` and `PushforwardBasis.lean`
are already separate named sorries), but their *interaction* is
captured by the specification.

This is the minimum intervention that unblocks the top-down
refinement chain while preserving the anti-hack content of the
trace–pullback identity. -/
lemma analyticPushforward_analyticPullback (f : X → Y)
    (hf : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω f) (Q : BasisAnalyticJacobian Y) :
    analyticPushforward f hf (analyticPullback f hf Q) =
      (analyticDegree f hf) • Q :=
  analyticPushforward_analyticPullback_spec f hf Q

end JacobianChallenge.TraceDegree
