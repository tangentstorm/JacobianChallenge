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

/-- **Analytic degree identity.** For non-constant maps, the analytic
degree equals the geometric branched degree.

Sorry-free: definitional via the construction in `PullbackBasis.lean`. -/
theorem analyticDegree_eq_branchedDegree (f : X → Y)
    (hf : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω f) (hnonconst : ¬ ∃ y₀, ∀ x, f x = y₀) :
    analyticDegree f hf =
      JacobianChallenge.HolomorphicForms.branchedDegree
        (JacobianChallenge.Blueprint.branchedCoverData_of_nonconstant_holomorphic
          (JacobianChallenge.HolomorphicForms.HolomorphicMap.isHolomorphic_of_contMDiff hf)
          hnonconst) := by
  unfold analyticDegree basisAnalyticPullbackBundle
  simp [hnonconst]

/-- **Analytic degree of constant maps.** The degree of a constant map is zero.

Sorry-free: definitional via the construction in `PullbackBasis.lean`. -/
theorem analyticDegree_constant (f : X → Y)
    (hf : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω f) (hconst : ∃ y₀, ∀ x, f x = y₀) :
    analyticDegree f hf = 0 := by
  unfold analyticDegree basisAnalyticPullbackBundle
  simp [hconst]

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
| Degree of holomorphic map | **PARTIALLY PROVED** | Project-local `branchedDegree` exists in `HolomorphicForms/BranchedCover.lean`. Connected to `analyticDegree` via `analyticDegree_eq_branchedDegree`. |
| Branched covering | **PARTIALLY PROVED** | Project-local `BranchedCoverData` exists. Analytic constructor `branchedCoverData_of_nonconstant_holomorphic` is implemented. |
| Pullback of forms | **PROVED** | `pullbackFormsBundled` implemented in `HolomorphicForms/PullbackBundled.lean`. |
| Trace of forms | **STUBBED** | `traceFormsBundled` stubbed in `HolomorphicForms/TraceBundled.lean`. |
| Trace–pullback identity | **STUBBED** | `trace_pullback_identity` in `HolomorphicForms/TraceBundled.lean`. |

#### Blockers

The primary blocker is now the **smoothness of the trace map** and the
**proof of the trace–pullback identity** at the form level. The
basis-aligned assembly is now structurally sound and delegates to
these two analytic gaps.

#### Dependency graph

```
analyticPushforward_analyticPullback
  │
  ├── analyticPushforward  (dual of pullbackFormsBundled)
  │
  ├── analyticPullback     (dual of traceFormsBundled)
  │
  └── analyticDegree       (branchedDegree)
```

The identity `analyticPushforward f hf (analyticPullback f hf Q) = d • Q`
follows from the form-level identity `traceFormsBundled f hf (pullbackFormsBundled f hf η) = d • η`
by dualization and descent through the period quotient. -/
lemma analyticPushforward_analyticPullback (f : X → Y)
    (hf : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω f) (Q : BasisAnalyticJacobian Y) :
    analyticPushforward f hf (analyticPullback f hf Q) =
      (analyticDegree f hf) • Q :=
  analyticPushforward_analyticPullback_spec f hf Q


end JacobianChallenge.TraceDegree
