import Jacobian.TraceDegree.PullbackBasis
import Jacobian.TraceDegree.PushforwardBasis
import Jacobian.HolomorphicForms.TraceSpec
import Jacobian.TraceDegree.PiecewiseC1Instance
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
open JacobianChallenge.HolomorphicForms

variable {X : Type} [TopologicalSpace X] [T2Space X] [CompactSpace X]
  [ConnectedSpace X] [ChartedSpace ℂ X]
  [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X]
  [StableChartAt ℂ X]
  [JacobianChallenge.HolomorphicForms.FiniteDimensionalHolomorphicOneForms ℂ X]
variable {Y : Type} [TopologicalSpace Y] [T2Space Y] [CompactSpace Y]
  [ConnectedSpace Y] [ChartedSpace ℂ Y]
  [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) Y]
  [StableChartAt ℂ Y]
  [JacobianChallenge.HolomorphicForms.FiniteDimensionalHolomorphicOneForms ℂ Y]

/-- The (analytic) degree of a holomorphic map `f : X → Y` of compact
Riemann surfaces. This is intentionally opaque: basis-level pullback
data does not fabricate degree data, and the geometric identification
with branched degree is exposed through explicit hypotheses/frontier
lemmas. -/
noncomputable opaque analyticDegree (f : X → Y) (hf : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω f) : ℕ

/-- Bundled analytic trace/degree contract for a holomorphic map of compact
Riemann surfaces.

The fields are the mathematical laws needed by the public route theorems:
constant maps have degree zero, nonconstant analytic degree agrees with the
branched-cover degree supplied by the project constructor, the global trace
agrees with the local regular-fiber trace, trace after pullback is degree
multiplication on holomorphic forms, and the descended basis-aligned Jacobian
maps satisfy the corresponding push-pull identity. -/
structure AnalyticTraceDegreeSpec (f : X → Y)
    (hf : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω f) where
  /-- Constant maps have analytic degree zero. -/
  degree_constant : (∃ y₀, ∀ x, f x = y₀) → analyticDegree f hf = 0
  /-- For nonconstant maps, analytic degree agrees with the constructed
  branched-cover degree under the standard local ramification and weighted
  fiber conservation hypotheses. -/
  degree_eq_branched :
    ∀ (hkfold : HasLocalKfoldRamification f) (hw : HasWeightedFiberConservation f)
      (hnonconst : ¬ ∃ y₀, ∀ x, f x = y₀),
      analyticDegree f hf =
        branchedDegree
          (JacobianChallenge.Blueprint.branchedCoverData_of_nonconstant_holomorphic
            (isHolomorphic_of_contMDiff hf hkfold) hw hnonconst)
  /-- The global trace form agrees with the regular-value local trace. -/
  trace_regular : TraceFormsRegularSpec f hf
  /-- Form-level trace-pullback identity. -/
  trace_pullback :
    ∀ η : HolomorphicOneForm ℂ Y,
      traceFormsBundled f hf (pullbackFormsBundled f hf η) =
        (analyticDegree f hf : ℂ) • η
  /-- Basis-aligned Jacobian push-pull identity. -/
  push_pull :
    ∀ [PiecewiseC1PathRegularity X] [PiecewiseC1PathRegularity Y]
      (Q : BasisAnalyticJacobian Y),
      analyticPushforward f hf (analyticPullback f hf Q) =
        (analyticDegree f hf) • Q

/-- Frontier provider for the analytic trace/degree package.

This is the single named boundary for the current trace-degree cluster.  Its
content is the classical analytic construction of the global trace of
holomorphic one-forms, the analytic degree (zero for constant maps and the
branched-cover degree for nonconstant maps), the trace-pullback identity, and
the descent of that identity through the basis-aligned period quotient. -/
noncomputable def analyticTraceDegreeSpec_frontier (f : X → Y)
    (hf : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω f) :
    AnalyticTraceDegreeSpec f hf := by
  sorry

omit [T2Space X] [CompactSpace X] [ConnectedSpace X]
  [IsManifold 𝓘(ℂ) ω X] [StableChartAt ℂ X]
  [T2Space Y] [CompactSpace Y] [IsManifold 𝓘(ℂ) ω Y] [StableChartAt ℂ Y] in
/-- **Analytic degree identity, explicit form.** The equality between
the abstract analytic degree carried by `basisAnalyticPullbackBundle`
and the geometric branched degree is no longer manufactured from
`ContMDiff` alone; callers must provide the geometric degree witness. -/
theorem analyticDegree_eq_branchedDegree (f : X → Y)
    (hf : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω f)
    (hbc : JacobianChallenge.HolomorphicForms.BranchedCoverData X Y f)
    (hdegree : analyticDegree f hf = JacobianChallenge.HolomorphicForms.branchedDegree hbc) :
    analyticDegree f hf =
      JacobianChallenge.HolomorphicForms.branchedDegree hbc := hdegree

/-- **Analytic degree of constant maps.** The degree of a constant map is zero.
This is a genuine degree-theory frontier now that `analyticDegree` is no
longer faked by the basis pullback bundle. -/
theorem analyticDegree_constant (f : X → Y)
    (hf : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω f) (_hconst : ∃ y₀, ∀ x, f x = y₀) :
    analyticDegree f hf = 0 :=
  (analyticTraceDegreeSpec_frontier f hf).degree_constant _hconst

/-- Companion specification (anti-hack obligation): the trace-pullback
identity in basis-aligned form. This remains an explicit frontier; it
is not hidden as a fake field of the basis pullback bundle. -/
theorem analyticPushforward_analyticPullback_spec (f : X → Y)
    [PiecewiseC1PathRegularity X] [PiecewiseC1PathRegularity Y]
    (hf : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω f) (Q : BasisAnalyticJacobian Y) :
    analyticPushforward f hf (analyticPullback f hf Q) =
      (analyticDegree f hf) • Q :=
  (analyticTraceDegreeSpec_frontier f hf).push_pull Q

/- The trace–pullback identity, in basis-aligned form: pushforward
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
/-- Compatibility wrapper using the named trace-pullback frontier. -/
lemma analyticPushforward_analyticPullback (f : X → Y)
    [PiecewiseC1PathRegularity X] [PiecewiseC1PathRegularity Y]
    (hf : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω f) (Q : BasisAnalyticJacobian Y) :
    analyticPushforward f hf (analyticPullback f hf Q) =
      (analyticDegree f hf) • Q :=
  analyticPushforward_analyticPullback_spec f hf Q


end JacobianChallenge.TraceDegree
