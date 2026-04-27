import Jacobian.TraceDegree.PullbackBasis
import Jacobian.TraceDegree.PushforwardBasis

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
open JacobianChallenge.AbelJacobi

variable {X : Type*} [TopologicalSpace X] [T2Space X] [CompactSpace X]
  [ConnectedSpace X] [ChartedSpace ℂ X]
  [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X]
variable {Y : Type*} [TopologicalSpace Y] [T2Space Y] [CompactSpace Y]
  [ConnectedSpace Y] [ChartedSpace ℂ Y]
  [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) Y]

/-- The analytic degree of a holomorphic map between compact Riemann
surfaces. Equal to `0` for constant maps, otherwise the classical
branched-cover degree (generic-fiber cardinality with ramification
multiplicity).

Top-down obligation. Bottom-up: requires local normal form for
nonconstant holomorphic maps, ramification theory, and the constancy
detection step. -/
opaque analyticDegree (f : X → Y) (hf : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω f) : ℕ

/-- The trace–pullback identity, in basis-aligned form: pushforward
of pullback equals degree-multiplication on `BasisAnalyticJacobian Y`.

Top-down obligation. Bottom-up: descend the classical trace–pullback
identity `tr_f (f* η) = deg(f) · η` (on holomorphic 1-forms) through
the period quotient. -/
lemma analyticPushforward_analyticPullback (f : X → Y)
    (hf : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω f) (Q : BasisAnalyticJacobian Y) :
    analyticPushforward f hf (analyticPullback f hf Q) =
      (analyticDegree f hf) • Q := sorry

end JacobianChallenge.TraceDegree
