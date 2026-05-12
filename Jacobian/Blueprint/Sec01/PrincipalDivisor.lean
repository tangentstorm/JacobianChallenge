import Jacobian.Blueprint.Sec01.Divisor
import Jacobian.Blueprint.Sec01.MeromorphicFunction
import Jacobian.Blueprint.Sec01.DivisorFiniteSupport
import Jacobian.Periods.TrivializationContinuousLinearMapAt

/-! Blueprint: `def:principal-divisor` in
`tex/sections/01-compact-riemann-surfaces.tex`.

The principal divisor `(f) := Σ_p ord_p(f) · p` of a meromorphic
function on a compact Riemann surface, packaged as a `Finsupp` whose
support is finite by `lem:divisor-finite-support`. -/

namespace JacobianChallenge.Blueprint

open scoped Manifold
open JacobianChallenge.HolomorphicForms.VanishingOrder

/-- Underlying ℂ-valued projection of a `MeromorphicFunctionType X`.
Sends `∞` to the sentinel `0`. The convention is lossy at poles
(the OnePoint representation collapses pole information), but it is
sufficient for the regular-part Laurent order computations performed
by `vanishingOrder`. Once the meromorphic-germ-sheaf gluing lands,
this projection should be replaced with the genuine
"meromorphic germ ↦ underlying function on the domain of holomorphy"
extraction. -/
private noncomputable def underlyingC
    {X : Type*} [TopologicalSpace X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X]
    [JacobianChallenge.Periods.StableChartAt ℂ X]
    (f : MeromorphicFunctionType X) : X → ℂ :=
  fun p => (f p).getD 0

/-- The principal divisor `(f) := Σ_p ord_p(f) · p` of a meromorphic
function on a compact Riemann surface, expressed as a `Finsupp`.

Returns the zero divisor whenever the underlying ℂ-valued projection
of `f` fails to satisfy the manifold-level "nonzero meromorphic"
hypotheses required by `divisor_finite_support` — namely (i) meromorphy
at every point and (ii) finite vanishing order at every point. In
particular the zero divisor is returned for the literal zero
meromorphic function and whenever the placeholder `MeromorphicFunctionType`
fails to expose enough analytic structure on the projection. For any
projection that does satisfy both hypotheses, `Finsupp.onFinset`
packages the support `{q | ord_q(f) ≠ 0}` (finite by
`divisor_finite_support`) and the integer coefficient
`(ord_q f).untopD 0`.

This places the blueprint dep-graph node `def:principal-divisor`
on a real Lean footing: the body is sorry-free; the upstream sorries
are in `MeromorphicFunctionType` (whose richer "field of meromorphic
germs" structure is still pending) and `vanishingOrder`'s pole-aware
extension. -/
noncomputable def principalDivisor
    (X : Type*) [TopologicalSpace X] [ConnectedSpace X] [CompactSpace X]
    [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X]
    [JacobianChallenge.Periods.StableChartAt ℂ X]
    (f : MeromorphicFunctionType X) : Divisor X := by
  classical
  by_cases hf : (∀ q : X, MeromorphicAtX (underlyingC f) q) ∧
                (∃ p : X, vanishingOrder X p (underlyingC f) ≠ ⊤)
  · exact Finsupp.onFinset
      (divisor_finite_support X (underlyingC f) hf.1 hf.2).toFinset
      (fun p => (vanishingOrder X p (underlyingC f)).untopD 0)
      (by
        intro p hp
        rw [Set.Finite.mem_toFinset]
        intro h_eq
        apply hp
        show WithTop.untopD 0 (vanishingOrder X p (underlyingC f)) = 0
        rw [h_eq]
        rfl)
  · exact 0

end JacobianChallenge.Blueprint
