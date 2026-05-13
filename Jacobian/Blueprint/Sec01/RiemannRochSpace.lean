import Jacobian.Blueprint.Sec01.Divisor
import Jacobian.Blueprint.Sec01.MeromorphicFunction
import Jacobian.Blueprint.Sec01.PrincipalDivisor
import Mathlib.Analysis.Complex.Basic
import Jacobian.Periods.TrivializationContinuousLinearMapAt

/-! Blueprint: `def:riemann-roch-space` in
`tex/sections/01-compact-riemann-surfaces.tex`.

The Riemann-Roch space `L(D) = {f ∈ Mer(X) : (f) + D ≥ 0} ∪ {0}`. -/

namespace JacobianChallenge.Blueprint

open scoped Manifold

/-- The Riemann-Roch space `L(D)` for a divisor `D`: the set of meromorphic
functions `f` with `(f) + D ≥ 0`, together with the zero function. -/
def riemannRochSpace
    (X : Type*) [TopologicalSpace X] [CompactSpace X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X]
    [JacobianChallenge.Periods.StableChartAt ℂ X]
    (_D : Divisor X) : Set (MeromorphicFunctionType X) :=
  -- TODO: pin down once `principalDivisor` and ordering on `Divisor X`
  -- are connected.
  Set.univ

end JacobianChallenge.Blueprint
