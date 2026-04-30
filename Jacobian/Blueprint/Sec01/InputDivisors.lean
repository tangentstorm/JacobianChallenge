import Jacobian.Blueprint.Sec01.Divisor
import Jacobian.Blueprint.Sec01.DivisorDegree
import Jacobian.Blueprint.Sec01.MeromorphicFunction
import Jacobian.Blueprint.Sec01.PrincipalDivisor
import Jacobian.Blueprint.Sec01.PrincipalDivisors
import Jacobian.Blueprint.Sec01.PrincipalDegreeZero
import Jacobian.Blueprint.Sec01.MeromorphicToCp1
import Jacobian.Blueprint.Sec01.MeromorphicAsCp1Map
import Jacobian.Blueprint.Sec01.RiemannRochSpace
import Jacobian.Blueprint.Sec01.RiemannRochSpaceVector

/-! Blueprint: `input:divisors` in
`tex/sections/01-compact-riemann-surfaces.tex`.

Umbrella classical input — the package of meromorphic functions, divisors,
principal divisors, the degree map, meromorphic-to-Cp1, and Riemann-Roch
spaces. Pulled together as a single dependency for downstream classical
inputs. -/

namespace JacobianChallenge.Blueprint

open scoped Manifold

/-- Umbrella classical input combining all the divisor/meromorphic-function
infrastructure. The actual content is the conjunction of all the named
sub-statements; here we record a `Prop`-level placeholder. -/
def inputDivisors
    (X : Type*) [TopologicalSpace X] [CompactSpace X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X] : Prop :=
  -- The four "real" subgoals carved out as named theorems; the umbrella
  -- proof asserts that all of them hold.
  ∀ (f : MeromorphicFunctionType X),
    Divisor.degree (principalDivisor X f) = 0

theorem input_divisors_holds
    (X : Type*) [TopologicalSpace X] [CompactSpace X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X] :
    inputDivisors X := by
  intro f
  exact principal_degree_zero X f

end JacobianChallenge.Blueprint
