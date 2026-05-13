import Jacobian.HolomorphicForms.Meromorphic
import Jacobian.HolomorphicForms.MeromorphicDegree
import Mathlib.Topology.Compactification.OnePoint.Basic
import Jacobian.Periods.TrivializationContinuousLinearMapAt

open scoped Manifold

namespace JacobianChallenge.HolomorphicForms

/-- The Riemann-Roch output in genus zero: a meromorphic map to `OnePoint ℂ`
whose pole divisor is the point divisor `[pole]`. -/
structure GenusZeroSimplePoleMeromorphicMap
    (X : Type*) [TopologicalSpace X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X] where
  meromorphicMap : MeromorphicMapToSphere X
  pole : X
  simple_pole_cert : meromorphicMap.poles = Divisor.point pole

namespace GenusZeroSimplePoleMeromorphicMap

/-- The underlying map to the Riemann sphere. -/
def toMap {X : Type*} [TopologicalSpace X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X]
    [JacobianChallenge.Periods.StableChartAt ℂ X]
    (f : GenusZeroSimplePoleMeromorphicMap X) : X → OnePoint ℂ :=
  f.meromorphicMap.toMap

end GenusZeroSimplePoleMeromorphicMap

/-- Placeholder data after the compactness/properness step: the genus-zero
meromorphic map is a degree-one map to `OnePoint ℂ`.

The fields are the topological consequences needed by the final assembly:
continuity and bijectivity. A future refinement should replace this bridge by
properness plus the local degree calculation, then derive these fields. -/
structure GenusZeroProperDegreeOneMap
    (X : Type*) [TopologicalSpace X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X] where
  toMap : X → OnePoint ℂ
  continuous_toMap : Continuous toMap
  bijective_toMap : Function.Bijective toMap
  degree_one_data : ∃ f : MeromorphicMapToSphere X,
    toMap = f.toMap ∧ Nonempty (MeromorphicDegreeOneData X f)

/-- Placeholder data for the last analytic step: a degree-one meromorphic map
is a biholomorphic parametrization of `X` by `OnePoint ℂ`.

At the topological surface needed here, this is represented by the resulting
homeomorphism. Future work can strengthen the structure with a biholomorphism
type once the project has one. -/
structure GenusZeroBiholomorphicParametrization
    (X : Type*) [TopologicalSpace X] where
  toHomeomorph : X ≃ₜ OnePoint ℂ

end JacobianChallenge.HolomorphicForms