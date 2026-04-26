import Jacobian.ComplexTorus.ChartedSpace
import Jacobian.ComplexTorus.IsManifold
import Jacobian.ComplexTorus.LieAddGroup
import Jacobian.WorkPackets.StatementBank

/-!
# Witnesses for the StatementBank Queue B chart/manifold/Lie-group targets

The StatementBank Queue B placeholders for the chart, manifold, and
Lie-add-group targets are dischargeable now that the concrete
`ChartedSpace`, `IsManifold`, and `LieAddGroup` instances exist. The
witness theorems below provide each instance for the corresponding
`...Statement` shape.

This module records the witness theorems separately from the
StatementBank so the bank itself stays a pure list of targets.
-/

namespace JacobianChallenge.ComplexTorus

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V]

/-- Discharge the StatementBank charted-space target with the concrete
`complexTorusChartedSpace` instance. -/
theorem quotientChartedSpace_witness (Λ : FullComplexLattice V) :
    JacobianChallenge.ComplexTorus.quotientChartedSpaceStatement V Λ :=
  ⟨complexTorusChartedSpace Λ⟩

/-- Discharge the strengthened `IsManifold` target: bundle the concrete
`ChartedSpace` and `IsManifold` instances. -/
theorem quotientIsManifold_witness (Λ : FullComplexLattice V) :
    JacobianChallenge.ComplexTorus.quotientIsManifoldStatement V Λ :=
  ⟨complexTorusChartedSpace Λ, complexTorusIsManifold Λ⟩

/-- Discharge the strengthened `LieAddGroup` target: bundle the concrete
`ChartedSpace`, `IsManifold`, and `LieAddGroup` instances. -/
theorem quotientLieAddGroup_witness (Λ : FullComplexLattice V) :
    JacobianChallenge.ComplexTorus.quotientLieAddGroupStatement V Λ :=
  ⟨complexTorusChartedSpace Λ, complexTorusIsManifold Λ, lieAddGroup_quotient Λ⟩

end JacobianChallenge.ComplexTorus
