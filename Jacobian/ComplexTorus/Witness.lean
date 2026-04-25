import Jacobian.ComplexTorus.ChartedSpace
import Jacobian.ComplexTorus.IsManifold
import Jacobian.WorkPackets.StatementBank

/-!
# Witnesses for the StatementBank Queue B chart/manifold targets

The StatementBank file owns deliberately weak placeholder statements
(`quotientChartedSpaceStatement`, `quotientIsManifoldStatement`) for
the chart and manifold layer. With the concrete `ChartedSpace` and
`IsManifold` instances now in place, those placeholders are
dischargeable.

This module records the witness theorems separately from the
StatementBank so the bank itself stays a pure list of targets.
-/

namespace JacobianChallenge.ComplexTorus

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V]

/-- Discharge the StatementBank placeholder for the charted-space target:
the concrete `ChartedSpace` instance witnesses it. -/
theorem quotientChartedSpace_witness (Λ : FullComplexLattice V) :
    JacobianChallenge.ComplexTorus.quotientChartedSpaceStatement V Λ :=
  ⟨complexTorusChartedSpace Λ⟩

/-- Discharge the StatementBank placeholder for the manifold target:
the concrete `ChartedSpace` instance witnesses the existence-of-charts
shape currently used by `quotientIsManifoldStatement`. -/
theorem quotientIsManifold_witness (Λ : FullComplexLattice V) :
    JacobianChallenge.ComplexTorus.quotientIsManifoldStatement V Λ :=
  ⟨complexTorusChartedSpace Λ, trivial⟩

/-- Discharge the StatementBank placeholder for the Lie-add-group target.
The current `quotientLieAddGroupStatement` shape only asks for a
`ChartedSpace` witness; the actual smoothness of `+` and `-` (i.e.,
the `LieAddGroup` instance proper) is the layer above this and is
not yet built. -/
theorem quotientLieAddGroup_witness (Λ : FullComplexLattice V) :
    JacobianChallenge.ComplexTorus.quotientLieAddGroupStatement V Λ :=
  ⟨complexTorusChartedSpace Λ, trivial⟩

end JacobianChallenge.ComplexTorus
