import Jacobian.HolomorphicForms.PerronPoissonBoundary
import Jacobian.HolomorphicForms.PerronRemovableSingularity

/-!
# W6 adapter: the disc Dirichlet obligation, discharged (Perron engine B2 toolbox)

Blueprint node: `lem:perron-removable-singularity` (W6 of
`docs/perron-b2-dirichlet-phase0.md` §4); tracking #232.

`DiscDirichletInput`, the W3 named obligation of the W6
removable-singularity file, is exactly the solvability of the disc
Dirichlet problem for continuous circle data — which is what jc6's W3d
M4 closed-ball packaging (`PerronPoissonBoundary.lean`) provides.  This
file is the thin consumer adapter: zero analytical content, pure
obtain-and-apply.  The witness is `poissonSolution g c r`; harmonicity
on the open ball is `poissonSolution_harmonicOnNhd`, continuity on the
closed ball is `continuousOn_poissonSolution`, and the sphere `EqOn` is
the extension's off-ball branch (`poissonSolution_apply_of_mem_sphere`).
-/

namespace JacobianChallenge.HolomorphicForms

open Metric

/--
The disc Dirichlet problem is solvable for continuous circle data:
the W3 obligation of the W6 removable-singularity file, discharged by
jc6's W3d M4 closed-ball Dirichlet packaging.
-/
theorem discDirichletInput_of_poissonOperator : DiscDirichletInput :=
  fun c r hr g hg =>
    ⟨poissonSolution g c r, poissonSolution_harmonicOnNhd hr hg,
      continuousOn_poissonSolution hr hg,
      fun _ hz => poissonSolution_apply_of_mem_sphere hz⟩

end JacobianChallenge.HolomorphicForms
