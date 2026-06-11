import Jacobian.HolomorphicForms.PerronStageDipoleProfile
import Jacobian.HolomorphicForms.StageExhaustion

/-!
# Stage dipole boundary-control interface

This module records the A4 statement-level boundary-control payload for the
genus-zero Perron engine.  It packages boundary data built from the marked
dipole profiles and the bordered exhaustion, but deliberately does not solve
the Dirichlet/Perron problem or construct harmonic stage maps.
-/

namespace JacobianChallenge.HolomorphicForms

open Filter Set
open scoped Topology

/--
Stage-local compact bound data for later maximum-principle and Cauchy-bound
arguments.  The predicate is packaged separately so downstream consumers can
ask only for the bound interface, without depending on how the boundary
values are produced.
-/
structure StageDipoleCompactBound
    (X : Type*) [TopologicalSpace X] (stage : Set X) (potential : X → ℝ) where
  compactSet : Set X
  compact_subset_stage : compactSet ⊆ stage
  isCompact_compactSet : IsCompact compactSet
  bound : ℝ
  boundaryPotential_boundedOn_compact :
    ∀ x ∈ compactSet, |potential x| ≤ bound

/--
Compatibility of a stage boundary potential with one finite boundary-chart
piece from the bordered exhaustion.

The actual regularity and polygon estimates are A4 frontier work.  The fields
below expose the exact handles later Dirichlet and Cauchy-bound tasks need:
which boundary piece is being controlled, the controlling chart, and a finite
bound for the stage boundary datum on that piece.
-/
structure StageBoundaryChartControl
    (X : Type*) [TopologicalSpace X] [ChartedSpace ℂ X]
    {stage : Set X} (boundaryData : StageBoundaryChartData X stage)
    (potential : X → ℝ) where
  index : boundaryData.ChartIndex
  boundaryPiece_subset_source :
    boundaryData.boundaryPiece index ⊆ (boundaryData.chart index).source
  bound : ℝ
  potential_boundedOn_piece :
    ∀ x ∈ boundaryData.boundaryPiece index, |potential x| ≤ bound

/--
The A4 boundary-control payload for one bordered exhaustion.

For each stage, it records the real boundary potential to feed into the
Perron/Dirichlet solver, normalization at the marked base point, the two
logarithmic dipole singular profiles, continuity of the boundary datum on the
stage frontier (S6 repair, `docs/perron-b2-dirichlet-phase0.md` §2.6: without
it the A4 data admits everywhere-discontinuous junk and the B2 obligation is
refutable), compatibility with the finite boundary chart data, and
compact-subdomain bounds for later estimates.  With frontier continuity and
the compact frontier, a global frontier bound is derivable, so the one-piece
`boundaryChartControl` bound is left as is.
-/
structure StageDipoleBoundaryControl
    (X : Type*) [TopologicalSpace X] [ChartedSpace ℂ X]
    (e : X ≃ₜ OnePoint ℂ)
    (marked : GenusZeroStageMarkedData X e)
    (selected : StageSelectedCompactFamily X)
    (exhaustion : StageBorderedExhaustion X selected)
    (profiles : GenusZeroStageDipoleProfiles X e marked) where
  boundaryPotential : ℕ → X → ℝ
  base_normalized :
    ∀ n, boundaryPotential n marked.base = 0
  has_pos_log_profile :
    ∀ n, HasLogarithmicSingularityAtReal X marked.P0
      (boundaryPotential n) 1
  has_neg_log_profile :
    ∀ n, HasLogarithmicSingularityAtReal X marked.Pinf
      (boundaryPotential n) (-1)
  agrees_with_u0_near_P0 :
    ∀ n, Set.EqOn (boundaryPotential n) profiles.u0 (marked.U0 \ {marked.P0})
  agrees_with_uinf_near_Pinf :
    ∀ n, Set.EqOn (boundaryPotential n) profiles.uinf (marked.Uinf \ {marked.Pinf})
  continuousOn_boundaryPotential_frontier :
    ∀ n, ContinuousOn (boundaryPotential n) (frontier (exhaustion.stage n))
  boundaryChartControl :
    ∀ n, StageBoundaryChartControl X (exhaustion.boundaryData n) (boundaryPotential n)
  compactBound :
    ∀ n, StageDipoleCompactBound X (exhaustion.stage n) (boundaryPotential n)

/--
A4 frontier obligation: build the stage boundary-control payload from marked
data, local dipole profiles, and a bordered exhaustion.

This is intentionally narrower than the Dirichlet/Perron solver: it produces
only boundary potentials and estimates, not harmonic extensions.
-/
theorem exists_stageDipoleBoundaryControl
    (X : Type*) [TopologicalSpace X] [T2Space X] [ChartedSpace ℂ X]
    (e : X ≃ₜ OnePoint ℂ)
    (marked : GenusZeroStageMarkedData X e)
    (selected : StageSelectedCompactFamily X)
    (exhaustion : StageBorderedExhaustion X selected)
    (profiles : GenusZeroStageDipoleProfiles X e marked) :
    Nonempty (StageDipoleBoundaryControl X e marked selected exhaustion profiles) := by
  sorry

end JacobianChallenge.HolomorphicForms
