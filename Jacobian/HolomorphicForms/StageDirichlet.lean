import Jacobian.HolomorphicForms.StageDipoleBoundary
import Jacobian.HolomorphicForms.StageEventualContainment

/-!
# Stage Dirichlet harmonic-solution interface

This module records the B2 statement-level Perron/Dirichlet solution payload
for the genus-zero engine.  It consumes the existing stage exhaustion,
eventual-containment, and dipole boundary-control interfaces, but deliberately
does not construct harmonic conjugates, holomorphic stage maps, or Montel
limits.
-/

namespace JacobianChallenge.HolomorphicForms

open Set
open scoped Topology

/--
Consumer-facing harmonicity predicate for one real stage potential.

The predicate is phrased in the project's existing local-conjugate language:
on the active stage, away from the two marked singular points, the potential
admits a harmonic conjugate uniformly on a neighborhood contained in the
stage.  The shared neighborhood witness rules out vacuous one-point affine
conjugates and is the stage-local version of the contentful harmonic-off
interface already used by the dipole library.
-/
def StageHarmonicOn
    (X : Type*) [TopologicalSpace X] [ChartedSpace ℂ X]
    {e : X ≃ₜ OnePoint ℂ} (marked : GenusZeroStageMarkedData X e)
    (stage : Set X) (potential : X → ℝ) : Prop :=
  ∀ x, x ∈ stage → x ≠ marked.P0 → x ≠ marked.Pinf →
    ∃ U : Set X, IsOpen U ∧ x ∈ U ∧ U ⊆ stage ∧
      ∃ conjugate : X → ℝ,
        ∀ y, y ∈ U → IsHarmonicConjugateAtReal X potential conjugate y

/--
Boundary agreement over every finite boundary-chart piece in the A2 bordered
stage data.
-/
def StageBoundaryAgreement
    (X : Type*) [TopologicalSpace X] [ChartedSpace ℂ X]
    {stage : Set X} (boundaryData : StageBoundaryChartData X stage)
    (solution boundaryPotential : X → ℝ) : Prop :=
  ∀ i, Set.EqOn solution boundaryPotential (boundaryData.boundaryPiece i)

/--
The B2 Dirichlet/Perron solution payload for all bordered stages.

It packages one real solution per stage, neighborhood-uniform harmonicity on
the stage away from the marked singular points, agreement with the A4 boundary
datum on each finite boundary-chart piece, inherited base normalization and
logarithmic singular behavior, and compact-subdomain bounds for later Cauchy
estimates.
-/
structure StageDirichletHarmonicSolution
    (X : Type*) [TopologicalSpace X] [ChartedSpace ℂ X]
    (e : X ≃ₜ OnePoint ℂ)
    (marked : GenusZeroStageMarkedData X e)
    (selected : StageSelectedCompactFamily X)
    (exhaustion : StageBorderedExhaustion X selected)
    (profiles : GenusZeroStageDipoleProfiles X e marked)
    (boundaryControl :
      StageDipoleBoundaryControl X e marked selected exhaustion profiles) where
  harmonicPotential : ℕ → X → ℝ
  harmonicOn_stage :
    ∀ n, StageHarmonicOn X marked (exhaustion.stage n) (harmonicPotential n)
  agrees_boundary :
    ∀ n, StageBoundaryAgreement X (exhaustion.boundaryData n)
      (harmonicPotential n) (boundaryControl.boundaryPotential n)
  base_normalized :
    ∀ n, harmonicPotential n marked.base = 0
  has_pos_log_profile :
    ∀ n, HasLogarithmicSingularityAtReal X marked.P0
      (harmonicPotential n) 1
  has_neg_log_profile :
    ∀ n, HasLogarithmicSingularityAtReal X marked.Pinf
      (harmonicPotential n) (-1)
  compactBound :
    ∀ n, StageDipoleCompactBound X (exhaustion.stage n) (harmonicPotential n)
  boundaryCompactBound :
    ∀ n, StageDipoleCompactBound X (exhaustion.stage n)
      (boundaryControl.boundaryPotential n)
  boundaryCompactBound_eq :
    ∀ n, boundaryCompactBound n = boundaryControl.compactBound n

namespace StageDirichletHarmonicSolution

variable {X : Type*} [TopologicalSpace X] [ChartedSpace ℂ X]
variable {e : X ≃ₜ OnePoint ℂ}
variable {marked : GenusZeroStageMarkedData X e}
variable {selected : StageSelectedCompactFamily X}
variable {exhaustion : StageBorderedExhaustion X selected}
variable {profiles : GenusZeroStageDipoleProfiles X e marked}
variable {boundaryControl :
  StageDipoleBoundaryControl X e marked selected exhaustion profiles}

/-- The A4 boundary compact bounds are available from any B2 solution package. -/
theorem boundaryCompactBound_eq_boundaryControl
    (solution :
      StageDirichletHarmonicSolution X e marked selected exhaustion profiles
        boundaryControl)
    (n : ℕ) :
    solution.boundaryCompactBound n = boundaryControl.compactBound n := by
  exact solution.boundaryCompactBound_eq n

end StageDirichletHarmonicSolution

/--
B2 frontier obligation: solve the normalized stage Dirichlet/Perron problem
for the A4 boundary-control data.

This is intentionally narrower than the later harmonic-conjugate and
holomorphic-coordinate stages: it produces only real harmonic potentials with
boundary agreement, singular profile, normalization, and compact-bound data.
-/
theorem exists_stageDirichletHarmonicSolution
    (X : Type*) [TopologicalSpace X] [T2Space X] [ChartedSpace ℂ X]
    (e : X ≃ₜ OnePoint ℂ)
    (marked : GenusZeroStageMarkedData X e)
    (selected : StageSelectedCompactFamily X)
    (exhaustion : StageBorderedExhaustion X selected)
    (profiles : GenusZeroStageDipoleProfiles X e marked)
    (boundaryControl :
      StageDipoleBoundaryControl X e marked selected exhaustion profiles) :
    Nonempty
      (StageDirichletHarmonicSolution X e marked selected exhaustion profiles
        boundaryControl) := by
  sorry

end JacobianChallenge.HolomorphicForms
