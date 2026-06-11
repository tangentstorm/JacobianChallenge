import Jacobian.HolomorphicForms.StageDirichlet
import Jacobian.HolomorphicForms.StageEventualContainment

/-!
# Stage harmonic conjugates on cuts

This module records the B4 statement-level payload for choosing
single-valued harmonic conjugates on the cut stage domains.  It consumes the
A3 marked cut-system interface and the B2 real harmonic stage solutions, but
deliberately does not construct holomorphic stage coordinates or Montel
limits.
-/

namespace JacobianChallenge.HolomorphicForms

open Filter
open Set
open scoped Topology

/--
Pointwise conjugacy of a stage conjugate to the B2 harmonic potential on one
cut domain, away from the two marked singular points.
-/
def StageConjugateOnCut
    (X : Type*) [TopologicalSpace X] [ChartedSpace ℂ X]
    {e : X ≃ₜ OnePoint ℂ} (marked : GenusZeroStageMarkedData X e)
    (cutDomain : Set X) (potential conjugate : X → ℝ) : Prop :=
  ∀ x, x ∈ cutDomain → x ≠ marked.P0 → x ≠ marked.Pinf →
    IsHarmonicConjugateAtReal X potential conjugate x

/--
Selected-compact compatibility for one stage conjugate: a selected compactum
lies in the active cut domain and is disjoint from the cuts.  The actual
thresholds are supplied by `StageEventualContainment`; this predicate is the
B4 consumer-facing per-stage shape.
-/
def StageConjugateSelectedCompactReady
    (X : Type*) [TopologicalSpace X]
    (K cutDomain cutSet : Set X) : Prop :=
  K ⊆ cutDomain ∧ Disjoint K cutSet

/--
The B4 harmonic-conjugate payload for all cut stages.

It records one real conjugate per stage, compatibility with the A3
`StageConjugateReady` witness, marked-end exclusion from the cut domain,
pointwise conjugacy to the B2 potential on the cut domain, additive phase
normalization, and selected-compact compatibility interfaces needed before
chart-ball packaging.
-/
structure StageHarmonicConjugatesOnCuts
    (X : Type*) [TopologicalSpace X] [ChartedSpace ℂ X]
    (e : X ≃ₜ OnePoint ℂ)
    (marked : GenusZeroStageMarkedData X e)
    (selected : StageSelectedCompactFamily X)
    (exhaustion : StageBorderedExhaustion X selected)
    (profiles : GenusZeroStageDipoleProfiles X e marked)
    (boundaryControl :
      StageDipoleBoundaryControl X e marked selected exhaustion profiles)
    (cutSystem : StageMarkedCutSystem X marked selected exhaustion)
    (dirichlet :
      StageDirichletHarmonicSolution X e marked selected exhaustion profiles
        boundaryControl) where
  harmonicConjugate : ℕ → X → ℝ
  conjugateReady :
    ∀ n, StageConjugateReady X (cutSystem.cutDomain n)
  conjugateReady_eq_cutSystem :
    ∀ n, conjugateReady n = cutSystem.conjugateReady n
  conjugateOnCut :
    ∀ n, StageConjugateOnCut X marked (cutSystem.cutDomain n)
      (dirichlet.harmonicPotential n) (harmonicConjugate n)
  base_phase_normalized :
    ∀ n, marked.base ∈ cutSystem.cutDomain n →
      harmonicConjugate n marked.base = 0
  eventually_compactReady :
    ∀ i, ∀ᶠ n in atTop, StageConjugateSelectedCompactReady X
      (selected.compact i) (cutSystem.cutDomain n) (cutSystem.cutSet n)
  compactReadyBound :
    ∀ i, ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      StageConjugateSelectedCompactReady X (selected.compact i)
        (cutSystem.cutDomain n) (cutSystem.cutSet n)
  compactBound :
    ∀ n, StageDipoleCompactBound X (exhaustion.stage n)
      (dirichlet.harmonicPotential n)
  compactBound_eq_dirichlet :
    ∀ n, compactBound n = dirichlet.compactBound n

namespace StageHarmonicConjugatesOnCuts

variable {X : Type*} [TopologicalSpace X] [ChartedSpace ℂ X]
variable {e : X ≃ₜ OnePoint ℂ}
variable {marked : GenusZeroStageMarkedData X e}
variable {selected : StageSelectedCompactFamily X}
variable {exhaustion : StageBorderedExhaustion X selected}
variable {profiles : GenusZeroStageDipoleProfiles X e marked}
variable {boundaryControl :
  StageDipoleBoundaryControl X e marked selected exhaustion profiles}
variable {cutSystem : StageMarkedCutSystem X marked selected exhaustion}
variable {dirichlet :
  StageDirichletHarmonicSolution X e marked selected exhaustion profiles
    boundaryControl}

/-- The B4 package exposes the same cut-readiness witness as the A3 cut system. -/
theorem conjugateReady_eq
    (conjugates :
      StageHarmonicConjugatesOnCuts X e marked selected exhaustion profiles
        boundaryControl cutSystem dirichlet)
    (n : ℕ) :
    conjugates.conjugateReady n = cutSystem.conjugateReady n :=
  conjugates.conjugateReady_eq_cutSystem n

/-- The B2 compact bounds remain available from the B4 package. -/
theorem compactBound_eq_dirichlet'
    (conjugates :
      StageHarmonicConjugatesOnCuts X e marked selected exhaustion profiles
        boundaryControl cutSystem dirichlet)
    (n : ℕ) :
    conjugates.compactBound n = dirichlet.compactBound n :=
  conjugates.compactBound_eq_dirichlet n

end StageHarmonicConjugatesOnCuts

/--
B4 frontier obligation: choose globally compatible single-valued harmonic
conjugates on the cut domains for the B2 stage solutions.

This is intentionally narrower than holomorphic coordinate construction: it
produces only real conjugates and their cut-domain compatibility data.
-/
theorem exists_stageHarmonicConjugatesOnCuts
    (X : Type*) [TopologicalSpace X] [T2Space X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X]
    (e : X ≃ₜ OnePoint ℂ)
    (marked : GenusZeroStageMarkedData X e)
    (selected : StageSelectedCompactFamily X)
    (exhaustion : StageBorderedExhaustion X selected)
    (profiles : GenusZeroStageDipoleProfiles X e marked)
    (boundaryControl :
      StageDipoleBoundaryControl X e marked selected exhaustion profiles)
    (cutSystem : StageMarkedCutSystem X marked selected exhaustion)
    (dirichlet :
      StageDirichletHarmonicSolution X e marked selected exhaustion profiles
        boundaryControl) :
    Nonempty
      (StageHarmonicConjugatesOnCuts X e marked selected exhaustion profiles
        boundaryControl cutSystem dirichlet) := by
  sorry

end JacobianChallenge.HolomorphicForms
