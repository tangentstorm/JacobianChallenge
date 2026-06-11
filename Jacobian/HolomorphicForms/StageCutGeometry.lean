import Jacobian.HolomorphicForms.StageExhaustion

/-!
# One-stage cut geometry

This module records the stage-local structural payload for A3 cut geometry:
a cut domain, a cut set, their containment in one stage, and their
disjointness.  It deliberately stops before selected-compact avoidance,
marked-end bookkeeping, or any construction of simply-connected cut domains.
-/

namespace JacobianChallenge.HolomorphicForms

open Set
open scoped Topology

/--
Stage-local cut geometry for one bordered-exhaustion stage.

This is the structural part of one `StageCutSystem` fiber, separated from
eventual selected-compact and marked-end requirements.
-/
structure StageOneCutGeometry
    (X : Type*) [TopologicalSpace X] (stage : Set X) where
  cutDomain : Set X
  cutSet : Set X
  cutDomain_subset_stage : cutDomain ⊆ stage
  cutSet_subset_stage : cutSet ⊆ stage
  cutDomain_disjoint_cutSet : Disjoint cutDomain cutSet

namespace StageOneCutGeometry

variable {X : Type*} [TopologicalSpace X]
variable {stage : Set X} (G : StageOneCutGeometry X stage)

/-- The packaged cut domain lies inside the ambient stage. -/
theorem cutDomain_subset : G.cutDomain ⊆ stage :=
  G.cutDomain_subset_stage

/-- The packaged cut set lies inside the ambient stage. -/
theorem cutSet_subset : G.cutSet ⊆ stage :=
  G.cutSet_subset_stage

/-- The packaged cut domain is disjoint from the packaged cut set. -/
theorem disjoint_cutDomain_cutSet : Disjoint G.cutDomain G.cutSet :=
  G.cutDomain_disjoint_cutSet

variable [ChartedSpace ℂ X]

/--
Turn openness and simple connectedness of the packaged cut domain into the
existing conjugate-readiness predicate.
-/
theorem conjugateReady
    (hopen : IsOpen G.cutDomain)
    (hsimply : IsSimplyConnected G.cutDomain) :
    StageConjugateReady X G.cutDomain :=
  { isOpen_cutDomain := hopen
    simplyConnectedEnoughForConjugates := hsimply }

end StageOneCutGeometry

end JacobianChallenge.HolomorphicForms
