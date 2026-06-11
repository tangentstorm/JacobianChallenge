import Jacobian.HolomorphicForms.StageExhaustion

/-!
# One-stage cut geometry

This module records the stage-local structural payload for A3 cut geometry:
a cut domain, a cut set, their containment in one stage, and their
disjointness.  It deliberately stops before selected-compact avoidance,
marked-end bookkeeping, or any construction of simply-connected cut domains.
-/

namespace JacobianChallenge.HolomorphicForms

open Filter Set
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

/--
Selected-compact readiness for one packaged cut geometry: the compact set is
inside the cut domain and disjoint from the cut set.
-/
def SelectedCompactReady (K : Set X) : Prop :=
  K ⊆ G.cutDomain ∧ Disjoint K G.cutSet

/-- Build selected-compact readiness from containment and cut avoidance. -/
theorem selectedCompactReady_of_subset_disjoint {K : Set X}
    (hsubset : K ⊆ G.cutDomain) (hdisjoint : Disjoint K G.cutSet) :
    G.SelectedCompactReady K :=
  ⟨hsubset, hdisjoint⟩

/-- Read off cut-domain containment from selected-compact readiness. -/
theorem SelectedCompactReady.subset_cutDomain {K : Set X}
    (hready : G.SelectedCompactReady K) :
    K ⊆ G.cutDomain :=
  hready.1

/-- Read off cut-set avoidance from selected-compact readiness. -/
theorem SelectedCompactReady.disjoint_cutSet {K : Set X}
    (hready : G.SelectedCompactReady K) :
    Disjoint K G.cutSet :=
  hready.2

variable [ChartedSpace ℂ X]

variable {selected : StageSelectedCompactFamily X}
variable {exhaustion : StageBorderedExhaustion X selected}
variable (Gs : (n : ℕ) → StageOneCutGeometry X (exhaustion.stage n))

/--
Package eventual containment in cut domains and eventual cut avoidance into
eventual selected-compact readiness for one selected compactum.
-/
theorem eventually_selectedCompactReady
    (i : selected.Index)
    (hcontains :
      ∀ᶠ n in atTop, selected.compact i ⊆ (Gs n).cutDomain)
    (havoids :
      ∀ᶠ n in atTop, Disjoint (selected.compact i) (Gs n).cutSet) :
    ∀ᶠ n in atTop, (Gs n).SelectedCompactReady (selected.compact i) :=
  hcontains.and havoids

/--
Concrete selected-compact readiness bound obtained from eventual containment
and cut avoidance.
-/
theorem exists_selectedCompactReady_bound
    (i : selected.Index)
    (hcontains :
      ∀ᶠ n in atTop, selected.compact i ⊆ (Gs n).cutDomain)
    (havoids :
      ∀ᶠ n in atTop, Disjoint (selected.compact i) (Gs n).cutSet) :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      (Gs n).SelectedCompactReady (selected.compact i) :=
  eventually_atTop.mp
    (eventually_selectedCompactReady Gs i hcontains havoids)

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
