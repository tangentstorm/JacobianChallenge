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

variable {e : X ≃ₜ OnePoint ℂ}
variable (marked : GenusZeroStageMarkedData X e)

/--
Marked compatibility for one packaged cut geometry: both marked ends are
outside the cut domain, while the normalization base point lies inside it.
-/
def MarkedCompatible : Prop :=
  marked.P0 ∉ G.cutDomain ∧
    marked.Pinf ∉ G.cutDomain ∧
      marked.base ∈ G.cutDomain

/-- Build marked compatibility from the two endpoint exclusions and base membership. -/
theorem markedCompatible_of_notMem_notMem_mem
    (hP0 : marked.P0 ∉ G.cutDomain)
    (hPinf : marked.Pinf ∉ G.cutDomain)
    (hbase : marked.base ∈ G.cutDomain) :
    G.MarkedCompatible marked :=
  ⟨hP0, hPinf, hbase⟩

/-- The zero-marked endpoint is outside the cut domain. -/
theorem MarkedCompatible.P0_notMem_cutDomain
    (hmarked : G.MarkedCompatible marked) :
    marked.P0 ∉ G.cutDomain :=
  hmarked.1

/-- The infinity-marked endpoint is outside the cut domain. -/
theorem MarkedCompatible.Pinf_notMem_cutDomain
    (hmarked : G.MarkedCompatible marked) :
    marked.Pinf ∉ G.cutDomain :=
  hmarked.2.1

/-- The normalization base point lies in the cut domain. -/
theorem MarkedCompatible.base_mem_cutDomain
    (hmarked : G.MarkedCompatible marked) :
    marked.base ∈ G.cutDomain :=
  hmarked.2.2

/--
Package pointwise marked-end exclusions and eventual base membership into
eventual marked compatibility for the one-stage cut geometries.
-/
theorem eventually_markedCompatible
    (hP0 : ∀ n : ℕ, marked.P0 ∉ (Gs n).cutDomain)
    (hPinf : ∀ n : ℕ, marked.Pinf ∉ (Gs n).cutDomain)
    (hbase : ∀ᶠ n in atTop, marked.base ∈ (Gs n).cutDomain) :
    ∀ᶠ n in atTop, (Gs n).MarkedCompatible marked :=
  hbase.mono fun n hn =>
    markedCompatible_of_notMem_notMem_mem
      (Gs n) marked (hP0 n) (hPinf n) hn

/--
Concrete marked-compatibility bound obtained from pointwise marked-end
exclusions and eventual base membership.
-/
theorem exists_markedCompatible_bound
    (hP0 : ∀ n : ℕ, marked.P0 ∉ (Gs n).cutDomain)
    (hPinf : ∀ n : ℕ, marked.Pinf ∉ (Gs n).cutDomain)
    (hbase : ∀ᶠ n in atTop, marked.base ∈ (Gs n).cutDomain) :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n → (Gs n).MarkedCompatible marked :=
  eventually_atTop.mp (eventually_markedCompatible Gs marked hP0 hPinf hbase)

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

/--
Assemble a marked cut system from a sequence of already-packaged one-stage cut
geometries and the remaining global compatibility hypotheses.
-/
def stageMarkedCutSystem_of_stageOneCutGeometry_sequence
    {X : Type*} [TopologicalSpace X] [ChartedSpace ℂ X]
    {e : X ≃ₜ OnePoint ℂ}
    (marked : GenusZeroStageMarkedData X e)
    {selected : StageSelectedCompactFamily X}
    (exhaustion : StageBorderedExhaustion X selected)
    (Gs : (n : ℕ) → StageOneCutGeometry X (exhaustion.stage n))
    (hcontains :
      ∀ i, ∀ᶠ n in atTop, selected.compact i ⊆ (Gs n).cutDomain)
    (havoids :
      ∀ i, ∀ᶠ n in atTop, Disjoint (selected.compact i) (Gs n).cutSet)
    (hready : ∀ n, StageConjugateReady X (Gs n).cutDomain)
    (hP0 : ∀ n, marked.P0 ∉ (Gs n).cutDomain)
    (hPinf : ∀ n, marked.Pinf ∉ (Gs n).cutDomain)
    (hbase : ∀ᶠ n in atTop, marked.base ∈ (Gs n).cutDomain) :
    StageMarkedCutSystem X marked selected exhaustion :=
  { cutDomain := fun n => (Gs n).cutDomain
    cutSet := fun n => (Gs n).cutSet
    cutDomain_subset_stage := fun n => (Gs n).cutDomain_subset_stage
    cutSet_subset_stage := fun n => (Gs n).cutSet_subset_stage
    cutDomain_disjoint_cutSet := fun n => (Gs n).cutDomain_disjoint_cutSet
    eventually_contains_selected := hcontains
    cuts_avoid_selected_eventually := havoids
    conjugateReady := hready
    P0_notMem_cutDomain := hP0
    Pinf_notMem_cutDomain := hPinf
    eventually_base_mem := hbase }

end JacobianChallenge.HolomorphicForms
