import Jacobian.HolomorphicForms.OnePointCxIsManifold
import Jacobian.HolomorphicForms.PerronStageMarkedData
import Mathlib.AlgebraicTopology.FundamentalGroupoid.SimplyConnected

/-!
# Stage exhaustion and cut-system interfaces

This module records the statement-level A2/A3 topology interfaces for the
genus-zero Perron engine.  The declarations intentionally stop at bordered
stage domains and compatible cut domains; Perron/Dirichlet existence, harmonic
conjugates, and stage-map construction are downstream consumers.
-/

namespace JacobianChallenge.HolomorphicForms

open Filter Set
open scoped Topology

/--
The selected compacta that later Montel and chart-ball arguments require the
stage domains to contain eventually.
-/
structure StageSelectedCompactFamily (X : Type*) [TopologicalSpace X] where
  Index : Type
  compact : Index → Set X
  isCompact_compact : ∀ i, IsCompact (compact i)

/--
Finite chart control for the boundary of one bordered or chart-polygon stage.

The `boundaryPiece` fields are deliberately topological: downstream analytic
tasks may strengthen their regularity locally, but A2 only has to expose a
finite chart cover of the frontier.

The pieces are required to lie inside the stage frontier (S1 repair,
`docs/perron-b2-dirichlet-phase0.md` §2.1): without this, a piece may cover
the whole closed stage, which makes the downstream B2 Dirichlet obligation
refutable by forcing the solution to agree with non-harmonic boundary data on
an open subset of the stage.
-/
structure StageBoundaryChartData
    (X : Type*) [TopologicalSpace X] [ChartedSpace ℂ X] (stage : Set X) where
  ChartIndex : Type
  chart_fintype : Fintype ChartIndex
  chart : ChartIndex → OpenPartialHomeomorph X ℂ
  boundaryPiece : ChartIndex → Set X
  boundaryPiece_subset_source :
    ∀ i, boundaryPiece i ⊆ (chart i).source
  boundaryPiece_subset_frontier :
    ∀ i, boundaryPiece i ⊆ frontier stage
  frontier_subset_boundaryPieces :
    frontier stage ⊆ ⋃ i, boundaryPiece i

/--
Bordered exhaustion domains for the genus-zero Perron engine.

The fields are exactly the A2 payload: open stages, monotonicity, eventual
containment of selected compacta, and finite source-chart control of each
stage frontier.
-/
structure StageBorderedExhaustion
    (X : Type*) [TopologicalSpace X] [ChartedSpace ℂ X]
    (selected : StageSelectedCompactFamily X) where
  stage : ℕ → Set X
  isOpen_stage : ∀ n, IsOpen (stage n)
  monotone_stage : ∀ {m n}, m ≤ n → stage m ⊆ stage n
  eventually_contains_selected :
    ∀ i, ∀ᶠ n in atTop, selected.compact i ⊆ stage n
  boundaryData : ∀ n, StageBoundaryChartData X (stage n)

/--
The A3 "simply-connected enough" interface consumed by harmonic-conjugate
tasks.  It is intentionally packaged as a named predicate so B4 can require
this interface without depending on the eventual proof mechanism for cuts.
-/
structure StageConjugateReady
    (X : Type*) [TopologicalSpace X] [ChartedSpace ℂ X]
    (cutDomain : Set X) : Prop where
  isOpen_cutDomain : IsOpen cutDomain
  simplyConnectedEnoughForConjugates : IsSimplyConnected cutDomain

/--
A cut system compatible with a bordered exhaustion.

The fields are the A3 payload: each cut domain lies inside its stage, the cuts
avoid the selected compacta eventually, and every cut domain carries the
single-valued-conjugate readiness interface.
-/
structure StageCutSystem
    (X : Type*) [TopologicalSpace X] [ChartedSpace ℂ X]
    (selected : StageSelectedCompactFamily X)
    (exhaustion : StageBorderedExhaustion X selected) where
  cutDomain : ℕ → Set X
  cutSet : ℕ → Set X
  cutDomain_subset_stage :
    ∀ n, cutDomain n ⊆ exhaustion.stage n
  cutSet_subset_stage :
    ∀ n, cutSet n ⊆ exhaustion.stage n
  cutDomain_disjoint_cutSet :
    ∀ n, Disjoint (cutDomain n) (cutSet n)
  eventually_contains_selected :
    ∀ i, ∀ᶠ n in atTop, selected.compact i ⊆ cutDomain n
  cuts_avoid_selected_eventually :
    ∀ i, ∀ᶠ n in atTop, Disjoint (selected.compact i) (cutSet n)
  conjugateReady :
    ∀ n, StageConjugateReady X (cutDomain n)

/--
A marked-aware cut system compatible with a bordered exhaustion.

This wrapper is the R1/R4 amendment consumed by the B4 conjugate interface:
it keeps the existing unmarked `StageCutSystem` available for generic
eventual-containment algebra, and adds the genus-zero marked-end facts needed
to avoid the classical logarithmic-period obstruction.
-/
structure StageMarkedCutSystem
    (X : Type*) [TopologicalSpace X] [ChartedSpace ℂ X]
    {e : X ≃ₜ OnePoint ℂ} (marked : GenusZeroStageMarkedData X e)
    (selected : StageSelectedCompactFamily X)
    (exhaustion : StageBorderedExhaustion X selected)
    extends StageCutSystem X selected exhaustion where
  P0_notMem_cutDomain :
    ∀ n, marked.P0 ∉ cutDomain n
  Pinf_notMem_cutDomain :
    ∀ n, marked.Pinf ∉ cutDomain n
  eventually_base_mem :
    ∀ᶠ n in atTop, marked.base ∈ cutDomain n

/--
A2 frontier obligation: build the adapted bordered exhaustion from the
topological genus-zero input and selected compacta.
-/
theorem exists_stageBorderedExhaustion
    (X : Type*) [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X]
    (_e : X ≃ₜ OnePoint ℂ)
    (selected : StageSelectedCompactFamily X) :
    Nonempty (StageBorderedExhaustion X selected) := by
  sorry

/--
A3 frontier obligation: choose cuts compatible with a fixed bordered
exhaustion so harmonic conjugates can be made single-valued on each cut stage.
-/
theorem exists_stageCutSystem
    (X : Type*) [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X]
    (e : X ≃ₜ OnePoint ℂ)
    (marked : GenusZeroStageMarkedData X e)
    (selected : StageSelectedCompactFamily X)
    (exhaustion : StageBorderedExhaustion X selected) :
    Nonempty (StageMarkedCutSystem X marked selected exhaustion) := by
  sorry

end JacobianChallenge.HolomorphicForms
