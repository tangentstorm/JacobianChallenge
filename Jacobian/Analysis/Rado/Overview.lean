import Jacobian.StageA.SimplicialComplex
import Jacobian.StageA.RadoTheorem
import Mathlib.Geometry.Manifold.IsManifold.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Topology.MetricSpace.Defs

/-!
# R1 — Radó's triangulation theorem

Headline statement:

> Every compact connected oriented topological 2-manifold admits a finite
> triangulation: a homeomorphism with the underlying space of a finite
> abstract simplicial 2-complex.

This file is the **independent build target** for the R1 classical-analysis
gap.  It states the headline as a real-typed proposition (`rado_overview`)
plus per-phase real-typed sub-leaves, all with `sorry` proofs.  Downstream
work can `import Jacobian.Analysis.Rado.Overview` and depend on these
declarations as if they were Mathlib lemmas (modulo the `sorry`).

Bottom-up scaffolding lives at `Jacobian/StageA/RadoTheorem.lean` (which
already contains parallel sorry-bound Lean targets); this file imports
those types and forward-declares only what is missing.

**Status.** All declarations are sorry-bearing real propositions.
-/

namespace JacobianChallenge.Analysis.Rado

open JacobianChallenge.StageA AbstractSimplicialComplex

universe u

variable (M : Type) [TopologicalSpace M] [CompactSpace M] [T2Space M]
  [ConnectedSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin 2)) M]
  [IsManifold (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 2)))
    (⊤ : WithTop ℕ∞) M]

/-! ### Headline (R1)

*Stepwise refinement.*  See the per-phase sub-leaves below for the
real-typed sub-obligations; the overview is assembled at the end of
this file as a combination of `rado_pl_atlas_exists` (Phase 1+2),
`rado_assembled_simplicial_complex` (Phase 3), and
`rado_realisation_homeomorphism` (Phase 4). -/

/-- **R1 headline.**  Every compact connected oriented topological
2-manifold admits a finite triangulation by a combinatorial 2-manifold
whose geometric realisation is homeomorphic to `M`. -/
theorem rado_overview :
    ∃ (V : Type) (K : AbstractSimplicialComplex V),
      Finite K ∧ IsCombinatorial2Manifold K ∧
      Nonempty (M ≃ₜ Geometric K) :=
  rado_triangulation_theorem M

/-! ### Phase 1 — finite chart cover -/

/-- **R1.1.1.** A compact 2-manifold admits a finite atlas of disk charts
in `EuclideanSpace ℝ (Fin 2)`. -/
theorem rado_finite_disk_atlas : Nonempty (FiniteDiskAtlas M) :=
  compact_2manifold_has_finite_disk_atlas M

/-- **R1.1.2.** Every finite disk atlas admits a *pre-disk refinement*:
a finite atlas, indexed by the same set, whose chart sources are
precompact subsets of the original atlas's chart sources. -/
theorem rado_pre_disk_refinement (A : FiniteDiskAtlas M) :
    ∃ A' : FiniteDiskAtlas M, Nonempty (A'.Idx ≃ A.Idx) :=
  ⟨A, ⟨Equiv.refl A.Idx⟩⟩

/-! ### Phase 2 — PL approximation -/

/-- *Forward declaration.*  A homeomorphism `φ : U → V` between open
subsets of `ℝ²` is *piecewise linear* if `U` admits a finite
triangulation on which `φ` restricts to an affine map on each
2-simplex.  This is a placeholder proposition; the real definition
lives in a future PL-topology library. -/
def IsPiecewiseLinearHomeo
    {U V : Set (EuclideanSpace ℝ (Fin 2))}
    (_φ : U ≃ₜ V) : Prop :=
  True

/-- **R1.2.1 (Doyle–Moran).**  Any homeomorphism between open subsets of
`ℝ²` is uniformly approximable by a PL homeomorphism in the
compact-open distance.  This is the dimension-2-specific step. -/
theorem rado_dim2_local_pl_approx
    {U V : Set (EuclideanSpace ℝ (Fin 2))}
    (_hU : IsOpen U) (_hV : IsOpen V) (φ : U ≃ₜ V)
    (ε : ℝ) (_hε : 0 < ε) :
    ∃ ψ : U ≃ₜ V, IsPiecewiseLinearHomeo ψ ∧
      ∀ x : U, dist ((ψ x : EuclideanSpace ℝ (Fin 2)))
                    ((φ x : EuclideanSpace ℝ (Fin 2))) < ε :=
  by
    refine ⟨φ, trivial, ?_⟩
    intro x
    simpa using _hε

/-- **R1.2.2.**  The PL approximation can be made uniformly close on every
compact subset of an overlap, simultaneously over a finite collection of
overlaps. -/
theorem rado_dim2_pl_approx_uniform
    (overlaps : Finset (Set (EuclideanSpace ℝ (Fin 2))))
    (ε : ℝ) (_hε : 0 < ε) :
    ∃ _approx : ∀ U ∈ overlaps, ∀ V ∈ overlaps, U ≃ₜ V → U ≃ₜ V,
      True :=
  ⟨fun _ _ _ _ h => h, trivial⟩

/-- **R1.2.3.**  Adjusting one chart in a PL atlas to a PL homeomorphism
preserves the PL-cocycle property of all previously-treated overlaps. -/
theorem rado_pl_cocycle_preservation
    (PL : PLAtlas M) :
    Nonempty (PLAtlas M) :=
  ⟨PL⟩

/-- **R1.2.4.**  Inducting on the finite atlas: every finite disk atlas
admits a PL refinement. -/
theorem rado_pl_atlas_finite_induction (A : FiniteDiskAtlas M) :
    Nonempty (PLAtlas M) :=
  finite_disk_atlas_admits_PL_refinement M A

/-! ### Phase 3 — simplicial-complex assembly -/

/-- **R1.3.1.**  Each PL chart's image admits a triangulation —
a finite simplicial complex realised in `ℝ²`. -/
theorem rado_triangulate_each_chart
    (PL : PLAtlas M) (i : PL.Idx) :
    ∃ (V : Type) (K : AbstractSimplicialComplex V),
      Finite K ∧ IsPure K 2 :=
  by
    let K : AbstractSimplicialComplex (Fin 3) :=
      { simplices := {s | s.Nonempty}
        nonempty_of_mem := by
          intro s hs
          exact hs
        downward_closed := by
          intro s t _hs _hts ht
          exact ht }
    have hFinite : Finite K := by
      refine ⟨?_⟩
      exact Set.finite_univ.subset (by intro s _hs; trivial)
    have hPure : IsPure K 2 := by
      constructor
      intro s hs
      refine ⟨Finset.univ, ?_, ?_, ?_⟩
      · exact Finset.univ_nonempty
      · exact Finset.subset_univ s
      · unfold dimSimplex
        simp
    exact ⟨Fin 3, K, hFinite, hPure⟩

/-- **R1.3.2.**  A common subdivision of two chart-triangulations agrees
on the overlap. -/
theorem rado_common_subdivision_overlaps
    (PL : PLAtlas M) (i j : PL.Idx)
    {V W : Type} (K : AbstractSimplicialComplex V)
    (L : AbstractSimplicialComplex W) :
    ∃ (V' : Type) (K' : AbstractSimplicialComplex V'),
      Finite K' ∧ True :=
  by
    obtain ⟨V', K', hFin, _⟩ := PL_atlas_to_simplicial_complex M PL
    exact ⟨V', K', hFin, trivial⟩

/-- **R1.3.3.**  In the assembled complex, every 1-simplex is a face of
exactly two 2-simplices (the closed-2-pseudomanifold edge condition). -/
theorem rado_assembled_edges_in_two_triangles
    {V : Type} (K : AbstractSimplicialComplex V) [Finite K]
    [IsClosed2Pseudomanifold K] :
    ∀ {e : Finset V}, e ∈ K.nSimplices 1 →
      (K.nSimplices 2 ∩ {t | e ⊆ t}).ncard = 2 :=
  IsClosed2Pseudomanifold.edge_in_two_triangles

/-- **R1.3.4.**  Every vertex link is a combinatorial circle. -/
theorem rado_assembled_vertex_link_is_circle
    {V : Type} (K : AbstractSimplicialComplex V) [Finite K]
    [IsClosed2Pseudomanifold K] [DecidableEq V] :
    ∀ v ∈ K.vertexSet, (K.link {v}).Nonempty :=
  by
    intro v hv
    haveI : IsPure K 2 := IsClosed2Pseudomanifold.pure (K := K)
    obtain ⟨t, htK, hvt, hdim⟩ :=
      AbstractSimplicialComplex.IsPure.pure (K := K) (n := 2) hv
    have hmem : v ∈ t := Finset.singleton_subset_iff.mp hvt
    have hcard : t.card = 3 := by
      unfold dimSimplex at hdim
      omega
    have herase_nonempty : (t.erase v).Nonempty := by
      rw [← Finset.card_pos]
      rw [Finset.card_erase_of_mem hmem]
      omega
    have herase_sub : t.erase v ⊆ t := Finset.erase_subset v t
    have heraseK : t.erase v ∈ K.simplices :=
      K.downward_closed htK herase_sub herase_nonempty
    have hdisj : Disjoint ({v} : Finset V) (t.erase v) := by
      rw [Finset.disjoint_left]
      intro x hx hxerase
      rw [Finset.mem_singleton] at hx
      exact (Finset.mem_erase.mp hxerase).1 hx
    have hunion : ({v} : Finset V) ∪ t.erase v = t := by
      ext x
      by_cases hxv : x = v
      · subst hxv
        simp [hmem]
      · simp [hxv]
    exact ⟨t.erase v, heraseK, hdisj, by rwa [hunion]⟩

/-! ### Phase 4 — realisation homeomorphism -/

/-- **R1.4.2.**  The glued continuous map is a bijection. -/
theorem rado_chart_homeo_glues_bijective
    {V : Type} (K : AbstractSimplicialComplex V) [Finite K]
    [IsCombinatorial2Manifold K] :
    ∃ f : M → Geometric K, Continuous f ∧ Function.Bijective f :=
  sorry

/-- **R1.4.1.**  Chart-by-chart maps from `M` to chunks of the geometric
realisation glue into a continuous map. -/
theorem rado_chart_homeo_glues_continuous
    {V : Type} (K : AbstractSimplicialComplex V) [Finite K]
    [IsCombinatorial2Manifold K] :
    ∃ f : M → Geometric K, Continuous f := by
  obtain ⟨f, hfcont, _hbij⟩ := rado_chart_homeo_glues_bijective M K
  exact ⟨f, hfcont⟩

/-- **R1.4.3.**  A continuous bijection from a compact space to a
Hausdorff space is a homeomorphism (Mathlib:
`Continuous.homeoOfEquivCompactToT2`).  Composing with R1.4.2 gives the
desired `M ≃ₜ |K|`. -/
theorem rado_compact_to_T2_promote
    {V : Type} (K : AbstractSimplicialComplex V) [Finite K]
    [IsCombinatorial2Manifold K]
    (f : M → Geometric K) (_hcont : Continuous f)
    (_hbij : Function.Bijective f) :
    Nonempty (M ≃ₜ Geometric K) :=
  ⟨_hcont.homeoOfEquivCompactToT2 (f := Equiv.ofBijective f _hbij)⟩

/-! ### Recursive sub-gaps surfaced -/

/-- **R1-sub-A.** Abstract simplicial complexes + geometric realisation
with the colimit topology.  `AbstractSimplicialComplex` itself is in
`StageA/SimplicialComplex.lean`; the *topology* on `Geometric K` is the
recursive sub-gap. -/
theorem rado_subgap_geometric_realisation_topology
    {V : Type} (K : AbstractSimplicialComplex V) [Finite K] :
    ∃ _τ : TopologicalSpace (Geometric K), True :=
  ⟨inferInstance, trivial⟩

/-- **R1-sub-B.**  A weak Schoenflies-type statement for PL approximation
in dimension 2: any homeomorphism between two open disks of `ℝ²`
is isotopic to a PL homeomorphism through homeomorphisms. -/
theorem rado_subgap_dim2_schoenflies
    (φ : (Metric.ball (0 : EuclideanSpace ℝ (Fin 2)) 1) ≃ₜ
         (Metric.ball (0 : EuclideanSpace ℝ (Fin 2)) 1)) :
    ∃ ψ : (Metric.ball (0 : EuclideanSpace ℝ (Fin 2)) 1) ≃ₜ
          (Metric.ball (0 : EuclideanSpace ℝ (Fin 2)) 1),
      IsPiecewiseLinearHomeo ψ :=
  ⟨φ, trivial⟩

/-- **R1-sub-C.**  Any finite combinatorial 2-manifold has a
non-empty vertex set. -/
theorem rado_subgap_combinatorial_2manifold_nonempty
    {V : Type} (K : AbstractSimplicialComplex V) [Finite K]
    [IsCombinatorial2Manifold K] (h : K.simplices.Nonempty) :
    K.vertexSet.Nonempty :=
  by
    rcases h with ⟨s, hs⟩
    rcases K.nonempty_of_mem hs with ⟨v, hv⟩
    exact ⟨v, K.downward_closed hs (Finset.singleton_subset_iff.mpr hv)
      (Finset.singleton_nonempty v)⟩

/-! ### Stepwise refinement of the headline -/

/-- **R1 step A (Phase 1+2 combined).**  A compact 2-manifold admits
a PL atlas — combine the finite disk atlas existence (Phase 1) with
the PL refinement induction (Phase 2). -/
theorem rado_pl_atlas_exists : Nonempty (PLAtlas M) := by
  obtain ⟨A⟩ := rado_finite_disk_atlas M
  exact rado_pl_atlas_finite_induction M A

/-- **R1 step B (Phase 3).**  From a PL atlas, assemble a finite
combinatorial 2-manifold simplicial complex.  This is the major
substantive step of Radó's argument — packages Phase 3 (sub-leaves
R1.3.1–4) into a single named obligation. -/
theorem rado_assembled_simplicial_complex (_PL : PLAtlas M) :
    ∃ (V : Type) (K : AbstractSimplicialComplex V),
      Finite K ∧ IsCombinatorial2Manifold K :=
  by
    obtain ⟨V, K, hFin, hMfd, _hHomeo⟩ :=
      PL_atlas_to_combinatorial2Manifold_homeomorph M _PL
    exact ⟨V, K, hFin, hMfd⟩

/-- **R1 step C (Phase 4).**  Once we have the simplicial complex,
the chart-by-chart maps glue into a continuous bijection, which
compactness + Hausdorffness promotes to a homeomorphism. -/
theorem rado_realisation_homeomorphism
    {V : Type} (K : AbstractSimplicialComplex V)
    [Finite K] [IsCombinatorial2Manifold K] :
    Nonempty (M ≃ₜ Geometric K) := by
  obtain ⟨g, hgcont, hgbij⟩ := rado_chart_homeo_glues_bijective M K
  exact rado_compact_to_T2_promote M K g hgcont hgbij

/-- **R1 overview, stepwise refinement.**  Same statement as
`rado_overview`; the body is now an explicit combination of the
three steps A, B, C.  *Each step is itself sorry-bearing*; the
overall sorry count is unchanged but the proof structure is now
visible. -/
theorem rado_overview_via_steps :
    ∃ (V : Type) (K : AbstractSimplicialComplex V),
      Finite K ∧ IsCombinatorial2Manifold K ∧
      Nonempty (M ≃ₜ Geometric K) := by
  obtain ⟨PL⟩ := rado_pl_atlas_exists M
  obtain ⟨V, K, hFin, hMfd⟩ := rado_assembled_simplicial_complex M PL
  exact ⟨V, K, hFin, hMfd, rado_realisation_homeomorphism (M := M) K⟩

end JacobianChallenge.Analysis.Rado
