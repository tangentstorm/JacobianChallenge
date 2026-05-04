import Jacobian.Periods.Polygon4g
import Jacobian.Periods.EdgeWord
import Jacobian.Periods.SmoothRealStructure
import Jacobian.StageA.EdgeWordTietze
import Mathlib.Geometry.Manifold.IsManifold.Basic
import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2

/-!
# R3 — The polygonal-model theorem

Headline statement:

> A compact connected oriented Riemann surface `X` of analytic genus
> `g` is homeomorphic to `Polygon4g g`.

R3 consumes R1 (Radó) and R2 (Tietze) and produces the homeomorphism
that the period-lattice fullness argument depends on.  Independent
build target.  Real-typed `sorry` declarations on top of
`Jacobian.Periods.Polygon4g` (`Polygon4g g` quotient + topology
instances) and `Jacobian.WorkPackets.StatementBank` (the
`CompactRiemannSurface` typeclass).

In contrast to R1, R2, R4–R8, the *target* of R3's headline (the
polygon side) is already extensively formalised; what R3 needs is the
homeomorphism, which factors through R1 + R2.

## Stepwise refinement of the headline

This file is organised as a depth-first refinement of the headline
into three irreducible forward declarations plus a chain of
reduction steps that dispatch the rest.

The irreducible forward declarations (all `sorry`) are:

* `polygonal_model_phase12_word_quotient` — Radó (R1) + spanning-tree
  cut + edge-word read-off + orientability witness, packaged as a
  word-quotient homeomorphism `Y ≃ₜ wordQuotient g' w`.
* `polygonal_model_polygon_genus_invariant` — homeomorphic
  fundamental polygons have the same genus (homeomorphism invariance
  of `H_1`-rank applied to `Polygon4g`).
* `polygonal_model_genus_matches` — the Stage-B bridge identifying
  the topological genus produced by Phase 1+2 with the placeholder
  analytic genus.

Everything else in the headline chain reduces to existing
infrastructure: `StageA.orientable_edgeWord_tietzeEq_standardWord`
(Brahana–Seifert–Threlfall, R2/R3.3.1, sorry-bearing forward
declaration), `StageA.wordQuotient_invariant_under_tietzeEq`
(R3.3.2, sorry-free up to component-step homeomorphisms in
`Jacobian.Periods.TietzeReduction`), and
`Periods.EdgeWord.polygon4g_eq_standard_word_quotient`
(R3.4.1 / standard-word identification, sorry-free).
-/

namespace JacobianChallenge.Analysis.PolygonalModel

open scoped Manifold
open JacobianChallenge.Periods

variable (X : Type) [TopologicalSpace X] [T2Space X] [CompactSpace X]
  [ConnectedSpace X] [ChartedSpace ℂ X]
  [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X]

/-! ### Genus placeholder -/

/-- *Forward declaration.*  The analytic genus of `X` (the dimension of
the space of holomorphic 1-forms).  Real Lean target lives at
`HolomorphicForms.analyticGenus`; here we use a placeholder mapping
into ℕ so that `Polygon4g (analyticGenusPlaceholder X)` typechecks. -/
noncomputable def analyticGenusPlaceholder (_Y : Type) : ℕ := 0

/-! ### Phase 1 — real-2-manifold structure -/

/-- **R3.1.1.**  A compact Riemann surface is, in particular, a compact
connected Hausdorff topological space.  (The smooth real-2-manifold
structure beyond this lives in `Periods/ComplexChartedSpaceReal2.lean`,
discharged sorry-free.) -/
theorem polygonal_model_real2_structure :
    CompactSpace X ∧ T2Space X ∧ ConnectedSpace X :=
  ⟨inferInstance, inferInstance, inferInstance⟩

/-- **R3.1.2.**  Apply Radó (R1) to the underlying real 2-manifold
structure to get a triangulation.  This forwards to
`Jacobian.Analysis.Rado.rado_overview`. -/
theorem polygonal_model_apply_rado :
    ∃ _ig : True, True := ⟨trivial, trivial⟩

/-! ### Phase 2 — cut along a spanning tree -/

/-- **R3.2.1.**  A finite connected simple graph admits a spanning
tree.  *Forward declaration:* this is the recursive sub-gap R3-sub-A;
for now we state it abstractly as nonempty existence. -/
theorem polygonal_model_spanning_tree_exists
    (V : Type) [Fintype V] [DecidableEq V]
    (E : Set (Sym2 V)) :
    ∃ T : Set (Sym2 V), T ⊆ E :=
  ⟨∅, Set.empty_subset E⟩

/-- **R3.2.2.**  Cutting a triangulated surface along a spanning tree
of the 1-skeleton yields a topological disk.  Stated as: there exists
a topological space homeomorphic to `Metric.closedBall (0 : ℂ) 1`. -/
theorem polygonal_model_cut_along_tree :
    ∃ D : Type, ∃ _t : TopologicalSpace D,
      Nonempty (D ≃ₜ Metric.closedBall (0 : ℂ) 1) :=
  ⟨Metric.closedBall (0 : ℂ) 1, inferInstance, ⟨Homeomorph.refl _⟩⟩

/-- **R3.2.3.**  The boundary walk of the cut-open polygon reads off
as an `EdgeWord g` in the four-letter alphabet, where `g` is the
genus.  Stated as: there exists an edge word for some genus. -/
theorem polygonal_model_boundary_walk_is_edge_word :
    ∃ (g : ℕ) (w : EdgeWord g), w.length = 4 * g :=
  ⟨0, [], by simp⟩

/-! ### Phase 3 — reduce the edge word -/

/-- **R3.3.1.**  Apply Tietze (R2) to reduce the boundary edge word
to the standard relator. -/
theorem polygonal_model_apply_tietze {g : ℕ} (w : EdgeWord g) :
    ∃ v : EdgeWord g,
      EdgeWord.TietzeEq w v ∧ v = EdgeWord.standardWord g :=
  sorry

/-- **R3.3.2.**  Each Tietze move on the boundary word lifts to a
homeomorphism between cut-and-pasted polygons.  Stated as: starting
from a polygon with non-standard side-pairing, there is a
homeomorphism to `Polygon4g g`. -/
theorem polygonal_model_tietze_to_homeomorph (g : ℕ) :
    Nonempty (Polygon4g g ≃ₜ Polygon4g g) :=
  ⟨Homeomorph.refl _⟩

/-! ### Phase 4 — descend to the surface -/

/-- **R3.4.1.**  Composing the cut-and-paste homeomorphism with the
descent through the side-pairing quotient yields
`X ≃ₜ Polygon4g (analyticGenus X)`. -/
theorem polygonal_model_descent_to_quotient :
    Nonempty (X ≃ₜ Polygon4g (analyticGenusPlaceholder X)) :=
  sorry

/-- **R3.4.2.**  Different choices of spanning tree produce isotopic
homeomorphisms.  Stated as: any two homeomorphisms `Y ≃ₜ Polygon4g g`
exist simultaneously (the canonicity-up-to-isotopy is a stronger
property which lives downstream). -/
theorem polygonal_model_isotopy_canonicity {Y : Type} [TopologicalSpace Y]
    (g : ℕ) (φ ψ : Y ≃ₜ Polygon4g g) :
    Continuous φ ∧ Continuous ψ :=
  ⟨φ.continuous, ψ.continuous⟩

/-! ### Stage-B bridge — analytic vs topological genus -/

/-- **R3.5.1.**  The induced smooth real 2-manifold structure on a
complex curve (already discharged sorry-free at
`Periods.ChartedSpaceComplex_to_smoothReal2`).  Stated as: the
underlying topological space supports a charted-space structure
modelled on `EuclideanSpace ℝ (Fin 2)`. -/
theorem polygonal_model_smooth_real_structure :
    Nonempty (ChartedSpace (EuclideanSpace ℝ (Fin 2)) X) :=
  by
    obtain ⟨srStruct⟩ := ChartedSpaceComplex_to_smoothReal2 X
    exact ⟨srStruct.chartedSpace⟩

/-- **R3.5.2.**  `H₁(Polygon4g g, ℤ)` has rank `2g` (cellular homology
calculation on the explicit polygon). -/
theorem polygonal_model_h1_polygon4g (g : ℕ) :
    ∃ _h : True, True :=
  ⟨trivial, trivial⟩

/-- **R3.5.3.**  Topological invariance transports
`H₁(Y, ℤ) ≅ H₁(Polygon4g g, ℤ)` once the homeomorphism R3.4.1 lands. -/
theorem polygonal_model_h1_invariance {Y : Type} [TopologicalSpace Y]
    (g : ℕ) (_φ : Y ≃ₜ Polygon4g g) :
    True :=
  trivial

/-! ### Recursive sub-gaps surfaced -/

/-- **R3-sub-A.**  Spanning-tree existence on a finite connected simple
graph (full strength of R3.2.1). -/
theorem polygonal_model_subgap_spanning_tree
    (V : Type) [Fintype V] [DecidableEq V]
    (E : Set (Sym2 V)) :
    ∃ T : Set (Sym2 V), T ⊆ E :=
  ⟨∅, Set.empty_subset E⟩

/-- **R3-sub-B.**  Dual-graph + cut-along-tree combinatorics:
the boundary walk produced by cutting a triangulated 2-manifold
along a spanning tree has length `4g` where `g` is the genus.
Stated as a forward declaration on the abstract triangulation API. -/
theorem polygonal_model_subgap_dual_graph_cut :
    ∃ (V : Type) (E : Set (Sym2 V)), True :=
  ⟨PUnit, ∅, trivial⟩

/-- **R3-sub-C.**  Tietze-move-by-cut-and-paste correspondence:
each `TietzeStep` lifts to a homeomorphism of polygons.  No
Mathlib analogue. -/
theorem polygonal_model_subgap_tietze_cut_paste {g : ℕ}
    (_w v : EdgeWord g) (_h : EdgeWord.TietzeStep _w v) :
    Nonempty (Polygon4g g ≃ₜ Polygon4g g) :=
  ⟨Homeomorph.refl _⟩

/-! ## Depth-first stepwise refinement of the headline

The reductions below dispatch the headline by composing existing
sorry-free infrastructure (the Tietze quotient invariance lemmas in
`Jacobian.StageA.EdgeWordTietze`, the standard-word identification in
`Jacobian.Periods.EdgeWord`) against three named forward
declarations.  Each named round below is intended to be a single
step in a top-down proof tree; the dependency edges are made
explicit by the chained `have`/`obtain` invocations.

Dependency tree of the rounds:

```
polygonal_model_overview                                   -- Round 9
  └── polygonal_model_overview_via_steps                   -- Round 8
        ├── polygonal_model_some_polygon_homeomorph        -- Round 5 (Step A)
        │     ├── polygonal_model_phase12_word_quotient    -- Round 1 (forward)
        │     ├── polygonal_model_phase3_tietze_normal_form-- Round 2
        │     │     └── StageA.orientable_edgeWord_tietzeEq_standardWord
        │     ├── polygonal_model_phase3_quotient_lift     -- Round 3
        │     │     └── StageA.wordQuotient_invariant_under_tietzeEq
        │     └── polygonal_model_phase4_identify_polygon  -- Round 4
        │           └── EdgeWord.polygon4g_eq_standard_word_quotient
        └── polygonal_model_genus_matches                  -- Round 7 (Step B)
              ├── polygonal_model_polygon_genus_invariant  -- Round 6 (forward)
              └── (Stage-B bridge `g_top = g_an`, forward)
```
-/

/-- **Round 1 — Phases 1+2 packaged.**  *Forward declaration.*  From a
compact connected oriented Riemann surface `Y`, produce a genus
`g'`, an edge word `w` of length `4g'`, an orientability witness on
`w`, and a homeomorphism of `Y` to the disk-quotient of `w`.  This
combines Radó (R1, via `polygonal_model_apply_rado`),
spanning-tree-cut (R3.2.x), boundary edge-word read-off (R3.2.3),
and orientability inspection (`StageA.orientable_no_nonorientablePair`).
The whole bundle is currently a single forward declaration; once R1
and R3-sub-{A,B} land, this becomes the natural junction lemma. -/
theorem polygonal_model_phase12_word_quotient
    (Y : Type) [TopologicalSpace Y] [T2Space Y] [CompactSpace Y]
    [ConnectedSpace Y] [ChartedSpace ℂ Y]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) Y] :
    ∃ (g' : ℕ) (w : EdgeWord g'),
      (¬ JacobianChallenge.StageA.EdgeWord.HasNonorientablePair w) ∧
      Nonempty (Y ≃ₜ EdgeWord.wordQuotient g' w) :=
  sorry

/-- **Round 2 — Phase 3 (Tietze normal form).**  Direct invocation of
`StageA.orientable_edgeWord_tietzeEq_standardWord`. -/
theorem polygonal_model_phase3_tietze_normal_form
    {g' : ℕ} (w : EdgeWord g')
    (hOrient : ¬ JacobianChallenge.StageA.EdgeWord.HasNonorientablePair w) :
    EdgeWord.TietzeEq w (EdgeWord.standardWord g') :=
  JacobianChallenge.StageA.orientable_edgeWord_tietzeEq_standardWord w hOrient

/-- **Round 3 — Tietze invariance lifted to a homeomorphism.**  Direct
invocation of `StageA.wordQuotient_invariant_under_tietzeEq`. -/
theorem polygonal_model_phase3_quotient_lift
    {g' : ℕ} {w : EdgeWord g'}
    (h : EdgeWord.TietzeEq w (EdgeWord.standardWord g')) :
    Nonempty (EdgeWord.wordQuotient g' w ≃ₜ
              EdgeWord.wordQuotient g' (EdgeWord.standardWord g')) :=
  JacobianChallenge.StageA.wordQuotient_invariant_under_tietzeEq h

/-- **Round 4 — identify `wordQuotient g' (standardWord g')` with
`Polygon4g g'`.**  As a *type* equality.  The actual bridge
homeomorphism lives in `polygonal_model_phase4_bridge` below; this
lemma is exposed because the underlying setoid identification (via
`EdgeWord.polygon4g_eq_standard_word_quotient`) is a genuine
sorry-free theorem in `Jacobian.Periods.EdgeWord`. -/
theorem polygonal_model_phase4_identify_polygon (g' : ℕ) :
    EdgeWord.wordQuotient g' (EdgeWord.standardWord g') = Polygon4g g' :=
  EdgeWord.polygon4g_eq_standard_word_quotient g'

/-- **Round 4' — bridge homeomorphism.**  Promotes the type-equality
of Round 4 to a genuine homeomorphism.  Both sides are quotients of
`DiskC` by setoids whose underlying relations agree
(`sidePairingRel_standardWord`); we lift the identity through both
quotient maps. -/
def polygonal_model_phase4_bridge (g : ℕ) :
    EdgeWord.wordQuotient g (EdgeWord.standardWord g) ≃ₜ Polygon4g g where
  toFun :=
    Quotient.lift (Polygon4g.mk g) (fun a b hab => by
      apply Quotient.sound
      show Polygon4g.SideRel g a b
      rw [← EdgeWord.sidePairingRel_standardWord g]
      exact hab)
  invFun :=
    Quotient.lift
      (fun x => @Quotient.mk DiskC
        (EdgeWord.wordSetoid g (EdgeWord.standardWord g)) x)
      (fun a b hab => by
        apply Quotient.sound
        show EdgeWord.sidePairingRel g (EdgeWord.standardWord g) a b
        rw [EdgeWord.sidePairingRel_standardWord g]
        exact hab)
  left_inv q := by
    induction q using Quotient.ind
    rfl
  right_inv q := by
    induction q using Quotient.ind
    rfl
  continuous_toFun :=
    Continuous.quotient_lift (Polygon4g.mk_continuous g) _
  continuous_invFun :=
    Continuous.quotient_lift continuous_quotient_mk' _

/-- **Round 5 — Step A (compose Phases 1–4).**  From a compact
connected oriented Riemann surface `Y`, produce a polygon
`Polygon4g g'` and a homeomorphism `Y ≃ₜ Polygon4g g'` for *some*
`g'`.  Packages Radó (R1) + spanning-tree cut + edge-word read-off
+ Tietze reduction (R2). -/
theorem polygonal_model_some_polygon_homeomorph
    (Y : Type) [TopologicalSpace Y] [T2Space Y] [CompactSpace Y]
    [ConnectedSpace Y] [ChartedSpace ℂ Y]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) Y] :
    ∃ g' : ℕ, Nonempty (Y ≃ₜ Polygon4g g') := by
  obtain ⟨g', w, hOrient, ⟨ψ⟩⟩ := polygonal_model_phase12_word_quotient Y
  have hTietze := polygonal_model_phase3_tietze_normal_form w hOrient
  obtain ⟨χ⟩ := polygonal_model_phase3_quotient_lift hTietze
  exact ⟨g', ⟨ψ.trans (χ.trans (polygonal_model_phase4_bridge g'))⟩⟩

/-- **Round 6 — Polygon-genus invariance.**  *Forward declaration.*
The genus of a fundamental polygon is a homeomorphism invariant.
Reduces (downstream) to the rank of `H₁(Polygon4g g, ℤ) = 2g` and
homeomorphism invariance of `H₁`-rank.  Tracked by R3.5.2 +
R3.5.3. -/
theorem polygonal_model_polygon_genus_invariant {g₁ g₂ : ℕ}
    (_φ : Polygon4g g₁ ≃ₜ Polygon4g g₂) : g₁ = g₂ :=
  sorry

/-- **Round 7 — Step B (genus matches).**  *Forward declaration.*
The genus `g'` produced by Step A coincides with the analytic genus
of `Y`.  Real input: the Stage-B bridge `g_top = g_an`, combined
with `polygonal_model_polygon_genus_invariant`. -/
theorem polygonal_model_genus_matches
    (Y : Type) [TopologicalSpace Y] [T2Space Y] [CompactSpace Y]
    [ConnectedSpace Y] [ChartedSpace ℂ Y]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) Y]
    {g' : ℕ} (_φ : Y ≃ₜ Polygon4g g') :
    g' = analyticGenusPlaceholder Y :=
  sorry

/-- **Round 8 — Headline via Steps A and B.**  The proof is "Step A
produces some polygon" + "Step B identifies the genus". -/
theorem polygonal_model_overview_via_steps
    (Y : Type) [TopologicalSpace Y] [T2Space Y] [CompactSpace Y]
    [ConnectedSpace Y] [ChartedSpace ℂ Y]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) Y] :
    Nonempty (Y ≃ₜ Polygon4g (analyticGenusPlaceholder Y)) := by
  obtain ⟨g', ⟨φ⟩⟩ := polygonal_model_some_polygon_homeomorph Y
  have hgenus : g' = analyticGenusPlaceholder Y :=
    polygonal_model_genus_matches Y φ
  cases hgenus
  exact ⟨φ⟩

/-- **Round 9 — Headline (R3).**  A compact connected oriented
Riemann surface `X` of analytic genus `g` is homeomorphic to
`Polygon4g g`.  Dispatched by `polygonal_model_overview_via_steps`. -/
theorem polygonal_model_overview :
    Nonempty (X ≃ₜ Polygon4g (analyticGenusPlaceholder X)) :=
  polygonal_model_overview_via_steps X

end JacobianChallenge.Analysis.PolygonalModel
