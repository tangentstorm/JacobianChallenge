import Jacobian.Periods.Polygon4gEdgeSimplex
import Jacobian.Periods.SingularChainElement

/-!
# Edge chains on the polygon (Phase 3)

Phase 3 of the cellular Hurewicz infrastructure plan
(`ref/plans/cellular-hurewicz-plan.md`).

Each edge loop on `Polygon4g (g+1)` is packaged as an element of the
singular chain group at level 1, called `edgeChain g i`, and the loop
closure is recorded as `edgeChain_isCycle g i` (currently dependent
on the Phase 2 boundary-decomposition leaf and a polygon-vertex
identification leaf).

## Status

* `edgeChain g i` — sorry-free (composition of Phase 1.5
  `edgeSimplex` with Phase 2 `singularChainElement`).
* `boundaryParam_one_eq_succ_zero` — sorry-free numerical identity
  `boundaryParam g k 1 = boundaryParam g (k+1) 0` (same exponential
  value at the same angle).
* `polygon4g_succ_vertex_{a,b}_pair_{zero,one}` — sorry-free, the
  four within-handle vertex identifications coming directly from
  `mk_a_pair`/`mk_b_pair`.
* `polygon4g_succ_handle_vertices_equal` — sorry-free, the four
  vertices `4i, 4i+1, 4i+2, 4i+3` of handle `i` are all identified.
* `polygon4g_succ_handle_link` — sorry-free, the b-pair identification
  linking adjacent handles.
* `edgeSimplex_endpoints_equal` — **sorry-free**: the two endpoints
  of edge `i` are identified, derived from
  `polygon4g_succ_handle_vertices_equal`.
* `edgeChain_isCycle` — Phase 3 leaf (placeholder `True`): boundary
  of `edgeChain g i` vanishes. Will become a real equation once
  Phase 2's `singularChainElement_boundary_decomposition` is
  upgraded from a `True` stub to the genuine alternating-sum
  equation.

The vertex-identification block (originally sub-sorry'd as
`polygon4g_succ_allVerticesEqual`) is now landed concretely — every
edge in the polygon has its endpoints identified by a finite chain
of within-handle side-pairings, with no induction over handles
needed (since the two endpoints of edge `i` lie in the same handle).
-/

namespace JacobianChallenge.Periods

open Complex Set AlgebraicTopology

/-- Numerical identity: the angle at the end of arc `k` equals the
angle at the start of arc `k+1`. -/
lemma boundaryAngle_one_eq_succ_zero (g k : ℕ) :
    boundaryAngle g k 1 = boundaryAngle g (k + 1) 0 := by
  unfold boundaryAngle boundaryAngle'
  push_cast
  ring_nf

/-- Numerical identity in `ℂ`: the boundary parameter at the end of
arc `k` equals the parameter at the start of arc `k+1`. -/
lemma boundaryParamC_one_eq_succ_zero (g k : ℕ) :
    boundaryParamC g k 1 = boundaryParamC g (k + 1) 0 := by
  unfold boundaryParamC boundaryParamC'
  change exp (((boundaryAngle g k 1 : ℂ)) * I) =
    exp (((boundaryAngle g (k + 1) 0 : ℂ)) * I)
  rw [boundaryAngle_one_eq_succ_zero]

/-- The `DiskC` lift of the boundary-arc endpoint identity. -/
lemma boundaryParam_one_eq_succ_zero (g k : ℕ) :
    boundaryParam g k 1 = boundaryParam g (k + 1) 0 := by
  unfold boundaryParam
  ext
  exact boundaryParamC_one_eq_succ_zero g k

/-- Within-handle a-pair identification at `t = 0`: vertex `4i` ~
vertex `4i+3` of the genus-`(g+1)` polygon. -/
lemma polygon4g_succ_vertex_a_pair_zero
    (g : ℕ) (i : Fin (g + 1)) :
    Polygon4g.mk (g + 1) (boundaryParam (g + 1) (4 * i.val) 0)
      = Polygon4g.mk (g + 1) (boundaryParam (g + 1) (4 * i.val + 3) 0) := by
  have h := Polygon4g.mk_a_pair (g + 1) i 0 ⟨le_refl 0, zero_le_one⟩
  simp only [sub_zero] at h
  rw [h, boundaryParam_one_eq_succ_zero]

/-- Within-handle a-pair identification at `t = 1`: vertex `4i+1` ~
vertex `4i+2` of the genus-`(g+1)` polygon. -/
lemma polygon4g_succ_vertex_a_pair_one
    (g : ℕ) (i : Fin (g + 1)) :
    Polygon4g.mk (g + 1) (boundaryParam (g + 1) (4 * i.val + 1) 0)
      = Polygon4g.mk (g + 1) (boundaryParam (g + 1) (4 * i.val + 2) 0) := by
  have h := Polygon4g.mk_a_pair (g + 1) i 1 ⟨zero_le_one, le_refl 1⟩
  rw [show (1 - 1 : ℝ) = 0 from by ring] at h
  rw [← boundaryParam_one_eq_succ_zero]
  exact h

/-- Within-handle b-pair identification at `t = 0`: vertex `4i+1` ~
vertex `4i+4` (= `4(i+1)`) of the genus-`(g+1)` polygon. -/
lemma polygon4g_succ_vertex_b_pair_zero
    (g : ℕ) (i : Fin (g + 1)) :
    Polygon4g.mk (g + 1) (boundaryParam (g + 1) (4 * i.val + 1) 0)
      = Polygon4g.mk (g + 1) (boundaryParam (g + 1) (4 * i.val + 4) 0) := by
  have h := Polygon4g.mk_b_pair (g + 1) i 0 ⟨le_refl 0, zero_le_one⟩
  simp only [sub_zero] at h
  rw [h, boundaryParam_one_eq_succ_zero]

/-- Within-handle b-pair identification at `t = 1`: vertex `4i+2` ~
vertex `4i+3` of the genus-`(g+1)` polygon. -/
lemma polygon4g_succ_vertex_b_pair_one
    (g : ℕ) (i : Fin (g + 1)) :
    Polygon4g.mk (g + 1) (boundaryParam (g + 1) (4 * i.val + 2) 0)
      = Polygon4g.mk (g + 1) (boundaryParam (g + 1) (4 * i.val + 3) 0) := by
  have h := Polygon4g.mk_b_pair (g + 1) i 1 ⟨zero_le_one, le_refl 1⟩
  rw [show (1 - 1 : ℝ) = 0 from by ring] at h
  rw [← boundaryParam_one_eq_succ_zero]
  exact h

/-- All four boundary vertices `4i, 4i+1, 4i+2, 4i+3` of handle `i` of
the genus-`(g+1)` polygon are identified in `Polygon4g (g+1)`.
Combines the four within-handle pair identifications above. -/
lemma polygon4g_succ_handle_vertices_equal
    (g : ℕ) (i : Fin (g + 1)) (a b : Fin 4) :
    Polygon4g.mk (g + 1) (boundaryParam (g + 1) (4 * i.val + a.val) 0)
      = Polygon4g.mk (g + 1) (boundaryParam (g + 1) (4 * i.val + b.val) 0) := by
  -- Reduce both sides to vertex (4*i.val + 3) via the explicit chain
  -- 0 ~ 3, 1 ~ 2 ~ 3, so 0 ~ 3 ~ 2 ~ 1 (and trivially 3 ~ 3).
  have h_0_3 : Polygon4g.mk (g + 1) (boundaryParam (g + 1) (4 * i.val) 0)
      = Polygon4g.mk (g + 1) (boundaryParam (g + 1) (4 * i.val + 3) 0) :=
    polygon4g_succ_vertex_a_pair_zero g i
  have h_1_2 : Polygon4g.mk (g + 1) (boundaryParam (g + 1) (4 * i.val + 1) 0)
      = Polygon4g.mk (g + 1) (boundaryParam (g + 1) (4 * i.val + 2) 0) :=
    polygon4g_succ_vertex_a_pair_one g i
  have h_2_3 : Polygon4g.mk (g + 1) (boundaryParam (g + 1) (4 * i.val + 2) 0)
      = Polygon4g.mk (g + 1) (boundaryParam (g + 1) (4 * i.val + 3) 0) :=
    polygon4g_succ_vertex_b_pair_one g i
  -- Each value `a.val ∈ {0, 1, 2, 3}` reduces to vertex `4i+3`.
  have hto3 : ∀ c : Fin 4,
      Polygon4g.mk (g + 1) (boundaryParam (g + 1) (4 * i.val + c.val) 0)
        = Polygon4g.mk (g + 1) (boundaryParam (g + 1) (4 * i.val + 3) 0) := by
    intro c
    fin_cases c
    · exact h_0_3
    · exact h_1_2.trans h_2_3
    · simpa using h_2_3
    · rfl
  rw [hto3 a, ← hto3 b]

/-- Adjacent-handle linking: vertex `4i+4` (= `4(i+1)`) is identified
with the vertex `4i+1` of the previous handle, hence with all the
within-handle vertices. Concretely the b-pair identification. -/
lemma polygon4g_succ_handle_link
    (g : ℕ) (i : Fin (g + 1)) :
    Polygon4g.mk (g + 1) (boundaryParam (g + 1) (4 * i.val + 4) 0)
      = Polygon4g.mk (g + 1) (boundaryParam (g + 1) (4 * i.val + 1) 0) :=
  (polygon4g_succ_vertex_b_pair_zero g i).symm

/-- The endpoints of edge `i` of the genus-`(g+1)` polygon are
identified in the quotient `Polygon4g (g+1)`.

Sorry-free; uses the within-handle identification
`polygon4g_succ_handle_vertices_equal` since both endpoints lie in
the same handle (the arc index is `4 * (i.val / 2) + (i.val % 2)`
and its successor is `4 * (i.val / 2) + (i.val % 2) + 1`, both at
most `4 * (i.val / 2) + 3`). -/
lemma edgeSimplex_endpoints_equal (g : ℕ) (i : Fin (2 * (g + 1))) :
    Polygon4g.mk (g + 1) (boundaryParam (g + 1) (edgeArcIdx g i) 0)
      = Polygon4g.mk (g + 1) (boundaryParam (g + 1) (edgeArcIdx g i) 1) := by
  rw [boundaryParam_one_eq_succ_zero]
  have hj_lt : i.val / 2 < g + 1 := by
    have : i.val < 2 * (g + 1) := i.isLt
    omega
  let j : Fin (g + 1) := ⟨i.val / 2, hj_lt⟩
  have hr_lt : i.val % 2 < 4 := by omega
  have hr_succ_lt : i.val % 2 + 1 < 4 := by omega
  have h := polygon4g_succ_handle_vertices_equal g j
    (⟨i.val % 2, hr_lt⟩) (⟨i.val % 2 + 1, hr_succ_lt⟩)
  show Polygon4g.mk (g + 1) (boundaryParam (g + 1) (4 * (i.val / 2) + i.val % 2) 0) =
    Polygon4g.mk (g + 1) (boundaryParam (g + 1) (4 * (i.val / 2) + i.val % 2 + 1) 0)
  convert h using 3

/-- The chain-complex generator (level 1) of the i-th edge loop on the
genus-`(g+1)` polygon. -/
noncomputable def edgeChain (g : ℕ) (i : Fin (2 * (g + 1))) :
    SingularChainCoproduct (Polygon4g (g + 1)) 1 :=
  singularChainElement (edgeSimplex g i)

/-- The two faces of an edge simplex are equal as continuous maps from
`stdSimplex ℝ (Fin 1)` to the polygon. Both faces are constant maps
to the (single, identified) polygon vertex, since `stdSimplex ℝ (Fin 1)`
is a singleton.

Sorry-free: uses `Subsingleton (stdSimplex ℝ (Fin 1))` plus
`edgeSimplex_endpoints_equal` for the value equality. -/
lemma edgeSimplex_faces_eq (g : ℕ) (i : Fin (2 * (g + 1))) :
    singularSimplexFace (edgeSimplex g i) 0
      = singularSimplexFace (edgeSimplex g i) 1 := by
  -- Provide the `Subsingleton` instance explicitly (the implicit search
  -- doesn't unfold `Fin (0 + 1)`).
  haveI : Subsingleton (stdSimplex ℝ (Fin 1)) := inferInstance
  haveI : Subsingleton (stdSimplex ℝ (Fin (0 + 1))) := this
  ext s
  -- Both sides reduce to evaluating `edgeSimplex g i` at the
  -- corresponding vertex of `stdSimplex ℝ (Fin 2)`.
  -- Since `stdSimplex ℝ (Fin 1)` is a singleton, replace `s` by
  -- `stdSimplex.vertex 0` (the vertex at index 0).
  have hs : s = stdSimplex.vertex 0 := Subsingleton.elim _ _
  rw [hs]
  show edgeSimplex g i (stdSimplex.map (Fin.succAbove 0) (stdSimplex.vertex 0))
    = edgeSimplex g i (stdSimplex.map (Fin.succAbove 1) (stdSimplex.vertex 0))
  rw [stdSimplex.map_vertex, stdSimplex.map_vertex]
  -- `Fin.succAbove 0 0 = 1` and `Fin.succAbove 1 0 = 0`.
  have h0 : (Fin.succAbove (0 : Fin 2) 0 : Fin 2) = 1 := by decide
  have h1 : (Fin.succAbove (1 : Fin 2) 0 : Fin 2) = 0 := by decide
  rw [h0, h1]
  -- These are exactly `edgeSimplex_vertex_one` and `edgeSimplex_vertex_zero`.
  show edgeSimplex g i (stdSimplexVertex 1) = edgeSimplex g i (stdSimplexVertex 0)
  rw [edgeSimplex_vertex_one, edgeSimplex_vertex_zero]
  exact (edgeSimplex_endpoints_equal g i).symm

/-- **Phase 3 leaf (sorry-free given Phase 2.5).** The chain-complex
generator of the i-th edge loop is a 1-cycle: its boundary in
`SingularChainCoproduct (Polygon4g (g+1)) 0` vanishes.

Proof: apply `singularChainElement_boundary_decomposition` at `n = 0`
to expand `d_1 (edgeChain g i)` as a two-term sum, then use
`edgeSimplex_faces_eq` to make the two terms cancel. -/
theorem edgeChain_isCycle (g : ℕ) (i : Fin (2 * (g + 1))) :
    (((singularChainComplexFunctor (ModuleCat ℤ)).obj
        (ModuleCat.of ℤ ℤ)).obj (TopCat.of (Polygon4g (g + 1)))).d 1 0
        (edgeChain g i : SingularChainCoproduct (Polygon4g (g + 1)) 1)
      = 0 := by
  rw [show edgeChain g i = singularChainElement (edgeSimplex g i) from rfl]
  rw [singularChainElement_boundary_decomposition (Polygon4g (g + 1)) 0
        (edgeSimplex g i)]
  -- Sum over Fin 2 expands to two terms:
  -- (-1)^0 • singularChainElement (face σ 0) + (-1)^1 • singularChainElement (face σ 1)
  -- = singularChainElement (face σ 0) - singularChainElement (face σ 1)
  rw [Fin.sum_univ_two]
  -- The two faces are equal as continuous maps, so they yield the same
  -- chain element; the sum of the corresponding terms is zero.
  rw [show singularSimplexFace (edgeSimplex g i) 0
        = singularSimplexFace (edgeSimplex g i) 1 from
      edgeSimplex_faces_eq g i]
  show ((-1 : ℤ) ^ ((0 : Fin 2) : ℕ)) •
        (singularChainElement (singularSimplexFace (edgeSimplex g i) 1) :
          SingularChainCoproduct (Polygon4g (g + 1)) 0)
      + ((-1 : ℤ) ^ ((1 : Fin 2) : ℕ)) •
        singularChainElement (singularSimplexFace (edgeSimplex g i) 1)
      = 0
  simp [pow_zero, pow_one, one_smul, add_neg_cancel]

/-- The concrete edge chain indexed by the one-cells of `Polygon4g g`.
For `g = 0` the index type is empty; for `g = h + 1` this is the
existing `edgeChain h`.  This version matches the `Fin (2 * g)` indexing
used by the project-side cellular model and Hurewicz comparison data. -/
noncomputable def edgeChainOnGenus (g : ℕ) (i : Fin (2 * g)) :
    SingularChainCoproduct (Polygon4g g) 1 := by
  cases g with
  | zero =>
      exact False.elim (Fin.elim0 i)
  | succ h =>
      exact edgeChain h i

/-- The genus-indexed concrete edge chain is a singular 1-cycle. -/
theorem edgeChainOnGenus_isCycle (g : ℕ) (i : Fin (2 * g)) :
    (((singularChainComplexFunctor (ModuleCat ℤ)).obj
        (ModuleCat.of ℤ ℤ)).obj (TopCat.of (Polygon4g g))).d 1 0
        (edgeChainOnGenus g i : SingularChainCoproduct (Polygon4g g) 1)
      = 0 := by
  cases g with
  | zero =>
      exact False.elim (Fin.elim0 i)
  | succ h =>
      exact edgeChain_isCycle h i

end JacobianChallenge.Periods
