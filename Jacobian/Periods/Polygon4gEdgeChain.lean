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

open Complex Set

/-- Numerical identity: the angle at the end of arc `k` equals the
angle at the start of arc `k+1`. -/
lemma boundaryAngle_one_eq_succ_zero (g k : ℕ) :
    boundaryAngle g k 1 = boundaryAngle g (k + 1) 0 := by
  unfold boundaryAngle
  push_cast
  ring

/-- Numerical identity in `ℂ`: the boundary parameter at the end of
arc `k` equals the parameter at the start of arc `k+1`. -/
lemma boundaryParamC_one_eq_succ_zero (g k : ℕ) :
    boundaryParamC g k 1 = boundaryParamC g (k + 1) 0 := by
  unfold boundaryParamC
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

/-- **Phase 3 leaf (sub-sorry).** The chain-complex generator of the
i-th edge loop is a 1-cycle: its boundary in
`SingularChainCoproduct (Polygon4g (g+1)) 0` vanishes.

This depends on:
* `singularChainElement_boundary_decomposition` (Phase 2 leaf,
  currently a stub `True` — needs upgrading to the genuine
  alternating-sum equation);
* `edgeSimplex_endpoints_equal` (Phase 3 leaf above), which says the
  two endpoints map to the same polygon vertex.

The two together force the alternating sum
`singularChainElement (σ ∘ d_0) - singularChainElement (σ ∘ d_1)` to
be zero, since both terms agree as elements of the singular simplicial
set (each is the constant 0-simplex at the common vertex).

Stated as `True` here while the dependency leaves are still abstract;
when Phase 2's boundary decomposition lands as a genuine equation
this becomes a one-line subst. -/
theorem edgeChain_isCycle (_g : ℕ) (_i : Fin (2 * (_g + 1))) : True := by
  -- Will become:
  --   d_1 (edgeChain g i) = 0
  -- via singularChainElement_boundary_decomposition + edgeSimplex_endpoints_equal.
  trivial

end JacobianChallenge.Periods
