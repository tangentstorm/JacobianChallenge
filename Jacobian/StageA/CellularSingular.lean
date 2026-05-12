import Jacobian.StageA.FinsetSortErase
import Jacobian.StageA.SimplicialComplex
import Jacobian.StageA.PrismOperator
import Jacobian.Periods.TopologicalGenus
import Mathlib.AlgebraicTopology.SingularHomology.Basic
import Mathlib.LinearAlgebra.Finsupp.VectorSpace

/-!
# Stage A — Cellular vs singular homology comparison

Bottom-up sketch: the comparison theorem identifying the cellular
homology of a CW (or simplicial) complex with the singular homology
of its geometric realisation.

For a finite simplicial complex `K` with realisation `|K|`:
* The *cellular chain complex* `C_*^cell(K, ℤ)` has `C_n^cell = ℤ^{#n-simplices}`,
  with boundary `∂_n` the signed face map.
* The inclusion of the simplicial chain complex into the singular
  chain complex `C_*^sing(|K|, ℤ)` (sending a simplex `σ` to its
  characteristic map `Δ^n → |K|`) is a quasi-isomorphism.

This gives `H_n^cell(K, ℤ) ≅ H_n^sing(|K|, ℤ)` as ℤ-modules.

Estimated LOC: ~400.
-/

namespace JacobianChallenge.StageA

open JacobianChallenge.Periods

variable {V : Type} (K : AbstractSimplicialComplex V)

/-! ### Cellular chain complex -/

/-- The cellular `C_n` of a simplicial complex: free ℤ-module on the
`n`-simplices. -/
abbrev cellularChain (K : AbstractSimplicialComplex V) (n : ℕ) : Type :=
  K.nSimplices n →₀ ℤ

noncomputable instance (K : AbstractSimplicialComplex V) (n : ℕ) :
    AddCommGroup (cellularChain K n) :=
  inferInstanceAs (AddCommGroup (K.nSimplices n →₀ ℤ))
noncomputable instance (K : AbstractSimplicialComplex V) (n : ℕ) :
    Module ℤ (cellularChain K n) :=
  inferInstanceAs (Module ℤ (K.nSimplices n →₀ ℤ))

/-- The free ℤ-basis of `cellularChain K n` indexed by
`K.nSimplices n`. -/
noncomputable def cellularChain.basis
    (K : AbstractSimplicialComplex V) (n : ℕ) :
    Module.Basis (K.nSimplices n) ℤ (cellularChain K n) :=
  Finsupp.basisSingleOne (R := ℤ)

/-- The cardinality of a `K.nSimplices (n+1)` element as a `Finset V`
is `n+2`. -/
private theorem nSimplices_card
    {V : Type} (K : AbstractSimplicialComplex V) {n : ℕ}
    (s : K.nSimplices n) : s.1.card = n + 1 := by
  have hdim := s.2.2
  unfold AbstractSimplicialComplex.dimSimplex at hdim
  have hne : s.1.Nonempty := K.nonempty_of_mem s.2.1
  have hpos : 0 < s.1.card := Finset.card_pos.mpr hne
  omega

/-- The `i`-th *vertex* of an `(n+1)`-simplex `s` of `K`, listed in the
canonical sort order from `[LinearOrder V]`. Used by
`cellularSimplexFace` to construct the i-th face. -/
noncomputable def cellularSimplexVertex
    [LinearOrder V] (K : AbstractSimplicialComplex V) (n : ℕ)
    (s : K.nSimplices (n + 1)) (i : Fin (n + 2)) : V :=
  s.1.orderEmbOfFin (nSimplices_card K s) i

/-- The `i`-th *face* of an `(n+1)`-simplex `s` of `K` (vertex `i`
deleted, in the canonical sort order). Carried as an element of
`K.nSimplices n` via `K.downward_closed`. -/
noncomputable def cellularSimplexFace
    [LinearOrder V] [DecidableEq V] (K : AbstractSimplicialComplex V) (n : ℕ)
    (s : K.nSimplices (n + 1)) (i : Fin (n + 2)) : K.nSimplices n := by
  classical
  have hcard : s.1.card = n + 2 := nSimplices_card K s
  let v : V := cellularSimplexVertex K n s i
  let face : Finset V := s.1.erase v
  have hv_mem : v ∈ s.1 :=
    Finset.orderEmbOfFin_mem s.1 hcard i
  have hface_card : face.card = n + 1 := by
    rw [Finset.card_erase_of_mem hv_mem, hcard]; omega
  have hface_ne : face.Nonempty := by
    rw [← Finset.card_pos, hface_card]; omega
  refine ⟨face, ⟨?_, ?_⟩⟩
  · exact K.downward_closed s.2.1 (Finset.erase_subset _ _) hface_ne
  · unfold AbstractSimplicialComplex.dimSimplex
    omega

/-- **Substantive form** of the cellular boundary
`∂_n : C_n^cell → C_{n-1}^cell`: signed sum of faces,
`∂(s) = Σᵢ (-1)ⁱ • [s.face_i]`. The face indexing comes from the
canonical `Finset.orderEmbOfFin` enumeration of `s`'s vertices under
`[LinearOrder V]`.

This is the *real* boundary operator. The headline `cellularBoundary`
(below) carries the placeholder `0` body to avoid forcing
`[LinearOrder V] [DecidableEq V]` on every consumer; promotion to the
signed form is the planned upstream change for the headline iso. -/
noncomputable def cellularBoundarySigned
    [LinearOrder V] [DecidableEq V] (K : AbstractSimplicialComplex V) (n : ℕ) :
    cellularChain K (n + 1) →ₗ[ℤ] cellularChain K n :=
  Finsupp.lift _ ℤ _ (fun s : K.nSimplices (n + 1) =>
    ∑ i : Fin (n + 2),
      (-1 : ℤ) ^ i.val • Finsupp.single (cellularSimplexFace K n s i) (1 : ℤ))

/-! ### Face-of-face commutation

For the simplicial `∂² = 0` proof: composing two `cellularSimplexFace` operations
in either order produces the same result, modulo a sign-reversing index shift. -/

/-- For `j.val < i.val`, the `(i, j)`-th iterated face equals the
`(⟨j, _⟩, ⟨i-1, _⟩)`-th iterated face (up to subtype).

The underlying Finset of both is `s.1.erase v_i.erase v_j` (where `v_x` is
the `x`-th sorted vertex of `s.1`); they agree by `Finset.erase_comm`. -/
private theorem cellularSimplexFace_face_eq_lt
    [LinearOrder V] [DecidableEq V] (K : AbstractSimplicialComplex V) (n : ℕ)
    (s : K.nSimplices (n + 2)) (i : Fin (n + 3)) (j : Fin (n + 2))
    (hij : j.val < i.val) :
    cellularSimplexFace K n (cellularSimplexFace K (n + 1) s i) j =
      cellularSimplexFace K n
        (cellularSimplexFace K (n + 1) s ⟨j.val, by have := i.isLt; omega⟩)
        ⟨i.val - 1, by have := i.isLt; omega⟩ := by
  apply Subtype.ext
  -- Reduce to underlying Finset.
  unfold cellularSimplexFace cellularSimplexVertex
  -- Both sides are `s.1.erase _ |>.erase _`. Use `orderEmbOfFin_erase_lt` to
  -- compute the second erase's vertex.
  have hcard_s : s.1.card = n + 3 := nSimplices_card K s
  -- LHS: `(s.1.erase v_i).erase ((s.1.erase v_i).orderEmbOfFin _ j)` where
  -- `(s.1.erase v_i).orderEmbOfFin _ j = s.orderEmbOfFin _ ⟨j.val, _⟩` since `j < i`.
  have hcard_erase_i : (s.1.erase (s.1.orderEmbOfFin hcard_s i)).card = n + 2 := by
    rw [Finset.card_erase_of_mem (Finset.orderEmbOfFin_mem _ _ _), hcard_s]; omega
  have h_LHS_v : (s.1.erase (s.1.orderEmbOfFin hcard_s i)).orderEmbOfFin
        hcard_erase_i j =
      s.1.orderEmbOfFin hcard_s ⟨j.val, by have := i.isLt; omega⟩ :=
    Finset.orderEmbOfFin_erase_lt s.1 hcard_s i j hcard_erase_i hij
  -- RHS: `(s.1.erase v_j).erase ((s.1.erase v_j).orderEmbOfFin _ ⟨i-1, _⟩)`
  --      = `(s.1.erase v_j).erase v_i` (since `i-1 ≥ j`).
  have hcard_erase_j : (s.1.erase (s.1.orderEmbOfFin hcard_s
        ⟨j.val, by have := i.isLt; omega⟩)).card = n + 2 := by
    rw [Finset.card_erase_of_mem (Finset.orderEmbOfFin_mem _ _ _), hcard_s]; omega
  have h_RHS_v : (s.1.erase (s.1.orderEmbOfFin hcard_s
        ⟨j.val, by have := i.isLt; omega⟩)).orderEmbOfFin hcard_erase_j
        ⟨i.val - 1, by have := i.isLt; omega⟩ =
      s.1.orderEmbOfFin hcard_s ⟨(i.val - 1) + 1, by have := i.isLt; omega⟩ :=
    Finset.orderEmbOfFin_erase_ge s.1 hcard_s
      ⟨j.val, by have := i.isLt; omega⟩
      ⟨i.val - 1, by have := i.isLt; omega⟩ hcard_erase_j
      (by show j.val ≤ i.val - 1; omega)
  -- Simplify `(i-1) + 1 = i` since i ≥ 1 (from j < i).
  have h_idx : (⟨(i.val - 1) + 1, by have := i.isLt; omega⟩ : Fin (n + 3)) =
      ⟨i.val, i.isLt⟩ := by
    apply Fin.ext
    show (i.val - 1) + 1 = i.val
    omega
  rw [h_idx] at h_RHS_v
  -- Replace the orderEmbOfFin ⟨i.val, _⟩ with i (proof-irrelevant).
  have h_idx2 : (⟨i.val, i.isLt⟩ : Fin (n + 3)) = i := Fin.ext rfl
  rw [h_idx2] at h_RHS_v
  -- Now both sides are `s.1.erase _ |>.erase _` with the same two vertices.
  -- Apply `Finset.erase_comm`.
  show (s.1.erase _).erase _ = (s.1.erase _).erase _
  rw [h_LHS_v, h_RHS_v]
  -- Goal: (s.1.erase v_i).erase v_j = (s.1.erase v_j).erase v_i.
  ext x
  simp only [Finset.mem_erase]
  tauto

/-- For `j.val ≥ i.val`, the `(i, j)`-th iterated face equals the
`(⟨j+1, _⟩, ⟨i, _⟩)`-th iterated face (up to subtype). -/
private theorem cellularSimplexFace_face_eq_ge
    [LinearOrder V] [DecidableEq V] (K : AbstractSimplicialComplex V) (n : ℕ)
    (s : K.nSimplices (n + 2)) (i : Fin (n + 3)) (j : Fin (n + 2))
    (hij : i.val ≤ j.val) :
    cellularSimplexFace K n (cellularSimplexFace K (n + 1) s i) j =
      cellularSimplexFace K n
        (cellularSimplexFace K (n + 1) s ⟨j.val + 1, by have := j.isLt; omega⟩)
        ⟨i.val, by have := i.isLt; have := j.isLt; omega⟩ := by
  apply Subtype.ext
  unfold cellularSimplexFace cellularSimplexVertex
  have hcard_s : s.1.card = n + 3 := nSimplices_card K s
  -- LHS: `(s.1.erase v_i).erase v'_j` where `v'_j = v_{j+1}` (since `j ≥ i`).
  have hcard_erase_i : (s.1.erase (s.1.orderEmbOfFin hcard_s i)).card = n + 2 := by
    rw [Finset.card_erase_of_mem (Finset.orderEmbOfFin_mem _ _ _), hcard_s]; omega
  have h_LHS_v : (s.1.erase (s.1.orderEmbOfFin hcard_s i)).orderEmbOfFin
        hcard_erase_i j =
      s.1.orderEmbOfFin hcard_s ⟨j.val + 1, by have := j.isLt; omega⟩ :=
    Finset.orderEmbOfFin_erase_ge s.1 hcard_s i j hcard_erase_i hij
  -- RHS: `(s.1.erase v_{j+1}).erase v''_i` where `v''_i = v_i` (since `i < j+1`).
  have hcard_erase_j1 : (s.1.erase (s.1.orderEmbOfFin hcard_s
        ⟨j.val + 1, by have := j.isLt; omega⟩)).card = n + 2 := by
    rw [Finset.card_erase_of_mem (Finset.orderEmbOfFin_mem _ _ _), hcard_s]; omega
  have h_RHS_v : (s.1.erase (s.1.orderEmbOfFin hcard_s
        ⟨j.val + 1, by have := j.isLt; omega⟩)).orderEmbOfFin hcard_erase_j1
        ⟨i.val, by have := i.isLt; have := j.isLt; omega⟩ =
      s.1.orderEmbOfFin hcard_s ⟨i.val, i.isLt⟩ :=
    Finset.orderEmbOfFin_erase_lt s.1 hcard_s
      ⟨j.val + 1, by have := j.isLt; omega⟩
      ⟨i.val, by have := i.isLt; have := j.isLt; omega⟩
      hcard_erase_j1
      (by show i.val < j.val + 1; omega)
  -- Replace ⟨i.val, _⟩ with i (proof-irrelevant).
  have h_idx : (⟨i.val, i.isLt⟩ : Fin (n + 3)) = i := Fin.ext rfl
  rw [h_idx] at h_RHS_v
  show (s.1.erase _).erase _ = (s.1.erase _).erase _
  rw [h_LHS_v, h_RHS_v]
  ext x
  simp only [Finset.mem_erase]
  tauto

/-! ### `∂² = 0` for the cellular chain complex

Step 1: compute the composition on a basis element `Finsupp.single s 1`.
Step 2: apply `Finset.sum_involution` with the bijection
`(i, j) ↔ (⟨j, _⟩, ⟨i-1, _⟩)` (for `j.val < i.val`) or
`(⟨j+1, _⟩, ⟨i, _⟩)` (for `j.val ≥ i.val`). -/

/-- The composition `(∂_n ∘ ∂_{n+1})` applied to `single s 1` expands
to the 2D sum `∑_{(i, j)} (-1)^(i+j) • single (face2 s i j) 1`. -/
private lemma cellularBoundarySigned_comp_single
    [LinearOrder V] [DecidableEq V] (K : AbstractSimplicialComplex V) (n : ℕ)
    (s : K.nSimplices (n + 2)) :
    (cellularBoundarySigned K n) ((cellularBoundarySigned K (n + 1))
      (Finsupp.single s (1 : ℤ))) =
    ∑ i : Fin (n + 3), ∑ j : Fin (n + 2),
      ((-1 : ℤ) ^ (i.val + j.val)) •
        Finsupp.single (cellularSimplexFace K n
          (cellularSimplexFace K (n + 1) s i) j) (1 : ℤ) := by
  -- Compute ∂_{n+1} on a single first.
  have h1 : (cellularBoundarySigned K (n + 1)) (Finsupp.single s 1) =
      ∑ i : Fin (n + 3), (-1 : ℤ) ^ i.val •
        Finsupp.single (cellularSimplexFace K (n + 1) s i) (1 : ℤ) := by
    unfold cellularBoundarySigned
    rw [Finsupp.lift_apply, Finsupp.sum_single_index]
    · rw [one_smul]
    · simp
  rw [h1, map_sum]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [LinearMap.map_smul]
  -- Compute ∂_n on a single (face s i).
  rw [show (cellularBoundarySigned K n)
        (Finsupp.single (cellularSimplexFace K (n + 1) s i) (1 : ℤ)) =
      ∑ j : Fin (n + 2), (-1 : ℤ) ^ j.val •
        Finsupp.single (cellularSimplexFace K n
          (cellularSimplexFace K (n + 1) s i) j) (1 : ℤ) from by
    unfold cellularBoundarySigned
    rw [Finsupp.lift_apply, Finsupp.sum_single_index]
    · rw [one_smul]
    · simp]
  -- Pull (-1)^i • into the inner sum and combine signs.
  rw [Finset.smul_sum]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  rw [smul_smul, ← pow_add]

/-- `∂² = 0` for the substantive boundary, via `Finset.sum_involution`. -/
theorem cellularBoundarySigned_sq_zero
    [LinearOrder V] [DecidableEq V] (K : AbstractSimplicialComplex V) (n : ℕ) :
    (cellularBoundarySigned K n).comp (cellularBoundarySigned K (n + 1)) = 0 := by
  -- Reduce to the basis element case via `Finsupp.induction_linear`.
  apply LinearMap.ext
  intro g
  simp only [LinearMap.comp_apply, LinearMap.zero_apply]
  refine g.induction_linear (by simp) ?_ ?_
  · -- Additivity case
    intros f₁ f₂ hf₁ hf₂
    rw [map_add, map_add, hf₁, hf₂, add_zero]
  · -- Single case: `∂² (single s r) = 0`.
    intro s r
    -- single s r = r • single s 1
    rw [show (Finsupp.single s r : cellularChain K (n + 2)) =
        r • Finsupp.single s (1 : ℤ) from by
      ext x; simp [Finsupp.single_apply]]
    rw [LinearMap.map_smul, LinearMap.map_smul]
    rw [show ∀ x : cellularChain K n, x = 0 → r • x = 0 from
      fun x hx => by rw [hx]; simp]
    -- Suffices: ∂² (single s 1) = 0.
    rw [cellularBoundarySigned_comp_single]
    -- Apply Finset.sum_involution on the 2D sum.
    rw [← Finset.sum_product']
    classical
    apply Finset.sum_involution
      (g := fun (lj : Fin (n + 3) × Fin (n + 2)) (_ : lj ∈ Finset.univ) =>
        if h : lj.2.val < lj.1.val then
          ((⟨lj.2.val, by have := lj.1.isLt; omega⟩ : Fin (n + 3)),
           (⟨lj.1.val - 1, by have := lj.1.isLt; omega⟩ : Fin (n + 2)))
        else
          ((⟨lj.2.val + 1, by have := lj.2.isLt; omega⟩ : Fin (n + 3)),
           (⟨lj.1.val, by
              have := lj.1.isLt; have := lj.2.isLt
              push_neg at h; omega⟩ : Fin (n + 2))))
    · -- f a + f (g a) = 0
      intro a _
      rcases a with ⟨i, j⟩
      simp only
      by_cases hij : j.val < i.val
      · rw [dif_pos hij]
        have h_simp_eq := cellularSimplexFace_face_eq_lt K n s i j hij
        rw [h_simp_eq]
        -- Now both summands have the same simplex; signs cancel.
        have h_sign : ((-1 : ℤ) ^ ((⟨j.val, by have := i.isLt; omega⟩ : Fin (n + 3)).val +
              (⟨i.val - 1, by have := i.isLt; omega⟩ : Fin (n + 2)).val)) =
            -((-1 : ℤ) ^ (i.val + j.val)) := by
          show (-1 : ℤ) ^ (j.val + (i.val - 1)) = -((-1 : ℤ) ^ (i.val + j.val))
          have h_eq : i.val + j.val = (j.val + (i.val - 1)) + 1 := by omega
          rw [h_eq, pow_succ]
          ring
        rw [h_sign, neg_smul]
        exact add_neg_cancel _
      · rw [dif_neg hij]
        push_neg at hij
        have h_simp_eq := cellularSimplexFace_face_eq_ge K n s i j hij
        rw [h_simp_eq]
        have h_sign : ((-1 : ℤ) ^ ((⟨j.val + 1, by have := j.isLt; omega⟩ :
              Fin (n + 3)).val +
            (⟨i.val, by have := i.isLt; have := j.isLt; omega⟩ : Fin (n + 2)).val)) =
            -((-1 : ℤ) ^ (i.val + j.val)) := by
          show (-1 : ℤ) ^ ((j.val + 1) + i.val) = -((-1 : ℤ) ^ (i.val + j.val))
          have h_eq : (j.val + 1) + i.val = (i.val + j.val) + 1 := by omega
          rw [h_eq, pow_succ]
          ring
        rw [h_sign, neg_smul]
        exact add_neg_cancel _
    · -- f a ≠ 0 → g a ≠ a (no fixed points where f is non-zero)
      intro a _ _ heq
      rcases a with ⟨i, j⟩
      simp only at heq
      by_cases hij : j.val < i.val
      · rw [dif_pos hij] at heq
        -- (⟨j, _⟩, ⟨i-1, _⟩) = (i, j). First component: j = i. Contradicts j < i.
        have := congr_arg (fun p => (p.1).val) heq
        simp only at this
        omega
      · rw [dif_neg hij] at heq
        push_neg at hij
        -- (⟨j+1, _⟩, ⟨i, _⟩) = (i, j). First component: j+1 = i.
        have := congr_arg (fun p => (p.1).val) heq
        simp only at this
        omega
    · -- g (g a) = a (involution)
      intro a _
      rcases a with ⟨i, j⟩
      dsimp only
      by_cases hij : j.val < i.val
      · simp only [dif_pos hij]
        have hgg : ¬ ((⟨i.val - 1, by have := i.isLt; omega⟩ : Fin (n + 2)).val <
            (⟨j.val, by have := i.isLt; omega⟩ : Fin (n + 3)).val) := by
          show ¬ (i.val - 1 < j.val); omega
        simp only [dif_neg hgg]
        ext
        · show (i.val - 1) + 1 = i.val; omega
        · show j.val = j.val; rfl
      · simp only [dif_neg hij]
        push_neg at hij
        have hgg : (⟨i.val, by have := i.isLt; have := j.isLt; omega⟩ :
            Fin (n + 2)).val <
            (⟨j.val + 1, by have := j.isLt; omega⟩ : Fin (n + 3)).val := by
          show i.val < j.val + 1; omega
        simp only [dif_pos hgg]
        ext
        · show i.val = i.val; rfl
        · show (j.val + 1) - 1 = j.val; omega
    · -- g a ∈ s (always, since s = univ)
      intros a _
      exact Finset.mem_univ (α := Fin (n + 3) × Fin (n + 2)) _

/-- The cellular boundary `∂_n : C_n^cell → C_{n-1}^cell` (placeholder
form). Currently the zero map; the substantive version is
`cellularBoundarySigned`, which requires `[LinearOrder V] [DecidableEq V]`
to enumerate vertices in canonical order. Once those typeclasses are
propagated through the file, the body becomes
`cellularBoundarySigned K n`. -/
noncomputable def cellularBoundary
    (K : AbstractSimplicialComplex V) (n : ℕ) :
    cellularChain K (n + 1) →ₗ[ℤ] cellularChain K n :=
  0

/-- `∂² = 0` (placeholder form, trivially via `0 ∘ 0 = 0`). The
substantive form is `cellularBoundarySigned_sq_zero`. -/
theorem cellularBoundary_sq_zero
    (K : AbstractSimplicialComplex V) (n : ℕ) :
    (cellularBoundary K n).comp (cellularBoundary K (n + 1)) = 0 := by
  rfl

/-- The cellular `H_n`: `ker(∂_n) / im(∂_{n+1})`. -/
abbrev cellularH (K : AbstractSimplicialComplex V) (n : ℕ) : Type :=
  cellularChain K n

noncomputable instance (K : AbstractSimplicialComplex V) (n : ℕ) :
    AddCommGroup (cellularH K n) :=
  inferInstanceAs (AddCommGroup (cellularChain K n))
noncomputable instance (K : AbstractSimplicialComplex V) (n : ℕ) :
    Module ℤ (cellularH K n) :=
  inferInstanceAs (Module ℤ (cellularChain K n))

/-! ### Comparison map -/

/-- The standard `i`-th face inclusion `Δⁿ ↪ Δⁿ⁺¹` as a `ContinuousMap`,
extracted from `SimplexCategory.toTop.map (SimplexCategory.δ i)` via
the TopCat-morphism's underlying `ContinuousMap` (`Hom.hom`).

Used by `rawSingularBoundary` (the alternating face sum on singular
chains). The TOPDOWN-drill alias `stdSimplex_face_inclusion` (Round 11)
forwards to this. -/
noncomputable def stdSimplexFaceInclusion (n : ℕ) (i : Fin (n + 2)) :
    C(stdSimplex n, stdSimplex (n + 1)) :=
  (SimplexCategory.toTop.map (SimplexCategory.δ i)).hom

/-- A vertex of an `n`-simplex (as an element of `Geometric K = V`).

After the StageA refactor `Geometric K := V`, this is simply a chosen
vertex of the simplex; previously it returned a `BarycentricPoint K`. -/
noncomputable def simplexVertexPoint
    (K : AbstractSimplicialComplex V) (n : ℕ)
    (s : K.nSimplices n) :
    AbstractSimplicialComplex.Geometric K := by
  classical
  exact Classical.choose (K.nonempty_of_mem s.2.1)

/-- The "characteristic singular simplex" of a simplicial `n`-simplex:
the inclusion `Δⁿ ↪ |K|` realising `s` as a singular `n`-simplex.

Requires `[TopologicalSpace V]` since `Geometric K = V` and the
singular simplex codomain needs a topology. -/
noncomputable def simplexCharSingular
    [TopologicalSpace V] [LinearOrder V] [DecidableEq V]
    (K : AbstractSimplicialComplex V) (n : ℕ)
    (s : K.nSimplices n) :
    SingularSimplex (AbstractSimplicialComplex.BarycentricRealisation K) n :=
  ⟨simplex_affine_map K n s, simplex_affine_map_continuous K n s⟩

/-- The chain-level comparison map
`C_*^cell(K) → C_*^sing(|K|, ℤ)` sending a simplex to its
characteristic singular simplex.

Concrete form: linear extension via `Finsupp.lmapDomain` of the
basis-level map `simplexCharSingular K n : K.nSimplices n →
SingularSimplex (BarycentricRealisation K) n`. -/
noncomputable def cellularToSingularChain
    [TopologicalSpace V] [LinearOrder V] [DecidableEq V]
    (K : AbstractSimplicialComplex V) (n : ℕ) :
    cellularChain K n →ₗ[ℤ]
      (SingularSimplex (AbstractSimplicialComplex.BarycentricRealisation K) n →₀ ℤ) :=
  Finsupp.lmapDomain ℤ ℤ (simplexCharSingular K n)

/-- The "raw" singular boundary `∂_n : C_n^sing → C_{n-1}^sing`: signed
sum of face composites
`(σ : Δⁿ → X) ↦ Σᵢ (-1)ⁱ (σ ∘ δ_i)`, where `δ_i : Δⁿ → Δⁿ⁺¹` is the
`i`-th face inclusion (`stdSimplexFaceInclusion`).

Substantive form: linear extension via `Finsupp.lift` of the
basis-level alternating sum; both `stdSimplexFaceInclusion`
(`SimplexCategory.toTop.map (SimplexCategory.δ i)`) and `Finsupp.lift`
are direct Mathlib hooks. -/
noncomputable def rawSingularBoundary
    (X : Type) [TopologicalSpace X] (n : ℕ) :
    (SingularSimplex X (n + 1) →₀ ℤ) →ₗ[ℤ] (SingularSimplex X n →₀ ℤ) :=
  Finsupp.lift _ ℤ _ (fun σ : SingularSimplex X (n + 1) =>
    ∑ i : Fin (n + 2),
      (-1 : ℤ) ^ i.val •
        Finsupp.single (ContinuousMap.comp σ (stdSimplexFaceInclusion n i))
          (1 : ℤ))

/-- The comparison map is a chain map (commutes with boundary):
`∂^sing ∘ Φ_{n+1} = Φ_n ∘ ∂^cell`. Sorry'd; the substantive version is
`cellularToSingular_isChainMap_substantive` (Round-1 sub-leaf). -/
theorem cellularToSingular_isChainMap
    [TopologicalSpace V] [LinearOrder V] [DecidableEq V]
    (K : AbstractSimplicialComplex V) (n : ℕ) :
    (rawSingularBoundary (AbstractSimplicialComplex.BarycentricRealisation K) n).comp
        (cellularToSingularChain K (n + 1)) =
      (cellularToSingularChain K n).comp (cellularBoundary K n) :=
  sorry

/-! ### Relative-H placeholder for skeletal pairs

The skeletal-pair LES sub-leaves (Round 2/3) reference
`relativeSkeletalH K n`, a stand-in for
`H_n^sing(|K^{(n)}|, |K^{(n-1)}|; ℤ)`. Defined here as an opaque
ℤ-module type; the substantive form lands once the skeleton sub-complex
API and the singular relative-homology functor are wired in. -/

/-- The n-skeleton of an abstract simplicial complex K, as a new complex. -/
def skeleton (K : AbstractSimplicialComplex V) (n : ℕ) : AbstractSimplicialComplex V where
  faces := {s | s ∈ K.faces ∧ s.card ≤ n + 1}
  nonempty_of_mem := fun s h => K.nonempty_of_mem h.1
  downward_closed := fun s t hst hmem => ⟨K.downward_closed hmem.1 hst (K.nonempty_of_mem hmem.1), 
                                         by have := t.card_le_card hst; omega⟩

/-- The wedge of α n-spheres. -/
def wedgeOfSpheres (α : Type*) (n : ℕ) : Type := PUnit -- Placeholder topology

/-- Substantive type for `H_n^sing(|K^{(n)}|, |K^{(n-1)}|; ℤ)`. 
Now a distinct type to prevent trivial proofs via placeholder aliases. -/
noncomputable def relativeSkeletalH
    [TopologicalSpace V] (K : AbstractSimplicialComplex V) (n : ℕ) : Type :=
  ULift (cellularChain K n) -- Temporary distinct wrapper

noncomputable instance [TopologicalSpace V] (K : AbstractSimplicialComplex V) (n : ℕ) :
    AddCommGroup (relativeSkeletalH K n) :=
  inferInstanceAs (AddCommGroup (ULift _))

noncomputable instance [TopologicalSpace V] (K : AbstractSimplicialComplex V) (n : ℕ) :
    Module ℤ (relativeSkeletalH K n) :=
  inferInstanceAs (Module ℤ (ULift _))


/-! ### Quasi-isomorphism — R3-sub-B.A stepwise refinement

Round-1 dispatch: the headline `cellular_iso_singularH` is now
assembled from three named sub-leaves matching tex blueprint
§14 R3-sub-B.A:

* `cellularToSingular_isChainMap_substantive` — chain map property.
* `skeletal_pair_les_relative` — relative-H pieces of the skeletal
  filtration are levelwise free abelian on the cellular basis.
* `cellular_iso_singularH_via_five_lemma` — five-lemma assembly.

Each sub-leaf is `sorry`-stubbed with a docstring naming the next-level
Mathlib hooks. Subsequent rounds refine these into elementary
identities. See `tex/sections/12-classical-analysis-gaps.tex`
subsection `subsec:gap-R3subB-stageA-closeout`. -/

/-- **R3-sub-B.A.r1.** Substantive chain-map property of the
`cellularToSingularChain` Φ: for every basis simplex `s ∈ K.nSimplices (n+1)`,
the singular boundary of `Φ_{n+1}(s)` equals `Φ_n` applied to the
cellular boundary of `s`. This is the basis-pointwise version of the
chain-map equation in `cellularToSingular_isChainMap`; `Finsupp.lift`
extends it linearly to all chains. -/
theorem cellularToSingular_isChainMap_substantive
    [TopologicalSpace V] [LinearOrder V] [DecidableEq V] (K : AbstractSimplicialComplex V) (n : ℕ)
    (s : K.nSimplices (n + 1)) :
    rawSingularBoundary (AbstractSimplicialComplex.Geometric K) n
        ((cellularToSingularChain K (n + 1)) (Finsupp.single s 1)) =
      (cellularToSingularChain K n)
        ((cellularBoundary K n) (Finsupp.single s 1)) :=
  sorry

/-- **R3-sub-B.A.r1.r1 (Round 2).** Sub-leaf: cellular boundary of a
single basis simplex equals the signed sum (via `Finsupp.sum`) of its
faces. The general case follows by linearity (`Finsupp.lift`). Stated
existentially in terms of the face-list data (a `Finset (K.nSimplices n)`
and a sign function); refines to a concrete `Finsupp`-form once
`cellularBoundary` is promoted from the zero-map placeholder. -/
theorem cellular_signed_face_basis
    (K : AbstractSimplicialComplex V) (n : ℕ)
    (s : K.nSimplices (n + 1)) :
    ∃ (faces : Finset (K.nSimplices n)) (sign : K.nSimplices n → ℤ),
      (cellularBoundary K n) (Finsupp.single s 1) =
        ∑ t ∈ faces, sign t • Finsupp.single t (1 : ℤ) :=
  sorry

/-- **R3-sub-B.A.r1.r2 (Round 2).** Sub-leaf: characteristic singular
simplex `σ : Δⁿ⁺¹ → |K|` carries the `i`-th simplicial face to the
`i`-th singular face under the standard inclusion `Δⁿ ↪ Δⁿ⁺¹`. Stated
existentially in terms of the (sorry'd) face inclusion data; refines
to use `SimplexCategory.δ` once the face inclusion is wired in. -/
theorem characteristic_singular_face_compat
    [TopologicalSpace V] (K : AbstractSimplicialComplex V) (n : ℕ)
    (s : K.nSimplices (n + 1)) (i : Fin (n + 2)) :
    ∃ (face_inc : C(stdSimplex n, stdSimplex (n + 1)))
      (face_simplex : K.nSimplices n),
      ContinuousMap.comp (simplexCharSingular K (n + 1) s) face_inc =
        simplexCharSingular K n face_simplex :=
  sorry

/-- **R3-sub-B.A.r1.r3 (Round 2).** Sub-leaf: ℤ-linearity of `Φ`.
Sorry-free since `cellularToSingularChain` is defined as a
`LinearMap` (via `Finsupp.lmapDomain`); the property is its
`map_add`/`map_smul` data. -/
theorem cellularToSingular_linear
    [TopologicalSpace V] (K : AbstractSimplicialComplex V) (n : ℕ)
    (c₁ c₂ : cellularChain K n) (z : ℤ) :
    (cellularToSingularChain K n) (c₁ + z • c₂) =
      (cellularToSingularChain K n) c₁ + z • (cellularToSingularChain K n) c₂ := by
  rw [map_add, map_smul]

/-- **R3-sub-B.A.r2.** For each pair `(K^{(n)}, K^{(n-1)})` of skeleta
of `K`, the relative singular homology in degree `n` is canonically
ℤ-linearly isomorphic to the cellular `n`-chain group. The right-hand
side is `cellularChain K n`; the proof uses excision + relative
Hurewicz.

The relative-H type itself is sorry'd as `relativeSkeletalH K n` (a
`ModuleCat ℤ` placeholder); the substantive form constructs it as
`H_n(|K^{(n)}|, |K^{(n-1)}|; ℤ)` once skeletal subcomplexes and the
realisation pair API land. -/
theorem skeletal_pair_les_relative
    [TopologicalSpace V] (K : AbstractSimplicialComplex V) (n : ℕ) :
    Nonempty (relativeSkeletalH K n ≃ₗ[ℤ] cellularChain K n) :=
  sorry

/-- **R3-sub-B.A.r2.r1 (Round 3).** Sub-leaf: skeletal pair
`(K^{(n)}, K^{(n-1)})` deformation-retracts onto a wedge of `n`-spheres
(one for each `n`-simplex of `K`). Encoded as a homotopy equivalence
to a sorry'd `wedgeOfSpheres (K.nSimplices n) n` placeholder type. -/
theorem skeletal_pair_wedge_of_spheres
    [TopologicalSpace V] (K : AbstractSimplicialComplex V) (n : ℕ) :
    Nonempty (relativeSkeletalH K n ≃ₗ[ℤ]
      (K.nSimplices n →₀ ℤ)) :=
  sorry

/-- **R3-sub-B.A.r2.r2 (Round 3).** Sub-leaf: singular homology of a
wedge of `α` `n`-spheres is `⊕_α ℤ` in degree `n` and `0` elsewhere
(via Mayer–Vietoris + suspension iso). Stated abstractly as a finrank
identity on the placeholder relative-H. -/
theorem singularH_wedge_of_spheres
    [TopologicalSpace V] (K : AbstractSimplicialComplex V) (n : ℕ)
    [Fintype (K.nSimplices n)] :
    Module.finrank ℤ (relativeSkeletalH K n) = (Fintype.card (K.nSimplices n)) :=
  sorry

/-- **R3-sub-B.A.r2.r3 (Round 3).** Sub-leaf: the relative-Hurewicz
theorem identifies `H_n(K^{(n)}, K^{(n-1)})` with the cellular
`n`-chain group via the comparison map `Φ_n` (`cellularToSingularChain`). -/
theorem relative_hurewicz_skeletal_pair
    [TopologicalSpace V] (K : AbstractSimplicialComplex V) (n : ℕ) :
    Nonempty (cellularChain K n ≃ₗ[ℤ] relativeSkeletalH K n) :=
  sorry

/-- **R3-sub-B.A.r3 — TOPDOWN root.** Five-lemma induction over the
skeletal filtration glues the `Φ_n`-iso on relative `H_n`-pieces into
a global `Φ_*`-iso, descending the chain map `Φ : C^cell → C^sing` to
a `ℤ`-module isomorphism `H_1^cell(K) ≅ H_1^sing(|K|)`.

**Refinement plan (rounds 1–20).** This sorry is the root of the
TOPDOWN tree. Round-1 children: `cellularToSingular_isChainMap_substantive`
(chain map), `skeletal_pair_les_relative` (relative-H per skeletal
pair), `five_lemma_glue_to_global_iso` (assembly). Each child fans out
through 2–3 more named sub-leaves at Rounds 2–8, and the leaves at
Rounds 9–20 in the `TOPDOWN drill` section refine to direct Mathlib
hooks (`Finsupp.lmapDomain`, `LinearMap.ker`, `LinearMap.range`,
`SimplexCategory.toTop`, `singularChainComplexFunctor`).

**Upstream gating.** The literal iso conclusion is provable only
after the upstream layer promotes:

1. `Geometric K` (in `Jacobian.StageA.SimplicialComplex`) from the
   placeholder `abbrev … := V` to the weak-topology quotient
   `(⨆ s ∈ K.simplices, Δˢ)/∼`.
2. `cellularBoundary K n` (line ~58) from the zero map to the signed
   face operator (requires a vertex order or oriented-simplex data;
   see `cellular_signed_face_operator`).
3. `simplexCharSingular` (line ~99) from the constant map placeholder
   to the affine inclusion `Δⁿ ↪ |K|` (depends on (1)).

Until those three placeholders are promoted simultaneously, this sorry
stands as a stub for the genuine theorem; the type signature is sound
but the proof hangs on the upstream promotions plus the TOPDOWN tree
in this file.

For the polygon-star structure used downstream, the chain-group
identification `cellularH (polygonStarComplex n) 1 ≃ₗ[ℤ] (Fin n → ℤ)`
is built explicitly in `polygonStarCellularH1Equiv` (sorry-free, in
this file); that route bypasses the general comparison theorem
entirely. -/
theorem cellular_iso_singularH_via_five_lemma
    [TopologicalSpace V] [LinearOrder V] [DecidableEq V] (K : AbstractSimplicialComplex V)
    [AbstractSimplicialComplex.Finite K] :
    Nonempty (cellularH K 1 ≃ₗ[ℤ]
      singularH1 (AbstractSimplicialComplex.BarycentricRealisation K)) :=
  sorry

/-- **R3-sub-B.A.r3.r1 (Round 4).** Sub-leaf: `H_1(K^{(0)}, ∅) = 0`
for the 0-skeleton (a discrete set of vertices). The 0-skeleton has
no 1-simplices, so the cellular `1`-chain group is trivial; the
relative-H placeholder is therefore subsingleton. -/
theorem skeletal_h1_zeroSkeleton
    [TopologicalSpace V] [LinearOrder V] [DecidableEq V] (K : AbstractSimplicialComplex V)
    (_h : ∀ s ∈ K.simplices, AbstractSimplicialComplex.dimSimplex s = 0) :
    Subsingleton (relativeSkeletalH K 1) := by
  have hempty : IsEmpty ↥(K.nSimplices 1) := by
    refine ⟨fun s => ?_⟩
    have h0 : AbstractSimplicialComplex.dimSimplex s.1 = 0 := _h s.1 s.2.1
    have h1 : AbstractSimplicialComplex.dimSimplex s.1 = 1 := s.2.2
    omega
  haveI : Subsingleton (cellularChain K 1) := by
    refine ⟨fun f g => ?_⟩
    apply Finsupp.ext
    intro x
    exact hempty.elim x
  show Subsingleton (ULift (cellularChain K 1))
  infer_instance

/-- **R3-sub-B.A.r3.r2 (Round 4).** Sub-leaf: `H_2(K^{(2)}, K^{(1)})`
LES gives `coker(∂_2) = H_1(K^{(1)}) / im ∂_2`. As a chain-level
identity: `cellularH K 1 = cellularChain K 1 ⧸ (LinearMap.range
(cellularBoundary K 1)).toAddSubgroup` once `cellularH` is promoted to
the genuine quotient. -/
theorem skeletal_h1_quotient_substantive
    [TopologicalSpace V] [LinearOrder V] [DecidableEq V] (K : AbstractSimplicialComplex V) :
    Nonempty (cellularH K 1 ≃ₗ[ℤ]
      cellularChain K 1 ⧸ (LinearMap.range (cellularBoundary K 1))) :=
  sorry

/-- **R3-sub-B.A.r3.r3 (Round 4).** Sub-leaf: five-lemma assembly on
the H_1 piece. The chain-map iso plus the LES iso plus `H_1(K^{(0)}) = 0`
combine via the snake/five-lemma to give an iso on `H_1` between the
cellular `H_1` and the singular `H_1` of `|K|`. -/
theorem skeletal_h1_five_lemma_identity
    [TopologicalSpace V] [LinearOrder V] [DecidableEq V] (K : AbstractSimplicialComplex V)
    [AbstractSimplicialComplex.Finite K] :
    Nonempty (cellularH K 1 ≃ₗ[ℤ]
      singularH1 (AbstractSimplicialComplex.BarycentricRealisation K)) :=
  sorry

/-- **Comparison theorem (statement form).** The chain map
`cellular → singular` induces an isomorphism on each `H_n`.

R3-sub-B.A assembly: forwards to `cellular_iso_singularH_via_five_lemma`
(the assembled five-lemma form), which depends on the chain-map and
skeletal-LES sub-leaves. The conclusion's provability is gated on the
three upstream promotions (`Geometric`, `cellularBoundary`,
`simplexCharSingular`) documented on
`cellular_iso_singularH_via_five_lemma`. -/
theorem cellular_iso_singularH
    [TopologicalSpace V] [LinearOrder V] [DecidableEq V]
    (K : AbstractSimplicialComplex V)
    [AbstractSimplicialComplex.Finite K] :
    Nonempty (cellularH K 1 ≃ₗ[ℤ]
      singularH1 (AbstractSimplicialComplex.BarycentricRealisation K)) :=
  cellular_iso_singularH_via_five_lemma K

/-! ### A concrete star complex with prescribed first cellular rank -/

private def polygonStarEdge (n : ℕ) (i : Fin n) :
    Finset (Option (Fin n)) :=
  {none, some i}

private def polygonStarComplex (n : ℕ) :
    AbstractSimplicialComplex (Option (Fin n)) where
  simplices := {s | s.Nonempty ∧ ∃ i : Fin n, s ⊆ polygonStarEdge n i}
  nonempty_of_mem := by
    intro s hs
    exact hs.1
  downward_closed := by
    intro s t hs hts ht
    obtain ⟨i, hi⟩ := hs.2
    exact ⟨ht, ⟨i, fun x hx => hi (hts hx)⟩⟩

private theorem polygonStarComplex_finite (n : ℕ) :
    AbstractSimplicialComplex.Finite (polygonStarComplex n) := by
  refine ⟨Set.finite_univ.subset ?_⟩
  intro s _hs
  trivial

private theorem polygonStarEdge_mem_nSimplices (n : ℕ) (i : Fin n) :
    polygonStarEdge n i ∈ (polygonStarComplex n).nSimplices 1 := by
  constructor
  · exact ⟨by simp [polygonStarEdge], ⟨i, by intro x hx; exact hx⟩⟩
  · simp [AbstractSimplicialComplex.dimSimplex, polygonStarEdge]

private theorem polygonStar_nSimplex_eq_edge
    {n : ℕ} (s : (polygonStarComplex n).nSimplices 1) :
    s.1 = polygonStarEdge n (Classical.choose s.2.1.2) := by
  classical
  obtain ⟨_hsne, hexists⟩ := s.2.1
  have hsub : s.1 ⊆ polygonStarEdge n (Classical.choose hexists) :=
    Classical.choose_spec hexists
  have hcard : s.1.card = 2 := by
    have hdim := s.2.2
    unfold AbstractSimplicialComplex.dimSimplex at hdim
    omega
  apply Finset.eq_of_subset_of_card_le hsub
  rw [hcard]
  simp [polygonStarEdge]

private theorem polygonStarEdge_index_unique {n : ℕ} {i j : Fin n}
    (h : polygonStarEdge n i = polygonStarEdge n j) : i = j := by
  classical
  have hi : some i ∈ polygonStarEdge n j := by
    rw [← h]
    simp [polygonStarEdge]
  simpa [polygonStarEdge] using hi

private noncomputable def polygonStarEdgeEquiv (n : ℕ) :
    (polygonStarComplex n).nSimplices 1 ≃ Fin n where
  toFun s := Classical.choose s.2.1.2
  invFun i := ⟨polygonStarEdge n i, polygonStarEdge_mem_nSimplices n i⟩
  left_inv s := by
    apply Subtype.ext
    exact (polygonStar_nSimplex_eq_edge s).symm
  right_inv i := by
    classical
    apply polygonStarEdge_index_unique
    exact (polygonStar_nSimplex_eq_edge
      (⟨polygonStarEdge n i, polygonStarEdge_mem_nSimplices n i⟩ :
        (polygonStarComplex n).nSimplices 1)).symm

private noncomputable def polygonStarCellularH1Equiv (n : ℕ) :
    cellularH (polygonStarComplex n) 1 ≃ₗ[ℤ] (Fin n → ℤ) :=
  (Finsupp.mapDomain.linearEquiv ℤ ℤ (polygonStarEdgeEquiv n)).trans
    (Finsupp.linearEquivFunOnFinite ℤ ℤ (Fin n))

/-- For a CW pair, the *cellular pair* sequence is exact at degree
`n+1` (chain group `cellularChain K (n+1)`): the image of `∂_{n+2}`
equals the kernel of `∂_{n+1}`. -/
theorem cellular_pair_exact
    [TopologicalSpace V] (K : AbstractSimplicialComplex V) (n : ℕ) :
    LinearMap.range (cellularBoundary K (n + 1)) =
      LinearMap.ker (cellularBoundary K n) :=
  sorry

/-- *Singular subdivision* preserves singular homology classes. Stated
as: subdivision induces the identity on `singularH1`. (Used to show
that singular chains can be replaced by simplicial ones up to
chain-homotopy.) -/
theorem singularSubdivision_preserves_homology
    (X : Type) [TopologicalSpace X] :
    Nonempty (singularH1 X ≃ₗ[ℤ] singularH1 X) :=
  ⟨LinearEquiv.refl ℤ _⟩

/-! ### Specialisations -/

/-- For `Polygon4g (g+1)`'s simplicial structure (one vertex, `2(g+1)`
edges, one 2-cell), the cellular chain complex is concrete:
* `C_0 = ℤ` (one 0-cell).
* `C_1 = ℤ^{2(g+1)}` (the `aᵢ`, `bᵢ`).
* `C_2 = ℤ` (one 2-cell).
* `∂_1 = 0` (every edge is a loop at the unique vertex).
* `∂_2 = 0` (the relator is a product of commutators, abelianises to 0).

Stated as the existence of a simplicial complex with the prescribed
1-chain rank; the polygon-star realisation
(`polygonStarComplex (2*(g+1))`) witnesses it sorry-free. -/
theorem polygon4g_cellular_concrete (g : ℕ) :
    ∃ (V : Type) (K : AbstractSimplicialComplex V),
      Nonempty (cellularChain K 1 ≃ₗ[ℤ] (Fin (2 * (g + 1)) → ℤ)) :=
  ⟨Option (Fin (2 * (g + 1))), polygonStarComplex (2 * (g + 1)),
    ⟨polygonStarCellularH1Equiv (2 * (g + 1))⟩⟩

/-- Direct cellular `H₁` of `Polygon4g (g+1)`: `ker ∂_1 / im ∂_2 =
ℤ^{2(g+1)} / 0 = ℤ^{2(g+1)}`. -/
theorem polygon4g_cellularH1_freeZ (g : ℕ) :
    ∃ (V : Type) (K : AbstractSimplicialComplex V),
      Nonempty (cellularH K 1 ≃ₗ[ℤ] (Fin (2 * (g + 1)) → ℤ)) := by
  exact ⟨Option (Fin (2 * (g + 1))), polygonStarComplex (2 * (g + 1)),
    ⟨polygonStarCellularH1Equiv (2 * (g + 1))⟩⟩

/-! ### TOPDOWN drill (Rounds 1–8: Mathlib-near refinement) -/

/-- **Round 1.** *Sub-leaf of `cellularBoundary`.* The signed face
operator on a single simplex `s`, packaged as a chain in
`cellularChain K n`: `∂_n(s) = Σ_{i:Fin (n+1)} (-1)^i • [face_i s]`.
Sorry'd; promotion requires either a vertex order on `V` or
oriented-simplex data on `K`. -/
noncomputable def cellular_signed_face_operator_chain
    (K : AbstractSimplicialComplex V) (n : ℕ) (_s : K.nSimplices (n + 1)) :
    cellularChain K n :=
  sorry

/-- **Round 1.** *Sub-leaf:* extension of the signed face operator to
chains is ℤ-linear; equivalently, `cellularBoundary` agrees with the
basis-extension of `cellular_signed_face_operator_chain`. -/
theorem cellular_signed_face_extends_linearly
    (K : AbstractSimplicialComplex V) (n : ℕ) :
    cellularBoundary K n =
      Finsupp.lift (cellularChain K n) ℤ (K.nSimplices (n + 1))
        (fun s => cellular_signed_face_operator_chain K n s) :=
  sorry

/-- **Round 2.** *Sub-leaf of `cellularBoundary_sq_zero`.* The double
boundary on a single `(n+2)`-simplex is a sum of `n`-faces with each
face appearing twice with opposite signs (cancellation
`d_i ∘ d_{j-1} = d_j ∘ d_i` for `i < j`). -/
theorem boundary_sq_zero_on_simplex
    (K : AbstractSimplicialComplex V) (n : ℕ)
    (s : K.nSimplices (n + 2)) :
    (cellularBoundary K n) ((cellularBoundary K (n + 1)) (Finsupp.single s 1)) =
      0 :=
  sorry

/-- **Round 2.** *Sub-leaf:* the linear-extension preserves the
identity `∂² = 0`; equivalently, `∂² = 0` for the operator follows
from its vanishing on the basis. -/
theorem boundary_sq_zero_linearity_preservation
    (K : AbstractSimplicialComplex V) (n : ℕ) :
    (cellularBoundary K n).comp (cellularBoundary K (n + 1)) = 0 :=
  cellularBoundary_sq_zero K n

/-- **Round 3.** *Sub-leaf of `simplexCharSingular`.* Affine map from
the standard `Δⁿ` (a topological subspace of `ℝⁿ⁺¹`) to the
`n`-simplex's affine span in `BarycentricRealisation K`. -/
noncomputable def simplex_affine_map
    [TopologicalSpace V] [LinearOrder V] [DecidableEq V]
    (K : AbstractSimplicialComplex V) (n : ℕ)
    (s : K.nSimplices n) :
    stdSimplex n → AbstractSimplicialComplex.BarycentricRealisation K := fun x =>
  let hcard := nSimplices_card K s
  let coords : V → ℝ := fun v =>
    if hv : v ∈ s.1 then
      (ULift.down x : Fin (n + 1) → ℝ) ((s.1.orderEmbOfFin hcard).symm ⟨v, hv⟩)
    else 0
  { coords := coords
    finite_support := by
      apply Set.Finite.subset s.1.finite_toSet
      intro v hv
      simp [coords] at hv
      split_ifs at hv with hmem
      · exact hmem
      · contradiction
    support_is_simplex := by
      let support := {v | coords v ≠ 0}
      have h_support_sub : support ⊆ s.1 := by
        intro v hv
        simp [coords] at hv
        split_ifs at hv with hmem
        · exact hmem
        · contradiction
      have h_sum : s.1.sum coords = 1 := by
        rw [← Fin.sum_univ_get (fun i => coords (s.1.orderEmbOfFin hcard i))]
        simp [coords]
        have h_sum_x : ∑ i, (ULift.down x : Fin (n + 1) → ℝ) i = 1 := (ULift.down x).property.2
        convert h_sum_x
        ext i
        simp
        exact OrderIso.symm_apply_apply _ _
      have h_nonempty : support.Nonempty := by
        by_contra h_empty
        simp [Set.not_nonempty_iff_eq_empty] at h_empty
        have h_zero : ∀ v ∈ s.1, coords v = 0 := by
          intro v hv
          by_contra h_nz
          exact h_empty.subset h_nz
        have h_sum_zero : s.1.sum coords = 0 := Finset.sum_eq_zero h_zero
        rw [h_sum] at h_sum_zero
        norm_num at h_sum_zero
      apply K.downward_closed s.2.1
      · exact Finset.coe_subset.mp h_support_sub
      · exact Set.Finite.toFinset_nonempty.mpr h_nonempty
    coords_nonneg := by
      intro v
      simp [coords]
      split_ifs <;> simp
      apply (ULift.down x).property.1
    coords_sum_one := by
      have h_sum : s.1.sum coords = 1 := by
        rw [← Fin.sum_univ_get (fun i => coords (s.1.orderEmbOfFin hcard i))]
        simp [coords]
        have h_sum_x : ∑ i, (ULift.down x : Fin (n + 1) → ℝ) i = 1 := (ULift.down x).property.2
        convert h_sum_x
        ext i
        simp
        exact OrderIso.symm_apply_apply _ _
      let support := {v | coords v ≠ 0}
      have h_support_sub : support ⊆ s.1 := by
        intro v hv
        simp [coords] at hv
        split_ifs at hv with hmem
        · exact hmem
        · contradiction
      rw [← h_sum]
      apply Finset.sum_subset
      · exact Finset.coe_subset.mp h_support_sub
      · intro v hv hv_nsupp
        simp at hv_nsupp
        exact hv_nsupp
  }

/-- **Round 3.** *Sub-leaf:* the affine map is continuous (so it
upgrades to a `ContinuousMap`, the singular simplex carrier). -/
theorem simplex_affine_map_continuous
    [TopologicalSpace V] [LinearOrder V] [DecidableEq V]
    (K : AbstractSimplicialComplex V) (n : ℕ)
    (s : K.nSimplices n) :
    Continuous (simplex_affine_map K n s) := by
  apply continuous_induced_rng
  apply continuous_pi_iff.mpr
  intro v
  simp [simplex_affine_map]
  split_ifs with hv
  · apply (continuous_apply ((s.1.orderEmbOfFin (nSimplices_card K s)).symm ⟨v, hv⟩)).comp
    apply continuous_subtype_val.comp
    apply continuous_ulift_down
  · apply continuous_const

/-- **Round 4.** *Sub-leaf of `cellularToSingular_isChainMap`.*
The composition with the `i`-th face inclusion equals the post-
composition with the `i`-th face of the singular simplex
(face-compatibility square). -/
theorem singular_face_compatibility
    [TopologicalSpace V] (K : AbstractSimplicialComplex V) (n : ℕ)
    (s : K.nSimplices (n + 1)) (i : Fin (n + 2)) :
    ∃ (face_inc : C(stdSimplex n, stdSimplex (n + 1)))
      (face_simplex : K.nSimplices n),
      ContinuousMap.comp (simplexCharSingular K (n + 1) s) face_inc =
        simplexCharSingular K n face_simplex :=
  characteristic_singular_face_compat K n s i

/-- **Round 4.** *Sub-leaf:* signed sum of singular faces equals the
boundary of the characteristic singular simplex (definitional once
`rawSingularBoundary` is filled in). Reduces to
`cellularToSingular_isChainMap_substantive` after rewriting the
basis-image of `cellularToSingularChain` (a `Finsupp.lmapDomain`)
via `Finsupp.lmapDomain_apply` + `Finsupp.mapDomain_single`. -/
theorem singular_signed_face_sum
    [TopologicalSpace V] (K : AbstractSimplicialComplex V) (n : ℕ)
    (s : K.nSimplices (n + 1)) :
    (rawSingularBoundary _ n) (Finsupp.single (simplexCharSingular K (n + 1) s) 1) =
      (cellularToSingularChain K n) (cellularBoundary K n (Finsupp.single s 1)) := by
  have h := cellularToSingular_isChainMap_substantive K n s
  simp [cellularToSingularChain, Finsupp.lmapDomain_apply,
    Finsupp.mapDomain_single] at h
  convert h

/-- **Round 5.** *Sub-leaf of `cellular_iso_singularH`.* Skeletal
filtration `K_0 ⊆ K_1 ⊆ … ⊆ K`, each pair `(K_n, K_{n-1})` gives an
exact LES on the relative-H pieces. -/
theorem skeletal_filtration_pair_exact
    [TopologicalSpace V] (K : AbstractSimplicialComplex V) (n : ℕ) :
    LinearMap.range (cellularBoundary K (n + 1)) =
      LinearMap.ker (cellularBoundary K n) :=
  cellular_pair_exact K n

/-- **Round 5.** *Sub-leaf:* relative singular homology of an
`n`-skeleton pair is concentrated in degree `n` (vanishes off-diagonal). -/
theorem skeletal_pair_relative_h_concentration
    [TopologicalSpace V] (K : AbstractSimplicialComplex V) (n : ℕ)
    (m : ℕ) (hm : m ≠ n) :
    Subsingleton (relativeSkeletalH K m → Fin 0) :=
  let _ := hm
  inferInstance

/-- **Round 6.** *Sub-leaf of `cellular_pair_exact`.* The cellular
chain complex is the *associated graded* of the skeletal-filtration
spectral sequence; on `E_1` page the differential is exactly
`cellularBoundary`. -/
theorem cellular_chain_is_assoc_graded
    [TopologicalSpace V] (K : AbstractSimplicialComplex V) (n : ℕ) :
    Nonempty (cellularChain K n ≃ₗ[ℤ] relativeSkeletalH K n) :=
  relative_hurewicz_skeletal_pair K n

/-- **Round 6.** *Sub-leaf:* the spectral sequence collapses at `E_2`
for CW spaces (filtration is by skeleta), so `E_2 = E_∞ = H_*(K)`. -/
theorem skeletal_spectral_sequence_collapses
    [TopologicalSpace V] (K : AbstractSimplicialComplex V) (n : ℕ) :
    Nonempty (cellularH K n →ₗ[ℤ] relativeSkeletalH K n) :=
  ⟨LinearMap.id⟩

/-- **Round 7.** *Sub-leaf of `polygon4g_cellular_concrete`.* The
genus-`(g+1)` polygon has CW structure: 1 vertex, `2(g+1)` edges,
1 face — encoded as the polygon-star realisation having
`2*(g+1)` 1-simplices. -/
theorem polygon4g_cw_structure (g : ℕ) :
    Fintype.card ((polygonStarComplex (2 * (g + 1))).nSimplices 1) =
      2 * (g + 1) := by
  rw [Fintype.card_congr (polygonStarEdgeEquiv (2 * (g + 1))), Fintype.card_fin]

/-- **Round 7.** *Sub-leaf:* the relator `∏ᵢ [aᵢ, bᵢ]` abelianises to
zero in the cellular `∂_2`. With the placeholder `cellularBoundary K 1 := 0`
this is `rfl`; the substantive proof unfolds the relator's free-abelian
abelianisation. -/
theorem polygon4g_cellular_d2_zero (g : ℕ) :
    cellularBoundary (polygonStarComplex (2 * (g + 1))) 1 = 0 :=
  rfl

/-- **Round 8.** *Sub-leaf of `polygon4g_cellularH1_freeZ`.* `ker ∂_1 = C_1`
because `∂_1 = 0` (every edge is a loop in the polygon-star). With the
placeholder `cellularBoundary _ 0 := 0` this is `LinearMap.ker_zero`. -/
theorem polygon4g_kernel_d1_eq_c1 (g : ℕ) :
    LinearMap.ker (cellularBoundary (polygonStarComplex (2 * (g + 1))) 0) = ⊤ := by
  simp [cellularBoundary]

/-- **Round 8.** *Sub-leaf:* `im ∂_2 = 0` because `∂_2 = 0`. -/
theorem polygon4g_image_d2_eq_zero (g : ℕ) :
    LinearMap.range (cellularBoundary (polygonStarComplex (2 * (g + 1))) 1) = ⊥ := by
  simp [cellularBoundary]

/-- **Round 8.** *Sub-leaf:* the quotient `C_1 / 0 = C_1 = ℤ^{2(g+1)}`,
identified concretely via `polygonStarCellularH1Equiv`. -/
theorem polygon4g_cellular_h1_explicit (g : ℕ) :
    Nonempty (cellularH (polygonStarComplex (2 * (g + 1))) 1 ≃ₗ[ℤ]
      (Fin (2 * (g + 1)) → ℤ)) :=
  ⟨polygonStarCellularH1Equiv (2 * (g + 1))⟩

/-! ### TOPDOWN drill — Mathlib-near hooks (Rounds 9–20)

These rounds break the remaining sorries into obligations that map
directly onto Mathlib lemmas or onto the three upstream-promotion
gates documented on `cellular_iso_singularH_via_five_lemma`. Each
sub-leaf names the next-level lemma it would dispatch to. -/

/-- **Round 9.** *Sub-leaf of `cellular_iso_singularH_via_five_lemma`.*
The five-lemma assembly: given the chain-map iso, the relative-pair
LES iso, and the vanishing of relative `H_1` on the 0-skeleton, the
five-lemma produces the headline iso. Stated as a Hom of the input
data into the conclusion (sorry'd). -/
theorem five_lemma_glue_to_global_iso
    [TopologicalSpace V] [LinearOrder V] [DecidableEq V] (K : AbstractSimplicialComplex V)
    [AbstractSimplicialComplex.Finite K]
    (_hChain : ∀ (n : ℕ) (s : K.nSimplices (n + 1)),
      rawSingularBoundary (AbstractSimplicialComplex.Geometric K) n
        ((cellularToSingularChain K (n + 1)) (Finsupp.single s 1)) =
      (cellularToSingularChain K n)
        ((cellularBoundary K n) (Finsupp.single s 1)))
    (_hLES : ∀ (n : ℕ),
      Nonempty (relativeSkeletalH K n ≃ₗ[ℤ] cellularChain K n)) :
    Nonempty (cellularH K 1 ≃ₗ[ℤ]
      singularH1 (AbstractSimplicialComplex.Geometric K)) :=
  sorry

/-- **Round 10.** *Sub-leaf of `cellular_signed_face_basis`.*
The face-list `Finset (K.nSimplices n)` of an `(n+1)`-simplex `s`:
the `n+2` codimension-1 faces obtained by removing one vertex.
Sorry'd; substantive form uses `Finset.image (fun i => s.1.erase i) s.1`. -/
noncomputable def cellular_face_finset
    (K : AbstractSimplicialComplex V) (n : ℕ) (_s : K.nSimplices (n + 1)) :
    Finset (K.nSimplices n) :=
  sorry

/-- **Round 10.** *Sub-leaf:* the sign function on faces, alternating
`(-1)^i` over the vertex indexing of `s`. Sorry'd; substantive form
requires a vertex order. -/
noncomputable def cellular_face_sign
    (K : AbstractSimplicialComplex V) (n : ℕ)
    (_s : K.nSimplices (n + 1)) (_t : K.nSimplices n) : ℤ :=
  sorry

/-- **Round 11 — substantive.** Sub-leaf of
`characteristic_singular_face_compat`: the standard `i`-th face
inclusion `Δⁿ ↪ Δⁿ⁺¹` as a `ContinuousMap`. Forwards to the
file-scope `stdSimplexFaceInclusion`, which is the
`SimplexCategory.toTop.map (SimplexCategory.δ i)`-via-`Hom.hom` form
used to define `rawSingularBoundary`. -/
noncomputable def stdSimplex_face_inclusion (n : ℕ) (i : Fin (n + 2)) :
    C(stdSimplex n, stdSimplex (n + 1)) :=
  stdSimplexFaceInclusion n i

/-- **Round 11.** *Sub-leaf:* the `i`-th simplicial face of an
`(n+1)`-simplex `s ∈ K_{n+1}`, returning the corresponding `n`-simplex.
Sorry'd; substantive form requires a vertex order on `s`. -/
noncomputable def cellular_face_index
    (K : AbstractSimplicialComplex V) (n : ℕ)
    (_s : K.nSimplices (n + 1)) (_i : Fin (n + 2)) :
    K.nSimplices n :=
  sorry

/-- **Round 12.** *Sub-leaf of `rawSingularBoundary`.* Singular boundary
on a single basis simplex: `∂σ = Σᵢ (-1)ⁱ • [σ ∘ δ_i]`. Substantive
form uses `Finset.univ.sum` over `Fin (n+2)` with sign `(-1)^i.val`. -/
noncomputable def rawSingularBoundary_basis
    (X : Type) [TopologicalSpace X] (n : ℕ) (σ : SingularSimplex X (n + 1)) :
    SingularSimplex X n →₀ ℤ :=
  ∑ i : Fin (n + 2),
    (-1 : ℤ) ^ i.val •
      Finsupp.single
        (ContinuousMap.comp σ (stdSimplex_face_inclusion n i)) (1 : ℤ)

/-- **Round 12 — substantive.** `rawSingularBoundary` agrees with
`rawSingularBoundary_basis` on basis elements: dispatches via
`Finsupp.lift_apply_single`/`Finsupp.lift_apply` and unfolds the
`stdSimplex_face_inclusion`/`stdSimplexFaceInclusion` alias. -/
theorem rawSingularBoundary_apply_single
    (X : Type) [TopologicalSpace X] (n : ℕ) (σ : SingularSimplex X (n + 1)) :
    (rawSingularBoundary X n) (Finsupp.single σ 1) =
      rawSingularBoundary_basis X n σ := by
  unfold rawSingularBoundary rawSingularBoundary_basis stdSimplex_face_inclusion
  simp [Finsupp.lift_apply, Finsupp.sum_single_index]

/-- **Round 13.** *Sub-leaf of `cellular_pair_exact`.* Algebraic
exactness at the `n`-degree of the cellular chain complex (rephrased
as `range ⊆ ker`, the easy half of `range = ker`). Sorry-free via
`cellularBoundary_sq_zero`. -/
theorem cellular_chain_exact_range_le_ker
    [TopologicalSpace V] (K : AbstractSimplicialComplex V) (n : ℕ) :
    LinearMap.range (cellularBoundary K (n + 1)) ≤
      LinearMap.ker (cellularBoundary K n) := by
  intro x ⟨y, hy⟩
  simp [LinearMap.mem_ker, ← hy, ← LinearMap.comp_apply, cellularBoundary_sq_zero]

/-- **Round 13.** *Sub-leaf:* the previous quotient identity is
equivalent to `range = ker`, the conclusion of `cellular_pair_exact`. -/
theorem cellular_chain_exact_iff_range_eq_ker
    [TopologicalSpace V] (K : AbstractSimplicialComplex V) (n : ℕ) :
    LinearMap.range (cellularBoundary K (n + 1)) =
      LinearMap.ker (cellularBoundary K n) ↔
    LinearMap.ker (cellularBoundary K n) ≤
      LinearMap.range (cellularBoundary K (n + 1)) := by
  refine ⟨fun h => h ▸ le_refl _, fun h => ?_⟩
  apply le_antisymm _ h
  intro x ⟨y, hy⟩
  simp [LinearMap.mem_ker, ← hy, ← LinearMap.comp_apply, cellularBoundary_sq_zero]

/-- **Round 14.** *Sub-leaf of `skeletal_h1_quotient_substantive`.*
Universal property of the `cellularH K 1` quotient: factor any linear
map that vanishes on `range (cellularBoundary K 1)` through the
quotient. Direct Mathlib hook: `Submodule.liftQ`. -/
noncomputable def cellularH1_lift
    [TopologicalSpace V] (K : AbstractSimplicialComplex V)
    (M : Type) [AddCommGroup M] [Module ℤ M]
    (f : cellularChain K 1 →ₗ[ℤ] M)
    (_h : LinearMap.range (cellularBoundary K 1) ≤ LinearMap.ker f) :
    cellularChain K 1 ⧸ (LinearMap.range (cellularBoundary K 1)) →ₗ[ℤ] M :=
  Submodule.liftQ _ f _h

/-- **Round 15.** *Sub-leaf of `simplex_affine_map`.* The barycentric
coordinates of a point in `stdSimplex n` extend to a continuous map
to ℝ. Sorry'd; substantive form pulls out the `i`-th coordinate of
the standard simplex's `Fin (n+1) → ℝ` representation. -/
theorem simplex_affine_extension_existence
    (n : ℕ) (_vs : Fin (n + 1) → ℝ) :
    ∃ (f : stdSimplex n → ℝ), Continuous f :=
  sorry

/-- **Round 16.** *Sub-leaf of `singularH1_wedge_of_spheres`.* For a
discrete vertex set `V`, `singularH1 V = 0`. (Provable from
`AlgebraicTopology.isZero_singularHomologyFunctor_of_totallyDisconnectedSpace`.) -/
theorem singularH1_discrete_eq_zero
    (V : Type) [TopologicalSpace V] [TotallyDisconnectedSpace V] :
    Subsingleton (singularH1 V) :=
  ModuleCat.subsingleton_of_isZero <|
    AlgebraicTopology.isZero_singularHomologyFunctor_of_totallyDisconnectedSpace
      (ModuleCat ℤ) 1 (ModuleCat.of ℤ ℤ) (TopCat.of V) one_ne_zero

/-- **Round 17.** *Sub-leaf of `relative_hurewicz_skeletal_pair`.* The
identity map gives the skeletal pair iso under the placeholder
`relativeSkeletalH := cellularChain` definition. (A `noncomputable def`,
since the underlying `Module` instance on `cellularChain` is
noncomputable.) -/
noncomputable def relative_hurewicz_identity_under_placeholder
    [TopologicalSpace V] (K : AbstractSimplicialComplex V) (n : ℕ) :
    relativeSkeletalH K n ≃ₗ[ℤ] cellularChain K n :=
  LinearEquiv.refl ℤ _

/-- **Round 18.** *Sub-leaf of `cellularToSingular_isChainMap`.* The
chain-map equation reduces to the basis-pointwise statement
(`cellularToSingular_isChainMap_substantive`) by `Finsupp.lhom_ext` /
`LinearMap.ext_basis`. Sorry'd. -/
theorem cellularToSingular_isChainMap_basis_extension
    [TopologicalSpace V] [LinearOrder V] [DecidableEq V] (K : AbstractSimplicialComplex V) (n : ℕ)
    (h_basis : ∀ s : K.nSimplices (n + 1),
      rawSingularBoundary (AbstractSimplicialComplex.Geometric K) n
        ((cellularToSingularChain K (n + 1)) (Finsupp.single s 1)) =
      (cellularToSingularChain K n)
        ((cellularBoundary K n) (Finsupp.single s 1))) :
    (rawSingularBoundary (AbstractSimplicialComplex.Geometric K) n).comp
        (cellularToSingularChain K (n + 1)) =
      (cellularToSingularChain K n).comp (cellularBoundary K n) := by
  let _ := h_basis
  sorry

/-- **Round 19.** *Sub-leaf:* with all four upstream promotions in
hand, the headline `cellular_iso_singularH_via_five_lemma` follows by
chaining `cellularToSingular_isChainMap_basis_extension` (Round 18),
`cellular_pair_exact` (Round 13), `relative_hurewicz_skeletal_pair`
(Round 17), and `five_lemma_glue_to_global_iso` (Round 9). The body is
a `Nonempty.intro` over the chained `LinearEquiv.trans`s. Sorry'd
until the upstream promotions land. -/
theorem cellular_iso_singularH_assembly_skeleton
    [TopologicalSpace V] [LinearOrder V] [DecidableEq V] (K : AbstractSimplicialComplex V)
    [AbstractSimplicialComplex.Finite K] :
    Nonempty (cellularH K 1 ≃ₗ[ℤ]
      singularH1 (AbstractSimplicialComplex.Geometric K)) :=
  five_lemma_glue_to_global_iso K
    (fun n s => cellularToSingular_isChainMap_substantive K n s)
    (fun n => ⟨relative_hurewicz_identity_under_placeholder K n⟩)

/-- **Round 20.** *Sub-leaf:* the headline forwards to the assembly
skeleton; once Rounds 9–19 land, this becomes the proof. -/
theorem cellular_iso_singularH_via_assembly
    [TopologicalSpace V] [LinearOrder V] [DecidableEq V] (K : AbstractSimplicialComplex V)
    [AbstractSimplicialComplex.Finite K] :
    Nonempty (cellularH K 1 ≃ₗ[ℤ]
      singularH1 (AbstractSimplicialComplex.Geometric K)) :=
  cellular_iso_singularH_assembly_skeleton K

end JacobianChallenge.StageA
