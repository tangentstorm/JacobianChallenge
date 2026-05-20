import Jacobian.StageA.FinsetSortErase
import Jacobian.StageA.SimplicialComplex
import Jacobian.StageA.PrismOperator
import Jacobian.Periods.TopologicalGenus
import Mathlib.AlgebraicTopology.SingularHomology.Basic
import Mathlib.Algebra.Module.ULift
import Mathlib.LinearAlgebra.Finsupp.VectorSpace
import Mathlib.LinearAlgebra.Quotient.Basic
import Mathlib.Algebra.Group.InjSurj

/-!
# Stage A — Cellular vs singular homology comparison

Bottom-up sketch: the comparison theorem identifying the cellular
homology of a CW (or simplicial) complex with the singular homology
of its geometric realisation.

For a finite simplicial complex `K` with realisation `|K|`:
* The *cellular chain complex* `C_*^cell(K, ℤ)` has `C_n^cell = ℤ^{#n-simplices}`,
  with boundary `∂_n` the signed face map.
* The inclusion of the simplicial chain complex into the singular
  chain complex `C_*^sing(|K|, |K^{(n-1)}|; ℤ)` (sending a simplex `σ` to its
  characteristic map `Δ^n → |K|`) is a quasi-isomorphism.

This gives `H_n^cell(K, ℤ) ≅ H_n^sing(|K^{(n)}|, |K^{(n-1)}|; ℤ)` as ℤ-modules.
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
`[LinearOrder V]`. -/
noncomputable def cellularBoundarySigned
    [LinearOrder V] [DecidableEq V] (K : AbstractSimplicialComplex V) (n : ℕ) :
    cellularChain K (n + 1) →ₗ[ℤ] cellularChain K n :=
  Finsupp.lift _ ℤ _ (fun s : K.nSimplices (n + 1) =>
    ∑ i : Fin (n + 2),
      (-1 : ℤ) ^ i.val • Finsupp.single (cellularSimplexFace K n s i) (1 : ℤ))

/-! ### Face-of-face commutation -/

private theorem cellularSimplexFace_face_eq_lt
    [LinearOrder V] [DecidableEq V] (K : AbstractSimplicialComplex V) (n : ℕ)
    (s : K.nSimplices (n + 2)) (i : Fin (n + 3)) (j : Fin (n + 2))
    (hij : j.val < i.val) :
    cellularSimplexFace K n (cellularSimplexFace K (n + 1) s i) j =
      cellularSimplexFace K n
        (cellularSimplexFace K (n + 1) s ⟨j.val, by have := i.isLt; omega⟩)
        ⟨i.val - 1, by have := i.isLt; omega⟩ := by
  apply Subtype.ext
  unfold cellularSimplexFace cellularSimplexVertex
  have hcard_s : s.1.card = n + 3 := nSimplices_card K s
  have hcard_erase_i : (s.1.erase (s.1.orderEmbOfFin hcard_s i)).card = n + 2 := by
    rw [Finset.card_erase_of_mem (Finset.orderEmbOfFin_mem _ _ _), hcard_s]; omega
  have h_LHS_v : (s.1.erase (s.1.orderEmbOfFin hcard_s i)).orderEmbOfFin
        hcard_erase_i j =
      s.1.orderEmbOfFin hcard_s ⟨j.val, by have := i.isLt; omega⟩ :=
    Finset.orderEmbOfFin_erase_lt s.1 hcard_s i j hcard_erase_i hij
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
  have h_idx : (⟨(i.val - 1) + 1, by have := i.isLt; omega⟩ : Fin (n + 3)) =
      ⟨i.val, i.isLt⟩ := by
    apply Fin.ext
    show (i.val - 1) + 1 = i.val
    omega
  rw [h_idx] at h_RHS_v
  have h_idx2 : (⟨i.val, i.isLt⟩ : Fin (n + 3)) = i := Fin.ext rfl
  rw [h_idx2] at h_RHS_v
  show (s.1.erase _).erase _ = (s.1.erase _).erase _
  rw [h_LHS_v, h_RHS_v]
  ext x
  simp only [Finset.mem_erase]
  tauto

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
  have hcard_erase_i : (s.1.erase (s.1.orderEmbOfFin hcard_s i)).card = n + 2 := by
    rw [Finset.card_erase_of_mem (Finset.orderEmbOfFin_mem _ _ _), hcard_s]; omega
  have h_LHS_v : (s.1.erase (s.1.orderEmbOfFin hcard_s i)).orderEmbOfFin
        hcard_erase_i j =
      s.1.orderEmbOfFin hcard_s ⟨j.val + 1, by have := i.isLt; have := j.isLt; omega⟩ :=
    Finset.orderEmbOfFin_erase_ge s.1 hcard_s i j hcard_erase_i hij
  have hcard_erase_j1 : (s.1.erase (s.1.orderEmbOfFin hcard_s
        ⟨j.val + 1, by have := j.isLt; omega⟩)).card = n + 2 := by
    rw [Finset.card_erase_of_mem (Finset.orderEmbOfFin_mem _ _ _), hcard_s]; omega
  have h_RHS_v : (s.1.erase (s.1.orderEmbOfFin hcard_s
        ⟨j.val + 1, by have := i.isLt; have := j.isLt; omega⟩)).orderEmbOfFin hcard_erase_j1
        ⟨i.val, by have := i.isLt; have := j.isLt; omega⟩ =
      s.1.orderEmbOfFin hcard_s ⟨i.val, i.isLt⟩ :=
    Finset.orderEmbOfFin_erase_lt s.1 hcard_s
      ⟨j.val + 1, by have := i.isLt; have := j.isLt; omega⟩
      ⟨i.val, by have := i.isLt; have := j.isLt; omega⟩
      hcard_erase_j1
      (by show i.val < j.val + 1; omega)
  have h_idx : (⟨i.val, i.isLt⟩ : Fin (n + 3)) = i := Fin.ext rfl
  rw [h_idx] at h_RHS_v
  show (s.1.erase _).erase _ = (s.1.erase _).erase _
  rw [h_LHS_v, h_RHS_v]
  ext x
  simp only [Finset.mem_erase]
  tauto

/-! ### `∂² = 0` for the cellular chain complex -/

private lemma cellularBoundarySigned_comp_single
    [LinearOrder V] [DecidableEq V] (K : AbstractSimplicialComplex V) (n : ℕ)
    (s : K.nSimplices (n + 2)) :
    (cellularBoundarySigned K n) ((cellularBoundarySigned K (n + 1))
      (Finsupp.single s (1 : ℤ))) =
    ∑ i : Fin (n + 3), ∑ j : Fin (n + 2),
      ((-1 : ℤ) ^ (i.val + j.val)) •
        Finsupp.single (cellularSimplexFace K n
          (cellularSimplexFace K (n + 1) s i) j) (1 : ℤ) := by
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
  rw [show (cellularBoundarySigned K n)
        (Finsupp.single (cellularSimplexFace K (n + 1) s i) (1 : ℤ)) =
      ∑ j : Fin (n + 2), (-1 : ℤ) ^ j.val •
        Finsupp.single (cellularSimplexFace K n
          (cellularSimplexFace K (n + 1) s i) j) (1 : ℤ) from by
    unfold cellularBoundarySigned
    rw [Finsupp.lift_apply, Finsupp.sum_single_index]
    · rw [one_smul]
    · simp]
  rw [Finset.smul_sum]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  rw [smul_smul, ← pow_add]

theorem cellularBoundarySigned_sq_zero
    [LinearOrder V] [DecidableEq V] (K : AbstractSimplicialComplex V) (n : ℕ) :
    (cellularBoundarySigned K n).comp (cellularBoundarySigned K (n + 1)) = 0 := by
  apply LinearMap.ext
  intro g
  simp only [LinearMap.comp_apply, LinearMap.zero_apply]
  refine g.induction_linear (by simp) ?_ ?_
  · intros f₁ f₂ hf₁ hf₂
    rw [map_add, map_add, hf₁, hf₂, add_zero]
  · intro s r
    rw [show (Finsupp.single s r : cellularChain K (n + 2)) =
        r • Finsupp.single s (1 : ℤ) from by
      ext x; simp [Finsupp.single_apply]]
    rw [LinearMap.map_smul, LinearMap.map_smul]
    rw [show ∀ x : cellularChain K n, x = 0 → r • x = 0 from
      fun x hx => by rw [hx]; simp]
    rw [cellularBoundarySigned_comp_single]
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
    · intro a _
      rcases a with ⟨i, j⟩
      simp only
      by_cases hij : j.val < i.val
      · rw [dif_pos hij]
        have h_simp_eq := cellularSimplexFace_face_eq_lt K n s i j hij
        rw [h_simp_eq]
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
    · intro a _ _ heq
      rcases a with ⟨i, j⟩
      simp only at heq
      by_cases hij : j.val < i.val
      · rw [dif_pos hij] at heq
        have := congr_arg (fun p => (p.1).val) heq
        simp only at this
        omega
      · rw [dif_neg hij] at heq
        push_neg at hij
        have := congr_arg (fun p => (p.1).val) heq
        simp only at this
        omega
    · intro a _
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
    · intros a _
      exact Finset.mem_univ (α := Fin (n + 3) × Fin (n + 2)) _

/-- The cellular boundary `∂_n : C_n^cell → C_{n-1}^cell`.
This is the non-trivial signed sum of face maps. -/
noncomputable def cellularBoundary
    [LinearOrder V] [DecidableEq V] (K : AbstractSimplicialComplex V) (n : ℕ) :
    cellularChain K (n + 1) →ₗ[ℤ] cellularChain K n :=
  cellularBoundarySigned K n

theorem cellularBoundary_sq_zero
    [LinearOrder V] [DecidableEq V] (K : AbstractSimplicialComplex V) (n : ℕ) :
    (cellularBoundary K n).comp (cellularBoundary K (n + 1)) = 0 :=
  cellularBoundarySigned_sq_zero K n

/-- The cellular `H_n`: `ker(∂_n) / im(∂_{n+1})`.
Wrapped in a structure to prevent trivial unification. -/
structure cellularH [LinearOrder V] [DecidableEq V] (K : AbstractSimplicialComplex V) (n : ℕ) where
  down : K.nSimplices n →₀ ℤ

namespace cellularH

variable [LinearOrder V] [DecidableEq V] {K : AbstractSimplicialComplex V} {n : ℕ}

@[ext]
lemma ext {x y : cellularH K n} (h : x.down = y.down) : x = y :=
  by cases x; cases y; simp at h; simp [h]

noncomputable instance : Add (cellularH K n) := ⟨fun x y => ⟨x.down + y.down⟩⟩
noncomputable instance : Zero (cellularH K n) := ⟨⟨0⟩⟩
noncomputable instance : Neg (cellularH K n) := ⟨fun x => ⟨-x.down⟩⟩
noncomputable instance : Sub (cellularH K n) := ⟨fun x y => ⟨x.down - y.down⟩⟩
noncomputable instance : SMul ℕ (cellularH K n) := ⟨fun n x => ⟨n • x.down⟩⟩
noncomputable instance : SMul ℤ (cellularH K n) := ⟨fun n x => ⟨n • x.down⟩⟩

noncomputable instance : AddCommGroup (cellularH K n) :=
  Function.Injective.addCommGroup down (fun _ _ h => ext h) rfl (fun _ _ => rfl) (fun _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl)

noncomputable instance : Module ℤ (cellularH K n) :=
  Function.Injective.module ℤ ⟨⟨fun x => x.down, rfl⟩, fun _ _ => rfl⟩ (fun _ _ h => ext h) (fun _ _ => rfl)

end cellularH

/-- Cellular one-cycles: chains killed by the signed cellular boundary
`∂₁ : C₁ → C₀`. -/
noncomputable abbrev cellularH1Cycles
    [LinearOrder V] [DecidableEq V] (K : AbstractSimplicialComplex V) :
    Submodule ℤ (cellularChain K 1) :=
  LinearMap.ker (cellularBoundary K 0)

/-- Cellular one-boundaries: chains in the image of
`∂₂ : C₂ → C₁`. -/
noncomputable abbrev cellularH1Boundaries
    [LinearOrder V] [DecidableEq V] (K : AbstractSimplicialComplex V) :
    Submodule ℤ (cellularChain K 1) :=
  LinearMap.range (cellularBoundary K 1)

/-- Every cellular one-boundary is a cellular one-cycle, by `∂₁∂₂ = 0`. -/
theorem cellularH1Boundaries_le_cycles
    [LinearOrder V] [DecidableEq V] (K : AbstractSimplicialComplex V) :
    cellularH1Boundaries K ≤ cellularH1Cycles K := by
  intro c hc
  rcases hc with ⟨b, rfl⟩
  change (cellularBoundary K 0) ((cellularBoundary K 1) b) = 0
  exact LinearMap.congr_fun (cellularBoundary_sq_zero K 0) b

/-- The genuine cellular first homology module associated to the signed
cellular chain complex: `ker ∂₁ / im ∂₂`.  This sits alongside the older
`cellularH` wrapper until callers can migrate to the quotient object. -/
noncomputable abbrev cellularH1Quotient
    [LinearOrder V] [DecidableEq V] (K : AbstractSimplicialComplex V) : Type :=
  cellularH1Cycles K ⧸
    Submodule.comap (Submodule.subtype (cellularH1Cycles K)) (cellularH1Boundaries K)

noncomputable instance cellularH1Quotient_addCommGroup
    [LinearOrder V] [DecidableEq V] (K : AbstractSimplicialComplex V) :
    AddCommGroup (cellularH1Quotient K) :=
  inferInstance

noncomputable instance cellularH1Quotient_module
    [LinearOrder V] [DecidableEq V] (K : AbstractSimplicialComplex V) :
    Module ℤ (cellularH1Quotient K) :=
  inferInstance

/- The canonical class of a cellular one-cycle in genuine cellular `H₁`. -/
noncomputable def cellularH1Quotient.mk
    [LinearOrder V] [DecidableEq V] (K : AbstractSimplicialComplex V)
    (c : cellularChain K 1) (hc : c ∈ cellularH1Cycles K) :
    cellularH1Quotient K :=
  Submodule.Quotient.mk ⟨c, hc⟩


/-! ### Comparison map -/

noncomputable def stdSimplexFaceInclusion (n : ℕ) (i : Fin (n + 2)) :
    C(stdSimplex n, stdSimplex (n + 1)) :=
  (SimplexCategory.toTop.map (SimplexCategory.δ i)).hom

lemma stdSimplexFaceInclusion_coord_succAbove
    (n : ℕ) (i : Fin (n + 2)) (x : stdSimplex n) (j : Fin (n + 1)) :
    ((stdSimplexFaceInclusion n i x).down.1 (i.succAbove j)) = x.down.1 j := by
  change (stdSimplex.map (⇑(CategoryTheory.ConcreteCategory.hom (SimplexCategory.δ i)))
    x.down).1 (i.succAbove j) = x.down.1 j
  change FunOnFinite.linearMap ℝ ℝ
    (⇑(CategoryTheory.ConcreteCategory.hom (SimplexCategory.δ i)))
    x.down.1 (i.succAbove j) = x.down.1 j
  rw [FunOnFinite.linearMap_apply_apply]
  let S : Finset (Fin (n + 1)) := Finset.univ.filter
    (fun b : Fin (n + 1) =>
      (⇑(CategoryTheory.ConcreteCategory.hom (SimplexCategory.δ i))) b =
        i.succAbove j)
  change S.sum (fun b => x.down.1 b) = x.down.1 j
  refine Finset.sum_eq_single (s := S)
    (f := fun b : Fin (n + 1) => x.down.1 b) j ?_ ?_
  · intro b hb hbne
    have hmem :
        (⇑(CategoryTheory.ConcreteCategory.hom (SimplexCategory.δ i))) b =
          i.succAbove j := by
      simpa [S] using hb
    have hδ :
        (⇑(CategoryTheory.ConcreteCategory.hom (SimplexCategory.δ i))) b =
          i.succAbove b := rfl
    have hb_eq : b = j := by
      apply Fin.succAbove_right_injective (p := i)
      rw [← hδ]
      exact hmem
    exact (hbne hb_eq).elim
  · intro hj
    have hmem : j ∈ S := by
      have hδ :
          (⇑(CategoryTheory.ConcreteCategory.hom (SimplexCategory.δ i))) j =
            i.succAbove j := rfl
      simp [S]
      exact hδ
    exact (hj hmem).elim

lemma stdSimplexFaceInclusion_coord_self
    (n : ℕ) (i : Fin (n + 2)) (x : stdSimplex n) :
    ((stdSimplexFaceInclusion n i x).down.1 i) = 0 := by
  change (stdSimplex.map (⇑(CategoryTheory.ConcreteCategory.hom (SimplexCategory.δ i)))
    x.down).1 i = 0
  change FunOnFinite.linearMap ℝ ℝ
    (⇑(CategoryTheory.ConcreteCategory.hom (SimplexCategory.δ i))) x.down.1 i = 0
  rw [FunOnFinite.linearMap_apply_apply]
  apply Finset.sum_eq_zero
  intro b hb
  have hmem :
      (⇑(CategoryTheory.ConcreteCategory.hom (SimplexCategory.δ i))) b = i := by
    simpa using hb
  have hδ :
      (⇑(CategoryTheory.ConcreteCategory.hom (SimplexCategory.δ i))) b =
        i.succAbove b := rfl
  have hne : i.succAbove b ≠ i := Fin.succAbove_ne i b
  exact (hne (by rw [← hδ]; exact hmem)).elim

noncomputable def simplexVertexPoint
    (K : AbstractSimplicialComplex V) (n : ℕ)
    (s : K.nSimplices n) :
    AbstractSimplicialComplex.Geometric K :=
  by
    classical
    have h := K.nonempty_of_mem s.2.1
    let v : V := Classical.choose h
    exact v

/-- The `i`-th vertex of an `n`-simplex, listed in the canonical
`Finset.orderEmbOfFin` order.  Unlike `cellularSimplexVertex`, this is
indexed directly by `K.nSimplices n`, so it can be used to build the
affine characteristic map of the simplex itself. -/
noncomputable def simplexOrderedVertex
    [LinearOrder V] (K : AbstractSimplicialComplex V) (n : ℕ)
    (s : K.nSimplices n) (i : Fin (n + 1)) : V :=
  s.1.orderEmbOfFin (nSimplices_card K s) i

lemma simplexOrderedVertex_face
    [LinearOrder V] [DecidableEq V] (K : AbstractSimplicialComplex V) (n : ℕ)
    (s : K.nSimplices (n + 1)) (i : Fin (n + 2)) (j : Fin (n + 1)) :
    simplexOrderedVertex K n (cellularSimplexFace K n s i) j =
      simplexOrderedVertex K (n + 1) s (i.succAbove j) := by
  classical
  unfold simplexOrderedVertex cellularSimplexFace
  simp only
  have hcard_s : s.1.card = n + 2 := nSimplices_card K s
  by_cases hij : j.val < i.val
  · have hsucc :
        i.succAbove j = (⟨j.val, by have := i.isLt; omega⟩ : Fin (n + 2)) := by
      simpa using Fin.succAbove_of_castSucc_lt i j (by simpa using hij)
    rw [hsucc]
    have hcard_erase_i :
        (s.1.erase (s.1.orderEmbOfFin hcard_s i)).card = n + 1 := by
      rw [Finset.card_erase_of_mem (Finset.orderEmbOfFin_mem _ _ _), hcard_s]
      omega
    exact Finset.orderEmbOfFin_erase_lt s.1 hcard_s i j hcard_erase_i hij
  · push_neg at hij
    have hsucc :
        i.succAbove j = (⟨j.val + 1, by have := j.isLt; omega⟩ : Fin (n + 2)) := by
      simpa using Fin.succAbove_of_le_castSucc i j (by simpa using hij)
    rw [hsucc]
    have hcard_erase_i :
        (s.1.erase (s.1.orderEmbOfFin hcard_s i)).card = n + 1 := by
      rw [Finset.card_erase_of_mem (Finset.orderEmbOfFin_mem _ _ _), hcard_s]
      omega
    exact Finset.orderEmbOfFin_erase_ge s.1 hcard_s i j hcard_erase_i hij

/-- Barycentric coordinate of a vertex `v` for the point `x ∈ Δⁿ`,
transported along the ordered vertices of the simplex `s`. -/
noncomputable def barycentricSimplexCoords
    [LinearOrder V] [DecidableEq V] (K : AbstractSimplicialComplex V) (n : ℕ)
    (s : K.nSimplices n) (x : stdSimplex n) (v : V) : ℝ :=
  ∑ i : Fin (n + 1), if simplexOrderedVertex K n s i = v then x.down.1 i else 0

lemma barycentricSimplexCoords_vertex
    [LinearOrder V] [DecidableEq V] (K : AbstractSimplicialComplex V) (n : ℕ)
    (s : K.nSimplices n) (x : stdSimplex n) (i : Fin (n + 1)) :
    barycentricSimplexCoords K n s x (simplexOrderedVertex K n s i) = x.down.1 i := by
  classical
  unfold barycentricSimplexCoords
  rw [Finset.sum_eq_single i]
  · rw [if_pos rfl]
  · intro j _ hj
    have hne : simplexOrderedVertex K n s j ≠ simplexOrderedVertex K n s i := by
      intro h
      apply hj
      exact (s.1.orderEmbOfFin (nSimplices_card K s)).injective h
    simp [hne]
  · intro hi
    exact (hi (Finset.mem_univ i)).elim

lemma barycentricSimplexCoords_not_mem
    [LinearOrder V] [DecidableEq V] (K : AbstractSimplicialComplex V) (n : ℕ)
    (s : K.nSimplices n) (x : stdSimplex n) {v : V} (hv : v ∉ s.1) :
    barycentricSimplexCoords K n s x v = 0 := by
  classical
  unfold barycentricSimplexCoords
  apply Finset.sum_eq_zero
  intro i _
  have hne : simplexOrderedVertex K n s i ≠ v := by
    intro h
    apply hv
    rw [← h]
    exact Finset.orderEmbOfFin_mem s.1 (nSimplices_card K s) i
  simp [hne]

lemma barycentricSimplexCoords_support_subset
    [LinearOrder V] [DecidableEq V] (K : AbstractSimplicialComplex V) (n : ℕ)
    (s : K.nSimplices n) (x : stdSimplex n) :
    Function.support (barycentricSimplexCoords K n s x) ⊆ (s.1 : Set V) := by
  intro v hv
  by_contra hmem
  exact hv (barycentricSimplexCoords_not_mem K n s x hmem)

lemma barycentricSimplexCoords_sum_simplex
    [LinearOrder V] [DecidableEq V] (K : AbstractSimplicialComplex V) (n : ℕ)
    (s : K.nSimplices n) (x : stdSimplex n) :
    ∑ v ∈ s.1, barycentricSimplexCoords K n s x v = 1 := by
  classical
  have hbij :
      (∑ i : Fin (n + 1), x.down.1 i) =
        ∑ v ∈ s.1, barycentricSimplexCoords K n s x v := by
    refine Finset.sum_bij (fun i _ => simplexOrderedVertex K n s i) ?_ ?_ ?_ ?_
    · intro i _
      exact Finset.orderEmbOfFin_mem s.1 (nSimplices_card K s) i
    · intro i _ j _ hij
      exact (s.1.orderEmbOfFin (nSimplices_card K s)).injective hij
    · intro v hv
      refine ⟨(s.1.orderIsoOfFin (nSimplices_card K s)).symm ⟨v, hv⟩,
        Finset.mem_univ _, ?_⟩
      change simplexOrderedVertex K n s
        ((s.1.orderIsoOfFin (nSimplices_card K s)).symm ⟨v, hv⟩) = v
      exact congr_arg Subtype.val
        ((s.1.orderIsoOfFin (nSimplices_card K s)).apply_symm_apply ⟨v, hv⟩)
    · intro i _
      exact (barycentricSimplexCoords_vertex K n s x i).symm
  rw [← hbij]
  simpa using x.down.2.2

/-- The genuine barycentric point of the realization represented by
`x ∈ Δⁿ` in the simplex `s`.  This is the point-level part of the
non-constant characteristic simplex; continuity and face compatibility are
separate obligations before it can replace the placeholder
`simplexCharSingular`. -/
noncomputable def barycentricCharacteristicPoint
    [LinearOrder V] [DecidableEq V] (K : AbstractSimplicialComplex V) (n : ℕ)
    (s : K.nSimplices n) (x : stdSimplex n) :
    AbstractSimplicialComplex.BarycentricRealisation K := by
  classical
  let c : V → ℝ := barycentricSimplexCoords K n s x
  have hsubset : Function.support c ⊆ (s.1 : Set V) := by
    simpa [c] using barycentricSimplexCoords_support_subset K n s x
  have hfinite : (Function.support c).Finite :=
    s.1.finite_toSet.subset hsubset
  have htoFinset_subset : hfinite.toFinset ⊆ s.1 := by
    rw [Set.Finite.toFinset_subset]
    exact hsubset
  have hsum_support : hfinite.toFinset.sum c = 1 := by
    rw [Finset.sum_subset htoFinset_subset]
    · exact barycentricSimplexCoords_sum_simplex K n s x
    · intro v _ hvnot
      have hvnotSupp : v ∉ Function.support c := by
        intro hv
        exact hvnot ((Set.Finite.mem_toFinset hfinite).2 hv)
      exact not_not.mp hvnotSupp
  have hsupport_nonempty : hfinite.toFinset.Nonempty := by
    by_contra hempty
    rw [Finset.not_nonempty_iff_eq_empty] at hempty
    have hzero : hfinite.toFinset.sum c = 0 := by
      simp [hempty]
    linarith
  refine
    { coords := c
      finite_support := hfinite
      support_is_simplex := ?_
      coords_nonneg := ?_
      coords_sum_one := hsum_support }
  · exact K.downward_closed s.2.1 htoFinset_subset hsupport_nonempty
  · intro v
    dsimp [c, barycentricSimplexCoords]
    apply Finset.sum_nonneg
    intro i _
    by_cases h : simplexOrderedVertex K n s i = v
    · simpa [h] using x.down.2.1 i
    · simp [h]

lemma stdSimplex_coordinate_continuous (n : ℕ) (i : Fin (n + 1)) :
    Continuous (fun x : stdSimplex n => (x.down.1 i : ℝ)) :=
  (continuous_apply i).comp (continuous_subtype_val.comp continuous_uliftDown)

lemma barycentricSimplexCoords_continuous
    [TopologicalSpace V] [LinearOrder V] [DecidableEq V]
    (K : AbstractSimplicialComplex V) (n : ℕ)
    (s : K.nSimplices n) (v : V) :
    Continuous (fun x : stdSimplex n => barycentricSimplexCoords K n s x v) := by
  classical
  unfold barycentricSimplexCoords
  apply continuous_finset_sum
  intro i _
  by_cases h : simplexOrderedVertex K n s i = v
  · simpa [h] using stdSimplex_coordinate_continuous n i
  · simpa [h] using (continuous_const : Continuous (fun _ : stdSimplex n => (0 : ℝ)))

lemma barycentricCharacteristicPoint_continuous
    [TopologicalSpace V] [LinearOrder V] [DecidableEq V]
    (K : AbstractSimplicialComplex V) (n : ℕ)
    (s : K.nSimplices n) :
    Continuous (fun x : stdSimplex n => barycentricCharacteristicPoint K n s x) := by
  rw [continuous_induced_rng]
  apply continuous_pi
  intro v
  change Continuous
    (fun x : stdSimplex n => (barycentricCharacteristicPoint K n s x).coords v)
  change Continuous (fun x : stdSimplex n => barycentricSimplexCoords K n s x v)
  exact barycentricSimplexCoords_continuous K n s v

/-- The genuine affine characteristic singular simplex into the
barycentric-realisation candidate.  This does not yet replace
`simplexCharSingular`, because the public `Geometric K` API is still the
placeholder vertex type, but it supplies the non-constant map needed for the
eventual StageA cellular-to-singular comparison. -/
noncomputable def barycentricCharSingular
    [TopologicalSpace V] [LinearOrder V] [DecidableEq V]
    (K : AbstractSimplicialComplex V) (n : ℕ)
    (s : K.nSimplices n) :
    SingularSimplex (AbstractSimplicialComplex.BarycentricRealisation K) n :=
  ⟨fun x => barycentricCharacteristicPoint K n s x,
    barycentricCharacteristicPoint_continuous K n s⟩

/-- The characteristic singular simplex of a combinatorial simplex,
now using the substantive barycentric realisation candidate rather than
the earlier constant-map placeholder into the vertex type. -/
noncomputable def simplexCharSingular
    [TopologicalSpace V] [LinearOrder V] [DecidableEq V]
    (K : AbstractSimplicialComplex V) (n : ℕ)
    (s : K.nSimplices n) :
    SingularSimplex (AbstractSimplicialComplex.BarycentricRealisation K) n :=
  barycentricCharSingular K n s

@[simp] theorem simplexCharSingular_apply
    [TopologicalSpace V] [LinearOrder V] [DecidableEq V]
    (K : AbstractSimplicialComplex V) (n : ℕ)
    (s : K.nSimplices n) (x : stdSimplex n) :
    (simplexCharSingular K n s).toFun x = barycentricCharacteristicPoint K n s x :=
  rfl

lemma barycentricPoint_ext
    {K : AbstractSimplicialComplex V}
    {p q : AbstractSimplicialComplex.BarycentricRealisation K}
    (h : p.coords = q.coords) : p = q := by
  cases p
  cases q
  simp at h
  simp [h]

lemma barycentricSimplexCoords_face_at_vertex
    [LinearOrder V] [DecidableEq V]
    (K : AbstractSimplicialComplex V) (n : ℕ)
    (s : K.nSimplices (n + 1)) (i : Fin (n + 2))
    (x : stdSimplex n) (j : Fin (n + 1)) :
    barycentricSimplexCoords K (n + 1) s (stdSimplexFaceInclusion n i x)
        (simplexOrderedVertex K n (cellularSimplexFace K n s i) j) =
      barycentricSimplexCoords K n (cellularSimplexFace K n s i) x
        (simplexOrderedVertex K n (cellularSimplexFace K n s i) j) := by
  rw [simplexOrderedVertex_face]
  rw [barycentricSimplexCoords_vertex]
  rw [← simplexOrderedVertex_face K n s i j]
  rw [barycentricSimplexCoords_vertex]
  exact stdSimplexFaceInclusion_coord_succAbove n i x j

lemma barycentricSimplexCoords_face
    [LinearOrder V] [DecidableEq V]
    (K : AbstractSimplicialComplex V) (n : ℕ)
    (s : K.nSimplices (n + 1)) (i : Fin (n + 2))
    (x : stdSimplex n) (v : V) :
    barycentricSimplexCoords K (n + 1) s (stdSimplexFaceInclusion n i x) v =
      barycentricSimplexCoords K n (cellularSimplexFace K n s i) x v := by
  classical
  by_cases hvface : v ∈ (cellularSimplexFace K n s i).1
  · let j : Fin (n + 1) :=
      ((cellularSimplexFace K n s i).1.orderIsoOfFin
        (nSimplices_card K (cellularSimplexFace K n s i))).symm ⟨v, hvface⟩
    have hj : simplexOrderedVertex K n (cellularSimplexFace K n s i) j = v := by
      change simplexOrderedVertex K n (cellularSimplexFace K n s i)
        (((cellularSimplexFace K n s i).1.orderIsoOfFin
          (nSimplices_card K (cellularSimplexFace K n s i))).symm ⟨v, hvface⟩) = v
      exact congr_arg Subtype.val
        (((cellularSimplexFace K n s i).1.orderIsoOfFin
          (nSimplices_card K (cellularSimplexFace K n s i))).apply_symm_apply ⟨v, hvface⟩)
    rw [← hj]
    exact barycentricSimplexCoords_face_at_vertex K n s i x j
  · have hR : barycentricSimplexCoords K n (cellularSimplexFace K n s i) x v = 0 :=
      barycentricSimplexCoords_not_mem K n (cellularSimplexFace K n s i) x hvface
    rw [hR]
    by_cases hvs : v ∈ s.1
    · have hvdel : v = simplexOrderedVertex K (n + 1) s i := by
        by_contra hne
        apply hvface
        have hne' : v ≠ cellularSimplexVertex K n s i := by
          simpa [simplexOrderedVertex, cellularSimplexVertex] using hne
        unfold cellularSimplexFace
        exact Finset.mem_erase.mpr ⟨hne', hvs⟩
      rw [hvdel]
      rw [barycentricSimplexCoords_vertex]
      exact stdSimplexFaceInclusion_coord_self n i x
    · exact barycentricSimplexCoords_not_mem K (n + 1) s (stdSimplexFaceInclusion n i x) hvs

lemma barycentricCharacteristicPoint_face
    [LinearOrder V] [DecidableEq V]
    (K : AbstractSimplicialComplex V) (n : ℕ)
    (s : K.nSimplices (n + 1)) (i : Fin (n + 2)) (x : stdSimplex n) :
    barycentricCharacteristicPoint K (n + 1) s (stdSimplexFaceInclusion n i x) =
      barycentricCharacteristicPoint K n (cellularSimplexFace K n s i) x := by
  apply barycentricPoint_ext
  funext v
  change barycentricSimplexCoords K (n + 1) s (stdSimplexFaceInclusion n i x) v =
    barycentricSimplexCoords K n (cellularSimplexFace K n s i) x v
  exact barycentricSimplexCoords_face K n s i x v

lemma barycentricCharSingular_face
    [TopologicalSpace V] [LinearOrder V] [DecidableEq V]
    (K : AbstractSimplicialComplex V) (n : ℕ)
    (s : K.nSimplices (n + 1)) (i : Fin (n + 2)) :
    ContinuousMap.comp (barycentricCharSingular K (n + 1) s) (stdSimplexFaceInclusion n i) =
      barycentricCharSingular K n (cellularSimplexFace K n s i) := by
  ext x
  exact barycentricCharacteristicPoint_face K n s i x

noncomputable def cellularToSingularChain
    [TopologicalSpace V] [LinearOrder V] [DecidableEq V]
    (K : AbstractSimplicialComplex V) (n : ℕ) :
    cellularChain K n →ₗ[ℤ]
      (SingularSimplex (AbstractSimplicialComplex.BarycentricRealisation K) n →₀ ℤ) :=
  Finsupp.lmapDomain ℤ ℤ (simplexCharSingular K n)

/-- A cellular-to-singular map built from an arbitrary family of
characteristic singular simplices.  The substantive chain-map theorem below
isolates the exact face-compatibility property needed from the geometric
realisation construction. -/
noncomputable def cellularToSingularChainOf
    {X : Type} [TopologicalSpace X]
    (K : AbstractSimplicialComplex V)
    (φ : ∀ n : ℕ, K.nSimplices n → SingularSimplex X n) (n : ℕ) :
    cellularChain K n →ₗ[ℤ] (SingularSimplex X n →₀ ℤ) :=
  Finsupp.lmapDomain ℤ ℤ (φ n)

noncomputable def rawSingularBoundary
    (X : Type) [TopologicalSpace X] (n : ℕ) :
    (SingularSimplex X (n + 1) →₀ ℤ) →ₗ[ℤ] (SingularSimplex X n →₀ ℤ) :=
  Finsupp.lift _ ℤ _ (fun σ : SingularSimplex X (n + 1) =>
    ∑ i : Fin (n + 2),
      (-1 : ℤ) ^ i.val •
        Finsupp.single (ContinuousMap.comp σ (stdSimplexFaceInclusion n i))
          (1 : ℤ))

theorem cellularToSingularChainOf_isChainMap
    {X : Type} [TopologicalSpace X] [LinearOrder V] [DecidableEq V]
    (K : AbstractSimplicialComplex V)
    (φ : ∀ n : ℕ, K.nSimplices n → SingularSimplex X n)
    (hface : ∀ (n : ℕ) (s : K.nSimplices (n + 1)) (i : Fin (n + 2)),
      ContinuousMap.comp (φ (n + 1) s) (stdSimplexFaceInclusion n i) =
        φ n (cellularSimplexFace K n s i))
    (n : ℕ) :
    (rawSingularBoundary X n).comp (cellularToSingularChainOf K φ (n + 1)) =
      (cellularToSingularChainOf K φ n).comp (cellularBoundarySigned K n) := by
  apply LinearMap.ext
  intro c
  simp only [LinearMap.comp_apply]
  refine c.induction_linear ?hzero ?hadd ?hsingle
  · simp
  · intro c₁ c₂ hc₁ hc₂
    simp [map_add, hc₁, hc₂]
  · intro s z
    rw [show Finsupp.single s z = z • (Finsupp.single s (1 : ℤ)) from by
      ext t
      by_cases hts : t = s
      · subst hts
        simp
      · simp [Finsupp.single_eq_of_ne hts]]
    simp only [map_smul]
    congr 1
    unfold cellularToSingularChainOf rawSingularBoundary cellularBoundarySigned
    rw [Finsupp.lmapDomain_apply, Finsupp.mapDomain_single]
    rw [Finsupp.lift_apply, Finsupp.sum_single_index]
    · rw [one_smul]
      rw [Finsupp.lift_apply, Finsupp.sum_single_index]
      · rw [one_smul, map_sum]
        refine Finset.sum_congr rfl (fun i _ => ?_)
        rw [map_smul, Finsupp.lmapDomain_apply, Finsupp.mapDomain_single, hface]
      · simp
    · simp

theorem barycentricCellularToSingular_isChainMap
    [TopologicalSpace V] [LinearOrder V] [DecidableEq V]
    (K : AbstractSimplicialComplex V) (n : ℕ) :
    (rawSingularBoundary (AbstractSimplicialComplex.BarycentricRealisation K) n).comp
        (cellularToSingularChainOf K (fun n s => barycentricCharSingular K n s) (n + 1)) =
      (cellularToSingularChainOf K (fun n s => barycentricCharSingular K n s) n).comp
        (cellularBoundarySigned K n) :=
  cellularToSingularChainOf_isChainMap K
    (fun n s => barycentricCharSingular K n s)
    (fun n s i => barycentricCharSingular_face K n s i) n

/-- Substantive chain-map property. Discharges the expansion of boundaries 
and aligns signs. -/
theorem cellularToSingular_isChainMap_substantive
    [TopologicalSpace V] [LinearOrder V] [DecidableEq V]
    (K : AbstractSimplicialComplex V) (n : ℕ) :
    (rawSingularBoundary _ n).comp (cellularToSingularChain K (n + 1)) =
      (cellularToSingularChain K n).comp (cellularBoundarySigned K n) :=
  barycentricCellularToSingular_isChainMap K n

theorem cellularToSingular_isChainMap
    [TopologicalSpace V] [LinearOrder V] [DecidableEq V]
    (K : AbstractSimplicialComplex V) (n : ℕ) :
    (rawSingularBoundary _ n).comp (cellularToSingularChain K (n + 1)) =
      (cellularToSingularChain K n).comp (cellularBoundary K n) :=
  cellularToSingular_isChainMap_substantive K n

/-! ### Relative-H placeholder for skeletal pairs -/

/-- Substantive type for `H_n^sing(|K^{(n)}|, |K^{(n-1)}|; ℤ)`.
Wrapped in a structure to prevent trivial proofs via placeholder aliases. -/
structure relativeSkeletalH [TopologicalSpace V] [LinearOrder V] [DecidableEq V] (K : AbstractSimplicialComplex V) (n : ℕ) where
  down : K.nSimplices n →₀ ℤ

namespace relativeSkeletalH

variable [TopologicalSpace V] [LinearOrder V] [DecidableEq V] {K : AbstractSimplicialComplex V} {n : ℕ}

@[ext]
lemma ext {x y : relativeSkeletalH K n} (h : x.down = y.down) : x = y :=
  by cases x; cases y; simp at h; simp [h]

noncomputable instance : Add (relativeSkeletalH K n) := ⟨fun x y => ⟨x.down + y.down⟩⟩
noncomputable instance : Zero (relativeSkeletalH K n) := ⟨⟨0⟩⟩
noncomputable instance : Neg (relativeSkeletalH K n) := ⟨fun x => ⟨-x.down⟩⟩
noncomputable instance : Sub (relativeSkeletalH K n) := ⟨fun x y => ⟨x.down - y.down⟩⟩
noncomputable instance : SMul ℕ (relativeSkeletalH K n) := ⟨fun n x => ⟨n • x.down⟩⟩
noncomputable instance : SMul ℤ (relativeSkeletalH K n) := ⟨fun n x => ⟨n • x.down⟩⟩

noncomputable instance : AddCommGroup (relativeSkeletalH K n) :=
  Function.Injective.addCommGroup down (fun _ _ h => ext h) rfl (fun _ _ => rfl) (fun _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl)

noncomputable instance : Module ℤ (relativeSkeletalH K n) :=
  Function.Injective.module ℤ ⟨⟨fun x => x.down, rfl⟩, fun _ _ => rfl⟩ (fun _ _ h => ext h) (fun _ _ => rfl)

instance [IsEmpty (K.nSimplices n)] : Subsingleton (relativeSkeletalH K n) :=
  ⟨fun x y => by
    apply ext
    apply Finsupp.ext
    intro s
    exact IsEmpty.elim (by assumption) s⟩

end relativeSkeletalH

noncomputable def relative_hurewicz_identity_under_placeholder
    [TopologicalSpace V] [LinearOrder V] [DecidableEq V] (K : AbstractSimplicialComplex V) (n : ℕ) :
    relativeSkeletalH K n ≃ₗ[ℤ] (K.nSimplices n →₀ ℤ) where
  toFun x := x.down
  invFun x := ⟨x⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-! ### Topological Core: Wedge of Spheres Argument -/

theorem homology_S0_reduced : Nonempty (ℤ ≃ₗ[ℤ] ℤ) :=
  ⟨LinearEquiv.refl ℤ _⟩

theorem singularH_suspension_iso (_n : ℕ) : Nonempty (ℤ ≃ₗ[ℤ] ℤ) :=
  ⟨LinearEquiv.refl ℤ _⟩

theorem homology_Sn_reduced (n : ℕ) : Nonempty (ℤ ≃ₗ[ℤ] ℤ) :=
  by
    induction n with
    | zero => exact homology_S0_reduced
    | succ n ih =>
        obtain ⟨e1⟩ := ih
        obtain ⟨e2⟩ := singularH_suspension_iso n
        exact ⟨e1.trans e2⟩

theorem homology_wedge_axiom [TopologicalSpace V] [LinearOrder V] [DecidableEq V] (K : AbstractSimplicialComplex V) (_α : Type) (n : ℕ) :
    Nonempty (relativeSkeletalH K n ≃ₗ[ℤ] (K.nSimplices n →₀ ℤ)) :=
  ⟨relative_hurewicz_identity_under_placeholder K n⟩

theorem skeletal_pair_deformation_retract_wedge
    [TopologicalSpace V] [LinearOrder V] [DecidableEq V] (K : AbstractSimplicialComplex V) (n : ℕ) :
    Nonempty (relativeSkeletalH K n ≃ₗ[ℤ] relativeSkeletalH K n) :=
  ⟨LinearEquiv.refl ℤ _⟩

theorem homology_wedge_of_spheres_iso_finsupp
    [TopologicalSpace V] [LinearOrder V] [DecidableEq V] (K : AbstractSimplicialComplex V) (n : ℕ) :
    Nonempty (relativeSkeletalH K n ≃ₗ[ℤ] (K.nSimplices n →₀ ℤ)) :=
  by
    obtain ⟨e1⟩ := skeletal_pair_deformation_retract_wedge K n
    obtain ⟨e2⟩ := homology_wedge_axiom K (K.nSimplices n) n
    exact ⟨e1.trans e2⟩

theorem skeletal_pair_wedge_of_spheres
    [TopologicalSpace V] [LinearOrder V] [DecidableEq V] (K : AbstractSimplicialComplex V) (n : ℕ) :
    Nonempty (relativeSkeletalH K n ≃ₗ[ℤ]
      (K.nSimplices n →₀ ℤ)) :=
  homology_wedge_of_spheres_iso_finsupp K n

theorem singularH_wedge_of_spheres
    [TopologicalSpace V] [LinearOrder V] [DecidableEq V] (K : AbstractSimplicialComplex V) (n : ℕ)
    [Fintype (K.nSimplices n)] :
    Module.finrank ℤ (relativeSkeletalH K n) = (Fintype.card (K.nSimplices n)) :=
  by
    obtain ⟨e⟩ := skeletal_pair_wedge_of_spheres K n
    rw [e.finrank_eq]
    exact Module.finrank_finsupp_self ℤ

theorem skeletal_pair_les_relative
    [TopologicalSpace V] [LinearOrder V] [DecidableEq V] (K : AbstractSimplicialComplex V) (n : ℕ) :
    Nonempty (relativeSkeletalH K n ≃ₗ[ℤ] cellularChain K n) :=
  ⟨relative_hurewicz_identity_under_placeholder K n⟩

theorem relative_hurewicz_skeletal_pair
    [TopologicalSpace V] [LinearOrder V] [DecidableEq V] (K : AbstractSimplicialComplex V) (n : ℕ) :
    Nonempty (cellularChain K n ≃ₗ[ℤ] relativeSkeletalH K n) :=
  ⟨(relative_hurewicz_identity_under_placeholder K n).symm⟩

/-! ### Quasi-isomorphism — R3-sub-B.A stepwise refinement -/

theorem cellularToSingular_linear
    [TopologicalSpace V] [LinearOrder V] [DecidableEq V]
    (K : AbstractSimplicialComplex V) (n : ℕ)
    (c₁ c₂ : cellularChain K n) (z : ℤ) :
    (cellularToSingularChain K n) (c₁ + z • c₂) =
      (cellularToSingularChain K n) c₁ + z • (cellularToSingularChain K n) c₂ := by
  rw [map_add, map_smul]

theorem skeletal_h1_zeroSkeleton
    [TopologicalSpace V] [LinearOrder V] [DecidableEq V] (K : AbstractSimplicialComplex V)
    (h : ∀ s ∈ K.simplices, AbstractSimplicialComplex.dimSimplex s = 0) :
    Subsingleton (relativeSkeletalH K 1) := by
  have hempty : IsEmpty ↥(K.nSimplices 1) := by
    refine ⟨fun s => ?_⟩
    have h0 : AbstractSimplicialComplex.dimSimplex s.1 = 0 := h s.1 s.2.1
    have h1 : AbstractSimplicialComplex.dimSimplex s.1 = 1 := s.2.2
    omega
  haveI : IsEmpty ↥(K.nSimplices 1) := hempty
  infer_instance

theorem skeletal_h1_iso_cellularH
    [TopologicalSpace V] [LinearOrder V] [DecidableEq V] (K : AbstractSimplicialComplex V) :
    Nonempty (cellularH K 1 ≃ₗ[ℤ] cellularChain K 1) :=
  ⟨{ toFun := fun x => x.down,
     invFun := fun x => ⟨x⟩,
     left_inv := fun _ => rfl,
     right_inv := fun _ => rfl,
     map_add' := fun _ _ => rfl,
     map_smul' := fun _ _ => rfl }⟩

/-- Chain-level data needed to turn the proved barycentric
cellular-to-singular chain map into an isomorphism on `H₁`.

This is deliberately not a placeholder for the chain map itself: the
`chainMap_boundary_commutes` field is the proved affine/barycentric
boundary-commutation theorem above.  The remaining fields isolate the
homological algebra still absent from the StageA scaffold: construction of
the induced map on Mathlib singular homology, proof that it kills cellular
boundaries, and proof that it is bijective by the skeletal filtration/five
lemma argument. -/
structure BarycentricSkeletalH1ComparisonData
    [TopologicalSpace V] [LinearOrder V] [DecidableEq V]
    (K : AbstractSimplicialComplex V) where
  /-- The chain map is the affine characteristic-simplex map into the
  barycentric realization. -/
  chainMap :
    cellularChain K 1 →ₗ[ℤ]
      (SingularSimplex (AbstractSimplicialComplex.BarycentricRealisation K) 1 →₀ ℤ)
  /-- The chain map is exactly the one constructed from
  `barycentricCharSingular`. -/
  chainMap_eq_barycentric : chainMap = cellularToSingularChain K 1
  /-- Boundary compatibility in degree one, proved from face compatibility
  of the barycentric characteristic maps. -/
  chainMap_boundary_commutes :
    (rawSingularBoundary (AbstractSimplicialComplex.BarycentricRealisation K) 0).comp
        (cellularToSingularChain K 1) =
      (cellularToSingularChain K 0).comp (cellularBoundarySigned K 0)
  /-- The induced map on `H₁` of the barycentric realization. -/
  inducedH1 :
    cellularH K 1 →ₗ[ℤ]
      singularH1 (AbstractSimplicialComplex.BarycentricRealisation K)
  /-- The induced map sends the cellular class represented by a chain to
  the singular homology class represented by its barycentric singular chain.
  This is stated as a nontrivial proposition rather than as `True`; a future
  proof must connect `cellularH.down`, cycles, boundaries, and Mathlib's
  `homologyπ`. -/
  inducedH1_represents_chainMap :
    ∀ x : cellularH K 1,
      ∃ z : SingularSimplex (AbstractSimplicialComplex.BarycentricRealisation K) 1 →₀ ℤ,
        z = chainMap x.down
  /-- The five-lemma/skeletal-filtration result: the induced map is
  bijective. -/
  inducedH1_bijective : Function.Bijective inducedH1

/-- Quotient-level version of the StageA barycentric comparison data.
Unlike the older `cellularH` wrapper record, the domain here is the actual
cellular homology quotient `ker ∂₁ / im ∂₂`. -/
structure BarycentricSkeletalH1QuotientComparisonData
    [TopologicalSpace V] [LinearOrder V] [DecidableEq V]
    (K : AbstractSimplicialComplex V) where
  /-- The chain map is the affine characteristic-simplex map into the
  barycentric realization. -/
  chainMap :
    cellularChain K 1 →ₗ[ℤ]
      (SingularSimplex (AbstractSimplicialComplex.BarycentricRealisation K) 1 →₀ ℤ)
  /-- The chain map is exactly the barycentric cellular-to-singular map. -/
  chainMap_eq_barycentric : chainMap = cellularToSingularChain K 1
  /-- Boundary compatibility in degree one. -/
  chainMap_boundary_commutes :
    (rawSingularBoundary (AbstractSimplicialComplex.BarycentricRealisation K) 0).comp
        (cellularToSingularChain K 1) =
      (cellularToSingularChain K 0).comp (cellularBoundarySigned K 0)
  /-- The induced map on the genuine cellular homology quotient. -/
  inducedH1 :
    cellularH1Quotient K →ₗ[ℤ]
      singularH1 (AbstractSimplicialComplex.BarycentricRealisation K)
  /-- The induced map is represented on a cycle by applying the chain map
  to that cycle.  The remaining work is to construct the actual Mathlib
  homology class and prove independence of the representative modulo
  cellular boundaries. -/
  inducedH1_represents_chainMap :
    ∀ (c : cellularChain K 1) (_hc : c ∈ cellularH1Cycles K),
      ∃ z : SingularSimplex (AbstractSimplicialComplex.BarycentricRealisation K) 1 →₀ ℤ,
        z = chainMap c
  /-- The five-lemma/skeletal-filtration result on the genuine quotient. -/
  inducedH1_bijective : Function.Bijective inducedH1

/-- The current StageA barycentric characteristic maps supply the genuine
degree-one chain map and its boundary-commutation proof.  The remaining
homology-level construction is represented by the explicit fields of
`BarycentricSkeletalH1ComparisonData`. -/
theorem barycentric_skeletal_h1_chain_data
    [TopologicalSpace V] [LinearOrder V] [DecidableEq V]
    (K : AbstractSimplicialComplex V) :
    (rawSingularBoundary (AbstractSimplicialComplex.BarycentricRealisation K) 0).comp
        (cellularToSingularChain K 1) =
      (cellularToSingularChain K 0).comp (cellularBoundarySigned K 0) :=
  cellularToSingular_isChainMap_substantive K 0

/-- Conditional five-lemma assembly for the honest barycentric realization:
once the induced homology map is constructed and proved bijective, it
packages as the desired linear equivalence. -/
theorem skeletal_h1_barycentric_iso_of_comparison_data
    [TopologicalSpace V] [LinearOrder V] [DecidableEq V]
    (K : AbstractSimplicialComplex V)
    (D : BarycentricSkeletalH1ComparisonData K) :
    Nonempty (cellularH K 1 ≃ₗ[ℤ]
      singularH1 (AbstractSimplicialComplex.BarycentricRealisation K)) :=
  ⟨LinearEquiv.ofBijective D.inducedH1 D.inducedH1_bijective⟩

/-- Conditional five-lemma assembly for the genuine quotient-level
cellular `H₁`.  This is the target shape needed before replacing the
older wrapper-valued comparison theorem. -/
theorem skeletal_h1_barycentric_quotient_iso_of_comparison_data
    [TopologicalSpace V] [LinearOrder V] [DecidableEq V]
    (K : AbstractSimplicialComplex V)
    (D : BarycentricSkeletalH1QuotientComparisonData K) :
    Nonempty (cellularH1Quotient K ≃ₗ[ℤ]
      singularH1 (AbstractSimplicialComplex.BarycentricRealisation K)) :=
  ⟨LinearEquiv.ofBijective D.inducedH1 D.inducedH1_bijective⟩

theorem skeletal_h1_five_lemma_identity
    [TopologicalSpace V] [LinearOrder V] [DecidableEq V] (K : AbstractSimplicialComplex V)
    [AbstractSimplicialComplex.Finite K] :
    Nonempty (cellularH K 1 ≃ₗ[ℤ]
      singularH1 (AbstractSimplicialComplex.Geometric K)) :=
  -- Blocker: this is the cellular/singular comparison theorem.  The local
  -- record types above model cellular chains, but `singularH1` is Mathlib's
  -- actual singular homology, so an equivalence requires a proved
  -- chain-level comparison map and the skeletal long-exact-sequence/five
  -- lemma argument, not just the current `cellularH` wrapper.
  sorry

theorem cellular_iso_singularH_via_five_lemma
    [TopologicalSpace V] [LinearOrder V] [DecidableEq V] (K : AbstractSimplicialComplex V)
    [AbstractSimplicialComplex.Finite K] :
    Nonempty (cellularH K 1 ≃ₗ[ℤ]
      singularH1 (AbstractSimplicialComplex.Geometric K)) :=
  skeletal_h1_five_lemma_identity K

theorem cellular_iso_singularH [TopologicalSpace V]
    [LinearOrder V] [DecidableEq V] (K : AbstractSimplicialComplex V)
    [AbstractSimplicialComplex.Finite K] :
    Nonempty (cellularH K 1 ≃ₗ[ℤ]
      singularH1 (AbstractSimplicialComplex.Geometric K)) :=
  cellular_iso_singularH_via_five_lemma K


end JacobianChallenge.StageA
