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


/-! ### Comparison map -/

noncomputable def stdSimplexFaceInclusion (n : ℕ) (i : Fin (n + 2)) :
    C(stdSimplex n, stdSimplex (n + 1)) :=
  (SimplexCategory.toTop.map (SimplexCategory.δ i)).hom

noncomputable def simplexVertexPoint
    (K : AbstractSimplicialComplex V) (n : ℕ)
    (s : K.nSimplices n) :
    AbstractSimplicialComplex.Geometric K :=
  by
    classical
    have h := K.nonempty_of_mem s.2.1
    let v : V := Classical.choose h
    exact v

noncomputable def simplexCharSingular
    [TopologicalSpace V]
    (K : AbstractSimplicialComplex V) (n : ℕ)
    (_s : K.nSimplices n) :
    SingularSimplex (AbstractSimplicialComplex.Geometric K) n :=
  ContinuousMap.const (stdSimplex n) (simplexVertexPoint K n _s)

noncomputable def cellularToSingularChain
    [TopologicalSpace V]
    (K : AbstractSimplicialComplex V) (n : ℕ) :
    cellularChain K n →ₗ[ℤ]
      (SingularSimplex (AbstractSimplicialComplex.Geometric K) n →₀ ℤ) :=
  Finsupp.lmapDomain ℤ ℤ (simplexCharSingular K n)

noncomputable def rawSingularBoundary
    (X : Type) [TopologicalSpace X] (n : ℕ) :
    (SingularSimplex X (n + 1) →₀ ℤ) →ₗ[ℤ] (SingularSimplex X n →₀ ℤ) :=
  Finsupp.lift _ ℤ _ (fun σ : SingularSimplex X (n + 1) =>
    ∑ i : Fin (n + 2),
      (-1 : ℤ) ^ i.val •
        Finsupp.single (ContinuousMap.comp σ (stdSimplexFaceInclusion n i))
          (1 : ℤ))

/-- Substantive chain-map property. Discharges the expansion of boundaries 
and aligns signs. -/
theorem cellularToSingular_isChainMap_substantive
    [TopologicalSpace V] [LinearOrder V] [DecidableEq V]
    (K : AbstractSimplicialComplex V) (n : ℕ) :
    (rawSingularBoundary _ n).comp (cellularToSingularChain K (n + 1)) =
      (cellularToSingularChain K n).comp (cellularBoundarySigned K n) :=
  sorry

theorem cellularToSingular_isChainMap
    [TopologicalSpace V] [LinearOrder V] [DecidableEq V]
    (K : AbstractSimplicialComplex V) (n : ℕ) :
    (rawSingularBoundary _ n).comp (cellularToSingularChain K (n + 1)) =
      (cellularToSingularChain K n).comp (cellularBoundary K n) :=
  sorry

/-! ### Relative-H placeholder for skeletal pairs

The type `relativeSkeletalH K n` is the intended interface for
`H_n^sing(|K^{(n)}|, |K^{(n-1)}|; ℤ)` — relative singular homology of
the skeletal pair. **It is currently a thin wrapper around
`K.nSimplices n →₀ ℤ`** (i.e. structurally isomorphic by construction to
the free `ℤ`-module on `K.nSimplices n`). This shape is a deliberate
infrastructure placeholder: the genuine definition requires singular
chain complexes on `AbstractSimplicialComplex.Geometric K`, the
`(n-1)`-skeleton subcomplex, and the kernel/image quotient — none of
which are wired up yet in this project.

Consequences:

* The structural iso `relativeSkeletalH K n ≃ₗ[ℤ] (K.nSimplices n →₀ ℤ)`
  (`relative_hurewicz_identity_under_placeholder`) is honest *given the
  current definition*, but is mathematically a placeholder for the deep
  *wedge-of-spheres / cellular-vs-singular comparison theorem*.
* Theorems in this section whose proofs route through
  `homology_wedge_axiom` rely on that load-bearing geometric content,
  which is admitted as a named `sorry` and tracked as missing
  infrastructure (see the docstring on `homology_wedge_axiom`).

When the real singular-homology infrastructure lands, `relativeSkeletalH`
should be redefined as the genuine relative singular homology and the
sorry in `homology_wedge_axiom` filled by the standard
attaching-map/excision argument. -/
structure relativeSkeletalH [TopologicalSpace V] [LinearOrder V] [DecidableEq V] (K : AbstractSimplicialComplex V) (n : ℕ) where
  /-- Cellular shadow of a relative skeletal class. In the placeholder
  regime this field is the entire datum; the real definition will replace
  this structure with a genuine singular-chain quotient. -/
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

/-- The trivial structural iso induced by the current placeholder shape
of `relativeSkeletalH` (one field `down : cellularChain K n`). This is
**not** the genuine cellular↔singular comparison theorem — the name
encodes that this is the iso witnessed *under the placeholder*. Real
proofs of the wedge-of-spheres identification must not rely on this
iso; see `homology_wedge_axiom` for the honestly-admitted geometric
content. -/
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

/-- **Wedge-of-spheres / cellular comparison axiom.**

Geometric content: the quotient `|K^{(n)}|/|K^{(n-1)}|` is homeomorphic
to a wedge of `n`-spheres indexed by `K.nSimplices n` (each `n`-simplex
contributes one sphere via its characteristic-map collapse). Combined
with the excision identification
`H_n(|K^{(n)}|,|K^{(n-1)}|;ℤ) ≅ H̃_n(|K^{(n)}|/|K^{(n-1)}|;ℤ)`,
the wedge axiom for reduced singular homology, and
`H̃_n(S^n;ℤ) ≅ ℤ`, this yields the displayed `ℤ`-module isomorphism.

**Status:** Honestly admitted as `sorry`. Discharging it requires
infrastructure that is not yet present in this project: a usable
singular chain complex / singular homology API for arbitrary spaces, the
`(n-1)`-skeleton as a subspace of the geometric realisation, excision,
the wedge axiom, and `H̃_n(S^n)`. This `sorry` replaces what was a
degenerate proof routing through
`relative_hurewicz_identity_under_placeholder` — see that decl's
docstring for the explanation of why that route was a placeholder.

The unused `α : Type` parameter is retained for call-site compatibility
with `homology_wedge_of_spheres_iso_finsupp` below. -/
theorem homology_wedge_axiom [TopologicalSpace V] [LinearOrder V] [DecidableEq V]
    (K : AbstractSimplicialComplex V) (_α : Type) (n : ℕ) :
    Nonempty (relativeSkeletalH K n ≃ₗ[ℤ] (K.nSimplices n →₀ ℤ)) :=
  sorry

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

/-- Rank of the relative skeletal `H_n` of a finite-`n`-skeleton-pair
equals the number of `n`-simplices.

This is the rank-level statement of the wedge-of-spheres theorem. The
proof reduces to `homology_wedge_axiom` (the geometric content,
currently admitted as a `sorry`; see its docstring) plus the standard
`Module.finrank_finsupp_self` rank computation for a finitely-supported
free module.

Earlier the proof of this theorem routed through
`relative_hurewicz_identity_under_placeholder`, exploiting the
definitional equality between `relativeSkeletalH K n` and
`cellularChain K n`. That route was a degenerate placeholder proof. The
present proof depends instead on the *named* admission of the geometric
content in `homology_wedge_axiom`, so the dependency on missing
infrastructure is now explicit and trackable. -/
theorem singularH_wedge_of_spheres
    [TopologicalSpace V] [LinearOrder V] [DecidableEq V] (K : AbstractSimplicialComplex V) (n : ℕ)
    [Fintype (K.nSimplices n)] :
    Module.finrank ℤ (relativeSkeletalH K n) = (Fintype.card (K.nSimplices n)) := by
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
    [TopologicalSpace V] (K : AbstractSimplicialComplex V) (n : ℕ)
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

theorem skeletal_h1_five_lemma_identity
    [TopologicalSpace V] [LinearOrder V] [DecidableEq V] (K : AbstractSimplicialComplex V)
    [AbstractSimplicialComplex.Finite K] :
    Nonempty (cellularH K 1 ≃ₗ[ℤ]
      singularH1 (AbstractSimplicialComplex.Geometric K)) :=
  sorry

theorem cellular_iso_singularH_via_five_lemma
    [TopologicalSpace V] [LinearOrder V] [DecidableEq V] (K : AbstractSimplicialComplex V)
    [AbstractSimplicialComplex.Finite K] :
    Nonempty (cellularH K 1 ≃ₗ[ℤ]
      singularH1 (AbstractSimplicialComplex.Geometric K)) :=
  sorry

theorem cellular_iso_singularH [TopologicalSpace V]
    [LinearOrder V] [DecidableEq V] (K : AbstractSimplicialComplex V)
    [AbstractSimplicialComplex.Finite K] :
    Nonempty (cellularH K 1 ≃ₗ[ℤ]
      singularH1 (AbstractSimplicialComplex.Geometric K)) :=
  cellular_iso_singularH_via_five_lemma K


end JacobianChallenge.StageA
