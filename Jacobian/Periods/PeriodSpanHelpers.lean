import Mathlib.LinearAlgebra.Complex.FiniteDimensional
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.Dimension.Constructions

/-!
# Helper lemmas for `periodSubgroup_spans_real`

Pure linear-algebra facts used to reduce the full-ℝ-rank obligation
for the period subgroup to the existence of `2g` ℝ-linearly
independent period vectors.

## Main results

* `finrank_real_fin_pi_complex` — `finrank ℝ (Fin g → ℂ) = 2 * g`.
* `span_real_eq_top_of_linearIndependent_fin` — `2g` ℝ-linearly
  independent vectors in `Fin g → ℂ` span the whole space over ℝ.
* `span_real_eq_top_of_subset_linearIndependent` — if a set `S`
  contains the range of `2g` ℝ-linearly independent vectors, its
  ℝ-span is `⊤`.
-/

open scoped ComplexConjugate

/-- `finrank ℝ (Fin g → ℂ) = 2 * g`. -/
theorem finrank_real_fin_pi_complex (g : ℕ) :
    Module.finrank ℝ (Fin g → ℂ) = 2 * g := by
  rw [Module.finrank_pi_fintype, Complex.finrank_real_complex,
      Finset.sum_const, Finset.card_fin, smul_eq_mul, mul_comm]

/-- `2g` ℝ-linearly independent vectors in `Fin g → ℂ` span the
full space over ℝ. Follows from dimension counting:
`finrank ℝ (Fin g → ℂ) = 2g`.

When `g = 0`, the space `Fin 0 → ℂ` is trivially zero-dimensional
and every submodule equals `⊤`. -/
theorem span_real_eq_top_of_linearIndependent_fin (g : ℕ)
    (b : Fin (2 * g) → Fin g → ℂ) (hli : LinearIndependent ℝ b) :
    Submodule.span ℝ (Set.range b) = ⊤ := by
  rcases Nat.eq_zero_or_pos g with rfl | hg
  · haveI : Unique (Fin 0 → ℂ) := Pi.uniqueOfIsEmpty _
    exact Subsingleton.elim _ _
  · haveI : Nonempty (Fin (2 * g)) := ⟨⟨0, by omega⟩⟩
    exact hli.span_eq_top_of_card_eq_finrank
      (by rw [Fintype.card_fin, finrank_real_fin_pi_complex])

/-- If a set `S` contains the range of `2g` ℝ-linearly independent
vectors in `Fin g → ℂ`, then `Submodule.span ℝ S = ⊤`. -/
theorem span_real_eq_top_of_subset_linearIndependent (g : ℕ)
    (S : Set (Fin g → ℂ))
    (b : Fin (2 * g) → Fin g → ℂ)
    (hli : LinearIndependent ℝ b)
    (hrange : Set.range b ⊆ S) :
    Submodule.span ℝ S = ⊤ :=
  top_le_iff.mp
    (span_real_eq_top_of_linearIndependent_fin g b hli ▸
      Submodule.span_mono hrange)
