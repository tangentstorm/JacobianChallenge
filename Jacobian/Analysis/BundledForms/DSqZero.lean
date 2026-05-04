import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# R9 — Algebraic core of `d² = 0`

This file dispatches the algebraic identity that sits at the bottom
of Chain J2 in the R9 stepwise refinement
(`tex/sections/12-classical-analysis-gaps.tex`, passes
`bfd-r9`, `bfd-r13`):

> For a symmetric "matrix" `S : ι → ι → ℝ` and an antisymmetric
> "matrix" `A : ι → ι → ℝ` indexed by a finite type `ι`, the
> double sum `∑ i, ∑ j, S i j * A i j` vanishes.

This is the purely-algebraic content of `d² = 0` once the
chart-local description has been unfolded: with
`S i j = ∂ᵢ ∂ⱼ f` (symmetric by Schwarz) and `A i j` the
`(dxⁱ ∧ dxʲ)`-coefficient (antisymmetric by the alternating
structure), the contraction `∑ S A` is the coefficient of
`d²f` in the chart, and the lemma below says it is zero.

Proof strategy: pair `(i, j)` with `(j, i)`, observing that
`S i j * A i j + S j i * A j i = 0` (symmetric × antisymmetric =
algebraic cancellation). Combined with `Finset.sum_comm` for the
re-indexing, this gives `Σ + Σ = 0`, hence `Σ = 0` over `ℝ`.
-/

namespace JacobianChallenge.Analysis.BundledForms.DSqZero

/-- **R9 Chain J2 algebraic core.**  Symmetric × antisymmetric
contraction over a finite index set vanishes over `ℝ`. -/
theorem sum_sym_antisym_eq_zero
    {ι : Type*} [Fintype ι]
    (S A : ι → ι → ℝ)
    (hS : ∀ i j, S i j = S j i)
    (hA : ∀ i j, A i j = -A j i) :
    ∑ i, ∑ j, S i j * A i j = 0 := by
  have pair : ∀ p q : ι, S p q * A p q + S q p * A q p = 0 := by
    intro p q
    rw [hS q p, hA q p]
    ring
  have hsum_pair :
      (∑ i, ∑ j, S i j * A i j) + (∑ i, ∑ j, S j i * A j i) = 0 := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_eq_zero (fun i _ => ?_)
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_eq_zero (fun j _ => pair i j)
  have hcomm :
      (∑ i, ∑ j, S j i * A j i) = (∑ i, ∑ j, S i j * A i j) :=
    Finset.sum_comm
  linarith

/-- **Diagonal vanishing for an antisymmetric form over `ℝ`.**
A direct corollary of the antisymmetry: `A i i = -A i i` forces
`A i i = 0` over `ℝ` (or any field of characteristic `≠ 2`). -/
theorem antisym_diag_eq_zero
    {ι : Type*} (A : ι → ι → ℝ) (hA : ∀ i j, A i j = -A j i) (i : ι) :
    A i i = 0 := by
  have h : A i i = -A i i := hA i i
  linarith

end JacobianChallenge.Analysis.BundledForms.DSqZero
