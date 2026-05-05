import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.LinearAlgebra.Alternating.Basic
import Mathlib.Analysis.Calculus.FDeriv.Symmetric

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

/-- **Lifted form of the algebraic core: arbitrary basis.** Given a
finite indexing `b : ι → V` of vectors in any real vector space `V`,
the contraction of a symmetric bilinear pairing `S` with an
antisymmetric pairing `α` along `b` vanishes. -/
theorem sum_sym_alt_contraction_eq_zero
    {ι : Type*} [Fintype ι] {V : Type*}
    (b : ι → V)
    (S : V → V → ℝ) (hS : ∀ v w, S v w = S w v)
    (α : V → V → ℝ) (hAlt : ∀ v w, α v w = -α w v) :
    ∑ i, ∑ j, S (b i) (b j) * α (b i) (b j) = 0 :=
  sum_sym_antisym_eq_zero
    (fun i j => S (b i) (b j))
    (fun i j => α (b i) (b j))
    (fun i j => hS (b i) (b j))
    (fun i j => hAlt (b i) (b j))

/-! ### Bridge to Mathlib's second-derivative symmetry -/

/-- **Schwarz-driven contraction vanishing (R9 J2 chart-local).**
For a `C²`-at-`x` real-valued function on a real normed space and any
finite-indexed family of test vectors `b : ι → E`, the sum
`∑ᵢⱼ (D²f x)(bᵢ, bⱼ) · α(bᵢ, bⱼ)` vanishes whenever `α` is
antisymmetric.  This is the chart-local content of `d²f = 0`:
`α` plays the role of the alternating two-form coefficient and
`D²f` plays the role of `∂ᵢ∂ⱼ f`, symmetric by Schwarz
(\code{ContDiffAt.isSymmSndFDerivAt}). -/
theorem schwarz_contraction_alt_eq_zero
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {ι : Type*} [Fintype ι]
    {f : E → ℝ} {x : E} (hf : ContDiffAt ℝ 2 f x)
    (b : ι → E)
    (α : E → E → ℝ) (hAlt : ∀ v w, α v w = -α w v) :
    ∑ i, ∑ j, fderiv ℝ (fderiv ℝ f) x (b i) (b j) * α (b i) (b j) = 0 := by
  -- Schwarz: the second Fréchet derivative is symmetric in its two arguments.
  have hsymm : IsSymmSndFDerivAt ℝ f x := by
    have hle : minSmoothness ℝ (2 : WithTop ℕ∞) ≤ (2 : WithTop ℕ∞) := by
      simp
    exact hf.isSymmSndFDerivAt hle
  exact sum_sym_alt_contraction_eq_zero b
      (fun v w => fderiv ℝ (fderiv ℝ f) x v w)
      (fun v w => hsymm.eq v w)
      α hAlt

/-! ### Bridge to Mathlib's `AlternatingMap` -/

open AlternatingMap in
/-- **Two-argument alternating map: swap negates.** Specialising
Mathlib's `AlternatingMap.map_swap` to the index type `Fin 2` and the
unique non-trivial transposition. -/
theorem alternatingMap_two_swap_neg
    {R : Type*} [CommSemiring R]
    {M N : Type*} [AddCommGroup M] [Module R M]
    [AddCommGroup N] [Module R N]
    (g : M [⋀^Fin 2]→ₗ[R] N) (v : Fin 2 → M) :
    g (v ∘ Equiv.swap (0 : Fin 2) (1 : Fin 2)) = - g v :=
  g.map_swap v (by decide)

/-- **Antisymmetry of the bilinear form induced by a two-argument
`AlternatingMap`.** This is the form in which the alternating-map
structure plugs into `sum_sym_antisym_eq_zero`. -/
theorem alternatingMap_two_antisym
    {R : Type*} [CommSemiring R]
    {M : Type*} [AddCommGroup M] [Module R M]
    {N : Type*} [AddCommGroup N] [Module R N]
    (g : M [⋀^Fin 2]→ₗ[R] N) (v w : M) :
    g ![v, w] = - g ![w, v] := by
  have h := alternatingMap_two_swap_neg g ![w, v]
  -- `![w, v] ∘ Equiv.swap 0 1 = ![v, w]` by extensionality on `Fin 2`.
  have hperm : (![w, v] : Fin 2 → M) ∘ Equiv.swap (0 : Fin 2) 1 = ![v, w] := by
    funext i
    fin_cases i <;> simp
  rw [hperm] at h
  exact h

end JacobianChallenge.Analysis.BundledForms.DSqZero
