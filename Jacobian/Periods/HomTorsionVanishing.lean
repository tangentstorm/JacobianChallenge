import Mathlib.Algebra.Module.Torsion.Free
import Mathlib.GroupTheory.OrderOfElement
import Mathlib.Data.Real.Basic
import Mathlib.LinearAlgebra.LinearIndependent.Defs

/-!
# Torsion-Hom vanishing: `Hom_ℤ(T, ℝ) = 0` for torsion `T`

Pure-algebra leaf backing the blueprint claim
`lem:hdr-r3` (Pass G2.3 of Chain G2 in §14.R6, Round 1):

> For a finitely generated abelian group `A = ℤ^r ⊕ T` (structure
> theorem), the torsion summand `T` contributes nothing to
> `Hom_ℤ(A, ℝ)`, because every ℤ-linear map `T →ₗ[ℤ] ℝ` is zero.

The argument is:

* For `a : T` of finite additive order `n ≥ 1`, ℤ-linearity gives
  `(n : ℤ) • φ a = φ ((n : ℤ) • a) = φ 0 = 0` in `ℝ`.
* `ℝ` is torsion-free as a ℤ-module (it is a `CharZero`-`IsDomain`,
  hence `NoZeroSMulDivisors ℤ ℝ`), so `(n : ℤ) ≠ 0` and the equation
  forces `φ a = 0`.

This file makes that argument formal so the blueprint's
`hdr-r3` leaf is `\leanok` rather than `\notready`.
-/

namespace JacobianChallenge.Periods

/-- **Lem `hdr-r3`** (R6, Chain G2, Pass 3): every ℤ-linear map from
a torsion ℤ-module to `ℝ` vanishes on torsion elements.

Stated pointwise: `φ a = 0` whenever `a` has finite additive order. -/
theorem homℤℝ_apply_eq_zero_of_isOfFinAddOrder
    {T : Type*} [AddCommGroup T] [Module ℤ T]
    (φ : T →ₗ[ℤ] ℝ) {a : T} (ha : IsOfFinAddOrder a) : φ a = 0 := by
  obtain ⟨n, hn_pos, hna⟩ : ∃ n : ℕ, 0 < n ∧ n • a = 0 :=
    isOfFinAddOrder_iff_nsmul_eq_zero.mp ha
  -- Convert nat smul to int smul.
  have hzna : (n : ℤ) • a = 0 := by
    rw [natCast_zsmul, hna]
  -- Apply ℤ-linearity.
  have hphi : (n : ℤ) • φ a = 0 := by
    rw [← LinearMap.map_smul_of_tower, hzna, map_zero]
  -- ℝ is torsion-free over ℤ.
  have hn_ne : (n : ℤ) ≠ 0 := Int.natCast_ne_zero.mpr hn_pos.ne'
  exact (smul_eq_zero.mp hphi).resolve_left hn_ne

/-- **Lem `hdr-r3`** (R6, Chain G2, Pass 3, bundled form):
`Hom_ℤ(T, ℝ) = 0` whenever `T` is a torsion abelian group, i.e.
every element of `T` has finite additive order. -/
theorem homℤℝ_eq_zero_of_isTorsion
    {T : Type*} [AddCommGroup T] [Module ℤ T]
    (hT : ∀ a : T, IsOfFinAddOrder a) (φ : T →ₗ[ℤ] ℝ) : φ = 0 := by
  ext a
  exact homℤℝ_apply_eq_zero_of_isOfFinAddOrder φ (hT a)

end JacobianChallenge.Periods
