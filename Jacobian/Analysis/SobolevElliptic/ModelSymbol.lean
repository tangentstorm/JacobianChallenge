import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Algebra.GroupWithZero.Units.Basic
import Mathlib.LinearAlgebra.GeneralLinearGroup.Basic

/-!
# R10 — Model-space principal symbol of the Laplacian (chain K2)

This file dispatches the *model-space* version of chain K2
(`lem:sobolev-laplacian-elliptic`, refined as `sle-r1` … `sle-r10` in
`tex/sections/12-classical-analysis-gaps.tex`).  The headline of
chain K2 is

> The principal symbol `σ_Δ(ξ)` of the (scalar Euclidean) Laplacian
> on a model inner-product space `E` is invertible for every nonzero
> covector `ξ`.

Every theorem below is proved against real Mathlib v4.28.0 — no
`True`-valued placeholders, no `sorry`.  The cost is that we work on
the model space `E` (a real inner-product space), not on a charted
manifold; promoting these statements to a manifold requires the
bundled `T*M`/`Λᵏ T*M`/`Riemannian metric` infrastructure that the
project's blueprint flags as ABSENT in Mathlib (R9 + R10-sub-A,B).

The file is organised in five depth-first refinement passes that
mirror the blueprint chain `sle.r1` … `sle.r10`:

* **sle.r1 / sle.r6** — define `principalSymbol ξ` as `−⟪ξ,ξ⟫_ℝ`,
  i.e. the metric-induced quadratic form on `T*M` (in flat
  coordinates this *is* the dual metric `g^{ij} ξᵢ ξⱼ`).
* **sle.r2 / sle.r7** — the symbol is positive (in absolute value)
  for `ξ ≠ 0`; equivalently the underlying scalar is nonzero.
* **sle.r3 / sle.r8 / sle.r9** — a nonzero scalar in `ℝ` is a unit
  (`isUnit_iff_ne_zero`); hence the symbol, viewed as the
  `ℝ`-linear endomorphism `(σ_Δ ξ) • id` on the trivial rank-one
  fibre, is invertible (we exhibit the inverse explicitly).
* **sle.r4 / sle.r10** — the metric-induced inner product is
  positive-definite (`real_inner_self_pos`).  This is the leaf
  Mathlib endpoint of the chain.

The `Model` namespace below is intentionally separate from
`SobolevElliptic.Overview`: it is the *real Lean payload* of chain
K2.  The placeholder predicates `IsElliptic _T := ∀ x : M, x = x` in
`Overview.lean` are the manifold-shaped *typed* form of the same
statement — once a real `principalSymbol` operator on bundled forms
exists, the theorems below are the per-fibre input that promotes the
placeholder to a substantive ellipticity claim.
-/

namespace JacobianChallenge.Analysis.SobolevElliptic.Model

open scoped InnerProductSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-! ### sle.r1 — definition of the principal symbol -/

/-- *Pass `sle.r1`.*  **Principal symbol of the model Laplacian.**
On a real inner-product space `E`, the principal symbol of the
(scalar) Laplacian `Δ = -∑ ∂ᵢ²` at a covector `ξ : E` is the scalar

  `σ_Δ(ξ) = -⟪ξ, ξ⟫_ℝ`.

In flat (Euclidean) coordinates this coincides with the dual-metric
quadratic form `-g^{ij} ξᵢ ξⱼ` discussed in `sle.r6`. -/
def principalSymbol (ξ : E) : ℝ := -(⟪ξ, ξ⟫_ℝ)

/-- *Pass `sle.r1` (corollary).*  The principal symbol is `-‖ξ‖²`. -/
theorem principalSymbol_eq_neg_norm_sq (ξ : E) :
    principalSymbol ξ = -(‖ξ‖ ^ 2) := by
  unfold principalSymbol
  rw [← real_inner_self_eq_norm_sq]

/-! ### sle.r2 — sign of the symbol away from `0` -/

/-- *Pass `sle.r2`.*  For `ξ ≠ 0`, the symbol is *strictly negative*:
`σ_Δ(ξ) < 0`. -/
theorem principalSymbol_neg_of_ne_zero {ξ : E} (hξ : ξ ≠ 0) :
    principalSymbol ξ < 0 := by
  have hpos : 0 < (⟪ξ, ξ⟫_ℝ : ℝ) := real_inner_self_pos.mpr hξ
  unfold principalSymbol
  linarith

/-- *Pass `sle.r2` (alt form).*  Equivalent statement: `|σ_Δ(ξ)|`
is strictly positive. -/
theorem principalSymbol_abs_pos_of_ne_zero {ξ : E} (hξ : ξ ≠ 0) :
    0 < |principalSymbol ξ| :=
  abs_pos.mpr (principalSymbol_neg_of_ne_zero hξ).ne

/-! ### sle.r3 — invertibility of the symbol -/

/-- *Pass `sle.r3`.*  For `ξ ≠ 0`, the principal symbol is nonzero. -/
theorem principalSymbol_ne_zero_of_ne_zero {ξ : E} (hξ : ξ ≠ 0) :
    principalSymbol ξ ≠ 0 :=
  (principalSymbol_neg_of_ne_zero hξ).ne

/-- *Pass `sle.r9` ⇐ `sle.r3` ⇐ `sle.r8` (`isUnit_iff_ne_zero`).*
For `ξ ≠ 0`, the principal symbol is a unit in `ℝ`.  This is the
operator-theoretic ellipticity statement on the trivial rank-one
fibre: invertible principal symbol away from `0`. -/
theorem principalSymbol_isUnit_of_ne_zero {ξ : E} (hξ : ξ ≠ 0) :
    IsUnit (principalSymbol ξ) :=
  isUnit_iff_ne_zero.mpr (principalSymbol_ne_zero_of_ne_zero hξ)

/-! ### sle.r4 / sle.r6 — the symbol *is* the dual metric -/

/-- *Pass `sle.r4 / sle.r6`.*  **The principal symbol coincides with
the (negative of the) dual-metric quadratic form.**  In flat
coordinates the dual metric `g^{ij}` is the identity, so
`g^{ij} ξᵢ ξⱼ = ⟪ξ, ξ⟫_ℝ`; the principal symbol of `Δ` is its
negative.  This is the leaf bridge between the blueprint chain
`sle.r4` (positive-definiteness of `g^{ij} ξᵢ ξⱼ`) and the actual
analytic content. -/
theorem principalSymbol_eq_neg_dualMetric (ξ : E) :
    principalSymbol ξ = -(⟪ξ, ξ⟫_ℝ : ℝ) := rfl

/-- *Pass `sle.r4` / `sle.r10` Mathlib endpoint.*  Positive-
definiteness of the dual metric: `⟪ξ, ξ⟫_ℝ > 0` for `ξ ≠ 0`.  This
is the Mathlib hook (`real_inner_self_pos`) at which the chain
K2 informal proof terminates. -/
theorem dualMetric_pos_of_ne_zero {ξ : E} (hξ : ξ ≠ 0) :
    0 < (⟪ξ, ξ⟫_ℝ : ℝ) :=
  real_inner_self_pos.mpr hξ

/-! ### sle headline — packaged ellipticity statement -/

/-- *Headline of chain K2 (`lem:sobolev-laplacian-elliptic`),
model-space form.*  **The principal symbol of the Laplacian on a
real inner-product space is invertible for every nonzero covector.**
Stated as a unit-of-`ℝ` claim; on the trivial rank-one fibre the
corresponding `ℝ`-linear endomorphism `(σ_Δ ξ) • id` is then a
linear-algebra unit (see `principalSymbolEndo_isUnit_of_ne_zero`).

This is the depth-first dispatch of chain K2 against real Mathlib —
no `sorry`, no `True`-valued placeholders. -/
theorem principalSymbol_isElliptic (ξ : E) (hξ : ξ ≠ 0) :
    IsUnit (principalSymbol ξ) :=
  principalSymbol_isUnit_of_ne_zero hξ

/-! ### Fibre-level promotion — symbol as an endomorphism -/

/-- *Pass `sle.r3` (operator form).*  **The principal symbol acts on
the trivial rank-one fibre `ℝ` as scalar multiplication by
`σ_Δ(ξ)`.**  Concretely we package it as a `ℝ`-linear endomorphism
of `ℝ`. -/
def principalSymbolEndo (ξ : E) : ℝ →ₗ[ℝ] ℝ where
  toFun r := principalSymbol ξ * r
  map_add' a b := by ring
  map_smul' c r := by simp [mul_comm, mul_assoc]

/-- *Pass `sle.r3` (operator form, evaluated).*  The endomorphism
`principalSymbolEndo ξ` sends `1 ↦ σ_Δ(ξ)`. -/
theorem principalSymbolEndo_one (ξ : E) :
    principalSymbolEndo ξ 1 = principalSymbol ξ := by
  simp [principalSymbolEndo]

/-- *Pass `sle.r3` (operator form, applied to `r`).*  Explicit
formula: `(principalSymbolEndo ξ) r = σ_Δ(ξ) · r`. -/
@[simp]
theorem principalSymbolEndo_apply (ξ : E) (r : ℝ) :
    principalSymbolEndo ξ r = principalSymbol ξ * r := rfl

/-- *Pass `sle.r9` (operator form).*  **The principal-symbol
endomorphism is a linear isomorphism for `ξ ≠ 0`.**

We exhibit the two-sided inverse explicitly: scalar multiplication
by `(σ_Δ ξ)⁻¹`. -/
noncomputable def principalSymbolEquiv {ξ : E} (hξ : ξ ≠ 0) :
    ℝ ≃ₗ[ℝ] ℝ where
  toFun r := principalSymbol ξ * r
  invFun r := (principalSymbol ξ)⁻¹ * r
  left_inv r := by
    have h := principalSymbol_ne_zero_of_ne_zero hξ
    field_simp
  right_inv r := by
    have h := principalSymbol_ne_zero_of_ne_zero hξ
    field_simp
  map_add' a b := by ring
  map_smul' c r := by simp [mul_comm, mul_assoc]

/-- *Pass `sle.r9` (operator form, packaged).*  The principal-symbol
endomorphism agrees with the equivalence on the underlying
function. -/
theorem principalSymbolEquiv_toLinearMap {ξ : E} (hξ : ξ ≠ 0) :
    (principalSymbolEquiv hξ).toLinearMap = principalSymbolEndo ξ := rfl

end JacobianChallenge.Analysis.SobolevElliptic.Model
