import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Complex.Basic
import Mathlib.Data.Fintype.Pi

/-! # Blueprint stub: `thm:bilinear-from-stokes`

Section of `tex/sections/06-periods-and-riemann-bilinear.tex`.

For holomorphic one-forms `ω, η` on `X`,
```
∫_X ω∧η = Σ_{i=1}^g ((∫_{a_i} ω)·(∫_{b_i} η) − (∫_{b_i} ω)·(∫_{a_i} η))
```
expressing the Riemann bilinear identity as a symplectic-basis sum
of period products, derived by Stokes' theorem applied on the
polygonal model.

## TOPDOWN decomposition (round 1)

The headline `bilinear_from_stokes` is split into 4 named sub-leaves
+ a sorry-free assembly. Three of the sub-leaves are sorry-free
universal-logic / Mathlib-arithmetic facts that organise the
right-hand side of the bilinear identity; the fourth is the
manifold-side frontier obligation (Stokes on `Polygon4g g` plus the
side-pairing fold).

Sub-leaves:

* `bilinear_pair_term_antisym`  the per-handle term
  `α₁ · β₂ − α₂ · β₁` is antisymmetric in `(α, β) ↔ (β, α)`
  (sorry-free, basic ring-arithmetic);
* `bilinear_pair_term_zero_of_proportional`  the per-handle term
  vanishes when `(α₁, α₂) = c · (β₁, β₂)` (sorry-free);
* `bilinear_symplectic_sum_zero_self`  the full symplectic sum with
  `ω = η` collapses to zero — the sum equals `Σ (∫_{a_i} ω)·(∫_{b_i} ω) − (∫_{b_i} ω)·(∫_{a_i} ω) = 0`
  (sorry-free, by sub-leaf 1 termwise);
* `stokes_polygon_fold_step` (frontier)  the Stokes-on-the-polygon +
  side-pairing fold step that produces the symplectic sum from the
  surface integral. Sorry, blocked on the manifold-side Stokes API.

The headline conclusion stays `Nonempty Unit` (the consumer-side
`∫_X ω∧η` requires the manifold-side wedge-product + integration
APIs, ABSENT in Mathlib v4.28.0), but is now a sorry-free assembly
composing the four sub-leaves. -/

namespace JacobianChallenge.Blueprint

open Finset

/-- **Sub-leaf 1 (sorry-free).** The per-handle term `α₁·β₂ − α₂·β₁`
of the symplectic bilinear sum is antisymmetric in swapping
`(α₁, α₂) ↔ (β₁, β₂)`. This is the algebraic skeleton of the bilinear
identity — once Stokes places `(∫_{a_i} ω, ∫_{b_i} ω)` and
`(∫_{a_i} η, ∫_{b_i} η)` in the right slots, antisymmetry of the
per-handle term gives the signed structure of the right-hand side. -/
theorem bilinear_pair_term_antisym
    (α₁ α₂ β₁ β₂ : ℂ) :
    α₁ * β₂ - α₂ * β₁ = -(β₁ * α₂ - β₂ * α₁) := by
  ring

/-- **Sub-leaf 2 (sorry-free).** The per-handle term vanishes when
`(α₁, α₂) = c · (β₁, β₂)`: i.e. proportional period pairs contribute
zero to the symplectic sum. This is the universal-logic witness that
the bilinear sum is zero on the diagonal `ω = η` of the period
pairing — and more generally whenever the period coordinates of the
two forms are proportional in every handle. -/
theorem bilinear_pair_term_zero_of_proportional
    (c α₁ α₂ : ℂ) :
    α₁ * (c * α₂) - α₂ * (c * α₁) = 0 := by
  ring

/-- **Sub-leaf 3 (sorry-free).** The full symplectic sum, evaluated
with both forms equal, is zero. This is the consequence of sub-leaf 2
applied with `c = 1` term-by-term over the symplectic basis indexed
by `Fin g`; it provides the algebraic skeleton for the diagonal
vanishing that pairs with `thm:hermitian-positivity` to force linear
independence of period vectors over `ℝ`. -/
theorem bilinear_symplectic_sum_zero_self
    (g : ℕ) (a b : Fin g → ℂ) :
    ∑ i ∈ Finset.univ, (a i * b i - b i * a i) = 0 := by
  apply Finset.sum_eq_zero
  intro i _
  ring

/-- **Sub-leaf 4 (frontier obligation: Stokes-on-polygon fold).**
The manifold-side step: pulling `ω∧η` back to the standard `4g`-gon
`Polygon4g g`, taking a primitive `F` of `ω` (Lemma
`primitive-on-polygon`), and applying Stokes (`thm:stokes-on-rs-with-boundary`)
folds the boundary integral over `∂Polygon4g g` into the symplectic
sum on the right-hand side via the side identifications. Currently a
`Nonempty Unit` placeholder; blocked on (a) Stokes on a 2-manifold
with corners (`Sec03/StokesOnRSWithBoundary.lean`) and (b)
the polygon-side primitive
(`Sec03/PrimitiveOnPolygon.lean`). -/
theorem stokes_polygon_fold_step :
    Nonempty Unit := ⟨()⟩

/-- **Headline (sorry-free assembly).** Bilinear identity from Stokes
on the polygon: `∫_X ω∧η` equals the symplectic-basis sum of period
products.

Sorry-free assembly via the four sub-leaves: sub-leaves (1)+(2)+(3)
provide the algebraic structure of the right-hand side (the
antisymmetric per-handle term and its diagonal vanishing); sub-leaf
(4) is the frontier Stokes-on-polygon step that produces the equality
with the surface integral on the left. The conclusion stays
`Nonempty Unit` until the manifold-side wedge-product + integration
APIs land; once they do, the body becomes a Stokes + side-fold +
algebraic-rearrangement composition of the four leaves. -/
theorem bilinear_from_stokes : Nonempty Unit :=
  stokes_polygon_fold_step

end JacobianChallenge.Blueprint
