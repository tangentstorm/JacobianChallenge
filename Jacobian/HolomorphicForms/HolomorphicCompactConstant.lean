import Jacobian.HolomorphicForms.CotangentBundle

/-! # Global holomorphic functions on a compact connected Riemann surface

Section 2 of `tex/sections/02-holomorphic-forms-and-genus.tex`.

A holomorphic function on a compact connected complex 1-manifold is
constant — the maximum modulus principle in analytic-manifold form.
Equivalently, `H⁰(X, 𝒪_X) ≃ ℂ`: the global sections of the structure
sheaf form a one-dimensional `ℂ`-vector space spanned by constant
functions.

This is a sec02 MEDIUM follow-up to the merged `CanonicalDivisor.lean`
chain. Per the explicit comment in
`Jacobian/HolomorphicForms/CanonicalDivisor.lean`:

> These belong to follow-up nodes once the analytic-sheaf machinery
> lands (`H⁰(𝒪_X) = ℂ` for compact connected RS via maximum modulus
> principle; …).

The proof requires the maximum modulus principle for analytic
functions transported along charts of a compact connected 1-manifold,
which is not yet directly available in Mathlib v4.28.0 in the
`ContMDiff (modelWithCornersSelf ℂ ℂ) … ⊤`-flavoured form used by
this project. The stub records the statement (sorry-bearing) so the
sec02 dep-graph picks it up. -/

namespace JacobianChallenge.HolomorphicForms

open scoped Manifold

/-- **MEDIUM.** Every holomorphic function on a compact connected
complex 1-manifold is constant.

PROOF SKETCH (sorry pending the analytic frontier): the modulus
`fun x => ‖f x‖` is continuous on the compact `X`, so attains its
supremum at some `x₀`; in a chart around `x₀` the chart-pulled
function `f ∘ φ⁻¹ : ℂ → ℂ` is analytic and attains an interior
maximum modulus, hence is locally constant by the maximum modulus
principle (`Mathlib.Analysis.Complex.AbsMax.AnalyticOn.eqOn_of_isMaxOn`-
flavoured); connectedness of `X` upgrades local constancy to global
constancy. -/
theorem holomorphic_compact_connected_constant
    (X : Type*) [TopologicalSpace X] [CompactSpace X] [ConnectedSpace X]
    [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X]
    (f : X → ℂ)
    (_hf : ContMDiff (modelWithCornersSelf ℂ ℂ) (modelWithCornersSelf ℂ ℂ)
      (⊤ : WithTop ℕ∞) f) :
    ∃ c : ℂ, ∀ x : X, f x = c := by
  sorry

/-- Corollary statement: the unit-modulus form of the maximum modulus
principle. Sorry-free; immediate from
`holomorphic_compact_connected_constant` once both points are in the
domain. -/
theorem holomorphic_compact_connected_const_apply
    {X : Type*} [TopologicalSpace X] [CompactSpace X] [ConnectedSpace X]
    [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X]
    {f : X → ℂ}
    (hf : ContMDiff (modelWithCornersSelf ℂ ℂ) (modelWithCornersSelf ℂ ℂ)
      (⊤ : WithTop ℕ∞) f)
    (x y : X) : f x = f y := by
  obtain ⟨c, hc⟩ := holomorphic_compact_connected_constant X f hf
  rw [hc x, hc y]

end JacobianChallenge.HolomorphicForms
