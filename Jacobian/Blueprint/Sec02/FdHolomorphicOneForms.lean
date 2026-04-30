import Jacobian.Blueprint.Sec02.InputFiniteDimensionality

/-! # Blueprint stub: `thm:fd-holomorphic-one-forms`

Section 2 of `tex/sections/02-holomorphic-forms-and-genus.tex`.

User-facing finite-dimensionality of `H⁰(X, Ω¹)` on a compact complex
1-manifold:

```text
dim_ℂ H⁰(X, Ω¹) < ∞
```

Direct consumer of `input:finite-dimensionality`. The downstream
worker discharges this by transporting the result of
`input_finite_dimensionality` along the canonical normed-space
realisation supplied by the production-side
`HolomorphicOneFormBanachData` (see
`Jacobian/HolomorphicForms/CompactRiemannSurface.lean`).

This is the named obligation that
`JacobianChallenge.HolomorphicForms.compactRiemannSurface_finiteDimensionalHolomorphicOneForms`
ultimately discharges in the production tree; the blueprint version is
the cleanly stub-able statement on the bare `HolomorphicOneForm`
type. -/

namespace JacobianChallenge.Blueprint

open scoped Manifold
open JacobianChallenge.HolomorphicForms

/-- Finite-dimensionality of holomorphic 1-forms on a compact complex
1-manifold. Conclusion is `FiniteDimensional ℂ` (matching
`fd_from_riesz` and `input_finite_dimensionality`); the
`Module.Finite` form is `FiniteDimensional` definitionally and a
corollary in either direction is a one-liner if needed downstream. -/
theorem fd_holomorphic_one_forms
    (X : Type*) [TopologicalSpace X] [T2Space X] [CompactSpace X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X] :
    FiniteDimensional ℂ (HolomorphicOneForm ℂ X) := by
  -- DEPENDS ON node 7 (`input_finite_dimensionality`), which in turn
  -- depends on node 5 (`hone_unit_ball_compact`). Once both landed, the
  -- discharge is plumbing only:
  --   1. extract a `HolomorphicOneFormBanachData X` realisation `B` from
  --      `JacobianChallenge.HolomorphicForms.holomorphicOneForm_normedSpace_uniformOnCompact`
  --      (Jacobian/HolomorphicForms/CompactRiemannSurface.lean);
  --   2. the realisation gives a `≃ₗ[ℂ]` `e : HolomorphicOneForm ℂ X ≃ₗ[ℂ] H`
  --      and a norm-match hypothesis `h_norm`;
  --   3. `have : FiniteDimensional ℂ H := input_finite_dimensionality X e h_norm`;
  --   4. transport back along `e.symm` via
  --      `LinearEquiv.finiteDimensional` (Mathlib).
  sorry

end JacobianChallenge.Blueprint
