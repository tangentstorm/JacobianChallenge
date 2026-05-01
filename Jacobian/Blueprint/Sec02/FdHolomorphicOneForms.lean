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

/-- Finite-dimensionality of holomorphic 1-forms on a compact connected
complex 1-manifold. The proof extracts a `HolomorphicOneFormBanachData`
from `holomorphicOneForm_normedSpace_uniformOnCompact`, installs the
resulting `NormedAddCommGroup` / `NormedSpace ℂ` instances, derives
local compactness via `holomorphicOneForm_locallyCompact_of_compactRiemannSurface`,
and closes with Riesz's theorem (`FiniteDimensional.of_locallyCompactSpace`).

(Aristotle a489296c, sorry-free transport.) -/
theorem fd_holomorphic_one_forms
    (X : Type*) [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X] :
    FiniteDimensional ℂ (HolomorphicOneForm ℂ X) := by
  obtain ⟨B⟩ := holomorphicOneForm_normedSpace_uniformOnCompact X
  letI : NormedAddCommGroup (HolomorphicOneForm ℂ X) := B.toNormedAddCommGroup
  letI : NormedSpace ℂ (HolomorphicOneForm ℂ X) := B.toNormedSpace
  letI : LocallyCompactSpace (HolomorphicOneForm ℂ X) :=
    holomorphicOneForm_locallyCompact_of_compactRiemannSurface X B
  exact FiniteDimensional.of_locallyCompactSpace ℂ

end JacobianChallenge.Blueprint
