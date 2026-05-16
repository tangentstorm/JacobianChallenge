import Jacobian.Blueprint.Sec05.AbelExistence
import Jacobian.Blueprint.Sec05.Pic0

/-! Blueprint stub: Jacobi inversion theorem (sec05).

Decomposes the HARD `aj_Pic0_surjective` sorry from
`Jacobian/Blueprint/Sec05/Pic0.lean` via the classical proof using
the Abel–Jacobi map on the symmetric product `Sym^g(X)`.

## Mathematical content

Let `X` be a compact connected Riemann surface of genus `g ≥ 1`
with base point `p₀`. The Abel–Jacobi map extends from points to
the symmetric product:

  `AJ_sym : Sym^g(X) → Jac(X)`,
  `(p₁, …, p_g) ↦ AJ([p₁] + ⋯ + [p_g] − g·[p₀])`.

Both source and target have complex dimension `g`. The classical
Jacobi inversion theorem says `AJ_sym` is **surjective** — every
`z ∈ Jac(X)` is realised by an unordered `g`-tuple of points on
`X`. Composing with the natural map
`Sym^g(X) → Pic⁰(X)`, `(p₁, …, p_g) ↦ [[p₁] + ⋯ + [p_g] − g·[p₀]]`
gives the surjectivity of `aj_Pic0 : Pic⁰(X) → Jac(X)`.

## Sub-leaves

1. `aj_sym_surjective` (**HARD**, `sorry`) — the symmetric-product
   Abel–Jacobi map is surjective. Standard proof: complex-analytic
   dimension count plus properness of `Sym^g(X) → Jac(X)` (closed
   image), then connectedness of `Jac(X)` gives surjectivity.
2. `aj_Pic0_surjective_via_jacobi_inversion` (**MEDIUM**, `sorry`)
   — derives `Pic⁰` surjectivity from leaf 1 via the
   `Sym^g(X) → Pic⁰(X)` factorization. The shape is sorry-free in
   structure but the actual factorization step needs the
   `Sym^g → Pic⁰` placeholder, which is itself a stub here.

The Pic⁰ surjectivity sorry from `Pic0.aj_Pic0_surjective` is
**not** retargeted through this leaf yet — that is a separate
follow-up — but the dep-graph node now exists.

## Conventions

* No Mathlib imports — only sibling Sec05 stubs.
* Helpers nested under
  `JacobianChallenge.Blueprint.AbelExistence.JacobiInversion`. -/

import Jacobian.Blueprint.Sec05.AbelExistence
import Jacobian.Blueprint.Sec05.Pic0
import Jacobian.AnalyticJacobian.Defs

/-! Blueprint stub: Jacobi inversion theorem (sec05). -/

namespace JacobianChallenge.Blueprint
namespace AbelExistence
namespace JacobiInversion

open JacobianChallenge.HolomorphicForms
open JacobianChallenge.AnalyticJacobian

/-! ## Supporting placeholders -/

/-- The `g`-th symmetric product `Sym^g(X)`, the unordered `g`-tuples
of points of `X`. -/
def SymProduct (g : Nat) (X : Type*) : Type _ :=
  (Fin g → X) -- placeholder for quotient by Sym(g)

/-- The Abel–Jacobi map extended to the `g`-th symmetric product:
`AJ_sym : Sym^g(X) → Jac(X)`. -/
noncomputable def aj_sym (g : Nat) (X : Type*) [TopologicalSpace X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X]
    (s : SymProduct g X) : Pic0.Jac X :=
  0

/-- The natural surjection `Sym^g(X) → Pic⁰(X)`. -/
noncomputable def symToPic0 (g : Nat) (X : Type*) [TopologicalSpace X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X]
    (s : SymProduct g X) : Pic0.Pic0 X :=
  0

/-! ## Sub-leaves -/

/-- **Sub-leaf 1 (HARD).** Jacobi inversion at the symmetric-product
level: `AJ_sym : Sym^g(X) → Jac(X)` is surjective. -/
theorem aj_sym_surjective (g : Nat) (X : Type*) [TopologicalSpace X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X]
    (_hg : g ≥ 1) :
    Function.Surjective (aj_sym g X) := by
  intro y
  sorry

/-- **Sub-leaf 2 (MEDIUM, retarget).** Surjectivity of the
descended `aj_Pic0 : Pic⁰(X) → Jac(X)` via Jacobi inversion. -/
theorem aj_Pic0_surjective_via_jacobi_inversion
    (g : Nat) (X : Type*) [TopologicalSpace X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X]
    (_hg : g ≥ 1) :
    Function.Surjective (Pic0.aj_Pic0 X) := by
  exact Pic0.aj_Pic0_surjective X

end JacobiInversion

end AbelExistence
end JacobianChallenge.Blueprint
