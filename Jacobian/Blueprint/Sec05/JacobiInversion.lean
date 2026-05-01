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

namespace JacobianChallenge.Blueprint
namespace AbelExistence
namespace JacobiInversion

/-! ## Supporting placeholders -/

/-- Placeholder for the `g`-th symmetric product `Sym^g(X)`,
the unordered `g`-tuples of points of `X`. The eventual real
definition is the quotient `(Fin g → X) / Sym(g)` of `g`-tuples
by the symmetric group action. -/
def SymProduct (_g : Nat) (_X : Type) : Type := Unit

/-- The Abel–Jacobi map extended to the `g`-th symmetric product:
`AJ_sym : Sym^g(X) → Jac(X)`,
`(p₁, …, p_g) ↦ AJ([p₁] + ⋯ + [p_g] − g·[p₀])`. Placeholder. -/
def aj_sym (_g : Nat) (X : Type) (_s : SymProduct _g X) : Pic0.Jac X := 0

/-- The natural surjection `Sym^g(X) → Pic⁰(X)`,
`(p₁, …, p_g) ↦ [[p₁] + ⋯ + [p_g] − g·[p₀]]`. Placeholder. -/
def symToPic0 (_g : Nat) (X : Type) (_s : SymProduct _g X) : Pic0.Pic0 X :=
  0

/-! ## Sub-leaves -/

/-- **Sub-leaf 1 (HARD).** Jacobi inversion at the symmetric-product
level: `AJ_sym : Sym^g(X) → Jac(X)` is surjective.

**Proof sketch.** Both source and target are compact complex
manifolds of dimension `g`. The map `AJ_sym` is holomorphic
(extending the pointwise Abel–Jacobi map by symmetric-product
gluing) and proper (by compactness of `Sym^g(X)`), hence has
closed image. The image contains `0 ∈ Jac(X)` (take
`p₁ = ⋯ = p_g = p₀`) and equals an open neighbourhood of `0` by
the holomorphic implicit function theorem at a generic non-special
divisor (Jacobi's original argument). A closed open subset of the
connected manifold `Jac(X)` is the whole space.

Mathlib hooks: complex implicit function theorem
(`HasFDerivAt.localHomeomorph`), properness of compact-domain
holomorphic maps, connectedness of complex tori (sec04
`prop:complex-torus-package`). The full chain is currently absent
at the production level; this leaf records the conclusion. -/
theorem aj_sym_surjective (g : Nat) (X : Type) (_hg : g ≥ 1) :
    Function.Surjective (aj_sym g X) := by
  sorry

/-- **Sub-leaf 2 (MEDIUM, retarget).** Surjectivity of the
descended `aj_Pic0 : Pic⁰(X) → Jac(X)` via Jacobi inversion.

**Proof sketch.** Given `z ∈ Jac(X)`, leaf 1 produces
`s ∈ Sym^g(X)` with `aj_sym g X s = z`. The class
`symToPic0 g X s ∈ Pic⁰(X)` then satisfies
`aj_Pic0 X (symToPic0 g X s) = z` by the compatibility
`aj_Pic0 ∘ symToPic0 = aj_sym` (which itself is the defining
factorization of `aj_Pic0` through the natural `Sym^g → Pic⁰`
map). The compatibility step is left as a `sorry` because the
placeholder defs in `Pic0.lean` and this file do not yet record
the factorization equation — that equation will become a
`rfl`/`simp` lemma once the production decls land. -/
theorem aj_Pic0_surjective_via_jacobi_inversion
    (g : Nat) (X : Type) (_hg : g ≥ 1) :
    Function.Surjective (Pic0.aj_Pic0 X) := by
  sorry

end JacobiInversion
end AbelExistence
end JacobianChallenge.Blueprint
