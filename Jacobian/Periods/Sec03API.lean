import Jacobian.HolomorphicForms.Defs
import Mathlib.Analysis.Complex.Basic
import Mathlib.Geometry.Manifold.IsManifold.Basic

/-!
# Sec 03 API: abstract algebra layer

Packet 1 of the sec03 (Periods + Riemann bilinear) refinement: the
abstract API surface that downstream packets
(`RiemannBilinearIdentity.lean`, `PeriodRank.lean`) refer to.

Definitions only. No theorems, no `sorry`. Bodies of the analytic
operations are deliberately `opaque` — concrete realisations belong
to Packets 2 and 3 once Stokes-on-RS and the wedge / Hodge-star API
land.

## Adaptation note: `H1Z`

The ChatGPT design references an `H1Z X` type for integral
1-homology. Two routes exist in the project:

* (A) Introduce `opaque H1Z X : Type` as a stand-in. Cleanest match
  to the design; production swap-out (to either `IntegralOneCycle X`
  in `Jacobian.Periods.IntegralOneCycle` or a path-class abstraction
  via `Jacobian.Periods.PeriodSubgroupApi`) happens in a later
  packet.
* (B) Use `IntegralOneCycle X : ModuleCat ℤ` directly. Functional but
  pulls in a `ModuleCat`-coercion detour at every call site that
  Packet 2/3 don't yet need.

We pick (A) here. Both downstream packets type-check against
`H1Z X` without committing to an implementation; the eventual swap
to `IntegralOneCycle X` is a one-line change in this file.
-/

namespace JacobianChallenge.Periods

open scoped Manifold
open JacobianChallenge.HolomorphicForms

/-- Opaque stand-in for `H₁(X, ℤ)`. To be replaced by the project's
`IntegralOneCycle X` once Packet 2 / 3 are wired up. -/
opaque H1Z (X : Type) [TopologicalSpace X] : Type

/-- A symplectic basis of `H₁(X, ℤ)` for a compact connected Riemann
surface of genus `g`: two `g`-tuples of integral 1-cycles `a`, `b`
that together form a basis with the standard intersection matrix
`a_i ⌣ a_j = b_i ⌣ b_j = 0` and `a_i ⌣ b_j = δ_{ij}`.

The `basis_complete` and `intersection_standard` fields are
placeholders (`Prop := True` defaults) so downstream packets can
reference the structure without committing to the homology /
intersection-pairing API. Concrete contents are filled in Packet 2 /
3 once `intersectionPairing : H1Z X → H1Z X → ℤ` is in place. -/
structure SymplecticBasis (X : Type) [TopologicalSpace X] (g : ℕ) where
  /-- The "α" half of the basis. -/
  a : Fin g → H1Z X
  /-- The "β" half of the basis. -/
  b : Fin g → H1Z X
  /-- Placeholder: `{a₁, …, a_g, b₁, …, b_g}` is a ℤ-basis of
  `H₁(X, ℤ)`. Concrete realisation deferred. -/
  basis_complete : Prop := True
  /-- Placeholder: the intersection matrix is the standard
  symplectic form. Concrete realisation deferred. -/
  intersection_standard : Prop := True

/-- Opaque wedge integral `∫_X ω ∧ η` of two holomorphic 1-forms.
For 1-forms on a 2-real-dimensional manifold this lands in `ℂ`
(after orienting). Concrete realisation deferred to Packet 2 (needs
the wedge-product + integration-of-2-forms API). -/
opaque wedgeIntegral
    (X : Type) [TopologicalSpace X] [CompactSpace X] [T2Space X]
    [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X]
    (_ω _η : HolomorphicOneForm ℂ X) : ℂ

/-- Opaque Hermitian pairing `⟨ω, η⟩ := i ∫_X ω ∧ conj η`. The factor
of `i` makes the pairing positive-definite on holomorphic 1-forms.
Concrete realisation deferred to Packet 2. -/
opaque hermitianPairing
    (X : Type) [TopologicalSpace X] [CompactSpace X] [T2Space X]
    [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X]
    (_ω _η : HolomorphicOneForm ℂ X) : ℂ

/-- Opaque period `∫_γ ω` of a holomorphic 1-form along an integral
1-cycle. Concrete realisation deferred to Packet 2 (needs the
multi-chart path integral, currently stubbed across many
`PathIntegral*.lean` files). -/
opaque period
    (X : Type) [TopologicalSpace X] [CompactSpace X] [T2Space X]
    [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X]
    (_γ : H1Z X) (_ω : HolomorphicOneForm ℂ X) : ℂ

/-- The period vector of `ω` against a symplectic basis: the
`2g`-tuple of complex numbers `(∫_{a_i} ω, ∫_{b_i} ω)`, with the `a`
periods filling the first `g` slots and the `b` periods filling the
last `g`. -/
noncomputable def periodVector
    (X : Type) [TopologicalSpace X] [CompactSpace X] [T2Space X]
    [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X]
    {g : ℕ} (sb : SymplecticBasis X g) (ω : HolomorphicOneForm ℂ X) :
    Fin (2 * g) → ℂ := fun i =>
  if h : i.val < g then
    period X (sb.a ⟨i.val, h⟩) ω
  else
    period X (sb.b ⟨i.val - g, by omega⟩) ω

end JacobianChallenge.Periods
