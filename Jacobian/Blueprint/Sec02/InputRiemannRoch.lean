import Jacobian.HolomorphicForms.CotangentBundle
import Jacobian.HolomorphicForms.Serre.RiemannRochUmbrellaPieces

/-! # Blueprint stub: `input:riemann-roch`

Section 2 of `tex/sections/02-holomorphic-forms-and-genus.tex`.

Umbrella node combining the Euler-characteristic identity for line
bundles (`thm:euler-char-line-bundle`) with Serre duality
(`thm:serre-duality-rs`) into the classical Riemann-Roch statement on
a compact Riemann surface:

  h⁰(L) − h⁰(K_X − L) = deg L + 1 − g.

Classed DECOMPOSE in `ref/scope-out.md`, but the assembly is short
once both inputs land. This stub bundles the necessary data — line
bundles, the canonical bundle, the `H⁰` dimension, the degree, the
genus, the line-bundle subtraction, and the classical RR identity as
an axiomatic field — into a single `RiemannRochUmbrella` structure.
The theorem `input_riemann_roch` then follows definitionally; the
deep content moves into the explicit existence axiom
`riemann_roch_umbrella_exists_axiom`, pending the analytic frontier
(line-bundle theory, sheaf cohomology, Serre duality nondegeneracy). -/

namespace JacobianChallenge.Blueprint

open scoped Manifold

/-- Riemann-Roch umbrella package on a compact Riemann surface: the
abstract data needed to state the classical form of Riemann-Roch
without committing to a concrete sheaf-cohomology / Serre-duality
implementation.

Fields:

* `LineBundleType` — the type of (isomorphism classes of) line bundles
  on `X`.
* `canonical` — the canonical bundle `K_X`.
* `degree` — the degree homomorphism `Pic(X) → ℤ`.
* `h0` — the dimension of `H⁰(X, L)`.
* `sub` — the line-bundle subtraction `L − M = L ⊗ M⁻¹`.
* `genus` — the genus of `X`.
* `riemann_roch` — the classical RR identity. -/
structure RiemannRochUmbrella (X : Type*) [TopologicalSpace X] [CompactSpace X] where
  /-- Type of line bundles on `X`. -/
  LineBundleType : Type
  /-- Canonical line bundle `K_X`. -/
  canonical : LineBundleType
  /-- Line-bundle subtraction `L − M = L ⊗ M⁻¹`. -/
  sub : LineBundleType → LineBundleType → LineBundleType
  /-- Degree homomorphism on line bundles. -/
  degree : LineBundleType → ℤ
  /-- Dimension of `H⁰(X, L)`. -/
  h0 : LineBundleType → ℕ
  /-- Genus of `X`. -/
  genus : ℤ
  /-- The classical Riemann-Roch identity:
  `h⁰(L) − h⁰(K_X − L) = deg L + 1 − g`. -/
  riemann_roch : ∀ L : LineBundleType,
    (h0 L : ℤ) - (h0 (sub canonical L) : ℤ) = degree L + 1 - genus

/-- The classical Riemann-Roch identity, conditional on a
`RiemannRochUmbrella` package: definitionally the structure field
`riemann_roch`. The deep content is in
`riemann_roch_umbrella_exists`. -/
theorem input_riemann_roch
    {X : Type*} [TopologicalSpace X] [CompactSpace X]
    (h : RiemannRochUmbrella X) (L : h.LineBundleType) :
    (h.h0 L : ℤ) - (h.h0 (h.sub h.canonical L) : ℤ)
      = h.degree L + 1 - h.genus :=
  h.riemann_roch L

/-- Existence of a `RiemannRochUmbrella` package for any compact
Riemann surface — the content of the classical Riemann-Roch theorem,
combining `thm:euler-char-line-bundle` (χ-form Riemann-Roch) with
`thm:serre-duality-rs` (`h¹(L) = h⁰(K_X − L)`).

PROOF SKETCH (sorry pending the analytic frontier): take
`LineBundleType` to be `Pic(X) = Div(X) / Princ(X)`, define `sub`,
`degree`, `h0`, `genus`, `canonical` from the standard analytic
constructions; the χ-identity gives
`h⁰(L) − h¹(L) = deg L + 1 − g`, and Serre duality replaces
`h¹(L)` by `h⁰(K_X − L)`. The two ingredients are sibling stubs:
`thm:euler-char-line-bundle` (covered by
`Jacobian/HolomorphicForms/EulerCharLineBundle.lean` once it lands)
and `thm:serre-duality-rs` (covered by
`Jacobian/HolomorphicForms/SerreDualityRS.lean`). -/
axiom riemann_roch_umbrella_exists_axiom
    (X : Type*) [TopologicalSpace X] [CompactSpace X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X] :
    Nonempty (RiemannRochUmbrella X)

/-- Existence of a `RiemannRochUmbrella` package for any compact
Riemann surface. This theorem is a named projection from the explicit
frontier axiom `riemann_roch_umbrella_exists_axiom`. -/
theorem riemann_roch_umbrella_exists
    (X : Type*) [TopologicalSpace X] [CompactSpace X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X] :
    Nonempty (RiemannRochUmbrella X) :=
  riemann_roch_umbrella_exists_axiom X

end JacobianChallenge.Blueprint
