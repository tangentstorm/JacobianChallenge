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
deep content moves into the existence axiom
`riemann_roch_umbrella_exists`, which is `sorry`-bearing pending the
analytic frontier (line-bundle theory, sheaf cohomology, Serre
duality nondegeneracy). -/

namespace JacobianChallenge.Blueprint

universe u

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
structure RiemannRochUmbrella (X : Type u) [TopologicalSpace X] [CompactSpace X] where
  /-- Type of line bundles on `X`. -/
  LineBundleType : Type (max 1 u)
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
    {X : Type u} [TopologicalSpace X] [CompactSpace X]
    (h : RiemannRochUmbrella X) (L : h.LineBundleType) :
    (h.h0 L : ℤ) - (h.h0 (h.sub h.canonical L) : ℤ)
      = h.degree L + 1 - h.genus :=
  h.riemann_roch L

/-! ## Sorry-free algebraic API around the umbrella identity

These lemmas are intentionally elementary rewrites of
`input_riemann_roch`; they provide a stable interface for downstream
blueprint nodes that want one side isolated (e.g. lower bounds, genus
recovery, or canonical-subtraction rearrangements) without repeatedly
re-proving integer arithmetic manipulations. -/

theorem input_riemann_roch_add_h0_sub
    {X : Type u} [TopologicalSpace X] [CompactSpace X]
    (h : RiemannRochUmbrella X) (L : h.LineBundleType) :
    (h.h0 L : ℤ) =
      h.degree L + 1 - h.genus + (h.h0 (h.sub h.canonical L) : ℤ) := by
  have hrr := input_riemann_roch h L
  linarith

theorem input_riemann_roch_add_genus
    {X : Type u} [TopologicalSpace X] [CompactSpace X]
    (h : RiemannRochUmbrella X) (L : h.LineBundleType) :
    (h.h0 L : ℤ) + h.genus =
      h.degree L + 1 + (h.h0 (h.sub h.canonical L) : ℤ) := by
  have hrr := input_riemann_roch h L
  linarith

theorem input_riemann_roch_sub_eq
    {X : Type u} [TopologicalSpace X] [CompactSpace X]
    (h : RiemannRochUmbrella X) (L : h.LineBundleType) :
    (h.h0 L : ℤ) - (h.degree L + 1 - h.genus) =
      (h.h0 (h.sub h.canonical L) : ℤ) := by
  have hrr := input_riemann_roch h L
  linarith

theorem input_riemann_roch_sub_eq'
    {X : Type u} [TopologicalSpace X] [CompactSpace X]
    (h : RiemannRochUmbrella X) (L : h.LineBundleType) :
    (h.h0 (h.sub h.canonical L) : ℤ) =
      (h.h0 L : ℤ) - (h.degree L + 1 - h.genus) := by
  symm
  exact input_riemann_roch_sub_eq h L

theorem input_riemann_roch_genus_solved
    {X : Type u} [TopologicalSpace X] [CompactSpace X]
    (h : RiemannRochUmbrella X) (L : h.LineBundleType) :
    h.genus = h.degree L + 1 - (h.h0 L : ℤ) + (h.h0 (h.sub h.canonical L) : ℤ) := by
  have hrr := input_riemann_roch h L
  linarith

theorem input_riemann_roch_degree_solved
    {X : Type u} [TopologicalSpace X] [CompactSpace X]
    (h : RiemannRochUmbrella X) (L : h.LineBundleType) :
    h.degree L = (h.h0 L : ℤ) - (h.h0 (h.sub h.canonical L) : ℤ) - 1 + h.genus := by
  have hrr := input_riemann_roch h L
  linarith

theorem input_riemann_roch_lower_bound
    {X : Type u} [TopologicalSpace X] [CompactSpace X]
    (h : RiemannRochUmbrella X) (L : h.LineBundleType) :
    h.degree L + 1 - h.genus ≤ (h.h0 L : ℤ) := by
  have hsub_nonneg : (0 : ℤ) ≤ (h.h0 (h.sub h.canonical L) : ℤ) := by
    exact Int.natCast_nonneg (h.h0 (h.sub h.canonical L))
  have hrr := input_riemann_roch_add_h0_sub h L
  linarith

theorem input_riemann_roch_nonneg_degree_bound
    {X : Type u} [TopologicalSpace X] [CompactSpace X]
    (h : RiemannRochUmbrella X) (L : h.LineBundleType)
    (hvanish : h.h0 (h.sub h.canonical L) = 0) :
    (h.h0 L : ℤ) = h.degree L + 1 - h.genus := by
  have hrr := input_riemann_roch h L
  simp [hvanish] at hrr
  exact hrr

theorem input_riemann_roch_canonical_sub_nonneg
    {X : Type u} [TopologicalSpace X] [CompactSpace X]
    (h : RiemannRochUmbrella X) (L : h.LineBundleType) :
    (h.h0 (h.sub h.canonical L) : ℤ) ≤ (h.h0 L : ℤ) - (h.degree L + 1 - h.genus) := by
  have hEq := input_riemann_roch_sub_eq h L
  linarith

theorem input_riemann_roch_h0_nonneg
    {X : Type u} [TopologicalSpace X] [CompactSpace X]
    (h : RiemannRochUmbrella X) (L : h.LineBundleType) :
    (0 : ℤ) ≤ (h.h0 L : ℤ) := by
  exact Int.natCast_nonneg (h.h0 L)

theorem input_riemann_roch_h0_sub_nonneg
    {X : Type u} [TopologicalSpace X] [CompactSpace X]
    (h : RiemannRochUmbrella X) (L : h.LineBundleType) :
    (0 : ℤ) ≤ (h.h0 (h.sub h.canonical L) : ℤ) := by
  exact Int.natCast_nonneg (h.h0 (h.sub h.canonical L))

theorem input_riemann_roch_bound_by_h0
    {X : Type u} [TopologicalSpace X] [CompactSpace X]
    (h : RiemannRochUmbrella X) (L : h.LineBundleType) :
    h.degree L + 1 - h.genus ≤ (h.h0 L : ℤ) := by
  exact input_riemann_roch_lower_bound h L

theorem input_riemann_roch_eq_zero_of_h0_eq_zero
    {X : Type u} [TopologicalSpace X] [CompactSpace X]
    (h : RiemannRochUmbrella X) (L : h.LineBundleType)
    (h0L : h.h0 L = 0) :
    (h.h0 (h.sub h.canonical L) : ℤ) = -(h.degree L + 1 - h.genus) := by
  have hrr := input_riemann_roch h L
  simp [h0L] at hrr
  linarith

theorem input_riemann_roch_eq_zero_of_h0_sub_eq_zero
    {X : Type u} [TopologicalSpace X] [CompactSpace X]
    (h : RiemannRochUmbrella X) (L : h.LineBundleType)
    (h0Sub : h.h0 (h.sub h.canonical L) = 0) :
    (h.h0 L : ℤ) = h.degree L + 1 - h.genus := by
  exact input_riemann_roch_nonneg_degree_bound h L h0Sub

theorem input_riemann_roch_compare_two
    {X : Type u} [TopologicalSpace X] [CompactSpace X]
    (h : RiemannRochUmbrella X) (L₁ L₂ : h.LineBundleType)
    (hdeg : h.degree L₁ = h.degree L₂)
    (hsub : h.h0 (h.sub h.canonical L₁) = h.h0 (h.sub h.canonical L₂)) :
    h.h0 L₁ = h.h0 L₂ := by
  have h1 := input_riemann_roch_add_h0_sub h L₁
  have h2 := input_riemann_roch_add_h0_sub h L₂
  have h1' : (h.h0 L₁ : ℤ) = h.degree L₂ + 1 - h.genus + (h.h0 (h.sub h.canonical L₂) : ℤ) := by
    simpa [hdeg, hsub] using h1
  have h2' : (h.h0 L₂ : ℤ) = h.degree L₂ + 1 - h.genus + (h.h0 (h.sub h.canonical L₂) : ℤ) := h2
  have : (h.h0 L₁ : ℤ) = (h.h0 L₂ : ℤ) := by linarith [h1', h2']
  exact Int.ofNat.inj this

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
theorem riemann_roch_umbrella_exists
    (X : Type u) [TopologicalSpace X] [CompactSpace X] [T2Space X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X]
    [CategoryTheory.HasSheafify (Opens.grothendieckTopology (TopCat.of X)) AddCommGrpCat.{0}]
    [CategoryTheory.HasExt.{0}
      (CategoryTheory.Sheaf (Opens.grothendieckTopology (TopCat.of X)) AddCommGrpCat.{0})]
    (hmod0 : ∀ L : HolomorphicForms.RSLineBundleSheaf X,
      Module ℂ (HolomorphicForms.RSSheafCohomology X L 0))
    (hmod1 : ∀ L : HolomorphicForms.RSLineBundleSheaf X,
      Module ℂ (HolomorphicForms.RSSheafCohomology X L 1)) :
    Nonempty (RiemannRochUmbrella X) := by
  refine ⟨{
    LineBundleType := HolomorphicForms.RSLineBundleSheaf X
    canonical := HolomorphicForms.RSDualizingSheaf X
    sub := HolomorphicForms.RSLineBundleSub X
    degree := HolomorphicForms.RSLineBundleDegree X
    h0 := fun L => by
      letI := hmod0 L
      exact Module.finrank ℂ (HolomorphicForms.RSSheafCohomology X L 0)
    genus := (HolomorphicForms.RSGenus X : ℤ)
    riemann_roch := ?_
  }⟩
  intro L
  letI := hmod0 L
  letI := hmod1 L
  letI := hmod0 (HolomorphicForms.RSLineBundleSub X (HolomorphicForms.RSDualizingSheaf X) L)
  simpa using HolomorphicForms.riemann_roch_classical_identity X L


end JacobianChallenge.Blueprint
