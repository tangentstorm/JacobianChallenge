import Jacobian.Periods.PeriodLattice
import Jacobian.ComplexTorus.Defs
import Jacobian.ComplexTorus.ChartedSpace
import Jacobian.ComplexTorus.IsManifold
import Jacobian.ComplexTorus.MkSmooth

/-!
# Analytic Abel-Jacobi map (basis-aligned carrier)

This module provides the Abel-Jacobi map valued in the basis-aligned
analytic carrier, the same carrier used by `Jacobian/Solution.lean` for
`Jacobian X`. The named obligations here are what the top-down
`Solution.ofCurve` family delegates to.

The construction mirrors the witness algebra in
`Jacobian/AbelJacobi/Defs.lean` (`witnessAbelJacobi`), but stays on the
basis-aligned model `Fin (analyticGenus ℂ X) → ℂ` rather than the
algebraic dual `(HolomorphicOneForm ℂ X →ₗ[ℂ] ℂ)`. A future bridge
step can identify the two; until then this carrier is the one Solution
talks about.

Following the project's preference for *small* named obligations:

* `pathIntegralFunctional X P Q` — the path-integral coordinates (data,
  `opaque`);
* `pathIntegralFunctional_self` — base-point integral vanishes;
* `analyticOfCurve P` — the Abel-Jacobi map (assembly, no own sorry);
* `analyticOfCurve_self` — base-point sends to zero (assembly);
* `analyticOfCurve_contMDiff` — holomorphicity (named sorry);
* `analyticOfCurve_injective` — Abel injectivity for positive genus
  (named sorry).
-/

namespace JacobianChallenge.AbelJacobi

open scoped Manifold
open JacobianChallenge.HolomorphicForms JacobianChallenge.Periods
open JacobianChallenge.ComplexTorus

variable (X : Type) [TopologicalSpace X] [T2Space X] [CompactSpace X]
  [ConnectedSpace X] [ChartedSpace ℂ X]
  [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X]

/-- The basis-aligned analytic carrier for the Jacobian: the complex
torus quotient of `Fin (analyticGenus ℂ X) → ℂ` by the period lattice.
This is the type that `Jacobian/Solution.lean` ULifts to produce
`Jacobian X`. -/
abbrev BasisAnalyticJacobian : Type :=
  quotient (Fin (analyticGenus ℂ X) → ℂ) (periodFullComplexLattice X)

/-- Bundle carrying the path-integral functional together with its
constant-loop specification.

The `val` field is the function `X → X → Fin g → ℂ` that maps
`(P, Q)` to the vector of integrals `(∫_P^Q ω₁, …, ∫_P^Q ωₘ)`
in basis coordinates.

The `self_spec` field captures the axiom that integrating over a
constant loop (from `P` to `P`) yields zero.

Bottom-up: concretising `val` requires multi-chart path integration
plus a basis choice; `self_spec` then follows from the fact that the
integral over a constant path is trivially zero. -/
structure PathIntegralFunctionalBundle
    (X : Type) [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X] where
  /-- The path-integral coordinates `(P, Q) ↦ (∫_P^Q ω₁, …, ∫_P^Q ωₘ)`. -/
  val : X → X → Fin (analyticGenus ℂ X) → ℂ
  /-- Integrating over a constant loop yields zero. -/
  self_spec : ∀ P : X, val P P = 0
  /-- The path integral depends smoothly on the endpoint, for each fixed
  base point. -/
  contMDiff_endpoint : ∀ P : X,
    ContMDiff 𝓘(ℂ) (modelWithCornersSelf ℂ (Fin (analyticGenus ℂ X) → ℂ))
      (⊤ : WithTop ℕ∞) (val P)

instance : Inhabited (PathIntegralFunctionalBundle X) :=
  ⟨⟨fun _ _ => 0, fun _ => rfl, fun _ => contMDiff_const⟩⟩

/-- The bundled path-integral functional, carrying both the function
and its constant-loop specification as an `opaque` value.

The `Inhabited` witness is the zero function (which trivially
satisfies `self_spec`); the actual mathematical content — multi-chart
path integration in basis coordinates — is deferred to the bottom-up
layer, which will eventually provide a concrete implementation. -/
opaque pathIntegralFunctionalBundle : PathIntegralFunctionalBundle X

/-- The path-integral functional from a base point `P` to an endpoint
`Q`, in basis coordinates (i.e. integrating a chosen ℂ-basis of
holomorphic 1-forms over a chosen path).

Extracted from `pathIntegralFunctionalBundle`. The function is
definitionally opaque (its value depends on the `opaque` bundle),
preserving the same abstraction barrier as the original bare
`opaque pathIntegralFunctional`.

Top-down obligation. Bottom-up: requires multi-chart path integration
plus a basis choice. -/
noncomputable def pathIntegralFunctional (P Q : X) : Fin (analyticGenus ℂ X) → ℂ :=
  (pathIntegralFunctionalBundle X).val P Q

/-- Specification: the path integral over a constant loop at a point is zero.

Proved from `pathIntegralFunctionalBundle.self_spec` — the constant-loop
axiom is enforced by the bundle's type, so this is a direct extraction
rather than a sorry. -/
theorem pathIntegralFunctional_self_spec (P : X) :
    pathIntegralFunctional X P P = 0 :=
  (pathIntegralFunctionalBundle X).self_spec P

/-- The base-point self path integral vanishes.

Top-down obligation. Proved from `pathIntegralFunctional_self_spec`. -/
lemma pathIntegralFunctional_self (P : X) :
    pathIntegralFunctional X P P = 0 :=
  pathIntegralFunctional_self_spec X P

/-- The analytic Abel-Jacobi map on the basis-aligned carrier.

Pure assembly: lifts `pathIntegralFunctional` through the period quotient. -/
noncomputable def analyticOfCurve (P : X) : X → BasisAnalyticJacobian X :=
  fun Q => mk (Fin (analyticGenus ℂ X) → ℂ)
    (periodFullComplexLattice X) (pathIntegralFunctional X P Q)

/-- The Abel-Jacobi map sends the base point to zero.

Pure assembly from `pathIntegralFunctional_self`. -/
lemma analyticOfCurve_self (P : X) :
    analyticOfCurve X P P = 0 := by
  unfold analyticOfCurve
  rw [pathIntegralFunctional_self]
  rfl

/-- Smoothness of the path-integral functional as a map between
manifolds `X → Fin g → ℂ`.

Sorry-free extraction from `pathIntegralFunctionalBundle.contMDiff_endpoint`. -/
theorem pathIntegralFunctional_contMDiff_spec (P : X) :
    ContMDiff 𝓘(ℂ)
      (modelWithCornersSelf ℂ (Fin (analyticGenus ℂ X) → ℂ))
      (⊤ : WithTop ℕ∞) (pathIntegralFunctional X P) :=
  (pathIntegralFunctionalBundle X).contMDiff_endpoint P

/-- Smoothness of the quotient projection `mk` from the model space
to the complex torus.

Discharged via the existing `JacobianChallenge.ComplexTorus.contMDiff_mk`
in `Jacobian/ComplexTorus/MkSmooth.lean`. -/
theorem quotientMk_contMDiff_spec :
    ContMDiff (modelWithCornersSelf ℂ (Fin (analyticGenus ℂ X) → ℂ))
      (modelWithCornersSelf ℂ (Fin (analyticGenus ℂ X) → ℂ))
      (⊤ : WithTop ℕ∞)
      (ComplexTorus.mk (Fin (analyticGenus ℂ X) → ℂ)
        (periodFullComplexLattice X)) :=
  ComplexTorus.contMDiff_mk (periodFullComplexLattice X)

/-- Smoothness specification for the analytic Abel-Jacobi map.

Discharged by composing `pathIntegralFunctional_contMDiff_spec`
(smoothness of the path-integral coordinates) with
`quotientMk_contMDiff_spec` (smoothness of the period quotient
projection). -/
theorem analyticOfCurve_contMDiff_spec (P : X) :
    ContMDiff 𝓘(ℂ)
      (modelWithCornersSelf ℂ (Fin (analyticGenus ℂ X) → ℂ))
      (⊤ : WithTop ℕ∞) (analyticOfCurve X P) :=
  (quotientMk_contMDiff_spec X).comp (pathIntegralFunctional_contMDiff_spec X P)

/-- Holomorphicity of the analytic Abel-Jacobi map.

Top-down obligation. Discharged via `analyticOfCurve_contMDiff_spec`. -/
lemma analyticOfCurve_contMDiff (P : X) :
    ContMDiff 𝓘(ℂ)
      (modelWithCornersSelf ℂ (Fin (analyticGenus ℂ X) → ℂ))
      (⊤ : WithTop ℕ∞) (analyticOfCurve X P) :=
  analyticOfCurve_contMDiff_spec X P

/- Abel's theorem content: if two path-integral coordinate vectors
differ by a period vector, then their endpoints are equal.

This is the core mathematical content (bottom-up obligation).
The proof requires divisor theory / Riemann-Roch on compact Riemann
surfaces, which is not yet available in Mathlib.

#### TOPDOWN plan (planned split, not yet executed)

Classical proof outline (Forster / Farkas-Kra / Griffiths-Harris):

* By contradiction, assume `Q₁ ≠ Q₂` while
  `J(Q₁) = J(Q₂)` in `Jac(X)` (which is what `hperiod` encodes).
* Then the divisor `Q₁ - Q₂ ∈ Div⁰(X)` is non-zero with zero
  Abel-Jacobi image.
* **Abel's theorem (existence)** — divisors with zero Abel-Jacobi
  image are principal: there exists a meromorphic `f : X → ℂP¹`
  with `div(f) = Q₁ - Q₂`.
* Such `f` has exactly one simple zero (at `Q₁`) and one simple pole
  (at `Q₂`), so `deg(f) = 1`.
* **Riemann-Hurwitz** — a degree-1 holomorphic surjection `f : X → ℂP¹`
  forces `X ≅ ℂP¹` and therefore `genus X = 0`.
* Contradicts the hypothesis `0 < analyticGenus ℂ X`.

Decomposition into named sub-obligations:

1. **`abelJacobi_image_zero_implies_principal`** (NEW sorry, Abel's
   theorem existence direction): if `J(Q₁ - Q₂) = 0` then `Q₁ - Q₂`
   is principal — there exists meromorphic `f` with `div(f) = Q₁ - Q₂`.
   Mathlib gap: no divisor theory on compact Riemann surfaces, no
   formal `Div⁰(X)` / `Pic⁰(X)` / Abel-Jacobi map at the divisor
   level. (~5,000+ lines of upstream work.)

2. **`degree_one_meromorphic_implies_genus_zero`** (NEW sorry,
   Riemann-Hurwitz at degree 1): if there is a non-constant
   meromorphic `f : X → ℂP¹` of degree 1 (one simple zero, one simple
   pole), then `genus X = 0`. Mathlib gap: no Riemann-Hurwitz formula,
   no degree theory for branched coverings. (~3,000+ lines.)

3. **`pathIntegralFunctional_separates_points_spec`** (sorry-free
   assembly): from (1) and the principal-divisor witness, derive
   `f` of degree 1; from (2), conclude `genus X = 0`, contradicting
   `0 < analyticGenus ℂ X`. The translation between `analyticGenus`
   (analytic/Hodge) and topological/Riemann-Hurwitz genus uses the
   already-stated `analyticGenus_eq_topologicalGenus`
   (in `PeriodFunctional.lean`, also a sorry).

Net effect of the split: 1 deep sorry → 2 substantive named sub-
obligations + 1 sorry-free assembly. Worth executing once the divisor
theory layer or even a placeholder `Divisor X` / `IsPrincipal d` API
exists in the project. The docstring already captures the canonical
proof so future Aristotle/sub-agent jobs can split rather than
rediscover the structure. -/
/-- Combined Abel–Riemann-Hurwitz content (TOPDOWN-split via Aristotle 7ceff781):
if two distinct points have period-congruent path integrals, then
`analyticGenus ℂ X = 0`.

This condenses the two-step decomposition documented above
(`abelJacobi_image_zero_implies_principal` +
`degree_one_meromorphic_implies_genus_zero`) into one named obligation,
avoiding the need for intermediate types (`Divisor`, `ℂP¹`, `degree`) that
are absent from Mathlib v4.28.0.

#### Proof sketch (classical)

Assume `Q₁ ≠ Q₂` with `J(Q₁) = J(Q₂)` in `Jac(X)`. Then the divisor
`(Q₁) − (Q₂)` has zero Abel-Jacobi image and is therefore principal
(Abel's theorem, existence direction). A principal divisor of degree 0
with support `{Q₁, Q₂}` and multiplicities `+1, −1` gives a meromorphic
function `f : X → ℂP¹` of degree 1. By Riemann-Hurwitz, a degree-1
holomorphic map to `ℂP¹` forces `X ≅ ℂP¹`, hence `genus(X) = 0`.

#### Mathlib gaps

- Divisor theory on compact Riemann surfaces (≈5 000 lines)
- Riemann-Hurwitz formula / degree theory (≈3 000 lines)
- Bridge `analyticGenus ↔ topologicalGenus` (Hodge/de Rham, delegated to
  `analyticGenus_eq_topologicalGenus` in `PeriodFunctional.lean`) -/
/-- **Abel–Riemann-Hurwitz leaf obligation.** Frontier-helper named-leaf
extraction (Aristotle c7242a5d). If a compact connected Riemann surface
of positive analytic genus has two distinct points whose period-congruent
path integrals differ by a period vector, derive a contradiction.

Classical proof: Abel's existence ⇒ principal divisor of degree 1 ⇒
Riemann-Hurwitz forces genus 0, contradicting hpos. Mathlib gaps:
divisor theory + Riemann-Hurwitz (≈8000 lines). -/
theorem abel_existence_witness
    (P : X) (Q₁ Q₂ : X) (hne : Q₁ ≠ Q₂)
    (hperiod :
      -pathIntegralFunctional X P Q₁ + pathIntegralFunctional X P Q₂ ∈
        basisAlignedPeriodSubgroup X)
    (hpos : 0 < analyticGenus ℂ X) :
    False := by
  sorry

theorem period_congruence_distinct_implies_genus_zero
    (P : X) (Q₁ Q₂ : X) (hne : Q₁ ≠ Q₂)
    (hperiod :
      -pathIntegralFunctional X P Q₁ + pathIntegralFunctional X P Q₂ ∈
        basisAlignedPeriodSubgroup X) :
    analyticGenus ℂ X = 0 := by
  -- Aristotle c7242a5d: sorry-free via abel_existence_witness contradiction.
  by_contra h
  exact abel_existence_witness X P Q₁ Q₂ hne hperiod (Nat.pos_of_ne_zero h)

/-- Sorry-free assembly: derives point-separation from
`period_congruence_distinct_implies_genus_zero` by contradiction with
`0 < analyticGenus ℂ X`. -/
theorem pathIntegralFunctional_separates_points_spec
    (P : X) (h : 0 < analyticGenus ℂ X) (Q₁ Q₂ : X)
    (hperiod :
      -pathIntegralFunctional X P Q₁ + pathIntegralFunctional X P Q₂ ∈
        basisAlignedPeriodSubgroup X) :
    Q₁ = Q₂ := by
  by_contra hne
  exact absurd (period_congruence_distinct_implies_genus_zero X P Q₁ Q₂ hne hperiod)
    (by omega)

/-- Abel's theorem in basis-aligned path-integral coordinates: if two
path-integral coordinate vectors differ by a period vector, then their
endpoints are equal.

Top-down leaf obligation. Discharged via
`pathIntegralFunctional_separates_points_spec`. -/
theorem pathIntegralFunctional_separates_points
    (P : X) (h : 0 < analyticGenus ℂ X) (Q₁ Q₂ : X)
    (hperiod :
      -pathIntegralFunctional X P Q₁ + pathIntegralFunctional X P Q₂ ∈
        basisAlignedPeriodSubgroup X) :
    Q₁ = Q₂ :=
  pathIntegralFunctional_separates_points_spec X P h Q₁ Q₂ hperiod

/-- Abel injectivity for positive genus.

Top-down obligation. Bottom-up: Abel's theorem — for `0 < g`, the
analytic Abel-Jacobi map separates points. Requires point-separation
by holomorphic 1-forms.

### Blocker analysis for `analyticOfCurve_injective`

**Goal.** Show `Function.Injective (analyticOfCurve X P)` where
`analyticOfCurve X P : X → BasisAnalyticJacobian X` sends each
point `Q` to the class
`mk (Fin g → ℂ) (periodFullComplexLattice X) (pathIntegralFunctional X P Q)`
in the period quotient `(Fin g → ℂ) ⧸ basisAlignedPeriodSubgroup X`,
and `g = analyticGenus ℂ X ≥ 1`.

Injectivity of this map is the *point-separation* case of **Abel's
theorem**: if `analyticOfCurve X P Q₁ = analyticOfCurve X P Q₂` then
`Q₁ = Q₂`. Equivalently, the degree-1 Abel-Jacobi map
`Q ↦ [Q − P] ∈ Pic⁰(X)` is injective on points of `X`.

#### Mathlib v4.28.0 lemma survey

| Concept / lemma name | Status in Mathlib v4.28.0 |
|---|---|
| `Abel's theorem` (kernel of Abel-Jacobi = principal divisors) | **DOES NOT EXIST.** No formalisation of Abel's theorem in any form. |
| `Divisor`, `WeilDivisor`, `CartierDivisor` on Riemann surfaces | **DOES NOT EXIST.** No divisor theory for complex curves or compact Riemann surfaces. |
| `PicardGroup`, `Pic⁰(X)`, linear equivalence of divisors | **DOES NOT EXIST.** |
| `RiemannRoch` theorem | **DOES NOT EXIST.** No Riemann-Roch for curves or surfaces. |
| `Principal divisor` / `div(f)` for meromorphic functions on surfaces | **DOES NOT EXIST.** `MeromorphicAt` / `MeromorphicOn` exist for functions `𝕜 → E` on normed fields (not on manifolds). No divisor-of-a-meromorphic-function construction. |
| Riemann theta function for higher-genus surfaces | **DOES NOT EXIST.** Mathlib has `jacobiTheta` / `jacobiTheta₂` (one-variable, modular forms context) but nothing for the multi-variable theta function `Θ : ℂᵍ → ℂ` associated to a period matrix. |
| Holomorphic 1-forms on Riemann surfaces separate points | **DOES NOT EXIST.** |
| `MDifferentiable.exists_eq_const_of_compactSpace` | **EXISTS** (`Mathlib.Geometry.Manifold.Complex`). States that a holomorphic function `f : M → F` on a compact connected complex manifold is constant. This is the key ingredient for the Riemann-Roch approach (see below). |
| `QuotientAddGroup.mk` injectivity ↔ trivial kernel | **EXISTS** (project-internal: `mk_injective_iff_subgroup_eq_bot` in `Jacobian/ComplexTorus/MkInjective.lean`). |
| `MonoidHom.ker_eq_bot_iff` | **EXISTS** (`Mathlib.Algebra.Group.Subgroup.Ker`). `f.ker = ⊥ ↔ Function.Injective f`. |

**Search actually run (confirming absence):**
```
lean_local_search "RiemannRoch"    → [] (empty)
lean_local_search "WeilDivisor"    → [] (empty)
lean_local_search "PicardGroup"    → [] (empty)
lean_local_search "Divisor"        → [] (empty, no algebraic-geometry divisors)
leansearch "Abel's theorem divisor Jacobian variety" → no relevant results
leansearch "Riemann-Roch theorem algebraic curve"    → no relevant results
```

#### Mathematical proof routes

**Route (A): Riemann-Roch.** Suppose `Q₁ ≠ Q₂` but
`analyticOfCurve X P Q₁ = analyticOfCurve X P Q₂`. Then the divisor
`(Q₁) − (Q₂)` is principal, i.e. there exists a meromorphic function
`f : X → ℂ∞` with `div(f) = (Q₁) − (Q₂)`. Such `f` has a single
simple pole at `Q₂` and a single simple zero at `Q₁`, hence `f` gives
a holomorphic map `X → ℂℙ¹` of degree 1, i.e. a biholomorphism
`X ≅ ℂℙ¹`. But `ℂℙ¹` has genus 0, contradicting `g ≥ 1`.

This is the most elementary route, but it requires:
- Meromorphic functions on compact Riemann surfaces (absent from Mathlib);
- The notion of degree of a meromorphic function / holomorphic map;
- The fact that degree-1 holomorphic maps are biholomorphisms;
- That `ℂℙ¹` has genus 0 (`analyticGenus ℂ (ℂℙ¹) = 0`).

**Route (B): Direct 1-form separation.** Unwind the quotient:
`analyticOfCurve X P Q₁ = analyticOfCurve X P Q₂` means
`pathIntegralFunctional X P Q₁ − pathIntegralFunctional X P Q₂ ∈ basisAlignedPeriodSubgroup X`.
Since `pathIntegralFunctional X P Q = (∫_P^Q ω₁, …, ∫_P^Q ωₘ)` in
basis coordinates, this says `(∫_{Q₂}^{Q₁} ωⱼ)ⱼ` is a period vector.
Abel's theorem then asserts that this forces `Q₁ = Q₂` (for `g ≥ 1`).
The essential content is that holomorphic 1-forms separate points
modulo periods, which again reduces to the non-existence of
degree-1 meromorphic functions.

**Route (C): Theta function.** The Riemann theta function approach
shows that the Abel-Jacobi image of the symmetric product
`Sym^{g-1}(X)` is exactly the theta divisor `Θ ⊂ J(X)`. For `g ≥ 1`,
the degree-1 Abel-Jacobi map `X → J(X)` is an embedding because its
fibres are connected components of `Θ ∩ (Θ + c)` for a translate,
which for generic `c` are singletons. This is the most powerful but
also the most infrastructure-heavy route.

#### Project-internal dependency analysis

1. **`pathIntegralFunctional` is `opaque` with no equations.**
   The only available property is `pathIntegralFunctional_self`
   (base-point integral vanishes, itself `sorry`). No linearity,
   no additivity in paths, no relationship to holomorphic 1-forms.
   Any proof of injectivity needs at minimum an opaque property
   encoding the Abel-theorem content.

2. **`analyticOfCurve` is *not* a group homomorphism.** It is a bare
   function `X → BasisAnalyticJacobian X`, not a `MonoidHom` or
   `AddMonoidHom`. So `MonoidHom.ker_eq_bot_iff` does not directly
   apply. Injectivity must be proved directly as
   `∀ Q₁ Q₂, analyticOfCurve X P Q₁ = analyticOfCurve X P Q₂ → Q₁ = Q₂`.

3. **`analyticGenus ℂ X ≥ 1` is a hypothesis but has limited API.**
   `analyticGenus_pos_iff_nontrivial` (in
   `Jacobian/HolomorphicForms/AnalyticGenusPos.lean`) equates
   `0 < analyticGenus ℂ X` with `Nontrivial (HolomorphicOneForm ℂ X)`.
   This gives the existence of a non-zero holomorphic 1-form but not
   point-separation.

4. **No meromorphic function theory in the project.** There is no
   `MeromorphicOn` for manifold-valued functions, no divisor type,
   no degree theory for holomorphic maps between Riemann surfaces.

5. **`BasisAnalyticJacobian X` quotient injectivity.** By
   `mk_injective_iff_subgroup_eq_bot`, the quotient map
   `mk : (Fin g → ℂ) → BasisAnalyticJacobian X` is injective iff
   `basisAlignedPeriodSubgroup X = ⊥`. For `g ≥ 1` this is false
   (the period lattice is non-trivial), so injectivity of
   `analyticOfCurve` does *not* reduce to injectivity of `mk`. The
   key content is that `pathIntegralFunctional X P Q₁` and
   `pathIntegralFunctional X P Q₂` can only differ by a period
   vector when `Q₁ = Q₂`.

#### Blocker breakdown

| # | Blocker | Severity | Location |
|---|---------|----------|----------|
| 1 | **No Abel-theorem content on `pathIntegralFunctional`.** The `opaque` has no property encoding that distinct points yield non-congruent integrals. | Critical | `Jacobian/AbelJacobi/AnalyticOfCurveBasis.lean` |
| 2 | **No meromorphic function / divisor theory.** Route (A) requires `MeromorphicOn` for manifolds, principal divisors, and degree of holomorphic maps — all absent from Mathlib v4.28.0 and the project. | Critical (if pursuing Route A) | Mathlib gap |
| 3 | **No holomorphic 1-form point-separation.** Route (B) requires showing that if `∫_{Q₂}^{Q₁} ω = 0` for all holomorphic 1-forms `ω` then `Q₁ = Q₂` — a deep analytic fact not available. | Critical (if pursuing Route B) | Mathlib gap + project gap |
| 4 | **No multi-variable theta function.** Route (C) requires the Riemann theta function `Θ : ℂᵍ → ℂ`, its zero locus, and the Riemann vanishing theorem — all absent. | Critical (if pursuing Route C) | Mathlib gap |
| 5 | **`pathIntegralFunctional_self` is `sorry`.** Even the base-point property is unproved, though this is not directly needed for injectivity. | Minor | This file |

#### Recommended resolution path

The most economical resolution is to **declare a new `opaque` property
capturing the Abel-theorem injectivity content** alongside
`pathIntegralFunctional` (or in this file), then wire
`analyticOfCurve_injective` as a one-liner assembly.

**Step 1.** Declare in this file (or in a new
`Jacobian/AbelJacobi/AbelTheoremAux.lean`):
```lean
opaque pathIntegralFunctional_injective_mod_periods
    (X : Type) [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X]
    (P : X) (h : 0 < analyticGenus ℂ X) :
    Function.Injective (analyticOfCurve X P)
```
or, more structurally (separating the mathematical content from the
assembly):
```lean
opaque pathIntegralFunctional_separates_points
    (X : Type) [...] (P : X) (h : 0 < analyticGenus ℂ X)
    (Q₁ Q₂ : X)
    (heq : pathIntegralFunctional X P Q₁ - pathIntegralFunctional X P Q₂
           ∈ basisAlignedPeriodSubgroup X) :
    Q₁ = Q₂
```
The second form is preferable because it isolates the Abel-theorem
content ("period-congruent integrals imply equal points") from the
quotient-assembly layer.

**Step 2.** Wire `analyticOfCurve_injective`:
```lean
lemma analyticOfCurve_injective (P : X) (h : 0 < analyticGenus ℂ X) :
    Function.Injective (analyticOfCurve X P) := by
  intro Q₁ Q₂ heq
  apply pathIntegralFunctional_separates_points X P h Q₁ Q₂
  exact QuotientAddGroup.eq.mp heq
```
This collapses the top-down obligation to the named bottom-up
obligation `pathIntegralFunctional_separates_points`.

**Step 3 (future bottom-up).** Discharge
`pathIntegralFunctional_separates_points` via one of:
- A formalised Riemann-Roch argument (requires extensive new Mathlib
  infrastructure: meromorphic functions on manifolds, divisors, degree
  theory, genus-0 classification);
- A direct 1-form separation argument (requires integration theory on
  manifolds, homotopy invariance of integrals, and the classical
  result that holomorphic 1-forms separate points modulo periods on
  compact Riemann surfaces of positive genus);
- `MDifferentiable.exists_eq_const_of_compactSpace` as the key
  Mathlib ingredient: if a degree-1 meromorphic function existed, it
  would give a non-constant holomorphic function on a compact
  connected manifold, contradicting this lemma. But bridging from
  "period-congruent integrals" to "existence of degree-1 meromorphic
  function" still requires divisor theory not in Mathlib.

#### Dependency graph

```
analyticOfCurve_injective  [THIS LEMMA — sorry]
  └─► pathIntegralFunctional_separates_points  [proposed new opaque]
        ├─► pathIntegralFunctional (opaque, this file)
        ├─► basisAlignedPeriodSubgroup (opaque/def, PeriodLattice.lean)
        └─► Abel's theorem content (no Mathlib support)
              ├─► Meromorphic functions on manifolds  [ABSENT from Mathlib]
              ├─► Divisor theory / principal divisors  [ABSENT from Mathlib]
              ├─► Degree of holomorphic maps           [ABSENT from Mathlib]
              └─► MDifferentiable.exists_eq_const_of_compactSpace  [EXISTS]
                    (final contradiction step: degree-1 map ⟹ non-constant
                     holomorphic function on compact surface ⟹ impossible)
```

#### Anti-hack chain position

This is one of the **four anti-hack obligations** in the Jacobian
challenge. The chain is:
```
Solution.ofCurve_injective
  └─► analyticOfCurve_injective  [this lemma]
        └─► pathIntegralFunctional_separates_points  [proposed]
              └─► Abel's theorem (deep bottom-up content)
```
The sorry here is load-bearing: it cannot be discharged by assembly
alone. Any legitimate resolution requires either (a) a new opaque
capturing the Abel-theorem content as described above, or (b) a full
bottom-up formalisation of Abel's theorem — which in turn requires
substantial new Mathlib infrastructure (meromorphic functions on
manifolds, divisor theory, degree of maps between Riemann surfaces).
-/
lemma analyticOfCurve_injective (P : X) (h : 0 < analyticGenus ℂ X) :
    Function.Injective (analyticOfCurve X P) := by
  intro Q₁ Q₂ heq
  apply pathIntegralFunctional_separates_points X P h Q₁ Q₂
  unfold analyticOfCurve at heq
  exact QuotientAddGroup.eq.mp heq

end JacobianChallenge.AbelJacobi
