import Jacobian.Periods.PeriodLattice
import Jacobian.ComplexTorus.Defs
import Jacobian.ComplexTorus.ChartedSpace
import Jacobian.ComplexTorus.IsManifold

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

/-- The path-integral functional from a base point `P` to an endpoint
`Q`, in basis coordinates (i.e. integrating a chosen ℂ-basis of
holomorphic 1-forms over a chosen path).

Top-down obligation. Bottom-up: requires multi-chart path integration
plus a basis choice. -/
opaque pathIntegralFunctional (P Q : X) : Fin (analyticGenus ℂ X) → ℂ

/-- Specification: the path integral over a constant loop at a point is zero.

Bottom-up obligation — requires multi-chart path-integration machinery. -/
theorem pathIntegralFunctional_self_spec (P : X) :
    pathIntegralFunctional X P P = 0 := sorry

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

/-- Smoothness specification for the analytic Abel-Jacobi map.

Bottom-up obligation: requires holomorphicity of path integrals
(`pathIntegralFunctional`) together with smoothness of the period
quotient projection `mk`. Neither ingredient is available in
Mathlib v4.28.0 (no `QuotientAddGroup.contMDiff_mk`, no manifold
path-integration theory), so this is recorded as a named sorry. -/
theorem analyticOfCurve_contMDiff_spec (P : X) :
    ContMDiff 𝓘(ℂ)
      (modelWithCornersSelf ℂ (Fin (analyticGenus ℂ X) → ℂ))
      (⊤ : WithTop ℕ∞) (analyticOfCurve X P) := sorry

/-- Holomorphicity of the analytic Abel-Jacobi map.

Top-down obligation. Discharged via `analyticOfCurve_contMDiff_spec`. -/
lemma analyticOfCurve_contMDiff (P : X) :
    ContMDiff 𝓘(ℂ)
      (modelWithCornersSelf ℂ (Fin (analyticGenus ℂ X) → ℂ))
      (⊤ : WithTop ℕ∞) (analyticOfCurve X P) :=
  analyticOfCurve_contMDiff_spec X P

/-- Abel's theorem content: if two path-integral coordinate vectors
differ by a period vector, then their endpoints are equal.

This is the core mathematical content (bottom-up obligation).
The proof requires divisor theory / Riemann-Roch on compact Riemann
surfaces, which is not yet available in Mathlib. -/
theorem pathIntegralFunctional_separates_points_spec
    (P : X) (h : 0 < analyticGenus ℂ X) (Q₁ Q₂ : X)
    (hperiod :
      -pathIntegralFunctional X P Q₁ + pathIntegralFunctional X P Q₂ ∈
        basisAlignedPeriodSubgroup X) :
    Q₁ = Q₂ := sorry

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
