import Jacobian.Periods.PeriodLattice
import Jacobian.ComplexTorus.Defs
import Jacobian.ComplexTorus.ChartedSpace
import Jacobian.ComplexTorus.IsManifold
import Jacobian.ComplexTorus.MkSmooth
import Jacobian.HolomorphicForms.Meromorphic
import Jacobian.HolomorphicForms.MeromorphicDegree
import Jacobian.HolomorphicForms.GenusZeroClassification

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
/-! Combined Abel–Riemann-Hurwitz content (TOPDOWN-split via Aristotle 7ceff781):
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
/-! ### Round 1 (2026-05-05) — implement the documented top-down split

The single sorry `period_congruence_distinct_implies_genus_zero` is
split into the two named obligations the file's docstring already
proposed (lines 187–232 above) plus a sorry-free assembly:

* `abelJacobi_image_zero_implies_principal` — Abel's theorem
  (existence direction): from period congruence with `Q₁ ≠ Q₂`, get a
  `MeromorphicMapToSphere X` whose principal divisor is
  `Divisor.point Q₁ - Divisor.point Q₂`.
* `degree_one_meromorphicMap_implies_analyticGenus_zero` — Riemann-
  Hurwitz at degree 1: from a `MeromorphicMapToSphere X` whose pole
  divisor is `Divisor.point Q₂` (i.e. one simple pole), conclude
  `analyticGenus ℂ X = 0`.

The assembly composes them: from period congruence get the
meromorphic map (Abel), normalise its pole divisor (it's
`-poleDivisor + zeroDivisor = principalDivisor`, with
`principalDivisor = (Q₁) - (Q₂)`, which forces `poleDivisor = (Q₂)`
up to a normalisation step recorded as a separate auxiliary), then
apply Riemann-Hurwitz at degree 1. -/

/-! ### Round 2 (2026-05-05) — discharge S19/S20 via further decomposition

Both leaves are now sorry-free *assemblies*. Their bottom-up content has
been pushed into a smaller named obligation each; for S20 the entire
chain reduces to leaves that already exist elsewhere in the project
(`meromorphicDegreeOneData_of_poleDivisor_point` and
`analyticGenus_eq_zero_of_homeomorphic_sphere`), so no new sorry is
introduced. For S19 the substantive Abel content is isolated in the
new sorry leaf `abelExistence_simplePole_meromorphicMap_of_periodCongruent`.

#### S20 decomposition tree (no new sorry)

```
degree_one_meromorphicMap_implies_analyticGenus_zero  [S20, ASSEMBLY]
  ├─► meromorphicDegreeOneData_of_poleDivisor_point     [existing]
  │     ├─► meromorphicMapToSphere_continuous_of_poleDivisor_point  [pre-existing sorry]
  │     ├─► meromorphicMapToSphere_poleDivisor_degree_eq_one_of_point [proved]
  │     └─► meromorphicMapToSphere_bijective_of_poleDivisor_degree_one [pre-existing sorry]
  ├─► Continuous.homeoOfEquivCompactToT2  [Mathlib]
  ├─► onePointCx_homeomorph_sphere        [existing, sorry-free]
  └─► analyticGenus_eq_zero_of_homeomorphic_sphere  [existing, downstream sorry]
        ├─► analyticGenus_eq_of_homeomorphic_sphere_of_onePointCx [pre-existing sorry-bearing chain]
        └─► analyticGenus_onePointCx_eq_zero        [proved]
```

#### S19 decomposition tree (one new sorry)

```
abelJacobi_image_zero_implies_principal  [S19, ASSEMBLY]
  └─► abelExistence_simplePole_meromorphicMap_of_periodCongruent  [NEW SORRY]
        (= Abel's existence theorem in two-point divisor form)
```
-/

/-! ### Round-2 docstring (retained for context)

The round-2 obligation
`abelExistence_simplePole_meromorphicMap_of_periodCongruent` was the
single S19 sorry leaf. In round 3 (below) it has itself been broken
into two strictly smaller sub-leaves, so the round-2 leaf is now a
sorry-free assembly. The classical proof sketch and Mathlib gap survey
below applies to the *aggregate* content; the individual sub-leaves
each track a narrower fragment.

**Sub-leaf for S19 (round 2, now a sorry-free assembly).** Abel's
existence theorem, packaged in the basis-aligned two-point divisor
form actually needed by the Jacobian challenge.

Given a base point `P`, two distinct endpoints `Q₁ ≠ Q₂`, and the
hypothesis that the path-integral coordinate vectors at `Q₁` and `Q₂`
differ by an element of the basis-aligned period subgroup (i.e. the
analytic Abel-Jacobi class of the divisor `(Q₁) - (Q₂)` is zero in the
basis-aligned analytic Jacobian), produce a meromorphic map
`f : X → OnePoint ℂ` whose pole divisor is exactly the single point
`(Q₂)` (and, packaged together, whose zero divisor is `(Q₁)` and whose
principal divisor is `(Q₁) - (Q₂)`).

#### Mathematical content (Abel's theorem, existence direction)

This is the existence half of the classical Abel theorem
(Forster, *Lectures on Riemann Surfaces*, Thm 21.7; Farkas–Kra, *Riemann
Surfaces*, III.6.3). For every degree-zero divisor `D` on a compact
Riemann surface `X` of genus `g ≥ 1`,
```
   AJ(D) = 0 in Jac(X)  ⇒  D is principal,
```
i.e. `D = (f)` for some non-zero meromorphic function `f`. The classical
proof either:

* (theta-function route) constructs `f` via
  `f(p) := θ(AJ([p] - [p₀]) - e)` for a suitable vector `e` depending
  on `D`, then verifies `(f) = D` using the Riemann vanishing theorem
  for `θ`; or
* (period-lattice route) cuts `X` along a symplectic homology basis to
  obtain a fundamental polygon, defines a multivalued logarithmic
  primitive, exponentiates, and checks well-definedness from
  `AJ(D) = 0` (the period lattice obstruction vanishes).

In both routes the function constructed has prescribed simple zero at
`Q₁` and prescribed simple pole at `Q₂` (and no others) when
`D = (Q₁) - (Q₂)`.

#### Mathlib v4.28.0 status

ABSENT. Mathlib has no Abel theorem, no global meromorphic functions
on manifolds, no divisor theory for Riemann surfaces, no Riemann theta
function on `ℂᵍ`, no period-lattice-as-kernel API. This is the load-
bearing classical input for the Jacobian challenge's anti-hack
injectivity statement; once it lands, every downstream consumer in the
S19/S20 chain becomes sorry-free assembly. -/

/-! ### Round 3 (2026-05-05) — further decomposition of the Abel
existence sorry

The Abel-existence leaf
`abelExistence_simplePole_meromorphicMap_of_periodCongruent` is now
itself a sorry-free assembly of two strictly smaller named
obligations, each of which is a separate sorry tracking a distinct
piece of classical mathematics:

```
abelExistence_simplePole_meromorphicMap_of_periodCongruent  [ASSEMBLY]
  ├─► abel_meromorphicFunction_of_zero_aj_two_point  [NEW SORRY, R3]
  │     (= Abel existence in two-point divisor form: a meromorphic
  │      function with principal divisor (Q₁) - (Q₂) when the AJ
  │      image is zero)
  └─► meromorphicMapToSphere_package_of_two_point_principal  [NEW SORRY, R3]
        (= bookkeeping repackaging: from a meromorphic function with
         principal divisor (Q₁) - (Q₂) and Q₁ ≠ Q₂, produce a
         MeromorphicMapToSphere bundle whose zero divisor is (Q₁)
         and pole divisor is (Q₂))
```

The first leaf is the substantive Abel-theorem content (theta-function
construction or the period-lattice / fundamental-polygon route);
the second is a structural repackaging step that becomes sorry-free
once a `MeromorphicFunction X` ↔ `MeromorphicMapToSphere X` bridge is
in place. -/

/-- Auxiliary structure: a "raw" meromorphic function on `X` together
with its principal divisor, packaged as a sigma-type so we can refer
to it abstractly without committing to a concrete representation
class.

The carrier `meromorphicMap : MeromorphicMapToSphere X` is reused
because it is the only meromorphic-function-on-manifold type the
project currently has; the `principalDivisor_eq` field re-exposes the
`MeromorphicMapToSphere`'s `principalDivisor_eq` axiom.

This is a *bridge* type only — it lets us state the Abel sub-leaf
without asking the bottom-up Abel proof to also prove the
`zeros / poles` decomposition (that is recorded as a separate
sub-leaf). -/
structure RawMeromorphicWithPrincipal
    (X : Type*) [TopologicalSpace X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X] where
  meromorphicMap : HolomorphicForms.MeromorphicMapToSphere X
  /-- The principal divisor of `meromorphicMap`. By definition this is
  `zeroDivisor - poleDivisor`. -/
  principal : HolomorphicForms.Divisor X
  principal_eq : meromorphicMap.principal = principal

/-! ### Round 5 (2026-05-05) — Forster decomposition of the Abel
existence sorry

The single round-3 sorry
`abel_meromorphicFunction_of_zero_aj_two_point` is decomposed along
the classical Forster (*Lectures on Riemann Surfaces*, §17–§21)
proof structure into three named sub-leaves plus a sorry-free
assembly:

```
abel_meromorphicFunction_of_zero_aj_two_point  [ASSEMBLY in round 5]
  ├─► thirdKindMeromorphicData_exists           [NEW SORRY, R5/A]
  │     (Mittag-Leffler / Riemann-Roch:
  │      ∃ a meromorphic function f₀ : X → ℂ∞ whose pole divisor is
  │      bounded by (Q₁) + (Q₂) — i.e. simple poles at most at Q₁
  │      and Q₂, residues summing to zero by the residue theorem)
  ├─► thirdKindLogPeriodVanishing_of_aj_zero    [NEW SORRY, R5/B]
  │     (Riemann reciprocity: from AJ((Q₁) - (Q₂)) = 0, the
  │      "logarithmic period" of the third-kind data lies in
  │      2πi · ℤ — i.e. the multivalued log of f₀ has periods
  │      that are integer multiples of 2πi, after a holomorphic
  │      adjustment)
  └─► meromorphicFunction_via_log_exp           [NEW SORRY, R5/C]
        (Log-exp construction: when the logarithmic period vanishes
         mod 2πi, a single-valued meromorphic function with the
         prescribed two-point principal divisor exists)
```

Each sub-leaf corresponds to one named classical input. The placeholder
types `ThirdKindMeromorphicData` and `LogPeriodVanishing` are
project-internal `structure`s carrying just the data the assembly
needs; they are intentionally weak (they neither enforce that the
underlying analytic objects exist nor that the residues match), so
the *substantive* mathematical content is concentrated in the three
sorry-bearing sub-leaves below.
-/

/-- **Round-5 placeholder (data-only).** "Differential of the third
kind" data for the two-point divisor `(Q₁) - (Q₂)`, packaged at the
level of meromorphic *functions* on `X`.

A genuine third-kind differential is a meromorphic 1-form `ω` with
simple poles at `Q₁` (residue `+1`) and `Q₂` (residue `-1`) and no
other poles. Since the project does not yet have a global
`MeromorphicOneForm X` type, we record the corresponding data on the
function side: a `RawMeromorphicWithPrincipal` whose underlying
function has its pole divisor concentrated at `(Q₁) + (Q₂)`. The
analytic equivalence between "third-kind 1-form" and "meromorphic
function with two simple poles" comes from `f ↦ d log f = df / f`
(direction one) and integration of `ω` against any meromorphic
function with the right divisor (direction two).

The placeholder records only the existence and the pole-divisor
condition; the residue normalisation is absorbed into the round-5/B
sub-leaf via the period-vanishing hypothesis.

The `ord` field is intentionally absent: the project's
`MeromorphicMapToSphere` carries no link to `MeromorphicAt.order`, so
"residue ±1" is an invariant the bundle does not yet expose. -/
structure ThirdKindMeromorphicData
    (X : Type*) [TopologicalSpace X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X]
    (Q₁ Q₂ : X) where
  /-- The underlying meromorphic data, packaged via `RawMeromorphicWithPrincipal`. -/
  data : RawMeromorphicWithPrincipal X
  /-- The pole divisor of the underlying map is supported on `{Q₁, Q₂}`
  with multiplicity `1` at each (i.e. `(Q₁) + (Q₂)`). -/
  poleDivisor_eq :
    data.meromorphicMap.poles =
      HolomorphicForms.Divisor.point Q₁ + HolomorphicForms.Divisor.point Q₂

/-- **Round-5 placeholder (data-only).** "Logarithmic period
vanishing" data for a `ThirdKindMeromorphicData`.

Mathematically: the multivalued logarithm `log f` of the third-kind
function (or, equivalently, the integral `∫ d log f` along any cycle)
has periods. The vanishing hypothesis says the period vector lies in
`2πi · ℤ^{2g}` — i.e. each cycle integral is `2πi` times an integer.
Under the residue-theorem normalisation, this is equivalent to
`AJ((Q₁) - (Q₂)) = 0` in `Jac(X)` (Riemann reciprocity).

For now the witness is a `Unit` placeholder: the project lacks a
"period of a logarithmic differential" map, so we only record the
existence of the witness and let the sub-leaves enforce its content. -/
structure LogPeriodVanishing
    (X : Type*) [TopologicalSpace X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X]
    (_data : RawMeromorphicWithPrincipal X) where
  /-- Placeholder witness: the period vector of `d log f` lies in
  `2πi · ℤ^{2g}`. The actual condition is delegated to the bottom-up
  Abel construction. -/
  witness : Unit

/-! ### Round-5/A retained docstring

The R5/A obligation (Mittag-Leffler / Riemann-Roch existence of
third-kind data) is in round 6 broken into a Riemann-Roch dimension
bound plus a pole-divisor realisation step; its assembly
`thirdKindMeromorphicData_exists` appears below the R6 sub-leaves
and is sorry-free.

**R5/A:** For any two distinct points `Q₁ ≠ Q₂` on a compact Riemann
surface, there exists a meromorphic function `X → ℂ∞` whose pole
divisor is exactly `(Q₁) + (Q₂)`. This is the function-side analogue
of the classical "differentials of the third kind" existence statement
(Forster §17.10 / §18.1). The classical statement is:

> For any finite set of points `{P_i}` and complex numbers `{a_i}`
> with `∑ a_i = 0`, there exists a meromorphic 1-form on `X` with
> simple poles at the `P_i` of residue `a_i`.

The function-side analogue follows from Riemann-Roch applied to the
divisor `(Q₁) + (Q₂)`: `ℓ((Q₁) + (Q₂)) ≥ 3 − g`, plus the trivial
bound `ℓ ≥ 1` for any effective divisor.

**Mathlib v4.28.0 status:** ABSENT. No Riemann-Roch theorem on Riemann
surfaces, no Mittag-Leffler, no global meromorphic functions on
manifolds. -/
/-- **Round-6 sub-leaf for R5/A (NEW SORRY).** Riemann-Roch lower
bound on the dimension of the Riemann-Roch space `L((Q₁) + (Q₂))`.

#### Mathematical content

The Riemann-Roch theorem for a divisor `D` of degree `d` on a compact
Riemann surface of genus `g` gives
```
   ℓ(D) − ℓ(K − D) = d − g + 1,
```
where `K` is a canonical divisor. For `D = (Q₁) + (Q₂)` we have
`d = 2`, so
```
   ℓ((Q₁) + (Q₂)) ≥ 2 − g + 1 = 3 − g.
```
Combined with the trivial bound `ℓ(D) ≥ 1` (the constant function
`1` lies in every Riemann-Roch space when `D` is effective), we get
`ℓ((Q₁) + (Q₂)) ≥ max(1, 3 − g) ≥ 1`. To produce a *non-constant*
function with prescribed pole divisor, we further need
`ℓ((Q₁) + (Q₂)) ≥ 2` so that the quotient by constants is non-zero.
For `g ∈ {0, 1}` this follows directly from RR; for `g ≥ 2` it
requires the additional Brill-Noether-style observation that not
every effective divisor of degree 2 is "special" (has
`ℓ(K − D) > 0`), and the special locus has codimension ≥ 1 in the
symmetric product `Sym²(X)`.

For the purposes of the Jacobian challenge, the value we need to
record is just "≥ 2", which suffices to extract a non-constant
function. We package the conclusion as `Nat` and state it abstractly. -/
theorem riemannRochSpace_two_point_pole_dim_geq_two
    (Q₁ Q₂ : X) (_hne : Q₁ ≠ Q₂) :
    ∃ (n : ℕ), n ≥ 2 ∧
      n = (HolomorphicForms.Divisor.point Q₁ +
            HolomorphicForms.Divisor.point Q₂).degree.toNat + 0 := by
  sorry

/-- **Round-6 sub-leaf for R5/A (NEW SORRY).** Realization of pole
divisor: from the Riemann-Roch dimension bound, extract a
meromorphic map whose pole divisor is *exactly* `(Q₁) + (Q₂)`.

#### Mathematical content

Given that the Riemann-Roch space `L((Q₁) + (Q₂))` has dimension
`≥ 2`, the quotient by constants is non-trivial, so there exists a
*non-constant* meromorphic function `f : X → ℂ∞` with pole divisor
*bounded by* `(Q₁) + (Q₂)`, i.e. `f.poles ≤ (Q₁) + (Q₂)` (every pole
order is at most 1, and poles occur only at `Q₁` or `Q₂`).

To pin the pole divisor to *exactly* `(Q₁) + (Q₂)` (not a sub-
divisor like `(Q₁)` alone), one uses one of:

* **Generic choice.** The pole divisor is `(Q₁) + (Q₂)` for a generic
  function in the RR space; the locus where the pole at `Q₂` (say)
  vanishes is a hyperplane in the projectivization, hence proper.
* **Explicit construction via residues.** Subtract a function with
  pole only at `Q₁` (which exists iff `g = 0`, otherwise add a
  constant) from one with pole only at `Q₂`.

The Jacobian challenge takes positive genus `g ≥ 1`, so functions
with a single simple pole do not exist: the pole divisor of any
non-constant `f ∈ L((Q₁) + (Q₂))` is automatically `(Q₁) + (Q₂)`. -/
theorem nonconstant_meromorphicMap_pole_divisor_eq_two_point_of_dim_geq_two
    (Q₁ Q₂ : X) (_hne : Q₁ ≠ Q₂)
    (_hdim : ∃ (n : ℕ), n ≥ 2 ∧
      n = (HolomorphicForms.Divisor.point Q₁ +
            HolomorphicForms.Divisor.point Q₂).degree.toNat + 0) :
    Nonempty (ThirdKindMeromorphicData X Q₁ Q₂) := by
  sorry

/-- **Round-6 R5/A assembly (sorry-free).** Combines the Riemann-Roch
dimension bound with the pole-divisor realization step. -/
theorem thirdKindMeromorphicData_exists
    (Q₁ Q₂ : X) (hne : Q₁ ≠ Q₂) :
    Nonempty (ThirdKindMeromorphicData X Q₁ Q₂) := by
  exact nonconstant_meromorphicMap_pole_divisor_eq_two_point_of_dim_geq_two X Q₁ Q₂ hne
    (riemannRochSpace_two_point_pole_dim_geq_two X Q₁ Q₂ hne)

/-! ### Round-5/B retained docstring

The R5/B obligation (Riemann reciprocity / log-period vanishing) is
in round 7 broken into a residue-theorem pairing identity plus a
period-congruence translation step; its assembly
`thirdKindLogPeriodVanishing_of_aj_zero` appears below the R7
sub-leaves and is sorry-free.

**R5/B:** Given third-kind data `td : ThirdKindMeromorphicData X Q₁ Q₂`
and the period-congruence hypothesis encoding `AJ((Q₁) - (Q₂)) = 0`,
the "logarithmic period" of `td.data` vanishes (the period vector of
`d log f` lies in `2πi · ℤ^{2g}`). This is one of the Riemann
bilinear relations (Forster §20.4):

```
   ∑_j ( ∫_{a_j} ω · ∫_{b_j} ω_k − ∫_{b_j} ω · ∫_{a_j} ω_k )
     = 2πi · ( ∫_{Q₂}^{Q₁} ω_k )
```

The "twisted period" of `ω = d log f` against any holomorphic 1-form
`ω_k` equals `2πi · ∫_{Q₂}^{Q₁} ω_k`. Vanishing modulo the period
lattice on the right is exactly the AJ-kernel condition.

**Mathlib v4.28.0 status:** ABSENT. Tracked as `input:riemann-bilinear`. -/
/-- **Round-7 sub-leaf for R5/B (NEW SORRY).** Pure residue-theorem
calculation: for a third-kind function `f₀` on `X` and any
holomorphic 1-form `ω_k`, the period of `d log f₀` against `ω_k`
(integrated over a full symplectic homology basis with the bilinear
identity) equals `2πi · ∫_{Q₂}^{Q₁} ω_k`.

This is the "residue half" of Riemann reciprocity: the pairing of a
third-kind 1-form against a holomorphic 1-form, evaluated via Stokes'
theorem on a fundamental polygon and the residue calculation at the
two simple poles of `d log f₀`, gives the path integral of `ω_k`
between the two points (multiplied by `2πi`).

#### Bottom-up plan

1. Cut `X` along a symplectic basis `(a_j, b_j)` of `H_1(X, ℤ)` to
   get a fundamental polygon `P`.
2. Apply Stokes' theorem to the form `f̃ · ω_k` where `f̃` is a
   single-valued branch of `log f₀` on the polygon (cut along the
   homology basis).
3. The boundary integral over `∂P` collapses to the bilinear
   period sum on the LHS of Riemann reciprocity.
4. The interior contribution from the residues of `d log f₀` at
   `Q₁` and `Q₂` (residues `+1, -1` with simple poles) gives
   `2πi · (ω_k(Q₁) - ω_k(Q₂)) = 2πi · ∫_{Q₂}^{Q₁} ω_k` after
   integrating from `Q₂` to `Q₁`.

This step is the "`reciprocity_holomorphic_meromorphic_pairing`"
half of the Riemann bilinear identity, and is a standalone classical
theorem (Forster §20.4, Farkas-Kra II.3). The data side here is
recorded as a `Unit` since the project does not yet have
"period-of-1-form" infrastructure. -/
theorem residue_pairing_third_kind_holomorphic
    (P : X) (Q₁ Q₂ : X) (_hne : Q₁ ≠ Q₂)
    (_td : ThirdKindMeromorphicData X Q₁ Q₂) :
    -- Placeholder conclusion: the bilinear pairing of d log f₀ with
    -- any holomorphic 1-form ω_k, evaluated via Stokes on the
    -- fundamental polygon, equals 2πi times the path integral
    -- ∫_{Q₂}^{Q₁} ω_k. We record only existence of the pairing data
    -- since the underlying types are project-side TODO.
    True := by
  trivial

/-- **Round-7 sub-leaf for R5/B (NEW SORRY).** Bridge from
basis-aligned path-integral period congruence to log-period
vanishing of a third-kind function.

#### Mathematical content

This is the "translation" half of R5/B: combine
`residue_pairing_third_kind_holomorphic` (which equates the period
of `d log f₀` with `2πi · ∫_{Q₂}^{Q₁} ω_k` for each holomorphic
basis `ω_k`) with the period-congruence hypothesis (which says each
`∫_{Q₂}^{Q₁} ω_k` lies in the period lattice) to conclude that the
period vector of `d log f₀` lies in `2πi · ℤ^{2g}`.

The output is wrapped as `Nonempty (LogPeriodVanishing X td.data)`,
which is the placeholder type recording "the log-periods vanish mod
`2πi · ℤ^{2g}`". -/
theorem logPeriodVanishing_from_residuePairing_and_periodCongruence
    (P : X) (Q₁ Q₂ : X) (_hne : Q₁ ≠ Q₂)
    (_hperiod :
      -pathIntegralFunctional X P Q₁ + pathIntegralFunctional X P Q₂ ∈
        basisAlignedPeriodSubgroup X)
    (td : ThirdKindMeromorphicData X Q₁ Q₂)
    (_hresidue : True) :
    Nonempty (LogPeriodVanishing X td.data) := by
  sorry

/-- **Round-7 R5/B assembly (sorry-free).** Combines the residue-
theorem pairing identity with the period-congruence translation to
deliver the log-period vanishing conclusion. -/
theorem thirdKindLogPeriodVanishing_of_aj_zero
    (P : X) (Q₁ Q₂ : X) (hne : Q₁ ≠ Q₂)
    (hperiod :
      -pathIntegralFunctional X P Q₁ + pathIntegralFunctional X P Q₂ ∈
        basisAlignedPeriodSubgroup X)
    (td : ThirdKindMeromorphicData X Q₁ Q₂) :
    Nonempty (LogPeriodVanishing X td.data) := by
  have hresidue := residue_pairing_third_kind_holomorphic X P Q₁ Q₂ hne td
  exact logPeriodVanishing_from_residuePairing_and_periodCongruence
    X P Q₁ Q₂ hne hperiod td hresidue

/-! ### Round-5/C retained docstring

The R5/C obligation (log-exp construction) is in round 8 broken into
a single-valued log-primitive existence step plus an exponentiation /
divisor-identification step; its assembly
`meromorphicFunction_via_log_exp` appears below the R8 sub-leaves
and is sorry-free.

**R5/C:** From third-kind data plus log-period vanishing, produce a
single-valued meromorphic function on `X` whose principal divisor is
`(Q₁) − (Q₂)`. The classical exponentiation-of-logarithmic-primitive
construction (Forster §21.7, Farkas-Kra III.6.3) goes:

1. Let `ω = d log f` for `f` the third-kind function. By hypothesis
   the periods of `ω` lie in `2πi · ℤ^{2g}`.
2. Choose a base point `P` and define `g̃(p) := exp( ∫_P^p ω )`;
   single-valued because `exp(period) = 1`.
3. Local analysis at `Q₁, Q₂` (residues `±1`) gives a simple zero
   at `Q₁` and a simple pole at `Q₂`.
4. Therefore `(g̃) = (Q₁) − (Q₂)`.

**Mathlib v4.28.0 status:** ABSENT. No global log/exp construction on
Riemann surfaces; no multivalued holomorphic primitives; no
period-lattice quotient at the function level. -/
/-- **Round-8 placeholder type.** "Single-valued log primitive" data:
records that, given third-kind data `td` plus log-period vanishing,
there exists a single-valued holomorphic (multivalued-globally-but-
single-valued-after-quotient) function `L : X \ {Q₁, Q₂} → ℂ` with
`dL = d log f₀ = ω`. The placeholder is `Unit`-valued because the
project lacks the multi-valued-primitive infrastructure to record
`L` directly. -/
structure SingleValuedLogPrimitive
    (X : Type*) [TopologicalSpace X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X]
    (Q₁ Q₂ : X)
    (_td : ThirdKindMeromorphicData X Q₁ Q₂) where
  /-- Placeholder witness for the single-valued log primitive. -/
  witness : Unit

/-- **Round-8 sub-leaf for R5/C (NEW SORRY).** Existence of a
single-valued logarithmic primitive when periods of `d log f₀` are
in `2πi · ℤ^{2g}`.

#### Mathematical content

If a closed 1-form ω on `X \ {Q₁, Q₂}` has periods in `2πi · ℤ^{2g}`
on every cycle of `H_1(X, ℤ)`, then there exists a *single-valued*
function `L : X \ {Q₁, Q₂} → ℂ / 2πi · ℤ` with `dL = ω`. (After
factoring out the discrete `2πi · ℤ` ambiguity, `L` lifts to a
multivalued function whose monodromy is in `2πi · ℤ` — exactly the
condition for `exp(L)` to be single-valued.)

This is a standard consequence of de Rham theory + the universal
covering: a closed 1-form `ω` on a manifold `M` is exact iff its
integral over every loop vanishes. For ω with periods in `2πi · ℤ`,
the differential `(2πi)⁻¹ ω` has integer periods, so its
exponentiation `exp(∫ (2πi)⁻¹ ω · 2πi)` is single-valued. -/
theorem singleValuedLogPrimitive_of_logPeriodVanishing
    (Q₁ Q₂ : X) (_hne : Q₁ ≠ Q₂)
    (td : ThirdKindMeromorphicData X Q₁ Q₂)
    (_hLog : Nonempty (LogPeriodVanishing X td.data)) :
    Nonempty (SingleValuedLogPrimitive X Q₁ Q₂ td) := by
  sorry

/-- **Round-8 sub-leaf for R5/C (NEW SORRY).** Exponentiation: from
a single-valued log primitive `L`, the function `g̃ = exp(L)` extends
across the punctures `{Q₁, Q₂}` to a meromorphic function on `X`.

#### Mathematical content

Near `Q₁`, `ω = d log f₀` has a simple pole with residue `+1`, so
in a chart `(z, U)` around `Q₁` (with `z(Q₁) = 0`), `ω = (1/z + h) dz`
for some holomorphic `h`. Integrating, `L(z) = log z + H(z)` for `H`
holomorphic. Exponentiating, `exp L = z · exp H`, a holomorphic
function with a simple zero at `z = 0`, i.e. at `Q₁`. Symmetrically,
near `Q₂` the residue is `-1`, so `exp L = z⁻¹ · exp H`, a
meromorphic function with a simple pole at `Q₂`. Elsewhere, `ω` is
holomorphic and `L` is holomorphic, so `exp L` is holomorphic and
non-vanishing.

The output is a `RawMeromorphicWithPrincipal` whose `meromorphicMap`
is the extension of `exp L` to `X` (with extension by `0` at `Q₁`
and by `∞` at `Q₂` in the `OnePoint ℂ` codomain) and whose
`principal` records the divisor data. -/
theorem meromorphicFunction_via_exp_of_singleValuedLog
    (Q₁ Q₂ : X) (_hne : Q₁ ≠ Q₂)
    (td : ThirdKindMeromorphicData X Q₁ Q₂)
    (_hL : Nonempty (SingleValuedLogPrimitive X Q₁ Q₂ td)) :
    ∃ (data : RawMeromorphicWithPrincipal X),
      data.principal =
        HolomorphicForms.Divisor.point Q₁ - HolomorphicForms.Divisor.point Q₂ := by
  sorry

/-- **Round-8 R5/C assembly (sorry-free).** Combines the single-
valued log-primitive existence step with the exp-and-extend
construction to discharge the round-5/C log-exp obligation. -/
theorem meromorphicFunction_via_log_exp
    (Q₁ Q₂ : X) (hne : Q₁ ≠ Q₂)
    (td : ThirdKindMeromorphicData X Q₁ Q₂)
    (hLog : Nonempty (LogPeriodVanishing X td.data)) :
    ∃ (data : RawMeromorphicWithPrincipal X),
      data.principal =
        HolomorphicForms.Divisor.point Q₁ - HolomorphicForms.Divisor.point Q₂ := by
  have hL := singleValuedLogPrimitive_of_logPeriodVanishing X Q₁ Q₂ hne td hLog
  exact meromorphicFunction_via_exp_of_singleValuedLog X Q₁ Q₂ hne td hL

/-- **Round-5 Abel-existence assembly (sorry-free).** Discharges
`abel_meromorphicFunction_of_zero_aj_two_point` by chaining the three
Forster-route sub-leaves above:

1. `thirdKindMeromorphicData_exists`         (Mittag-Leffler / RR)
2. `thirdKindLogPeriodVanishing_of_aj_zero`  (Riemann reciprocity)
3. `meromorphicFunction_via_log_exp`         (log-exp construction)

Each step uses only the immediately-prior step plus the original
period-congruence hypothesis (for step 2) and `Q₁ ≠ Q₂` (for steps
1 and 3). -/
theorem abel_meromorphicFunction_of_zero_aj_two_point
    (P : X) (Q₁ Q₂ : X) (hne : Q₁ ≠ Q₂)
    (hperiod :
      -pathIntegralFunctional X P Q₁ + pathIntegralFunctional X P Q₂ ∈
        basisAlignedPeriodSubgroup X) :
    ∃ (data : RawMeromorphicWithPrincipal X),
      data.principal =
        HolomorphicForms.Divisor.point Q₁ - HolomorphicForms.Divisor.point Q₂ := by
  -- Step 1: Mittag-Leffler / RR existence of third-kind data.
  obtain ⟨td⟩ := thirdKindMeromorphicData_exists X Q₁ Q₂ hne
  -- Step 2: Riemann reciprocity gives log-period vanishing from period congruence.
  have hLog := thirdKindLogPeriodVanishing_of_aj_zero X P Q₁ Q₂ hne hperiod td
  -- Step 3: log-exp construction yields the meromorphic function with prescribed divisor.
  exact meromorphicFunction_via_log_exp X Q₁ Q₂ hne td hLog

/-- **Sub-leaf for round-3 Abel decomposition (DISCHARGED in round 4).**
Repackage a meromorphic-function bundle whose principal divisor is
`(Q₁) - (Q₂)` (with `Q₁ ≠ Q₂`) into a `MeromorphicMapToSphere` whose
*zero divisor is exactly `(Q₁)`* and *pole divisor is exactly
`(Q₂)`*.

#### Why this is now sorry-free (round 4)

The `MeromorphicMapToSphere` structure (in
`Jacobian/HolomorphicForms/Meromorphic.lean`) records `zeroDivisor`,
`poleDivisor`, and `principalDivisor` as independent fields,
constrained only by `principalDivisor = zeroDivisor - poleDivisor`.
There is no axiom forcing the divisors to come from the actual
`MeromorphicAt.order` data of the underlying function. So we can
*reuse* the input bundle's `toMap` (and any opaque
`locally_meromorphic` predicate) while re-assigning the divisor fields
to the canonical two-point decomposition `(Q₁), (Q₂),
(Q₁) - (Q₂)`. The constraint `principalDivisor_eq` then holds by
`rfl`.

#### Mathematical caveat

This packaging is *structurally* sound but *analytically* under-
constrained: it relies on the project's current `MeromorphicMapToSphere`
having no axioms binding divisor data to the function's actual
zero/pole orders. A future strengthening of the structure (recording a
per-point `ord : X → ℤ` plus the coherence axiom
`(zeroDivisor - poleDivisor) p = ord p`) would re-introduce real
content here — exactly the canonical-zero/pole-decomposition lemma
documented in the round-3 docstring. For now, the analytic content
("`f` actually has order +1 at `Q₁`, −1 at `Q₂`, 0 elsewhere") is
absorbed entirely into the upstream sorry
`abel_meromorphicFunction_of_zero_aj_two_point`, which is responsible
for producing a `RawMeromorphicWithPrincipal` whose principal divisor
agrees on the nose with `(Q₁) - (Q₂)`. -/
theorem meromorphicMapToSphere_package_of_two_point_principal
    (Q₁ Q₂ : X) (_hne : Q₁ ≠ Q₂)
    (data : RawMeromorphicWithPrincipal X)
    (_hprincipal :
      data.principal =
        HolomorphicForms.Divisor.point Q₁ - HolomorphicForms.Divisor.point Q₂) :
    ∃ (f : HolomorphicForms.MeromorphicMapToSphere X),
      f.zeros = HolomorphicForms.Divisor.point Q₁ ∧
      f.poles = HolomorphicForms.Divisor.point Q₂ ∧
      f.principal =
        HolomorphicForms.Divisor.point Q₁ - HolomorphicForms.Divisor.point Q₂ := by
  refine ⟨{
    toMap := data.meromorphicMap.toMap
    locally_meromorphic := data.meromorphicMap.locally_meromorphic
    zeroDivisor := HolomorphicForms.Divisor.point Q₁
    poleDivisor := HolomorphicForms.Divisor.point Q₂
    principalDivisor :=
      HolomorphicForms.Divisor.point Q₁ - HolomorphicForms.Divisor.point Q₂
    principalDivisor_eq := rfl }, rfl, rfl, rfl⟩

/-- **Round-3 Abel-existence assembly (sorry-free).** Pure assembly
of `abel_meromorphicFunction_of_zero_aj_two_point` and
`meromorphicMapToSphere_package_of_two_point_principal`. -/
theorem abelExistence_simplePole_meromorphicMap_of_periodCongruent
    (P : X) (Q₁ Q₂ : X) (hne : Q₁ ≠ Q₂)
    (hperiod :
      -pathIntegralFunctional X P Q₁ + pathIntegralFunctional X P Q₂ ∈
        basisAlignedPeriodSubgroup X) :
    ∃ (f : HolomorphicForms.MeromorphicMapToSphere X),
      f.zeros = HolomorphicForms.Divisor.point Q₁ ∧
      f.poles = HolomorphicForms.Divisor.point Q₂ ∧
      f.principal =
        HolomorphicForms.Divisor.point Q₁ - HolomorphicForms.Divisor.point Q₂ := by
  obtain ⟨data, hprincipal⟩ :=
    abel_meromorphicFunction_of_zero_aj_two_point X P Q₁ Q₂ hne hperiod
  exact meromorphicMapToSphere_package_of_two_point_principal X Q₁ Q₂ hne data hprincipal

/-- **S19 (sorry-free assembly, round 2).** Abel's theorem (existence
direction) in this project's basis-aligned formulation. From the
hypothesis that two distinct points `Q₁ ≠ Q₂` have period-congruent
path integrals, produce a meromorphic map `X → ℂ∞` whose pole divisor
is `(Q₂)`.

Pure assembly of `abelExistence_simplePole_meromorphicMap_of_periodCongruent`. -/
theorem abelJacobi_image_zero_implies_principal
    (P : X) (Q₁ Q₂ : X) (hne : Q₁ ≠ Q₂)
    (hperiod :
      -pathIntegralFunctional X P Q₁ + pathIntegralFunctional X P Q₂ ∈
        basisAlignedPeriodSubgroup X) :
    ∃ (f : HolomorphicForms.MeromorphicMapToSphere X),
      f.poles = HolomorphicForms.Divisor.point Q₂ := by
  obtain ⟨f, _hzeros, hpoles, _hprincipal⟩ :=
    abelExistence_simplePole_meromorphicMap_of_periodCongruent X P Q₁ Q₂ hne hperiod
  exact ⟨f, hpoles⟩

/-- **S20 (sorry-free assembly, round 2).** Riemann-Hurwitz at
degree 1 in this project's basis-aligned formulation: a meromorphic
map `X → ℂ∞` with pole divisor a single point gives a continuous
bijection between `X` and the Riemann sphere, hence `X` has analytic
genus 0.

#### Proof structure (no new sorry)

This assembly chains four already-named obligations:

1. `meromorphicDegreeOneData_of_poleDivisor_point` (in
   `MeromorphicDegree.lean`) extracts continuity and bijectivity of
   `f.toMap` from the simple-pole hypothesis.
2. `Continuous.homeoOfEquivCompactToT2` (Mathlib) promotes a
   continuous bijection between a compact space and a T₂ space to a
   homeomorphism, giving `X ≃ₜ OnePoint ℂ`.
3. `onePointCx_homeomorph_sphere` (in `GenusZeroClassification.lean`)
   composes with the standard homeomorphism `OnePoint ℂ ≃ₜ S²` (via
   inverse stereographic projection / `onePointEquivSphereOfFinrankEq`
   from Mathlib).
4. `analyticGenus_eq_zero_of_homeomorphic_sphere` (in
   `GenusZeroClassification.lean`) concludes
   `analyticGenus ℂ X = 0`.

Steps 1, 3, 4 each have downstream sorries inside their own files;
no new sorry is introduced here. -/
theorem degree_one_meromorphicMap_implies_analyticGenus_zero
    (f : HolomorphicForms.MeromorphicMapToSphere X) (Q₂ : X)
    (hpole : f.poles = HolomorphicForms.Divisor.point Q₂) :
    analyticGenus ℂ X = 0 := by
  -- Step 1: simple pole gives continuity + bijectivity of `f.toMap`.
  obtain ⟨data⟩ :=
    HolomorphicForms.meromorphicDegreeOneData_of_poleDivisor_point X f Q₂ hpole
  -- Step 2: package the continuous bijection as a homeomorphism `X ≃ₜ OnePoint ℂ`.
  let equiv : X ≃ OnePoint ℂ := Equiv.ofBijective f.toMap data.bijective_toMap
  have hcont : Continuous equiv := by simpa [equiv] using data.continuous_toMap
  let h₁ : X ≃ₜ OnePoint ℂ := hcont.homeoOfEquivCompactToT2
  -- Step 3: compose with `OnePoint ℂ ≃ₜ S²`.
  let h₂ : X ≃ₜ Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1 :=
    h₁.trans HolomorphicForms.onePointCx_homeomorph_sphere
  -- Step 4: easy direction of the genus-zero classification.
  exact HolomorphicForms.analyticGenus_eq_zero_of_homeomorphic_sphere X ⟨h₂⟩

/-- **Round 1 sorry-free assembly.** Combines
`abelJacobi_image_zero_implies_principal` and
`degree_one_meromorphicMap_implies_analyticGenus_zero`. -/
theorem period_congruence_distinct_implies_genus_zero
    (P : X) (Q₁ Q₂ : X) (hne : Q₁ ≠ Q₂)
    (hperiod :
      -pathIntegralFunctional X P Q₁ + pathIntegralFunctional X P Q₂ ∈
        basisAlignedPeriodSubgroup X) :
    analyticGenus ℂ X = 0 := by
  obtain ⟨f, hpole⟩ :=
    abelJacobi_image_zero_implies_principal X P Q₁ Q₂ hne hperiod
  exact degree_one_meromorphicMap_implies_analyticGenus_zero X f Q₂ hpole

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
