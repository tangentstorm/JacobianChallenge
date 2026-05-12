import Jacobian.HolomorphicForms.SheafCohomologyRS
import Jacobian.HolomorphicForms.SerreDualityRS
import Jacobian.HolomorphicForms.Defs
import Mathlib.LinearAlgebra.Dimension.Finrank

/-!
# Euler characteristic of a line bundle on a compact Riemann surface

Frontier statement of the Euler-characteristic-of-line-bundle
formula (a.k.a. Riemann-Roch in its bare form):

  χ(X, L) = deg(L) + 1 - g

where `χ(X, L) = dim_ℂ H⁰(X, L) - dim_ℂ H¹(X, L)`, `deg(L)` is the
degree of the line bundle, and `g` is the genus of `X`.

## Mathlib v4.28.0 status

Per `ref/plans/sheaf-cohomology-rs.md` §2 and `ref/scope-out.md`,
the four classical-input ingredients are ABSENT:

* analytic structure sheaf `𝒪_X` and locally-free `𝒪_X`-module
  presentations of holomorphic line bundles,
* divisor ↔ line-bundle correspondence on a Riemann surface,
* `deg(L)` for a line bundle,
* finite-dimensionality of `H^q` for a coherent sheaf on a compact
  RS — covered as the frontier class
  `FiniteDimensionalSheafCohomologyRS` in
  `SheafCohomologyRS.lean`, but no concrete instance witnesses
  exist yet.

We therefore expose:

* `RSLineBundleDegree X L : ℤ` — frontier `def` (sorry) for `deg L`.
* `RSGenus X : ℕ` — frontier `def` (sorry) for the genus
  classically `dim_ℂ H¹(X, 𝒪_X)`.
* `RSEulerCharacteristic X L : ℤ` — concrete `def`, computed as
  `finrank ℂ H⁰(X, L) - finrank ℂ H¹(X, L)` once the consumer
  supplies the `[Module ℂ …]` instance arguments. (No sorry.)
* `euler_char_line_bundle X L` — frontier theorem (sorry) asserting
  the Riemann-Roch identity.

## What this file does NOT provide

* explicit divisor-of-a-line-bundle map,
* the `FiniteDimensionalSheafCohomologyRS` discharge for arbitrary
  line bundles (requires GAGA / coherent-sheaf machinery),
* Serre duality identification `H¹(L)* ≃ H⁰(L⁻¹ ⊗ K_X)` (lives in
  `SerreDualityRS.lean` already as a frontier class).

These belong to follow-up nodes
(`input:riemann-roch`, `prop:genus-zero-degree-one-map`).
-/

namespace JacobianChallenge.HolomorphicForms

open CategoryTheory

/-- **Frontier `def` (sorry).** The degree of a line-bundle sheaf on
a compact Riemann surface. Classically equal to the degree of any
divisor representing the line bundle, or equivalently
`deg(c₁(L)) ∈ H²(X, ℤ)`; both routes require analytic-sheaf or
de Rham machinery ABSENT in Mathlib v4.28.0. -/
noncomputable opaque RSLineBundleDegree
    (X : Type*) [TopologicalSpace X]
    (_L : RSLineBundleSheaf X) : ℤ

/-- The genus of a compact Riemann surface, defined as
`dim_ℂ H⁰(X, Ω¹_X) = Module.finrank ℂ (HolomorphicOneForm ℂ X)`.

Classically `g = dim_ℂ H¹(X, 𝒪_X) = dim_ℂ H⁰(X, Ω¹_X)` by Serre
duality / Hodge theory.  The `H⁰(X, Ω¹)` realisation avoids the
frontier sheaf-cohomology prerequisites (`HasSheafify`, `HasExt`,
`Module ℂ` on `H¹(X, 𝒪_X)`) and gives a concrete `ℕ` for every
complex-manifold charted space.  When the space of holomorphic
1-forms is not finite-dimensional, `Module.finrank` returns `0` by
Mathlib convention; for a compact Riemann surface this dimension is
always finite and equals the topological genus. -/
noncomputable def RSGenus
    (X : Type*) [TopologicalSpace X] [CompactSpace X] [T2Space X]
    [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X] : ℕ :=
  Module.finrank ℂ (HolomorphicOneForm ℂ X)

/-- The Euler characteristic of a line-bundle sheaf on a compact
Riemann surface, computed as
`finrank ℂ H⁰(X, L) - finrank ℂ H¹(X, L) : ℤ`.

Concrete (no sorry); however it requires the consumer to supply
`[Module ℂ (RSSheafCohomology X L q)]` instances for `q = 0, 1`
since `Sheaf.H` only gives `AddCommGroup`. The result is sensible
on cohomologies that turn out to be finite-dimensional ℂ-vector
spaces (witnessed by `FiniteDimensionalSheafCohomologyRS`); on
infinite-dimensional ones `Module.finrank` returns `0`, which is
the harmless Mathlib convention. -/
noncomputable def RSEulerCharacteristic
    (X : Type*) [TopologicalSpace X]
    [HasSheafify (Opens.grothendieckTopology (TopCat.of X)) AddCommGrpCat.{0}]
    [HasExt.{0} (Sheaf (Opens.grothendieckTopology (TopCat.of X)) AddCommGrpCat.{0})]
    (L : RSLineBundleSheaf X)
    [Module ℂ (RSSheafCohomology X L 0)]
    [Module ℂ (RSSheafCohomology X L 1)] : ℤ :=
  (Module.finrank ℂ (RSSheafCohomology X L 0) : ℤ) -
    (Module.finrank ℂ (RSSheafCohomology X L 1) : ℤ)

/-! ### TOPDOWN decomposition (round 1 → round 2 refinement)

The headline `euler_char_line_bundle` (Riemann-Roch in Euler-
characteristic form, `χ(X, L) = deg L + 1 - g`) is built from a
single fundamental frontier lemma `euler_char_eq_formula` that
states the Euler-characteristic equality. The `≥` and `≤`
directions and the headline equality all follow sorry-free from it.

The genuine analytic content — induction on degree via the short
exact sequence `0 → L → L(p) → ℂ_p → 0`, base case for the trivial
bundle, and Serre duality — is concentrated in `euler_char_eq_formula`.
-/

/-! ### R8-sub-C.B / R8-sub-C.C stepwise refinement (Round 1 → Round 2)

The sub-leaves for the classical proof structure are retained as
documentation placeholders. The actual proof obligation is unified
in `euler_char_eq_formula`, since the equality implies both
directional inequalities trivially.

* R8-sub-C.B (≥ direction): follows from equality.
* R8-sub-C.C (≤ direction): follows from equality. -/

/-- **R8-sub-C.B.r1.** Base case of the inductive proof of Riemann's
inequality: for the trivial bundle, `h⁰ = 1` and `h¹ = g` (via
Hodge `H¹(O_X) ≅ H⁰(K_X)*` and `dim H⁰(O_X) = 1` on a connected
compact RS). (Round 1 placeholder.) -/
theorem h0_minus_h1_trivial_bundle : True := by trivial

/-- **R8-sub-C.B.r2.** Euler-characteristic additivity along the
short exact sequence `0 → L → L(p) → ℂ_p → 0`: `χ(L(p)) = χ(L) + 1`.
The skyscraper sheaf `ℂ_p` has `h⁰ = 1, h¹ = 0`.
(Round 1 placeholder.) -/
theorem eulerChar_additive_ses_point : True := by trivial

/-- **R8-sub-C.B.r3 (strengthened).** The Euler-characteristic
equality `h⁰(L) - h¹(L) = deg L + 1 - g`, proved by strong induction
on `|deg L|` using the base case (r1) and the Euler-characteristic
additivity (r2). This is the fundamental frontier lemma from which
both directional inequalities follow.

**Frontier theorem (sorry).** The genuine analytic content — the
short exact sequence for twisting by a point, the base case for the
trivial bundle, and the induction — requires coherent-sheaf and
divisor machinery ABSENT in Mathlib v4.28.0. -/
theorem euler_char_eq_formula
    (X : Type*) [TopologicalSpace X] [CompactSpace X] [T2Space X]
    [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X]
    [HasSheafify (Opens.grothendieckTopology (TopCat.of X)) AddCommGrpCat.{0}]
    [HasExt.{0} (Sheaf (Opens.grothendieckTopology (TopCat.of X)) AddCommGrpCat.{0})]
    (L : RSLineBundleSheaf X)
    [Module ℂ (RSSheafCohomology X L 0)]
    [Module ℂ (RSSheafCohomology X L 1)] :
    (Module.finrank ℂ (RSSheafCohomology X L 0) : ℤ) -
        (Module.finrank ℂ (RSSheafCohomology X L 1) : ℤ) =
      RSLineBundleDegree X L + 1 - (RSGenus X : ℤ) := by
  -- BLOCKER (2026-05-12, claude/euler-char-formula-FnMyi):
  -- This theorem is unprovable in its current form against the
  -- v4.28.0 frontier.  Two independent obstructions:
  --
  -- 1. `RSLineBundleDegree` (above, lines 64-66) is declared
  --    `noncomputable opaque ... : ℤ` — i.e. an integer-valued
  --    function with no characterizing axioms or equations.  No
  --    nontrivial equation relating the LHS (a finrank difference)
  --    to `RSLineBundleDegree X L` can be discharged without first
  --    giving that symbol a real definition (or characterizing
  --    axioms).  Making the symbol agree with the LHS by fiat is
  --    explicitly the kind of hack-answer the project rules out.
  --
  -- 2. Even with a concrete `RSLineBundleDegree`, the classical
  --    proof requires inputs ABSENT in Mathlib v4.28.0 (see file
  --    header, lines 19-30, and `ref/scope-out.md`):
  --      * divisor ↔ line-bundle correspondence on a compact RS,
  --      * skyscraper sheaf `ℂ_p` and the twisting short exact
  --        sequence `0 → L → L(p) → ℂ_p → 0`,
  --      * base case `h⁰(O_X) = 1`, `h¹(O_X) = g` for the trivial
  --        line bundle (Hodge / Serre on the structure sheaf),
  --      * Serre-duality identification `H¹(L)* ≃ H⁰(L⁻¹ ⊗ K_X)`
  --        (the frontier class `SerreDualityRS` has no instances),
  --      * finite-dimensionality of `Hᵍ` for coherent sheaves on a
  --        compact RS (`FiniteDimensionalSheafCohomologyRS`, no
  --        instances).
  --
  -- The placeholder leaves at lines 133, 139, 188, 194, 199 of this
  -- file (`h0_minus_h1_trivial_bundle`, `eulerChar_additive_ses_point`,
  -- `dual_bundle_degree`, `serre_duality_h0_h1_swap`,
  -- `h0_minus_h1_le_via_dual`) are the intended Round-2 refinement
  -- targets that, once made into honest theorems, will combine to
  -- discharge this `sorry`.
  sorry

/-- **Sub-leaf 1 (Riemann's inequality, `≥` direction).** The integer
difference `(h⁰(L) : ℤ) - (h¹(L) : ℤ)` is at least `deg L + 1 - g`.

Sorry-free: follows immediately from the Euler-characteristic
equality `euler_char_eq_formula`. -/
theorem h0_minus_h1_ge_riemann
    (X : Type*) [TopologicalSpace X] [CompactSpace X] [T2Space X]
    [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X]
    [HasSheafify (Opens.grothendieckTopology (TopCat.of X)) AddCommGrpCat.{0}]
    [HasExt.{0} (Sheaf (Opens.grothendieckTopology (TopCat.of X)) AddCommGrpCat.{0})]
    (L : RSLineBundleSheaf X)
    [Module ℂ (RSSheafCohomology X L 0)]
    [Module ℂ (RSSheafCohomology X L 1)] :
    (Module.finrank ℂ (RSSheafCohomology X L 0) : ℤ) -
        (Module.finrank ℂ (RSSheafCohomology X L 1) : ℤ) ≥
      RSLineBundleDegree X L + 1 - (RSGenus X : ℤ) :=
  le_of_eq (euler_char_eq_formula X L).symm

/-- **R8-sub-C.C.r1.** Dual bundle degree:
`deg(L⁻¹ ⊗ K_X) = 2g - 2 - deg L`. The canonical bundle `K_X`
has `deg K_X = 2g - 2`; tensor + inverse degrees subtract.
(Round 1 placeholder.) -/
theorem dual_bundle_degree : True := by trivial

/-- **R8-sub-C.C.r2.** Serre-duality identification of cohomology
groups: `h⁰(L⁻¹ ⊗ K_X) = h¹(L)` and `h¹(L⁻¹ ⊗ K_X) = h⁰(L)` via
non-degeneracy of the Serre pairing.
(Round 1 placeholder; consumes `Jacobian/HolomorphicForms/SerreDualityRS.lean`.) -/
theorem serre_duality_h0_h1_swap : True := by trivial

/-- **R8-sub-C.C.r3.** Apply r-r3 of R8-sub-C.B (the `≥` direction)
to `L⁻¹ ⊗ K_X`; rewrite via r1 (degree) and r2 (Serre swap) to land
at the `≤` statement on `L`. (Round 1 placeholder.) -/
theorem h0_minus_h1_le_via_dual : True := by trivial

/-- **Sub-leaf 2 (Serre-duality direction, `≤`).** The integer
difference `(h⁰(L) : ℤ) - (h¹(L) : ℤ)` is at most `deg L + 1 - g`.

Sorry-free: follows immediately from the Euler-characteristic
equality `euler_char_eq_formula`. -/
theorem h0_minus_h1_le_riemann
    (X : Type*) [TopologicalSpace X] [CompactSpace X] [T2Space X]
    [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X]
    [HasSheafify (Opens.grothendieckTopology (TopCat.of X)) AddCommGrpCat.{0}]
    [HasExt.{0} (Sheaf (Opens.grothendieckTopology (TopCat.of X)) AddCommGrpCat.{0})]
    (L : RSLineBundleSheaf X)
    [Module ℂ (RSSheafCohomology X L 0)]
    [Module ℂ (RSSheafCohomology X L 1)] :
    (Module.finrank ℂ (RSSheafCohomology X L 0) : ℤ) -
        (Module.finrank ℂ (RSSheafCohomology X L 1) : ℤ) ≤
      RSLineBundleDegree X L + 1 - (RSGenus X : ℤ) :=
  le_of_eq (euler_char_eq_formula X L)

/-- **Sub-leaf 3 (sorry-free squeeze).** Combining the lower and upper
bounds gives the headline equality on the integer-difference form
`h⁰ - h¹`.  Now directly follows from `euler_char_eq_formula`. -/
theorem h0_minus_h1_eq_riemann_roch
    (X : Type*) [TopologicalSpace X] [CompactSpace X] [T2Space X]
    [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X]
    [HasSheafify (Opens.grothendieckTopology (TopCat.of X)) AddCommGrpCat.{0}]
    [HasExt.{0} (Sheaf (Opens.grothendieckTopology (TopCat.of X)) AddCommGrpCat.{0})]
    (L : RSLineBundleSheaf X)
    [Module ℂ (RSSheafCohomology X L 0)]
    [Module ℂ (RSSheafCohomology X L 1)] :
    (Module.finrank ℂ (RSSheafCohomology X L 0) : ℤ) -
        (Module.finrank ℂ (RSSheafCohomology X L 1) : ℤ) =
      RSLineBundleDegree X L + 1 - (RSGenus X : ℤ) :=
  euler_char_eq_formula X L

/-- **Sub-leaf 4 (sorry-free unfolding).** The Euler characteristic
unfolds definitionally to the integer difference of finranks. -/
theorem rsEulerCharacteristic_eq_h0_minus_h1
    (X : Type*) [TopologicalSpace X]
    [HasSheafify (Opens.grothendieckTopology (TopCat.of X)) AddCommGrpCat.{0}]
    [HasExt.{0} (Sheaf (Opens.grothendieckTopology (TopCat.of X)) AddCommGrpCat.{0})]
    (L : RSLineBundleSheaf X)
    [Module ℂ (RSSheafCohomology X L 0)]
    [Module ℂ (RSSheafCohomology X L 1)] :
    RSEulerCharacteristic X L =
      (Module.finrank ℂ (RSSheafCohomology X L 0) : ℤ) -
        (Module.finrank ℂ (RSSheafCohomology X L 1) : ℤ) := rfl

/-- **Headline theorem (sorry-free assembly).** Riemann-Roch for line
bundles on a compact Riemann surface, in Euler-characteristic form:

  χ(X, L) = deg(L) + 1 - g.

Assembled from the four sub-leaves above:
- (4) `rsEulerCharacteristic_eq_h0_minus_h1`: rewrite χ as h⁰ - h¹;
- (3) `h0_minus_h1_eq_riemann_roch`: rewrite h⁰ - h¹ as deg + 1 - g
  (itself equivalent to `euler_char_eq_formula`).

The genuine analytic obligation is isolated in the single frontier
lemma `euler_char_eq_formula`, which states the Euler-characteristic
equality directly. -/
theorem euler_char_line_bundle
    (X : Type*) [TopologicalSpace X] [CompactSpace X] [T2Space X]
    [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X]
    [HasSheafify (Opens.grothendieckTopology (TopCat.of X)) AddCommGrpCat.{0}]
    [HasExt.{0} (Sheaf (Opens.grothendieckTopology (TopCat.of X)) AddCommGrpCat.{0})]
    (L : RSLineBundleSheaf X)
    [Module ℂ (RSSheafCohomology X L 0)]
    [Module ℂ (RSSheafCohomology X L 1)] :
    RSEulerCharacteristic X L =
      RSLineBundleDegree X L + 1 - (RSGenus X : ℤ) := by
  rw [rsEulerCharacteristic_eq_h0_minus_h1 X L]
  exact h0_minus_h1_eq_riemann_roch X L

end JacobianChallenge.HolomorphicForms
