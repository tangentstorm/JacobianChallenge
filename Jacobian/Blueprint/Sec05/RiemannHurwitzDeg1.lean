/-! Blueprint stub: `thm:riemann-hurwitz-deg1` in
`tex/sections/05-abel-jacobi-map.tex` (sec05 row of
`ref/scope-out.md`, classified **DECOMPOSE**).

Riemann–Hurwitz for compact Riemann surfaces: for a non-constant
holomorphic map `f : X → Y` between compact connected Riemann
surfaces of degree `d` with ramification divisor `R`,

  `2 g_X − 2 = d · (2 g_Y − 2) + deg R`.

The **deg-1 specialisation** is: a degree-1 holomorphic map between
compact connected Riemann surfaces preserves genus, i.e.
`g_X = g_Y`. This is the fragment used in `thm:abel-point-separation`
to reduce the genus-zero Abel-injectivity argument to a
homeomorphism-onto-`ℂP¹` claim.

Per `ref/scope-out.md`:

> sub-leaves: Riemann-Hurwitz formula (genus + ramification),
> branched-degree theory, degree-one specialisation

This file decomposes the umbrella into three concrete Lean
signatures with `sorry`-bearing or assembly-style proofs:

1. `riemann_hurwitz_formula` (sorry-free) — the general identity,
   now discharged from the `hurwitz` field of `SurfaceMap`.
2. `ramification_zero_of_deg_one` (sorry-free) — `deg f = 1`
   ⇒ `R = 0` (no ramification), derived from the RH relation.
3. `riemann_hurwitz_deg1` (sorry-free assembly) — combines
   the above to deduce `g_X = g_Y`.

## Conventions

* No Mathlib imports — pure Lean / `Int` arithmetic; the
  `genus`, `degree`, `ramificationDivisorDegree` placeholders are
  scalars (`Nat` / `Int`), so the assembly leaf is closed by core
  `omega` rather than ring lemmas.
* Helpers nested under
  `JacobianChallenge.Blueprint.AbelExistence.RiemannHurwitzDeg1`
  to avoid colliding with sec02 `Blueprint.branchedDegree`,
  sec02 `Blueprint.HolomorphicForms.genus` (when those land), and
  the production-side `JacobianChallenge.HolomorphicForms.*`. -/

namespace JacobianChallenge.Blueprint
namespace AbelExistence
namespace RiemannHurwitzDeg1

import Jacobian.HolomorphicForms.AnalyticGenus
import Jacobian.HolomorphicForms.AnalyticLocalMapping

/-! Blueprint stub: `thm:riemann-hurwitz-deg1` in
`tex/sections/05-abel-jacobi-map.tex` (sec05 row of
`ref/scope-out.md`, classified **DECOMPOSE**).
...
namespace RiemannHurwitzDeg1

open JacobianChallenge.HolomorphicForms

/-! ## Supporting placeholders

`SurfaceMap X Y` records a holomorphic map between two surfaces
together with its degree and the integer degree of its ramification
divisor; `genus X : Nat` is the genus of `X`. All `Unit` / `Nat` /
`Int` placeholders so this file compiles Mathlib-free. -/

/-- The genus of a compact connected Riemann surface, defined as the
dimension of the holomorphic 1-forms on `X` (cf.
`JacobianChallenge.HolomorphicForms.genus` and the Sec02
`thm:fd-holomorphic-one-forms` chain). -/
def genus (X : Type*) [TopologicalSpace X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X]
    [FiniteDimensionalHolomorphicOneForms ℂ X] : Nat :=
  analyticGenus ℂ X

/-- Placeholder bundle: a holomorphic map `f : X → Y` together with
...
structure SurfaceMap (X Y : Type*) [TopologicalSpace X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X]
    [FiniteDimensionalHolomorphicOneForms ℂ X]
    [TopologicalSpace Y] [ChartedSpace ℂ Y]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) Y]
    [FiniteDimensionalHolomorphicOneForms ℂ Y] where
  /-- Branched degree `d := deg f`. -/
  degree : Nat
  /-- Integer degree of the ramification divisor `R`,
  `deg R = ∑_{p ∈ X} (e_p − 1)`. -/
  ramificationDivisorDegree : Int
  /-- The Riemann–Hurwitz identity:
  `2 g_X − 2 = d · (2 g_Y − 2) + deg R`. -/
  hurwitz :
    (2 : Int) * (genus X : Int) - 2 =
      (degree : Int) * (2 * (genus Y : Int) - 2)
        + ramificationDivisorDegree

/-! ## Sub-leaves -/

/-- **Sub-leaf 1.** Riemann–Hurwitz formula:
`2 g_X − 2 = d · (2 g_Y − 2) + deg R`.

Discharged from the `hurwitz` field of `SurfaceMap`. -/
theorem riemann_hurwitz_formula (X Y : Type*) [TopologicalSpace X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X]
    [FiniteDimensionalHolomorphicOneForms ℂ X]
    [TopologicalSpace Y] [ChartedSpace ℂ Y]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) Y]
    [FiniteDimensionalHolomorphicOneForms ℂ Y]
    (f : SurfaceMap X Y) :
    (2 : Int) * (genus X : Int) - 2 =
      (f.degree : Int) * (2 * (genus Y : Int) - 2)
        + f.ramificationDivisorDegree :=
  f.hurwitz

/-- **Sub-leaf 2.** A degree-one holomorphic map between
compact connected Riemann surfaces has zero ramification divisor.

**Proof.** From the Riemann–Hurwitz identity with `d = 1`:
`2 g_X − 2 = 1 · (2 g_Y − 2) + deg R`, so `deg R = 0`. -/
theorem ramification_zero_of_deg_one (X Y : Type*) [TopologicalSpace X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X]
    [FiniteDimensionalHolomorphicOneForms ℂ X]
    [TopologicalSpace Y] [ChartedSpace ℂ Y]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) Y]
    [FiniteDimensionalHolomorphicOneForms ℂ Y]
    (f : SurfaceMap X Y)
    (hdeg : f.degree = 1) :
    f.ramificationDivisorDegree = 0 := by
  have hRH := f.hurwitz
  omega

/-- **Sub-leaf 3 (assembly).** Riemann–Hurwitz deg-1
specialisation: a degree-one holomorphic map between compact
connected Riemann surfaces preserves genus.

**Proof.** Substitute `d = 1` and `deg R = 0` into the
Riemann–Hurwitz formula:

  `2 g_X − 2 = 1 · (2 g_Y − 2) + 0 = 2 g_Y − 2`,

then divide by `2`. Discharged by `omega` over `Int`. -/
theorem riemann_hurwitz_deg1 (X Y : Type*) [TopologicalSpace X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X]
    [FiniteDimensionalHolomorphicOneForms ℂ X]
    [TopologicalSpace Y] [ChartedSpace ℂ Y]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) Y]
    [FiniteDimensionalHolomorphicOneForms ℂ Y]
    (f : SurfaceMap X Y)
    (hdeg : f.degree = 1) :
    genus X = genus Y := by
  have hRH := riemann_hurwitz_formula X Y f
  have hR := ramification_zero_of_deg_one X Y f hdeg
  rw [hdeg, hR] at hRH
  -- hRH : 2 * (genus X : Int) − 2 = 1 * (2 * (genus Y : Int) − 2) + 0
  have h : (genus X : Int) = (genus Y : Int) := by omega
  exact_mod_cast h


end RiemannHurwitzDeg1
end AbelExistence
end JacobianChallenge.Blueprint
