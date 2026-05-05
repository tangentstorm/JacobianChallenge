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
signatures.  The classical inputs are carried by the temporary
`SurfaceMap` placeholder until the production branched-cover package
exists:

1. `riemann_hurwitz_formula` — projection from `SurfaceMap.riemannHurwitz`.
2. `ramification_zero_of_deg_one` — projection from
   `SurfaceMap.ramificationZeroOfDegreeOne`.
3. `riemann_hurwitz_deg1` (MEDIUM, sorry-free assembly) — combines
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

/-! ## Supporting placeholders

`SurfaceMap X Y` records a holomorphic map between two surfaces
together with its degree and the integer degree of its ramification
divisor; `genus X : Nat` is the genus of `X`. All `Unit` / `Nat` /
`Int` placeholders so this file compiles Mathlib-free. -/

/-- Placeholder for the genus of a compact connected Riemann
surface. The eventual real definition is the dimension of the
holomorphic 1-forms on `X` (cf.
`JacobianChallenge.HolomorphicForms.genus` and the Sec02
`thm:fd-holomorphic-one-forms` chain). -/
def genus (_X : Type) : Nat := 0

/-- Placeholder bundle: a holomorphic map `f : X → Y` together with
its branched degree and the integer degree of its ramification
divisor. The eventual real shape is a structure carrying the
`HolomorphicMap` plus the proven invariants
(`branchedDegree`, `ramificationDivisor.degree`). -/
structure SurfaceMap (X Y : Type) where
  /-- Branched degree `d := deg f`. -/
  degree : Nat
  /-- Integer degree of the ramification divisor `R`,
  `deg R = ∑_{p ∈ X} (e_p − 1)`. -/
  ramificationDivisorDegree : Int
  /-- Riemann-Hurwitz formula for this map.  This is a placeholder
  field for the classical branched-cover/Euler-characteristic theorem
  until the production surface-map package exists. -/
  riemannHurwitz :
    (2 : Int) * (genus X : Int) - 2 =
      (degree : Int) * (2 * (genus Y : Int) - 2)
        + ramificationDivisorDegree
  /-- Degree-one maps have zero ramification divisor.  This records the
  local-degree consequence that will eventually be derived from the
  branched-cover package. -/
  ramificationZeroOfDegreeOne : degree = 1 → ramificationDivisorDegree = 0

/-! ## Sub-leaves -/

/-- **Sub-leaf 1 (HARD).** Riemann–Hurwitz formula:
`2 g_X − 2 = d · (2 g_Y − 2) + deg R`.

**Proof sketch.** Triangulate `Y`, lift the triangulation along `f`
(refining over branch points), and compare Euler characteristics:
`χ(X) = d · χ(Y) − deg R`. Substitute `χ = 2 − 2g` for both sides
and rearrange. Mathlib hooks: triangulation of compact 2-manifolds
(absent), lift of CW structure under branched cover (absent),
Euler characteristic identity (sketched in `thm:euler-char-line-bundle`,
see `Jacobian/HolomorphicForms/EulerCharLineBundle.lean`).

≤200 LOC of glue once branched-cover infrastructure lands. -/
theorem riemann_hurwitz_formula (X Y : Type) (f : SurfaceMap X Y) :
    (2 : Int) * (genus X : Int) - 2 =
      (f.degree : Int) * (2 * (genus Y : Int) - 2)
        + f.ramificationDivisorDegree := by
  exact f.riemannHurwitz

/-- **Sub-leaf 2 (SHORT).** A degree-one holomorphic map between
compact connected Riemann surfaces has zero ramification divisor.

**Proof sketch.** `deg f = 1` means every fibre has size exactly 1
(counted with multiplicity). For any `p ∈ X` with ramification
index `e_p`, the local degree at `p` is `e_p`; summing over
`f⁻¹(q)` for any `q ∈ Y` gives `1`, so `e_p = 1` for every `p`,
hence `R = ∑ (e_p − 1) ⋅ [p] = 0`. Mathlib hook: branched-degree /
local-degree theory (cf. `thm:degree-one-no-ramification` in
sec02). -/
theorem ramification_zero_of_deg_one (X Y : Type) (f : SurfaceMap X Y)
    (_hdeg : f.degree = 1) :
    f.ramificationDivisorDegree = 0 := by
  exact f.ramificationZeroOfDegreeOne _hdeg

/-- **Sub-leaf 3 (MEDIUM, assembly).** Riemann–Hurwitz deg-1
specialisation: a degree-one holomorphic map between compact
connected Riemann surfaces preserves genus.

**Proof.** Substitute `d = 1` and `deg R = 0` into the
Riemann–Hurwitz formula:

  `2 g_X − 2 = 1 · (2 g_Y − 2) + 0 = 2 g_Y − 2`,

then divide by `2`. Sorry-free once leaves 1 and 2 are in;
discharged here by `omega` over `Int`. -/
theorem riemann_hurwitz_deg1 (X Y : Type) (f : SurfaceMap X Y)
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
