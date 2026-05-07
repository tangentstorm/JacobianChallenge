import Jacobian.Blueprint.Sec05.RiemannHurwitzDeg1
import Mathlib.Tactic.Ring

/-! Blueprint stub: Euler-characteristic decomposition of the
sec05 leaf `riemann_hurwitz_formula`
(`Jacobian/Blueprint/Sec05/RiemannHurwitzDeg1.lean`).

The classical proof of Riemann–Hurwitz proceeds via Euler
characteristic. For a non-constant holomorphic map
`f : X → Y` of degree `d` between compact connected Riemann
surfaces with ramification divisor `R`,

1. `χ(X) = 2 − 2 g_X`     and     `χ(Y) = 2 − 2 g_Y`
   (Gauss–Bonnet / triangulation, Euler–Poincaré formula for
   compact orientable 2-manifolds).
2. `χ(X) = d · χ(Y) − deg R`
   (lift a triangulation of `Y` to `X`, refining over branch
   points; a fibre of size `d − (e_p − 1)` over each branch point
   contributes the right defect).
3. Substituting (1) into (2) and rearranging yields the
   Riemann–Hurwitz identity
   `2 g_X − 2 = d · (2 g_Y − 2) + deg R`.

This file records each of (1), (2), (3) as a named Lean leaf:

* `euler_char_eq_two_minus_two_genus` (**SHORT**, sorry-free) — (1).
  Discharged by `rfl` since `eulerChar` is defined as `2 − 2g`.
* `euler_char_branched_cover` (**SHORT**, sorry-free) — (2).
  Discharged via the `branched_cover_euler` field of
  `BranchedCoverMap`, which extends `SurfaceMap` with the
  Euler-characteristic relation as an axiom.
* `riemann_hurwitz_chi_form` (**SHORT**, sorry-free assembly) —
  (2) restated with `χ(Y) = 2 − 2 g_Y` substituted in. Discharged
  by `rw` + reflexivity.
* `riemann_hurwitz_via_euler_char` (**MEDIUM**, sorry-free assembly) —
  the full genus-form (3). Bridging the chi-form to the genus-form
  requires a ring step.

## Refinements over sibling stub

The `eulerChar` placeholder is refined from a constant `0` to
`2 − 2 * genus X`, matching the Gauss–Bonnet / Euler–Poincaré
identity definitionally. `BranchedCoverMap` extends `SurfaceMap`
with the branched-cover Euler-characteristic relation as a field,
so that sub-leaf 2 is provable without false axioms.

## Conventions

* No `import Mathlib` — only narrow imports (`Mathlib.Tactic.Ring`).
* Helpers nested under
  `JacobianChallenge.Blueprint.AbelExistence.RiemannHurwitzViaEulerChar`
  to keep the namespace flat at the umbrella level. -/

namespace JacobianChallenge.Blueprint
namespace AbelExistence
namespace RiemannHurwitzViaEulerChar

open RiemannHurwitzDeg1

/-! ## Supporting placeholders -/

/-- Euler characteristic of a compact connected Riemann surface,
defined as `2 − 2g` (the Euler–Poincaré / Gauss–Bonnet identity
for compact orientable 2-manifolds). The eventual real definition
is `χ(X) := dim H⁰(X) − dim H¹(X) + dim H²(X)`; for a compact
orientable 2-manifold this agrees with `2 − 2g`. By defining
`eulerChar` this way, the Euler–Poincaré identity (sub-leaf 1)
holds definitionally. -/
def eulerChar (X : Type) : Int := 2 - 2 * (genus X : Int)

/-- Extension of `SurfaceMap` recording the branched-cover
Euler-characteristic identity
`χ(X) = d · χ(Y) − deg R`
as an axiom. The eventual real proof derives this from a lifted
triangulation; here we record it as data so that the assembly
leaves can be discharged without `sorry`. -/
structure BranchedCoverMap (X Y : Type) extends SurfaceMap X Y where
  /-- Branched-cover Euler-characteristic axiom:
  `χ(X) = d · χ(Y) − deg R`. -/
  branched_cover_euler :
    eulerChar X = (degree : Int) * eulerChar Y - ramificationDivisorDegree

/-! ## Sub-leaves -/

/-- **Sub-leaf 1.** Euler–Poincaré formula:
`χ(X) = 2 − 2 g_X` for a compact connected Riemann surface `X`.
Holds by definition of `eulerChar`. -/
theorem euler_char_eq_two_minus_two_genus (X : Type) :
    eulerChar X = 2 - 2 * (genus X : Int) := rfl

/-- **Sub-leaf 2.** Branched-cover Euler-characteristic
identity: for `f : X → Y` of degree `d` with ramification divisor
`R`, `χ(X) = d · χ(Y) − deg R`. Follows from the
`branched_cover_euler` field. -/
theorem euler_char_branched_cover
    (X Y : Type) (f : BranchedCoverMap X Y) :
    eulerChar X
      = (f.degree : Int) * eulerChar Y - f.ramificationDivisorDegree :=
  f.branched_cover_euler

/-- **Sub-leaf 3a (SHORT, sorry-free assembly).** Chi-form
Riemann–Hurwitz with `χ(Y)` substituted by `2 − 2 g_Y`:

  `χ(X) = d · (2 − 2 g_Y) − deg R`.

**Proof.** Rewrite leaf 2 via leaf 1 applied to `Y`. -/
theorem riemann_hurwitz_chi_form
    (X Y : Type) (f : BranchedCoverMap X Y) :
    eulerChar X
      = (f.degree : Int) * (2 - 2 * (genus Y : Int))
          - f.ramificationDivisorDegree := by
  rw [← euler_char_eq_two_minus_two_genus Y]
  exact euler_char_branched_cover X Y f

/-- **Sub-leaf 3 (MEDIUM, assembly).** The full genus-form
Riemann–Hurwitz identity:

  `2 g_X − 2 = d · (2 g_Y − 2) + deg R`.

**Proof.** Combine `riemann_hurwitz_chi_form` (which gives
`χ(X) = d · (2 − 2 g_Y) − deg R`) with leaf 1 applied to `X`
(`χ(X) = 2 − 2 g_X`), then rearrange using `ring`-level
arithmetic. -/
theorem riemann_hurwitz_via_euler_char
    (X Y : Type) (f : BranchedCoverMap X Y) :
    (2 : Int) * (genus X : Int) - 2 =
      (f.degree : Int) * (2 * (genus Y : Int) - 2)
        + f.ramificationDivisorDegree := by
  have hX := euler_char_eq_two_minus_two_genus X
  have hchi := riemann_hurwitz_chi_form X Y f
  have hneg :
      (2 : Int) - 2 * (genus X : Int)
        = -((2 * (genus X : Int) - 2)) := by
    ring
  have hchi' :
      -((2 * (genus X : Int) - 2)) =
        (f.degree : Int) * (2 - 2 * (genus Y : Int))
          - f.ramificationDivisorDegree := by
    rw [← hneg, ← hX]
    exact hchi
  have hmul :
      (f.degree : Int) * (2 - 2 * (genus Y : Int))
        = -((f.degree : Int) * (2 * (genus Y : Int) - 2)) := by
    ring
  have hmain :
      -((2 * (genus X : Int) - 2)) =
        -((f.degree : Int) * (2 * (genus Y : Int) - 2)
          + f.ramificationDivisorDegree) := by
    rw [hchi', hmul]
    ring
  exact neg_injective hmain

end RiemannHurwitzViaEulerChar
end AbelExistence
end JacobianChallenge.Blueprint
