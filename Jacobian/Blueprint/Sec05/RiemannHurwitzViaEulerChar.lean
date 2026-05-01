import Jacobian.Blueprint.Sec05.RiemannHurwitzDeg1

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

* `euler_char_eq_two_minus_two_genus` (**HARD**, `sorry`) — (1).
* `euler_char_branched_cover` (**HARD**, `sorry`) — (2).
* `riemann_hurwitz_chi_form` (**SHORT**, sorry-free assembly) —
  (2) restated with `χ(Y) = 2 − 2 g_Y` substituted in. Discharged
  by `rw` + reflexivity.
* `riemann_hurwitz_via_euler_char` (**MEDIUM**, `sorry`) — the
  full genus-form (3). Bridging the chi-form to the genus-form
  requires a ring step
  (`d · (2 − 2 g_Y) = −(d · (2 g_Y − 2))`) that is beyond core
  Lean's `omega`; production-side this uses `ring`/`linear_combination`.

The two assembly leaves give an alternative *proof structure* for
the HARD-classified `RiemannHurwitzDeg1.riemann_hurwitz_formula`
sorry: leaves (1) and (2) jointly imply the formula.

## Conventions

* No Mathlib imports — the only import is the sibling Sec05 stub
  for `genus`, `SurfaceMap`, `ramificationDivisorDegree`.
* Helpers nested under
  `JacobianChallenge.Blueprint.AbelExistence.RiemannHurwitzViaEulerChar`
  to keep the namespace flat at the umbrella level. -/

namespace JacobianChallenge.Blueprint
namespace AbelExistence
namespace RiemannHurwitzViaEulerChar

open RiemannHurwitzDeg1

/-! ## Supporting placeholder

`eulerChar X` is the Euler characteristic of `X`. The eventual
production target is the Euler characteristic of the underlying
2-manifold (`Mathlib.AlgebraicTopology.SimplicialSet`'s χ-invariant,
or the alternating sum of Betti numbers via
`Mathlib.Topology.Homotopy`/`Mathlib.AlgebraicTopology`). For the
deg-1 specialisation `χ = 2 − 2g` already suffices, so we keep
this stub a plain `Int`. -/

/-- Placeholder for the Euler characteristic of a compact connected
Riemann surface. The eventual real definition is
`χ(X) := dim H⁰(X) − dim H¹(X) + dim H²(X)` (the alternating sum
of Betti numbers); for a compact orientable 2-manifold this
agrees with `2 − 2g`. -/
def eulerChar (_X : Type) : Int := 0

/-! ## Sub-leaves -/

/-- **Sub-leaf 1 (HARD).** Euler–Poincaré formula:
`χ(X) = 2 − 2 g_X` for a compact connected Riemann surface `X`.

**Proof sketch.** Triangulate `X` as a compact orientable
2-manifold and apply Euler–Poincaré: `V − E + F = 2 − 2 g`.
Mathlib hooks: triangulation of compact 2-manifolds (absent),
genus-via-Betti-numbers identity (absent — `b₁ = 2g` for
compact orientable surfaces). -/
theorem euler_char_eq_two_minus_two_genus (X : Type) :
    eulerChar X = 2 - 2 * (genus X : Int) := by
  sorry

/-- **Sub-leaf 2 (HARD).** Branched-cover Euler-characteristic
identity: for `f : X → Y` of degree `d` with ramification divisor
`R`, `χ(X) = d · χ(Y) − deg R`.

**Proof sketch.** Pick a triangulation of `Y` containing the
branch locus among its vertices. Lift each cell to `X`: 1-cells
and 2-cells lift to `d` cells each (covering is unbranched away
from the branch points), while a vertex `q ∈ Y` lifts to
`|f⁻¹(q)| = d − (∑_{p ∈ f⁻¹(q)} (e_p − 1))` vertices. Summing
across the branch locus gives the defect `−deg R`. Mathlib hooks:
lift of CW structure under a branched cover (absent), local
ramification index theory (cf. sec02 `def:branched-degree` and
`thm:degree-one-no-ramification`). -/
theorem euler_char_branched_cover
    (X Y : Type) (f : SurfaceMap X Y) :
    eulerChar X
      = (f.degree : Int) * eulerChar Y - f.ramificationDivisorDegree := by
  sorry

/-- **Sub-leaf 3a (SHORT, sorry-free assembly).** Chi-form
Riemann–Hurwitz with `χ(Y)` substituted by `2 − 2 g_Y`:

  `χ(X) = d · (2 − 2 g_Y) − deg R`.

**Proof.** Rewrite leaf 2 via leaf 1 applied to `Y`. -/
theorem riemann_hurwitz_chi_form
    (X Y : Type) (f : SurfaceMap X Y) :
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
(`χ(X) = 2 − 2 g_X`), then rearrange. The remaining bridge from
`d · (2 − 2 g_Y) − R` to `d · (2 g_Y − 2) + R` is a ring step:
`d · (2 − 2 g_Y) = −(d · (2 g_Y − 2))`. Beyond core Lean's
`omega` (which treats `d · (2 − 2 g_Y)` and `d · (2 g_Y − 2)` as
unrelated nonlinear atoms); production-side this uses `ring` /
`linear_combination`. Left as `sorry` here to keep the file
Mathlib-free. -/
theorem riemann_hurwitz_via_euler_char
    (X Y : Type) (f : SurfaceMap X Y) :
    (2 : Int) * (genus X : Int) - 2 =
      (f.degree : Int) * (2 * (genus Y : Int) - 2)
        + f.ramificationDivisorDegree := by
  sorry

end RiemannHurwitzViaEulerChar
end AbelExistence
end JacobianChallenge.Blueprint
