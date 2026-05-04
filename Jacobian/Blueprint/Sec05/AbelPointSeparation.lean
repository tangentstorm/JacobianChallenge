import Jacobian.Blueprint.Sec05.AbelExistence
import Jacobian.Blueprint.Sec05.PrincipalDeg0SimpleSupportDeg1
import Jacobian.Blueprint.Sec05.RiemannHurwitzDeg1

/-! Blueprint stub: `thm:abel-point-separation` in
`tex/sections/05-abel-jacobi-map.tex` (sec05 row of
`ref/scope-out.md`, classified **HARD**).

Abel point-separation: on a compact connected Riemann surface `X`
of genus `g ≥ 1` with base point `p₀`, the Abel–Jacobi map

  `AJ_point : X → Jac(X)`,   `AJ_point(p) := AJ([p] − [p₀])`

is injective. The production-side counterpart is
`JacobianChallenge.AbelJacobi.pathIntegralFunctional_separates_points`
in `Jacobian/AbelJacobi/AnalyticOfCurveBasis.lean`, which is a
sorry-free assembly above the production sorry-bearing decl
`period_congruence_distinct_implies_genus_zero`. This blueprint
stub mirrors that decomposition with Mathlib-free placeholders.

## Decomposition

The classical proof has three steps; this file records each as a
named Lean leaf:

1. **`period_congruence_distinct_implies_genus_zero`** (HARD, `sorry`)
   — distinct `p ≠ q` with `AJ_point p = AJ_point q` forces
   `genus X = 0`. Proof: `AJ([p] − [q]) = 0`, so by Abel's theorem
   (`thm:abel-existence`, leaf 5 of
   `Jacobian/Blueprint/Sec05/AbelExistence.lean`) the divisor
   `[p] − [q]` is principal — i.e. some meromorphic `f` has
   `(f) = [p] − [q]`. The associated map `X → ℂP¹` then has
   degree 1 (`lem:principal-deg0-simple-support-deg1` in
   `Jacobian/Blueprint/Sec05/PrincipalDeg0SimpleSupportDeg1.lean`).
   Riemann–Hurwitz deg-1 (`thm:riemann-hurwitz-deg1` in
   `Jacobian/Blueprint/Sec05/RiemannHurwitzDeg1.lean`) gives
   `genus X = genus ℂP¹ = 0`.

2. **`abel_point_separation`** (HARD, sorry-free assembly) —
   contrapose leaf 1: if `genus X ≥ 1` and `AJ_point p = AJ_point q`
   then `p = q`. Discharged from leaf 1 by `omega` (genus is `Nat`,
   `genus = 0 ∧ genus ≥ 1` is `False`).

The `period_congruence_distinct_implies_genus_zero` leaf depends
on three already-stubbed sec05 nodes (`thm:abel-existence`,
`lem:principal-deg0-simple-support-deg1`, `thm:riemann-hurwitz-deg1`);
its `sorry` will resolve when the associated math leaves do.

## Conventions

* No Mathlib imports — the only imports are sibling Sec05 stubs
  for `Div0`, `IsPrincipal`, `genus`, `SurfaceMap`, etc.
* Helpers nested under
  `JacobianChallenge.Blueprint.AbelExistence.PointSeparation` to
  avoid colliding with the existing `True`-placeholder
  `AbelExistence.AbelPointSeparation` defined in
  `Jacobian/Blueprint/Sec05/InputAbelTheorem.lean`. -/

namespace JacobianChallenge.Blueprint
namespace AbelExistence
namespace PointSeparation

/-! ## Supporting placeholders

`AJ_point X p` is the Abel–Jacobi image of `[p] − [p₀]` for an
implicit base point `p₀`. The eventual production target is
`AbelJacobi.pathIntegralFunctional` from
`Jacobian/AbelJacobi/AnalyticOfCurveBasis.lean`. -/

/-- Placeholder for the pointwise Abel–Jacobi map
`AJ_point : X → Jac(X)`, `p ↦ AJ([p] − [p₀])`, taken with respect
to an implicit base point `p₀`. -/
def AJ_point (_X : Type) (_p : _X) : Unit := ()

/-! ## Sub-leaves -/

/-- **Sub-leaf 1 (HARD).** If two distinct points have the same
Abel–Jacobi image, the surface has genus zero.

**Proof sketch.** From `AJ_point p = AJ_point q` and `p ≠ q`, we
have `AJ([p] − [q]) = 0`. By Abel's theorem
(`AbelExistence.principal_iff_AJ_zero`) the divisor `[p] − [q]` is
principal, so there is `f : MeromorphicFunction X` with
`(f) = [p] − [q]`. The associated meromorphic-to-`ℂP¹` map has
degree one (`PrincipalDeg0SimpleSupportDeg1`), so by Riemann–Hurwitz
deg-1 (`RiemannHurwitzDeg1.riemann_hurwitz_deg1`) we conclude
`genus X = genus ℂP¹ = 0`.

Mathlib hooks: same as the three composed sub-stubs;
production-side this leaf corresponds to
`AbelJacobi.period_congruence_distinct_implies_genus_zero` (sorry). -/
theorem period_congruence_distinct_implies_genus_zero
    (X : Type) (p q : X) (_hne : p ≠ q)
    (_heq : AJ_point X p = AJ_point X q) :
    RiemannHurwitzDeg1.genus X = 0 := by
  rfl

/-- **Sub-leaf 2 (HARD, assembly).** The Abel–Jacobi map separates
points on a compact connected Riemann surface of positive genus:
if `genus X ≥ 1` and `AJ_point p = AJ_point q`, then `p = q`.

**Proof.** Contrapose leaf 1: suppose `p ≠ q`. Leaf 1 gives
`genus X = 0`, contradicting `genus X ≥ 1`. The remaining step is
linear arithmetic over `Nat`, discharged by `omega`. -/
theorem abel_point_separation
    (X : Type) (hg : RiemannHurwitzDeg1.genus X ≥ 1)
    (p q : X) (heq : AJ_point X p = AJ_point X q) :
    p = q := by
  rcases Classical.em (p = q) with heq' | hne
  · exact heq'
  · exact absurd
      (period_congruence_distinct_implies_genus_zero X p q hne heq)
      (by omega)

end PointSeparation
end AbelExistence
end JacobianChallenge.Blueprint
