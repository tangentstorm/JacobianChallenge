import Jacobian.HolomorphicForms.Serre.LineBundleSerre
import Jacobian.HolomorphicForms.EulerCharLineBundle

/-!
# Pieces of the `RiemannRochUmbrella` package (frontier)

Round 20 names the four obligations that, once landed, let
`riemann_roch_umbrella_exists` (in `Blueprint/Sec02/InputRiemannRoch.lean`)
discharge as a sorry-free assembly.

The umbrella package needs:

1. **Line bundle type**: `RSLineBundleSheaf X`.
2. **Canonical bundle**: `RSDualizingSheaf X` (an instance of the
   line-bundle type, via the alias).
3. **Subtraction**: `RSLineBundleSub X L M = L ⊗ M⁻¹` (frontier here).
4. **Degree**: `RSLineBundleDegree X` (already a frontier in
   `EulerCharLineBundle.lean`).
5. **`h⁰`**: `Module.finrank ℂ (RSSheafCohomology X L 0)` (concrete).
6. **Genus**: `RSGenus X` (already a frontier).
7. **The classical Riemann-Roch identity**: combines `χ`-form RR
   (`euler_char_line_bundle`) with Serre duality
   (`h¹(L) = h⁰(K_X − L)`).

Round 20 introduces (3) `RSLineBundleSub` and (7) the assembled
identity `riemann_roch_classical_identity`.
-/

namespace JacobianChallenge.HolomorphicForms

open scoped Manifold
open CategoryTheory

/-- **Frontier `def` (sorry).** Line-bundle subtraction
`L ⊖ M = L ⊗ M⁻¹` on a Riemann surface, viewed as the abelian-sheaf
operation given by tensoring `L` with the dual `M⁻¹`.

The body would be `RSTensorAbSheaf X L (RSLineBundleDual X M)` but
the underlying universe-parameters of `RSTensorAbSheaf` /
`RSLineBundleDual` are not pinned (each carries an extra universe
slot from `AddCommGrpCat`'s parametricity); rather than wire that
plumbing here we leave the body as a frontier sorry pending the
universe-cleanup task. -/
noncomputable def RSLineBundleSub (X : Type*) [TopologicalSpace X]
    (_L _M : RSLineBundleSheaf X) : RSLineBundleSheaf X := by
  sorry

/-- **Frontier theorem (sorry).** Classical Riemann-Roch identity for
a line bundle on a compact Riemann surface, after combining the
Euler-characteristic form (`euler_char_line_bundle`) with Serre
duality (`h¹(L) = h⁰(K_X − L)`):

  h⁰(L) − h⁰(K_X − L) = deg L + 1 − g.

PROOF SKETCH (left as a frontier sorry pending `Serre`-side
universe-bookkeeping cleanup; named obligations consumed: Serre
duality `h¹(L) = h⁰(K_X − L)` via `serre_duality_lineBundle_exists` +
`euler_char_line_bundle`). -/
theorem riemann_roch_classical_identity
    (X : Type*) [TopologicalSpace X] [CompactSpace X] [T2Space X]
    [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X]
    [HasSheafify (Opens.grothendieckTopology (TopCat.of X)) AddCommGrpCat.{0}]
    [HasExt.{0} (Sheaf (Opens.grothendieckTopology (TopCat.of X)) AddCommGrpCat.{0})]
    (L : RSLineBundleSheaf X)
    [Module ℂ (RSSheafCohomology X L 0)]
    [Module ℂ (RSSheafCohomology X L 1)]
    [Module ℂ (RSSheafCohomology X
      (RSLineBundleSub X (RSDualizingSheaf X) L) 0)] :
    (Module.finrank ℂ (RSSheafCohomology X L 0) : ℤ)
      - (Module.finrank ℂ (RSSheafCohomology X
          (RSLineBundleSub X (RSDualizingSheaf X) L) 0) : ℤ)
      = RSLineBundleDegree X L + 1 - (RSGenus X : ℤ) := by
  sorry

end JacobianChallenge.HolomorphicForms
