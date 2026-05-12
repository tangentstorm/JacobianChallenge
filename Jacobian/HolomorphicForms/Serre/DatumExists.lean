import Jacobian.HolomorphicForms.Serre.CanonicalDual
import Jacobian.HolomorphicForms.Serre.Datum
import Jacobian.HolomorphicForms.Serre.Pairing
import Jacobian.HolomorphicForms.Serre.Nondegeneracy
import Jacobian.Periods.TrivializationContinuousLinearMapAt

/-!
# Existence of the Serre-duality datum on the canonical dual (frontier)

Frontier theorem: for every abelian sheaf `F` on a compact Riemann
surface `X`, the canonical dual sheaf `serreDualSheaf X F` admits a
`SerreDualityRSDatum` (pairing + nondegeneracy).

This is the existential content of Serre duality, packaged as a
single sorry for round 2's refinement of `serre_duality_rs`. Round 3
will refine the body further into separate `pairing` and
`nondegenerate_{left,right}` obligations.
-/

namespace JacobianChallenge.HolomorphicForms

open scoped Manifold
open CategoryTheory

-- The structure `SerreDualityRSDatum` is declared in
-- `Jacobian/HolomorphicForms/Serre/Datum.lean`; we re-state the
-- existence claim here in terms of the canonical Serre-dual sheaf.
section
variable (X : Type*) [TopologicalSpace X] [CompactSpace X] [T2Space X]
  [ChartedSpace ℂ X]
  [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X]
  [JacobianChallenge.Periods.StableChartAt ℂ X]
  [HasSheafify (Opens.grothendieckTopology (TopCat.of X)) AddCommGrpCat.{0}]
  [HasExt.{0} (Sheaf (Opens.grothendieckTopology (TopCat.of X)) AddCommGrpCat.{0})]

/-- **Refined (round 3).** Existence of the Serre-duality datum on
the canonical dual `Hom(F, K_X)` is assembled from three named
obligations:

* `serrePairing X F` — the `ℂ`-bilinear pairing,
* `serrePairing_nondegenerate_left X F` — left nondegeneracy,
* `serrePairing_nondegenerate_right X F` — right nondegeneracy.

Each is itself a frontier sorry pinned to a downstream refinement
(round 4 and rounds 11/12).

The `letI`s thread through the frontier `Module ℂ` instances from
`CanonicalDual.lean`. -/
theorem serre_datum_for_canonical_dual_exists (F : RSAbSheaf X)
    [letI := serreDualSheaf_module_H0 X F
     Subsingleton (RSSheafCohomology X F 0)]
    [letI := serreDualSheaf_module_H1 X F
     Subsingleton (RSSheafCohomology X (serreDualSheaf X F) 1)] :
    letI := serreDualSheaf_module_H0 X F
    letI := serreDualSheaf_module_H1 X F
    Nonempty (
      JacobianChallenge.HolomorphicForms.SerreDualityRSDatum X F
        (serreDualSheaf X F)) :=
  letI := serreDualSheaf_module_H0 X F
  letI := serreDualSheaf_module_H1 X F
  ⟨{ pairing := serrePairing X F
     nondegenerate_left := serrePairing_nondegenerate_left X F
     nondegenerate_right := serrePairing_nondegenerate_right X F }⟩

end

end JacobianChallenge.HolomorphicForms
