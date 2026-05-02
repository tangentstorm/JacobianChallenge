import Jacobian.HolomorphicForms.SheafCohomologyRS
import Jacobian.HolomorphicForms.Serre.CotangentSheaf
import Jacobian.HolomorphicForms.Serre.DualizingSheaf
import Jacobian.HolomorphicForms.Serre.Datum
import Jacobian.HolomorphicForms.Serre.DatumExists

/-!
# Serre duality on a compact Riemann surface (project API layer)

Frontier statement of Serre duality for abelian sheaves on a compact
Riemann surface. The classical content is that for a coherent
analytic sheaf `F` on a compact Riemann surface `X` of genus `g`,
there is a perfect pairing

  Hᵍ(X, F) ⊗_ℂ H^{1-q}(X, Fᵛ ⊗ K_X) → H¹(X, K_X) ≃ ℂ

where `K_X` is the dualizing sheaf (= sheaf of holomorphic 1-forms in
the 1-dimensional case) and `Fᵛ` is the dual `𝒪_X`-module sheaf.

## Mathlib v4.28.0 status

Per `ref/plans/sheaf-cohomology-rs.md` §2 inventory, **all three**
analytic-side ingredients are ABSENT:

* the analytic structure sheaf `𝒪_X`,
* coherent analytic sheaves and their `Hom` / dual,
* the finite-dimensionality / duality theorem for `H^q` on a compact
  Riemann surface.

We therefore expose Serre duality as a **frontier theorem with a
sorry proof** plus a **frontier class** packaging the abstract Serre
datum (dualizing sheaf, pairing, nondegeneracy). Downstream consumers
(Riemann-Roch, period reciprocity, Abel-Jacobi torsor) can either:

* assume `[SerreDualityRSDatum X F]` as a hypothesis and reason
  parametrically, or
* invoke `serre_duality_rs` (sorry-bearing) when they want the
  bare existence claim and accept the upstream sorry.

Both paths cleanly accommodate landing the analytic-sheaf machinery
later: discharging the `sorry` and providing the canonical
`SerreDualityRSDatum` instance for coherent sheaves becomes a
self-contained piece of work that does not require touching this
file's downstream consumers.

## What this file provides (this round)

* `RSDualizingSheaf X` — frontier `def` for the dualizing sheaf
  `K_X` on `X`. Body is `sorry` because the canonical realisation
  (sheaf of holomorphic 1-forms / cotangent sheaf) requires
  locally-free `𝒪_X`-modules.
* `SerreDualityRSDatum X F` — frontier class bundling the abstract
  data of Serre duality for an individual sheaf `F`: the dual
  sheaf, the perfect pairing, and the nondegeneracy axiom.
  (No sorry; just the definition.)
* `serre_duality_rs X F` — frontier theorem asserting existence of
  a `SerreDualityRSDatum`. Body is `sorry`.

What is **not** provided: explicit construction of any of these for
specific sheaves, the cup-product / trace map underlying the
pairing, or the Hodge decomposition. Those belong to follow-up
nodes (`thm:euler-char-line-bundle`, `input:riemann-roch`,
`thm:bilinear-from-stokes`).
-/

namespace JacobianChallenge.HolomorphicForms

open CategoryTheory

-- `RSDualizingSheaf` is declared in
-- `Jacobian/HolomorphicForms/Serre/DualizingSheaf.lean` (round 1
-- refinement: delegates to `RSCotangentSheaf`). The original public
-- name is preserved verbatim through the namespace.

-- The structure `SerreDualityRSDatum` is now declared in
-- `Jacobian/HolomorphicForms/Serre/Datum.lean` to break the import
-- cycle introduced by the round-2/round-3 refinement. The original
-- public name `JacobianChallenge.HolomorphicForms.SerreDualityRSDatum`
-- is preserved verbatim.

/-- **Frontier theorem (sorry).** Serre duality on a compact Riemann
surface: every abelian sheaf admits a Serre duality datum against
some dual sheaf, with associated ℂ-vector-space structures on the
relevant cohomology groups.

This is the existence form expected from classical RS theory; the
proof is `sorry` here because every analytic-sheaf prerequisite
(coherent sheaves, dual `𝒪_X`-module, cup product into the
dualizing sheaf, nondegeneracy via Hodge / Dolbeault) is ABSENT in
Mathlib v4.28.0. Discharging the sorry is a downstream task that
will require landing those prerequisites first. -/
theorem serre_duality_rs
    (X : Type*) [TopologicalSpace X] [CompactSpace X] [T2Space X]
    [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X]
    [HasSheafify (Opens.grothendieckTopology (TopCat.of X)) AddCommGrpCat.{0}]
    [HasExt.{0} (Sheaf (Opens.grothendieckTopology (TopCat.of X)) AddCommGrpCat.{0})]
    (F : RSAbSheaf X) :
    ∃ (dualSheaf : RSAbSheaf X)
      (_ : Module ℂ (RSSheafCohomology X F 0))
      (_ : Module ℂ (RSSheafCohomology X dualSheaf 1)),
      Nonempty (SerreDualityRSDatum X F dualSheaf) := by
  refine ⟨serreDualSheaf X F, serreDualSheaf_module_H0 X F,
          serreDualSheaf_module_H1 X F, ?_⟩
  exact serre_datum_for_canonical_dual_exists X F

end JacobianChallenge.HolomorphicForms
