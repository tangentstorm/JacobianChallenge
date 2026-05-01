import Jacobian.HolomorphicForms.SheafCohomologyRS

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

/-- **Frontier `def` (sorry).** The dualizing sheaf `K_X` on a
topological space `X`, viewed as an abelian sheaf via the project's
`RSAbSheaf` alias. Classically `K_X` is the sheaf of holomorphic
1-forms; making this concrete in Lean requires locally-free
`𝒪_X`-modules, which are ABSENT in Mathlib v4.28.0. -/
noncomputable def RSDualizingSheaf (X : Type*) [TopologicalSpace X] :
    RSAbSheaf X :=
  sorry

/-- **Frontier structure.** Serre duality datum for a single abelian
sheaf `F` on a compact Riemann surface `X`, against a fixed candidate
dual sheaf `Fᵛ` (which classically is `F^∨ ⊗ K_X`).

Records the abstract data — pairing and nondegeneracy — needed to
state Riemann-Roch / Serre-pairing-style consequences without
committing to an explicit construction. Once coherent analytic
sheaves land in Mathlib (or via an ad-hoc argument for specific
sheaves), an inhabitant of this structure can be supplied and the
downstream machinery snaps together.

The `[Module ℂ ...]` instances on `H⁰(X, F)` and `H¹(X, Fᵛ)` are
required to talk about ℂ-linear pairings — they are not
auto-derivable from `Sheaf.H`'s `AddCommGroup`-only structure
(see `FiniteDimensionalSheafCohomologyRS`'s docstring).

Both nondegeneracy axioms are recorded in the conventional "left/right
radical is trivial" form. -/
structure SerreDualityRSDatum
    (X : Type*) [TopologicalSpace X] [CompactSpace X] [T2Space X]
    [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X]
    [HasSheafify (Opens.grothendieckTopology (TopCat.of X)) AddCommGrpCat.{0}]
    [HasExt.{0} (Sheaf (Opens.grothendieckTopology (TopCat.of X)) AddCommGrpCat.{0})]
    (F dualSheaf : RSAbSheaf X)
    [Module ℂ (RSSheafCohomology X F 0)]
    [Module ℂ (RSSheafCohomology X dualSheaf 1)] where
  /-- The Serre pairing `H⁰(X, F) × H¹(X, Fᵛ ⊗ K_X) → ℂ`. -/
  pairing :
    RSSheafCohomology X F 0 →ₗ[ℂ] RSSheafCohomology X dualSheaf 1 →ₗ[ℂ] ℂ
  /-- The pairing is nondegenerate on the left: a class in `H⁰(X, F)`
  pairing trivially with every class in `H¹(X, Fᵛ ⊗ K_X)` is zero. -/
  nondegenerate_left :
    ∀ a : RSSheafCohomology X F 0,
      (∀ b : RSSheafCohomology X dualSheaf 1, pairing a b = 0) → a = 0
  /-- The pairing is nondegenerate on the right: a class in
  `H¹(X, Fᵛ ⊗ K_X)` paired trivially with every class in `H⁰(X, F)`
  is zero. -/
  nondegenerate_right :
    ∀ b : RSSheafCohomology X dualSheaf 1,
      (∀ a : RSSheafCohomology X F 0, pairing a b = 0) → b = 0

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
  sorry

end JacobianChallenge.HolomorphicForms
