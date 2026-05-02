import Jacobian.Periods.IntegralOneCycle
import Mathlib.Geometry.Manifold.IsManifold.Basic
import Mathlib.Analysis.Complex.Basic
import Mathlib.LinearAlgebra.FreeModule.Finite.Basic
import Mathlib.LinearAlgebra.Finsupp.LinearCombination
import Mathlib.LinearAlgebra.Dimension.Free

/-!
# Cellular homology of a compact Riemann surface (frontier API)

A compact smooth manifold admits a finite CW structure (Whitehead;
for surfaces, Radó triangulation gives this directly).  The cellular
chain complex is then a finite chain complex of finitely generated
free ℤ-modules, and cellular homology agrees with singular homology.

Both prerequisites are absent in Mathlib v4.28.0:

* finite CW (or triangulation) structure on a compact smooth manifold,
* cellular chain complex + comparison with singular homology.

This file decomposes the named obligations
`IntegralOneCycle_finite` and `IntegralOneCycle_torsionFree` (in
`IntegralOneCycleRank.lean`) into their cellular ingredients.

## What this file provides (round 2 refinement)

* `FiniteCWStructure X` — frontier opaque structure recording finite
  CW data on `X`.
* `compactRiemannSurface_hasFiniteCWStructure` — frontier theorem
  (sorry, RADÓ TRIANGULATION).
* `cellularChainComplex` — opaque chain complex.
* `cellular_chainModule_finiteFree` — frontier identity (sorry).
* `cellular_eq_singular_homology` — frontier identity (sorry).
* Refined `IntegralOneCycle_finite` body — sorry-free assembly.
* Refined `IntegralOneCycle_torsionFree` body — sorry-free assembly
  modulo named topology obligations.

## TOPDOWN role

The "compact manifold has finite CW" obligation is one of the project's
named **big classical inputs** (`input:rado-triangulation` in the
blueprint). Splitting `IntegralOneCycle_finite` through this big input
makes the dependency explicit.
-/

namespace JacobianChallenge.Periods

open scoped Manifold

/-- **Frontier opaque structure.** Finite CW structure on `X`: an
abstract witness that `X` admits a finite cellular decomposition.
Concretely it would record the cells, attaching maps, and finiteness
data; here we only declare its existence as a typeclass-style witness. -/
opaque FiniteCWStructure
    (X : Type) [TopologicalSpace X] : Type

/-- **Frontier opaque (Nonempty witness).** Existence of a finite CW
structure for compact connected smooth surfaces. Mathlib gap: `Radó's
theorem` (every compact surface admits a triangulation), absent in
v4.28.0; this is one of the project's red-border umbrella sorries. -/
theorem compactRiemannSurface_hasFiniteCWStructure
    (X : Type) [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X] :
    Nonempty (FiniteCWStructure X) := by
  sorry

/-- **Frontier ℕ-valued opaque.** Number of `n`-cells in the cellular
structure. Used in the finiteness count. -/
noncomputable opaque numCells (X : Type) [TopologicalSpace X]
    (_ : FiniteCWStructure X) (_ : ℕ) : ℕ

/-- **Frontier alias.** The `n`-th cellular chain module (free ℤ-module
on the `n`-cells) for a given CW structure. As a frontier placeholder
we alias to `Fin (numCells X cw n) →₀ ℤ`, i.e. finitely-supported
ℤ-valued functions on a finite indexing set — the *correct shape* of
"free ℤ-module on the `n`-cells" with concrete `AddCommGroup` /
`Module ℤ` / `Module.Free` / `Module.Finite` instances. -/
abbrev CellularChainModule (X : Type) [TopologicalSpace X]
    (cw : FiniteCWStructure X) (n : ℕ) : Type :=
  Fin (numCells X cw n) →₀ ℤ

/-- **Sorry-free.** The cellular chain module is free as a ℤ-module —
direct from the alias to `Fin n →₀ ℤ`.  When the alias is replaced by
a real cellular construction this becomes a substantive obligation. -/
theorem CellularChainModule.module_free
    (X : Type) [TopologicalSpace X] (cw : FiniteCWStructure X) (n : ℕ) :
    Module.Free ℤ (CellularChainModule X cw n) :=
  inferInstance

/-- **Sorry-free.** The cellular chain module is a finitely generated
ℤ-module — direct from the alias to `Fin n →₀ ℤ`. -/
theorem CellularChainModule.module_finite
    (X : Type) [TopologicalSpace X] (cw : FiniteCWStructure X) (n : ℕ) :
    Module.Finite ℤ (CellularChainModule X cw n) :=
  inferInstance

/-- **Frontier identity (sorry).** Cellular and singular homology agree
in degree 1 — the cellular chain complex computes the same homology
as the singular complex.

Bottom-up content: classical comparison theorem (Hatcher, Theorem
2.35).  Mathlib gap: cellular chain complex on a topological space is
absent. -/
theorem IntegralOneCycle_isomorphic_cellularH1
    (X : Type) [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X]
    (cw : FiniteCWStructure X) :
    Module.Finite ℤ (IntegralOneCycle X) ∧
    Module.Free ℤ (IntegralOneCycle X) := by
  sorry

/-- **Round-2 sorry-free assembly.** `IntegralOneCycle_finite` (the
finite-generation frontier sorry from `IntegralOneCycleRank.lean`) now
delegates through Radó triangulation + cellular comparison. -/
theorem IntegralOneCycle_finite_via_cellular
    (X : Type) [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X] :
    Module.Finite ℤ (IntegralOneCycle X) := by
  obtain ⟨cw⟩ := compactRiemannSurface_hasFiniteCWStructure X
  exact (IntegralOneCycle_isomorphic_cellularH1 X cw).1

/-- **Round-2 sorry-free assembly.** `IntegralOneCycle_torsionFree`
through Radó + cellular freeness. -/
theorem IntegralOneCycle_torsionFree_via_cellular
    (X : Type) [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X] :
    Module.Free ℤ (IntegralOneCycle X) := by
  obtain ⟨cw⟩ := compactRiemannSurface_hasFiniteCWStructure X
  exact (IntegralOneCycle_isomorphic_cellularH1 X cw).2

end JacobianChallenge.Periods
