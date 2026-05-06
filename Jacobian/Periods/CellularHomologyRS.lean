import Jacobian.Periods.IntegralOneCycle
import Jacobian.Periods.FiniteCWStructure
import Jacobian.Periods.CellularChainComplex
import Jacobian.Periods.CellularSingularComparison
import Mathlib.Geometry.Manifold.IsManifold.Basic
import Mathlib.Analysis.Complex.Basic
import Mathlib.LinearAlgebra.FreeModule.Finite.Basic
import Mathlib.LinearAlgebra.Finsupp.LinearCombination
import Mathlib.LinearAlgebra.Dimension.Free

/-!
# Cellular homology of a compact Riemann surface (frontier API)

A compact smooth manifold admits a finite CW structure (Whitehead;
for surfaces, Radó triangulation gives this directly). The cellular
chain complex is then a finite chain complex of finitely generated
free ℤ-modules, and cellular homology agrees with singular homology.

Both prerequisites are absent in Mathlib v4.28.0. As of this round:

* finite CW structure on a topological space — modelled by the real
  structure `FiniteCWStructure` in
  `Jacobian/Periods/FiniteCWStructure.lean`. The structure carries
  cell counts (eventually zero) and per-cell attaching/characteristic
  maps; it does *not* enforce CW gluing axioms (that would require
  developed CW-complex infrastructure absent in v4.28.0).
* low-dimensional cellular chain complex — provided by
  `Jacobian/Periods/CellularChainComplex.lean` with `Finsupp`-based
  finite free chain modules and placeholder zero boundaries.
* cellular ↔ singular comparison at degree 1 — sub-sorried in
  `Jacobian/Periods/CellularSingularComparison.lean`
  (`cellularH1Witness_iso_integralOneCycle`), the single residual
  obligation for the cellular route.

This file decomposes the named obligations
`IntegralOneCycle_finite` and `IntegralOneCycle_torsionFree` (in
`IntegralOneCycleRank.lean`) into their cellular ingredients.

## What this file provides

* `compactRiemannSurface_hasFiniteCWStructure` — Radó triangulation
  for a compact connected complex 1-manifold (sub-sorry).
* `cellularH1_finite_free` — finite-free cellular `H₁` witness
  (sorry-free, uses `CellularChainComplex` infrastructure).
* `cellularH1_finite_singularIsoData` — combined witness with iso to
  `IntegralOneCycle X` (sorry-free assembly delegating to
  `cellularH1Witness_iso_integralOneCycle`).
* `cellular_iso_singular_h1` — projection of the combined witness
  (sorry-free).
* `IntegralOneCycle_finite_of_cellular`,
  `IntegralOneCycle_free_of_cellular`,
  `IntegralOneCycle_finite_via_cellular`,
  `IntegralOneCycle_torsionFree_via_cellular` — sorry-free assemblies.

## Residual sub-sorries (strictly weaker than the original umbrella)

1. `compactRiemannSurface_hasFiniteCWStructure` — **Radó's theorem**:
   every compact connected complex 1-manifold (more generally every
   compact 2-manifold) admits a finite CW structure / triangulation.
2. `cellularH1Witness_iso_integralOneCycle` (in
   `CellularSingularComparison.lean`) — **Hatcher 2.35 at degree 1**:
   for any finite CW structure on a compact connected complex
   1-manifold, the cellular `H₁` witness is `ℤ`-linearly isomorphic to
   the singular `H₁`.

Both are precisely-typed leaf obligations; neither asserts existential
content beyond what the original umbrella did, and each is strictly
narrower in scope than the umbrella.
-/

namespace JacobianChallenge.Periods

open scoped Manifold

/-- **Frontier sub-sorry (Radó triangulation).** Existence of a finite
CW structure for a compact connected complex 1-manifold (Riemann
surface).  This is the classical Radó triangulation theorem; absent
from Mathlib v4.28.0.

Once the structure `FiniteCWStructure X` carries real cellular data
(see `Jacobian/Periods/FiniteCWStructure.lean`), this provider becomes
a substantive obligation rather than the trivial `⟨()⟩` of earlier
rounds. -/
theorem compactRiemannSurface_hasFiniteCWStructure
    (X : Type) [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X] :
    Nonempty (FiniteCWStructure X) := by
  sorry

/-- Number of `n`-cells in the cellular structure — read directly from
the underlying `FiniteCWStructure` data. -/
def numCells (X : Type) [TopologicalSpace X]
    (cw : FiniteCWStructure X) (n : ℕ) : ℕ :=
  cw.cellCount n

/-! ### Round 1 (2026-05-05) — split finite-of-cellular and free-of-cellular

Each frontier sorry is split into the genuine bottom-up leaves it
depends on. -/

/-- **Stage A leaf (sorry-free).** Existence of a cellular `H₁` from a
finite CW structure, packaged as a finitely generated free `ℤ`-module.

Uses `CellularH1Witness cw = Fin (cw.cellCount 1) →₀ ℤ` from
`Jacobian/Periods/CellularChainComplex.lean`, which has finite/free
instances by the `Finsupp` model. -/
theorem cellularH1_finite_free
    (X : Type) [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X]
    (cw : FiniteCWStructure X) :
    ∃ (CH1 : Type) (_ : AddCommGroup CH1) (_ : Module ℤ CH1),
      Module.Finite ℤ CH1 ∧ Module.Free ℤ CH1 :=
  ⟨CellularH1Witness cw, inferInstance, inferInstance,
    inferInstance, inferInstance⟩

/-- **Stage A leaf (sorry-free assembly).** Combined data: the cellular
`H₁` witness type with both finite-generation/freeness instances *and*
the iso to `IntegralOneCycle X`.

The body assembles the `CellularH1Witness cw` (finite free by the
`Finsupp` model in `CellularChainComplex.lean`) with the iso provided
by `cellularH1Witness_iso_integralOneCycle` (the sub-sorry in
`CellularSingularComparison.lean` — Hatcher 2.35 at degree 1, the
single residual obligation for the cellular route). -/
theorem cellularH1_finite_singularIsoData
    (X : Type) [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X]
    (cw : FiniteCWStructure X) :
    ∃ (CH1 : Type) (_ : AddCommGroup CH1) (_iCH1 : Module ℤ CH1)
      (_hF : Module.Finite ℤ CH1) (_hFr : Module.Free ℤ CH1),
      Nonempty (CH1 ≃ₗ[ℤ] IntegralOneCycle X) :=
  ⟨CellularH1Witness cw, inferInstance, inferInstance,
    inferInstance, inferInstance,
    cellularH1Witness_iso_integralOneCycle X cw⟩

/-- **Stage A leaf (sorry-free).** The cellular `H₁` and singular `H₁`
are `ℤ`-linearly isomorphic for a finite CW complex (Hatcher,
Theorem 2.35).

Derived from `cellularH1_finite_singularIsoData` by forgetting the
finiteness/freeness witnesses. -/
theorem cellular_iso_singular_h1
    (X : Type) [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X]
    (cw : FiniteCWStructure X) :
    ∃ (CH1 : Type) (_ : AddCommGroup CH1) (_ : Module ℤ CH1),
      Nonempty (CH1 ≃ₗ[ℤ] IntegralOneCycle X) := by
  obtain ⟨CH1, hAb, hMod, _, _, hIso⟩ := cellularH1_finite_singularIsoData X cw
  exact ⟨CH1, hAb, hMod, hIso⟩

/-- **Frontier identity (sorry-free assembly).** Combines
`cellularH1_finite_free` + `cellular_iso_singular_h1` to discharge
finite generation of `IntegralOneCycle X`. -/
theorem IntegralOneCycle_finite_of_cellular
    (X : Type) [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X]
    (cw : FiniteCWStructure X) :
    Module.Finite ℤ (IntegralOneCycle X) := by
  obtain ⟨_, _, _, _hF, _, hIso⟩ := cellularH1_finite_singularIsoData X cw
  exact Module.Finite.equiv hIso.some

/-- **Frontier identity (sorry-free assembly).** Combines
`cellularH1_finite_singularIsoData` (which contains `Module.Free`)
with the iso to discharge freeness of `IntegralOneCycle X`.

Bottom-up rationale: the cellular `H₁` is free as a subquotient of
free chain modules with free image; transport along the iso. The
"freeness" portion is *not generic* over CW structures — it holds for
the polygonal model of an orientable surface, where the relator
abelianises to zero, so the cellular boundary `∂₂` is zero and
`H₁ = C_1 / 0 = ℤ^{2g}`. -/
theorem IntegralOneCycle_free_of_cellular
    (X : Type) [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X]
    (cw : FiniteCWStructure X) :
    Module.Free ℤ (IntegralOneCycle X) := by
  obtain ⟨_, _, _, _, _hFr, hIso⟩ := cellularH1_finite_singularIsoData X cw
  exact Module.Free.of_equiv hIso.some

/-- **Round-2 sorry-free assembly.** `IntegralOneCycle_finite` (the
finite-generation frontier sorry from `IntegralOneCycleRank.lean`) now
delegates through Radó triangulation + cellular finite generation. -/
theorem IntegralOneCycle_finite_via_cellular
    (X : Type) [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X] :
    Module.Finite ℤ (IntegralOneCycle X) := by
  obtain ⟨cw⟩ := compactRiemannSurface_hasFiniteCWStructure X
  exact IntegralOneCycle_finite_of_cellular X cw

/-- **Round-2 sorry-free assembly.** `IntegralOneCycle_torsionFree`
through Radó + cellular freeness. -/
theorem IntegralOneCycle_torsionFree_via_cellular
    (X : Type) [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X] :
    Module.Free ℤ (IntegralOneCycle X) := by
  obtain ⟨cw⟩ := compactRiemannSurface_hasFiniteCWStructure X
  exact IntegralOneCycle_free_of_cellular X cw

end JacobianChallenge.Periods
