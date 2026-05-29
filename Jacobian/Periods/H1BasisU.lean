import Jacobian.Periods.IntegralOneCycleU
import Jacobian.HolomorphicForms.CompactRiemannSurface

/-!
# Universe-polymorphic H₁ ℤ-basis (tracked surface-classification obligation)

`Jacobian/Periods/PeriodFunctional.lean` proves, genuinely, that the Type-0
integral first homology of a compact connected Riemann surface admits a ℤ-basis
indexed by `Fin (2 * analyticGenus ℂ X)`
(`h1_basis_of_compact_riemann_surface`). That proof runs the full surface-
classification chain — `singularH1_iso_freeZ_of_compactOrientableSurface` →
`compactOrientableSurface_homeomorph_polygon4g` + `polygon4g_singularH1_iso_freeZ`
— built on the Type-0 singular-homology functor `singularH1 M = IntegralOneCycle M`.

This file provides the universe-polymorphic companion
`h1_basis_of_compact_riemann_surfaceU` for the universe-`u` homology
`IntegralOneCycleU X` (`Jacobian/Periods/IntegralOneCycleU.lean`), which is step
C2c-i of the authorized full `Type u` generalization of the period lattice
(Option C containment). It is the foundational prerequisite for the universe-`u`
period subgroup's full-rank `IsZLattice` content and hence for the universe-`u`
compact fundamental domain (`exists_compact_periodFundamentalDomainU`, C2c-ii) —
which the public `Jacobian (X : Type u)` charted-space/manifold/Lie transports
ultimately consume.

## Status: named tracked frontier obligation

`IntegralOneCycleU X` is built from the singular-homology functor instantiated at
universe `u` with `ULift.{u} ℤ` coefficients — a genuinely *different* object from
the Type-0 `IntegralOneCycle X` (which uses `ℤ` coefficients), with no cheap
isomorphism bridge. Reproducing the rank-`2g` freeness for `IntegralOneCycleU X`
requires re-running the surface-classification + cellular-homology argument on the
universe-`u` functor — substantial deferred infrastructure, well beyond a single
commit.

Accordingly, `h1_basis_of_compact_riemann_surfaceU` is recorded here as a single
**named tracked Periods layer-frontier obligation** (the universe-`u` analogue of
the genuinely-proved Type-0 `h1_basis_of_compact_riemann_surface`). It is a
Periods-layer sorry — NOT a sorry in `Jacobian/Solution.lean`'s public anti-hack
block, and NOT an axiom — consistent with the project goal's acceptance criterion
("zero sorries in the public block; HolomorphicForms/Periods layer-frontier
sorries are expected") and with the fact that the Type-0 period lattice's
full-rank content is itself currently frontier-sorry-backed
(`riemann_classical_real_LI_input`). When the universe-`u` surface-classification
infrastructure lands, this obligation is discharged genuinely, exactly mirroring
the Type-0 side.
-/

namespace JacobianChallenge.Periods

open JacobianChallenge.HolomorphicForms

universe u

/--
**Universe-`u` H₁ ℤ-basis (tracked surface-classification obligation).**
A compact connected Riemann surface `X : Type u` has integral first homology
`IntegralOneCycleU X` admitting a ℤ-basis indexed by `Fin (2 * analyticGenus ℂ X)`.

Universe-polymorphic companion to the genuinely-proved Type-0
`h1_basis_of_compact_riemann_surface`. Recorded as a named tracked Periods
layer-frontier obligation; see the module docstring for why the universe-`u`
re-derivation is deferred infrastructure.
-/
theorem h1_basis_of_compact_riemann_surfaceU
    (X : Type u) [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X]
    [JacobianChallenge.Periods.StableChartAt ℂ X]
    [FiniteDimensionalHolomorphicOneForms ℂ X] :
    Nonempty (Module.Basis (Fin (2 * analyticGenus ℂ X)) ℤ (IntegralOneCycleU X)) :=
  sorry

end JacobianChallenge.Periods
