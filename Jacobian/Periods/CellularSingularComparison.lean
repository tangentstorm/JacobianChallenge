import Jacobian.Periods.CellularChainComplex
import Jacobian.Periods.IntegralOneCycle
import Mathlib.Geometry.Manifold.IsManifold.Basic
import Mathlib.Analysis.Complex.Basic

/-!
# Cellular ↔ singular comparison (degree 1, frontier sub-sorry)

This file contains the **single named sub-sorry** that, together with
the Radó-triangulation sub-sorry inside
`compactRiemannSurface_hasFiniteCWStructure`, is the only residue of
the original umbrella obligation
`cellularH1_finite_singularIsoData`.

## The residual obligation

Given a finite CW structure on a compact connected complex 1-manifold
`X` (i.e. a Riemann surface), the cellular `H₁` and the singular `H₁`
are `ℤ`-linearly isomorphic (Hatcher, *Algebraic Topology*,
Theorem 2.35).

We cast this as the existence of a `ℤ`-linear isomorphism between the
finite-free witness `CellularH1Witness cw` and `IntegralOneCycle X`.
The witness type is `Fin (cw.cellCount 1) →₀ ℤ`; in the orientable
surface case `cellCount 1 = 2g` and the iso is the classical
`H₁(Σ_g, ℤ) ≅ ℤ^{2g}` of an orientable closed surface of genus `g`.
For arbitrary CW data the cellular `H₁` would be a quotient
`ker ∂₁ / im ∂₂` of free modules; here we encode the degree-one
homology by its rank and isolate the gluing as the iso witness.

## Why this is *strictly weaker* than the umbrella

The umbrella `cellularH1_finite_singularIsoData` asks for an unspecified
witness type `CH1` together with `AddCommGroup`, `Module ℤ`,
`Module.Finite`, `Module.Free` instances, and an iso to
`IntegralOneCycle X`.  Here we have already produced the witness type
(`CellularH1Witness cw`), proven its `AddCommGroup`/`Module ℤ`
(definitional) and `Module.Finite`/`Module.Free` (from the `Finsupp`
model in `CellularChainComplex.lean`), so only the iso remains.

## Mathlib gap

`AlgebraicTopology.singularHomologyFunctor` is defined, but Mathlib
v4.28.0 does *not* have the cellular chain complex of a CW complex,
nor a comparison natural transformation to the singular chain complex,
nor the spectral-sequence / long-exact-sequence arguments that prove
the comparison is a quasi-isomorphism (Hatcher §2.2 Theorem 2.35).
This is one of the project's named "big classical inputs".
-/

namespace JacobianChallenge.Periods

open scoped Manifold

/-- **Frontier sub-sorry (cellular ↔ singular comparison, degree 1).**

For any finite CW structure `cw` on a compact connected complex
1-manifold `X`, the cellular `H₁` witness type
`CellularH1Witness cw = Fin (cw.cellCount 1) →₀ ℤ` is `ℤ`-linearly
isomorphic to the singular `H₁` `IntegralOneCycle X`.

This is the cellular ↔ singular comparison theorem
(Hatcher, *Algebraic Topology*, Theorem 2.35) at degree 1, restricted
to the surface case.

**Status (v4.28.0):** sub-sorry. Mathlib has neither the cellular
chain complex of a CW complex nor the long-exact-sequence comparison
argument. -/
theorem cellularH1Witness_iso_integralOneCycle
    (X : Type) [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X]
    (cw : FiniteCWStructure X) :
    Nonempty (CellularH1Witness cw ≃ₗ[ℤ] IntegralOneCycle X) := by
  sorry

end JacobianChallenge.Periods
