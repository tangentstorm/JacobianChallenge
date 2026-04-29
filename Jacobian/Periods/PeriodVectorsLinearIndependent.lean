/-!
# Gap analysis: ℝ-linear independence of period vectors

This file documents the mathematical prerequisites for
`periodVectors_linearIndependent` (stated in
`Jacobian/Periods/PeriodFunctional.lean`).

## Statement

```
theorem periodVectors_linearIndependent
    (X : Type) [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X] :
    ∃ (b : Fin (2 * analyticGenus ℂ X) → Fin (analyticGenus ℂ X) → ℂ),
      LinearIndependent ℝ b ∧
      ∀ i, b i ∈ ↑(AddSubgroup.map
        (holomorphicOneFormDualEquiv ℂ X).toLinearMap.toAddMonoidHom
        ((periodPairing ℂ X).range))
```

## Dependency tree

### Leaf 1: Homology rank of compact surfaces

**Claim:** For a compact connected Riemann surface `X` of genus `g`,
`H₁(X, ℤ) ≅ ℤ^{2g}` as ℤ-modules.

**Mathlib status (v4.28.0):** `singularHomologyFunctor` exists and is
functorial, but no computation of `H_n` for any specific space is
available. In particular, `H₁(S_g, ℤ) ≅ ℤ^{2g}` for the genus-`g`
surface is absent.

**What's needed:**
- Either a CW-decomposition–based computation (cell complex of the
  standard genus-`g` surface, cellular homology ≅ singular homology),
  or a Mayer–Vietoris argument.
- A proof that the abstract `IntegralOneCycle X` (= `H₁(X, ℤ)` from
  Mathlib's `singularHomologyFunctor`) has a ℤ-basis of cardinality
  `2 * analyticGenus ℂ X`. This also requires the topological genus
  to agree with the analytic genus (Riemann–Roch).

### Leaf 2: Period pairing implementation

**Claim:** `periodPairing ℂ X` actually computes `∫_σ ω`.

**Mathlib status (v4.28.0):** Currently `opaque`. Requires:
- Multi-chart path integration (lifting a path through chart
  boundaries; the single-chart version exists in
  `PathIntegralChart.lean`).
- ℤ-linearity in the cycle variable (sum of path integrals).
- Well-definedness modulo boundaries (Stokes' theorem for 1-forms
  on manifolds — absent in Mathlib).

### Leaf 3: Riemann bilinear relations

**Claim:** For a symplectic basis `{α_i, β_i}` of `H₁(X,ℤ)` and the
normalised basis `{ω_j}` of `H⁰(X, Ω¹)` satisfying
`∫_{α_i} ω_j = δ_{ij}`, the period matrix `τ_{ij} = ∫_{β_i} ω_j`
satisfies:
1. `τ` is symmetric: `τ_{ij} = τ_{ji}`.
2. `Im(τ)` is positive-definite.

Consequence: the `2g` period vectors
  `(δ_{1j}, …, δ_{gj})` for `j = 1,…,g`   (from α-cycles)
  `(τ_{1j}, …, τ_{gj})` for `j = 1,…,g`   (from β-cycles)
are ℝ-linearly independent in `ℂ^g ≅ ℝ^{2g}`.

**Proof sketch for Im(τ) > 0:**
For any nonzero `ω = Σ c_j ω_j`, the Riemann bilinear identity gives
  `∫_X ω ∧ ω̄ = 2i · c^* · Im(τ) · c`
and the Kähler identity `∫_X ω ∧ ω̄ = 2i ∫_X |ω|² dA > 0` (for
`ω ≠ 0`) shows `Im(τ)` is positive-definite.

**Mathlib status (v4.28.0):** None of these ingredients exist:
- Wedge product of differential forms on manifolds.
- The Riemann bilinear identity (Stokes on the polygon model).
- Kähler metric / Hodge theory on Riemann surfaces.

## Summary

The three leaves are independent of each other and each represents a
substantial formalisation effort:

| Leaf | Estimated difficulty | Key missing Mathlib piece |
|------|---------------------|--------------------------|
| Homology rank | Medium | Cellular/singular isomorphism, CW structure of surfaces |
| Period pairing | Medium–Hard | Multi-chart integration, Stokes for 1-forms |
| Riemann bilinear | Hard | Wedge products, Kähler geometry, Stokes on polygon |

The assembly from these three leaves to `periodVectors_linearIndependent`
is straightforward linear algebra (transport through the basis-aligned
dual equivalence preserves linear independence).
-/
