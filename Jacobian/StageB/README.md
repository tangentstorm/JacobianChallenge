# Stage B — Bottom-up infrastructure sketch

This directory contains stub sketches of the **bottom-up** Lean
infrastructure that Stage B of the polygonal-model proof needs:
the analytic / geometric content connecting `analyticGenus ℂ X` to
`rank_ℤ H_1(X, ℤ)` for compact connected Riemann surfaces.

## Files

| File | Topic | LOC | Mathlib gap |
|---|---|---|---|
| `DifferentialForms.lean` | Smooth `Ω^k(M)`, exterior derivative `d`, wedge, pullback, integration | ~125 | Partial — `MFDeriv` exists, bundled forms absent |
| `DeRhamComplex.lean` | de Rham cochain complex `Ω^*(M, ℝ)` and cohomology `H^*_dR(M, ℝ)`/`H^*_dR(M, ℂ)` | ~135 | Total absence |
| `DeRhamComparison.lean` | de Rham theorem: `H^k_dR(M, ℂ) ≅ H^k_sing(M, ℂ)` via integration | ~140 | Total absence |
| `LaplaceBeltrami.lean` | Riemannian metric, Hodge star, codifferential, Δ = dδ + δd, self-adjointness | ~130 | Total absence |
| `HarmonicForms.lean` | Harmonic forms, elliptic regularity, Hodge decomposition, Poincaré duality | ~95 | Total absence |
| `KahlerStructure.lean` | Kähler manifolds, Dolbeault `(p,q)` decomposition, Hodge symmetry | ~130 | Total absence |
| `CoherentSheaves.lean` | Structure sheaf `𝒪_X`, canonical sheaf `Ω¹_X`, sheaf cohomology, Cartan–Serre finiteness, Dolbeault iso | ~105 | Total absence |
| `SerreDuality.lean` | Trace map, cup-product / Yoneda pairing, non-degeneracy, dim consequence | ~100 | Total absence |

Each file is a **sketch** — every theorem is `sorry`, but the
statement-level shape, the named obligations, and the proof-route
documentation are committed to. A full Lean implementation of the
bottom-up content would be ~2000-4000 LOC (these stubs are ~960 LOC,
exhibiting ~85 typed declarations).

## Logical chain

The classical proof of Stage B's main identity
`rank_ℤ H_1(X, ℤ) = 2 · analyticGenus ℂ X` cascades through these
files as:

1. `DifferentialForms` → `DeRhamComplex` → `DeRhamComparison`:
   `dim_ℂ H¹_dR(X, ℂ) = rank_ℤ H_1(X, ℤ)`.
2. `LaplaceBeltrami` → `HarmonicForms`: every de Rham class has a
   harmonic representative.
3. `KahlerStructure`: harmonic forms split by `(p,q)`-bidegree;
   `H¹ = H^{1,0} ⊕ H^{0,1}`.
4. `CoherentSheaves` + Dolbeault: `H^{0,1}(X) = H¹(X, 𝒪)`.
5. `SerreDuality`: `H¹(X, 𝒪) ≅ H⁰(X, Ω¹)*`, so
   `dim H^{0,1} = dim H^{1,0} = analyticGenus ℂ X`.
6. Combine 3–5: `dim H¹_dR = 2 · analyticGenus ℂ X`.
7. Combine with 1: `rank_ℤ H_1 = 2 · analyticGenus ℂ X`. ∎

## Wiring

These files **do not** import or wire into the existing helper modules
(`Jacobian/Periods/HodgeDeRham.lean`, …). They live in parallel as a
**bottom-up roadmap**.

## Status

`lake build Jacobian.StageB.<File>` builds for each file (with
sorries).
