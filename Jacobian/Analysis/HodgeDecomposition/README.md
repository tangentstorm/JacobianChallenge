# R5 — Hodge decomposition on a compact Kähler manifold

**Headline.** On a compact Kähler manifold (in particular every
compact Riemann surface), `Δ = dδ + δd` is elliptic, has
finite-dimensional kernel, every de Rham class has a unique harmonic
representative, and harmonic forms split by `(p,q)`-bidegree.

**Lean target.**
`JacobianChallenge.Analysis.HodgeDecomposition.hodge_decomposition_overview`
in `Overview.lean`; full realisation will replace
`StageB.hodge_decomposition`.

**Build.** `lake build Jacobian.Analysis.HodgeDecomposition`

This is the **deepest** of the eight gaps.

## Classical proof (6 phases)

1. **Riemannian metric + Hodge `*`.** Pick metric `g`; induce metric
   on `Ω^k`; star `*: Ω^k → Ω^{n-k}`.
2. **Codifferential + Laplacian.** `δ = ±* d *`, `Δ = dδ + δd`.
3. **Ellipticity + elliptic regularity.** Principal symbol
   `|ξ|² · id`; smooth solutions of `Δω = f` for smooth `f`;
   Rellich–Kondrachov compactness on a compact manifold;
   Fredholm property.
4. **Orthogonal decomposition.** `Ω^k = H^k ⊕ d(Ω^{k-1}) ⊕ δ(Ω^{k+1})`,
   `L²`-orthogonal; finite-dim harmonic representatives.
5. **Kähler bigrading.** Kähler identities ⇒ `Δ_d = 2Δ_∂̄ = 2Δ_∂`;
   bigrading splits harmonic; Hodge symmetry.
6. **Riemann surface specialisation.** `H^{1,0}(X) ≅ H⁰(X, Ω¹)`;
   `dim = g`; `dim H¹ = 2g`.

## Lean plan (sub-leaves under `Overview.lean`)

19 sub-leaves across 6 phases.  See `Overview.lean` for the named
list.  The largest single piece is **Phase 3 (ellipticity +
regularity)**: Mathlib has neither manifold-Sobolev spaces, nor
elliptic regularity, nor Rellich–Kondrachov for forms.

## Recursive sub-gaps

* **R5-sub-A.** Riemannian metric on a manifold (~500 LOC, shared
  with R4-sub-C).
* **R5-sub-B.** Sobolev spaces of forms + elliptic regularity for
  second-order operators.  **The single largest sub-gap in the
  entire eight-node tree** — estimated 2500–4000 LOC.  Critical
  path for both R5 and R7.
* **R5-sub-C.** Rellich–Kondrachov for forms (~400 LOC after R5-sub-B).
* **R5-sub-D.** Fredholm-alternative on a compact manifold
  (~300 LOC).
* **R5-sub-E.** Kähler identities (~400 LOC).

## Plain-English

The Laplacian on forms is "`d` followed by its `L²`-adjoint, plus the
adjoint followed by `d`".  Every cohomology class has a unique
representative annihilated by it — a *harmonic* form.  On a compact
Kähler manifold, harmonic forms split further by complex bidegree:
holomorphic (`(1,0)`-type) and antiholomorphic (`(0,1)`-type), each
of dimension `g` on a Riemann surface.  This sharpens
"`H¹_dR` has dimension `2g`" to "the `2g` is `g + g`, and the two
`g`'s are conjugates of each other".  Without R5, the analytic
genus and the topological genus have no shared root.

The Lean cost is dominated by R5-sub-B (Sobolev / elliptic
regularity) — a major mathematical-foundations project in its own
right.

## See also

* Blueprint section `subsec:gap-R5-hodge` in
  `tex/sections/12-classical-analysis-gaps.tex`.
* Bottom-up sketch `Jacobian/StageB/{LaplaceBeltrami,
  HarmonicForms, KahlerStructure}.lean`.
* Top-down refinement `Jacobian/HolomorphicForms/Serre/HarmonicForms.lean`.

**Estimated full LOC** (R5 + sub-A through sub-E): 5500–8500.
