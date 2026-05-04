# R6 — Hodge / de Rham rank for a Riemann surface

**Headline.** For a compact connected oriented Riemann surface `X`
of analytic genus `g`, `rank_ℤ H₁(X, ℤ) = 2g`.

**Lean target.**
`JacobianChallenge.Analysis.HodgeDeRham.hodge_deRham_overview` in
`Overview.lean`; full realisation will replace
`Periods.hodge_deRham_rank_eq`.

**Build.** `lake build Jacobian.Analysis.HodgeDeRham`

R6 is the *assembly* gap: small in itself but consumes R4 + R5 + R7.

## Classical proof (3 stages)

1. **Hodge ⇒ `dim_ℂ H¹_dR(X, ℂ) = 2g`.** Apply R5 to split
   `H¹_dR = H^{1,0} ⊕ H^{0,1}`; apply R7 to identify `H^{1,0}` with
   holomorphic 1-forms (`dim = g`); Hodge symmetry gives
   `dim H^{0,1} = g`.
2. **De Rham ⇒ `H¹_sing(X, ℝ) ≅ H¹_dR(X, ℝ)`.** Apply R4.
3. **Universal coefficients ⇒ `rank_ℤ H₁(X, ℤ) = dim_ℝ H¹_sing(X, ℝ)`.**
   On a compact CW manifold,
   `H¹(X, ℝ) ≅ Hom(H₁(X, ℤ), ℝ)`, real dim = integer rank.

## Lean plan (sub-leaves under `Overview.lean`)

11 sub-leaves across 4 phases.  All routine assembly above R4/R5/R7;
the only locally non-trivial work is the singular UCT for manifolds
(R6-sub-A) and the finite-CW property of compact Riemann surfaces
(R6-sub-B, depends on R1).

## Recursive sub-gaps

* **R6-sub-A.** Universal-coefficient theorem in degree 1 for a CW
  manifold.  Algebraic UCT exists in Mathlib; geometric singular
  variant doesn't.  ~250 LOC.
* **R6-sub-B.** `H₁(X, ℤ)` finitely generated for a compact CW
  manifold.  ~150 LOC, depends on R1 (triangulation).
* **R6-sub-C.** `dim_ℝ Hom(A, ℝ) = rank_ℤ A` for a fg abelian group.
  ~80 LOC routine.

## Plain-English

R6 is the smallest gap by code, the most blocked by dependencies.
The headline says: a genus-`g` Riemann surface has `2g`
topologically independent loops in integer first homology — no more,
no less.  The proof is a chain of three identifications: Hodge +
Dolbeault give `dim_ℂ H¹_dR = 2g`; de Rham gives `H¹_sing = H¹_dR`;
universal coefficients gives `rank_ℤ H₁ = dim_ℝ H¹_sing`.

Why bother?  This is the rank fact every period-lattice argument
depends on: the symplectic basis `a_1, b_1, …, a_g, b_g` generates
`H₁(X, ℤ)` of rank `2g`, so the period vectors live in
`(H⁰(X, Ω¹))^∨ ≅ ℂ^g` and span a full-rank lattice.  No fullness, no
Jacobian.

## See also

* Blueprint section `subsec:gap-R6-hodge-deRham` in
  `tex/sections/12-classical-analysis-gaps.tex`.
* Top-down decomposition `Jacobian/Periods/HodgeDeRham.lean` (~30
  named sub-leaves, all sorry).
* Assembly target `Jacobian/Periods/AnalyticGenusEqTopologicalGenus.lean`.

**Estimated full LOC** (R6 + sub-A + sub-B + sub-C): 1100–1400.
