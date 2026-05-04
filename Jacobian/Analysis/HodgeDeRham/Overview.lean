/-!
# R6 — Hodge / de Rham rank for a Riemann surface

Headline statement:

> For a compact connected oriented Riemann surface `X` of analytic
> genus `g`, `rank_ℤ H₁(X, ℤ) = 2 g`.

R6 is the *assembly* gap: it consumes R4 (de Rham), R5 (Hodge
decomposition), and R7 (Dolbeault) and outputs the integer-rank
identity needed by the period-lattice fullness argument.

Independent build target.

Pre-existing scaffolding:
* `Jacobian/Periods/HodgeDeRham.lean` (top-down refinement; ~30
  named sub-leaves, all sorry).
* `Jacobian/Periods/AnalyticGenusEqTopologicalGenus.lean` (the wire
  from `analyticGenus` to `topologicalGenus`, sorry-free *above*
  R6 but consumes the headline as input).

**Status.** Every theorem here is a `True` placeholder; the
realisation `JacobianChallenge.Periods.hodge_deRham_rank_eq` remains
`sorry`.
-/

namespace JacobianChallenge.Analysis.HodgeDeRham

/-! ### Headline -/

/-- **R6 headline (placeholder type).**
`rank_ℤ H₁(X, ℤ) = 2 · analyticGenus ℂ X`. -/
theorem hodge_deRham_overview : True := trivial

/-! ### Sub-leaves — Phase 1: real-dimensional intermediate -/

/-- **R6.1.1.** `dim_ℝ H¹_dR(X, ℝ) = 2g`.  This is the headline
intermediate: it cleanly factors through Hodge `(p,q)` with the
Riemann-surface specialisation. -/
theorem hodge_deRham_dim_h1_dR_real : True := trivial

/-- **R6.1.2.** From Hodge decomposition (R5):
`H¹_dR(X, ℂ) = H^{1,0}(X) ⊕ H^{0,1}(X)`. -/
theorem hodge_deRham_h1_dR_split : True := trivial

/-- **R6.1.3.** From Dolbeault (R7) + Serre on compact Kähler:
`dim_ℂ H^{1,0}(X) = g`. -/
theorem hodge_deRham_dim_h10_eq_g : True := trivial

/-- **R6.1.4.** Hodge symmetry (R5.5.5):
`dim_ℂ H^{0,1}(X) = dim_ℂ H^{1,0}(X) = g`. -/
theorem hodge_deRham_dim_h01_eq_g : True := trivial

/-- **R6.1.5.** Combine R6.1.2 + R6.1.3 + R6.1.4:
`dim_ℂ H¹_dR(X, ℂ) = 2g`, hence `dim_ℝ H¹_dR(X, ℝ) = 2g`. -/
theorem hodge_deRham_dim_assembly : True := trivial

/-! ### Sub-leaves — Phase 2: from H¹_dR to H¹_sing -/

/-- **R6.2.1.** Apply de Rham (R4): `H¹_dR(X, ℝ) ≅ H¹_sing(X, ℝ)` as
real vector spaces. -/
theorem hodge_deRham_apply_deRham : True := trivial

/-- **R6.2.2.** `dim_ℝ H¹_sing(X, ℝ) = 2g`. -/
theorem hodge_deRham_dim_h1_sing : True := trivial

/-! ### Sub-leaves — Phase 3: from H¹_sing to H₁(X, ℤ) -/

/-- **R6.3.1.** Universal-coefficient theorem in degree 1 on a
finite-CW manifold: `H¹_sing(X, ℝ) ≅ Hom(H₁(X, ℤ), ℝ)`.  Mathlib has
the algebraic UCT (`AlgebraicTopology.UniversalCoefficient`) but
**not** the singular variant for manifolds. -/
theorem hodge_deRham_uct_degree_one : True := trivial

/-- **R6.3.2.** `H₁(X, ℤ)` is a *finitely generated* abelian group on
a compact CW manifold. -/
theorem hodge_deRham_h1_fg : True := trivial

/-- **R6.3.3.** `dim_ℝ Hom(H₁(X, ℤ), ℝ) = rank_ℤ H₁(X, ℤ)`. -/
theorem hodge_deRham_hom_dim_eq_rank : True := trivial

/-- **R6.3.4.** Combine R6.3.1 + R6.3.3:
`rank_ℤ H₁(X, ℤ) = dim_ℝ H¹_sing(X, ℝ)`. -/
theorem hodge_deRham_rank_eq_h1_sing_dim : True := trivial

/-! ### Sub-leaves — Phase 4: final assembly -/

/-- **R6.4.1.** Stitch R6.1.5 + R6.2.2 + R6.3.4:
`rank_ℤ H₁(X, ℤ) = 2g`. -/
theorem hodge_deRham_final : True := trivial

/-! ### Recursive sub-gaps surfaced

* **R6-sub-A.** Universal-coefficient theorem in degree 1 for a
  CW manifold (R6.3.1).  Algebraic UCT exists in Mathlib; geometric
  variant for `H_*^sing(X, ℤ)` does not.
* **R6-sub-B.** `H₁(X, ℤ)` finitely generated for a compact CW
  manifold (R6.3.2).  Mathlib has `H_*` for chain complexes but not
  the manifold-level finite-CW theorem.
* **R6-sub-C.** Universal-coefficient `Hom`-rank lemma
  `dim_ℝ Hom(A, ℝ) = rank_ℤ A` for a fg abelian group (R6.3.3).
  Routine; Mathlib has the building blocks. -/

theorem hodge_deRham_subgap_uct : True := trivial
theorem hodge_deRham_subgap_h1_fg : True := trivial
theorem hodge_deRham_subgap_hom_rank : True := trivial

end JacobianChallenge.Analysis.HodgeDeRham
