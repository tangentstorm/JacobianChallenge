import Jacobian.HolomorphicForms.DeRhamCohomology
import Jacobian.HolomorphicForms.RealSingularH1
import Jacobian.HolomorphicForms.DeRhamComparisonMap
import Jacobian.Periods.IntegralOneCycle
import Jacobian.Periods.RealHomologyTensor
import Mathlib.Geometry.Manifold.IsManifold.Basic
import Jacobian.Periods.TrivializationContinuousLinearMapAt

/-!
# De Rham theorem and singular bridge (frontier API)

The de Rham theorem identifies the de Rham cohomology of a smooth
manifold with the singular cohomology over ℝ:

  H^k_dR(X, ℝ) ≅ H^k_sing(X, ℝ) = Hom_ℤ(H_k(X, ℤ), ℝ).

Combined with the universal-coefficient theorem (over ℝ, hence the
torsion in `H_{k-1}(X, ℤ)` does not appear), this links

  dim_ℝ H¹_dR(X, ℝ) = rank_ℤ H₁(X, ℤ)

for any compact connected smooth manifold whose H₁ is finitely generated.

## Mathlib v4.28.0 status

ABSENT (de Rham complex on manifolds, de Rham theorem).
`Mathlib.AlgebraicTopology.SingularHomology.Basic` provides
`singularHomologyFunctor`, but no comparison map to a de Rham complex
exists — the project uses the resulting `IntegralOneCycle X` purely as
the integer-cycle module.

## What this file provides

* `realDim_deRhamH1_eq_finrank_homH1ℝ` — frontier theorem (sorry), the
  de Rham theorem in dimension 1: real dim of H¹_dR equals the
  ℝ-dim of `Hom_ℤ(H₁(X, ℤ), ℝ)`.

* `finrank_homH1ℝ_eq_finrank_intH1` — algebraic fact (sorry, but pure
  algebra not analysis): the ℝ-dim of `Hom_ℤ(M, ℝ)` for a finitely
  generated free ℤ-module `M` equals `Module.finrank ℤ M`.

* `realDim_deRhamH1_eq_h1_rank` — the assembled frontier identity used
  by the top-level `hodge_deRham_rank_eq` assembly: real dim H¹_dR =
  rank ℤ H₁.

## TOPDOWN role

This is the *de Rham side* of the rank chain. It is the first of two
named obligations (the other being the *Hodge side*) that the top-down
refinement of `hodge_deRham_rank_eq` delegates to.
-/

namespace JacobianChallenge.HolomorphicForms

open JacobianChallenge.Periods

open scoped Manifold

/-- **Frontier theorem (sorry, de Rham theorem in degree 1).**
`dim_ℝ H¹_dR(X, ℝ) = dim_ℝ H¹_sing(X, ℝ)` for a compact smooth manifold
`X`.

Bottom-up content: the de Rham theorem provides a chain map
`(Ω^*(X), d) → C^*_sing(X, ℝ)` (integration of forms over simplices)
which is a quasi-isomorphism on a smooth manifold (the partition-of-unity
argument). Mathlib gap: the chain map itself is absent (no de Rham
complex), and the singular cohomology dual side requires
`Mathlib.AlgebraicTopology.SingularCohomology.*` which is also incomplete.

This frontier theorem is the **central de Rham bridge** in the entire
`hodge_deRham_rank_eq` chain. It is the single named obligation that a
future Mathlib effort discharging "de Rham on compact smooth manifolds"
would replace with a real proof. -/
theorem realDim_deRhamH1_eq_realDim_singularH1
    (X : Type) [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X]
    [JacobianChallenge.Periods.StableChartAt ℂ X] :
    realDimDeRhamH1 X = realDimSingularH1 X :=
  realDimDeRhamH1_eq_realDimSingularH1_via_cocycle X

/-- **Frontier theorem (sorry).** Algebraic fact: for `M` a finitely
generated ℤ-module,
`dim_ℝ Hom_ℤ(M, ℝ) = rank_ℤ (M / torsion)`.

Specialised here to `M = IntegralOneCycle X`. Bottom-up content: Mathlib
has a `Module.Free.rank_finsupp` / `rank_pi` chain that yields the
identity for free modules; the torsion factor of a finitely generated
ℤ-module pairs trivially against ℝ.  This identity is **pure algebra**;
its sorry is small in scope and is independent of any
analytic / manifold-theoretic prerequisite — it is the natural
Aristotle-shaped leaf in this file.

Refinement direction: split into
`(a) IntegralOneCycle_finiteFree X : Module.Free ℤ (IntegralOneCycle X) ∧ Module.Finite ℤ _`
and
`(b) finrank_homℤℝ_of_free : ∀ M [Module.Free ℤ M] [Module.Finite ℤ M], Module.finrank ℝ (M →ₗ[ℤ] ℝ) = Module.finrank ℤ M`.
Both are pure linear-algebra obligations.  See `IntegralOneCycleRank.lean`. -/
theorem realDim_singularH1_eq_finrank_intH1
    (X : Type) [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X]
    [JacobianChallenge.Periods.StableChartAt ℂ X] :
    realDimSingularH1 X = Module.finrank ℤ (IntegralOneCycle X) :=
  realDim_singularH1_eq_finrank_intH1_via_uct X

/-- **Assembled (sorry-free).** De Rham–singular bridge:
`dim_ℝ H¹_dR(X, ℝ) = rank_ℤ H₁(X, ℤ)` for a compact connected Riemann
surface.  Combines the de Rham theorem
(`realDim_deRhamH1_eq_realDim_singularH1`) with the algebraic
UCT/finrank identity (`realDim_singularH1_eq_finrank_intH1`).

This is the **de Rham side** of the top-level `hodge_deRham_rank_eq`
assembly. -/
theorem realDim_deRhamH1_eq_finrank_intH1
    (X : Type) [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X]
    [JacobianChallenge.Periods.StableChartAt ℂ X] :
    realDimDeRhamH1 X = Module.finrank ℤ (IntegralOneCycle X) := by
  rw [realDim_deRhamH1_eq_realDim_singularH1 X,
      realDim_singularH1_eq_finrank_intH1 X]

end JacobianChallenge.HolomorphicForms
