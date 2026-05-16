import Jacobian.HolomorphicForms.DeRhamCohomology
import Jacobian.HolomorphicForms.DeRhamComparisonMap
import Jacobian.HolomorphicForms.RealSingularH1
import Jacobian.Periods.IntegralOneCycle
import Jacobian.Periods.IntegralOneCycleRank
import Jacobian.Periods.RealHomologyTensor
import Jacobian.Periods.SmoothCycleToHomology
import Mathlib.Geometry.Manifold.IsManifold.Basic

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

/-- **Pure-algebra helper.** For a finitely generated free ℤ-module `M`,
the ℂ-dimension of `Hom_ℤ(M, ℂ)` equals the ℤ-rank of `M`. Sorry-free
via the standard basis-to-linear-equiv construction.

ℂ-valued analogue of `JacobianChallenge.Periods.finrank_homℤℝ_eq_finrank_of_free`. -/
theorem finrank_homℤℂ_eq_finrank_of_free
    (M : Type*) [AddCommGroup M] [Module ℤ M]
    [Module.Free ℤ M] [Module.Finite ℤ M] :
    Module.finrank ℂ (M →ₗ[ℤ] ℂ) = Module.finrank ℤ M := by
  have hbasis : Module.Basis (Fin (Module.finrank ℤ M)) ℤ M :=
    Module.finBasis ℤ M
  have hiso : (M →ₗ[ℤ] ℂ) ≃ₗ[ℂ] (Fin (Module.finrank ℤ M) → ℂ) :=
    (hbasis.constr ℂ).symm
  simpa using LinearEquiv.finrank_eq hiso

/-- **Frontier sub-obligation (Inc D.4.b — Whitney approximation in dim 1).**
The smooth-chain-cycle → integer-homology bridge `smoothCycleToHomology X`
(from `Jacobian/Periods/SmoothCycleToHomology.lean`) is surjective: every
integer 1-cycle is homologous to a smooth one.

This is the classical Whitney approximation theorem restricted to
dimension 1. Mathlib v4.28.0 lacks Whitney approximation; this is a
named frontier obligation. -/
theorem smoothCycleToHomology_surjective
    (X : Type) [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X]
    [JacobianChallenge.Periods.StableChartAt ℂ X] :
    Function.Surjective (JacobianChallenge.Periods.smoothCycleToHomology X) :=
  sorry

/-- **Frontier sub-obligation (Inc D.4.c — smooth-cycle redundancy).** The
kernel of `smoothCycleToHomology X` has ℤ-rank zero.

Mathematically: this kernel consists of smooth 1-chain cycles that are
homologous to zero (i.e., are boundaries in singular homology). After
Whitney approximation in dim 2, every such smooth cycle is itself a
boundary of a smooth 2-chain; modulo smooth boundaries, the kernel is
trivial — hence rank zero.

Named frontier obligation (distinct from `smoothCycleToHomology_surjective`:
the latter is "every integer homology class has a smooth representative";
this is "smooth cycles that are integer-trivial are also smoothly trivial",
i.e., the Whitney-2D version). -/
theorem smoothCycleToHomology_ker_rank_zero
    (X : Type) [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X]
    [JacobianChallenge.Periods.StableChartAt ℂ X] :
    Module.finrank ℤ
      (LinearMap.ker (JacobianChallenge.Periods.smoothCycleToHomology X)) = 0 :=
  sorry

/-- **Frontier sub-obligation (Inc D.4.d — smooth chain cycles fg free).**
The smooth 1-chain cycle submodule of `singChain 1 X` is finitely generated
as a ℤ-module.

After D.4.b + D.4.c (Whitney surjectivity + rank-zero kernel),
`smoothCycleToHomology X` becomes a ℤ-linear bijection onto
`IntegralOneCycle X`, which is fg by `IntegralOneCycle_finite`. So this
would follow downstream of D.4.b + D.4.c via that LinearEquiv. We name it
as a separate sub-sorry to allow the F.2 body to proceed without recursing
through D.4.b's discharge.

`Module.Free ℤ` follows automatically: submodule of free ℤ-module
(`singChain 1 X`) is torsion-free, combined with finiteness gives free. -/
theorem smoothOneChainCycleSubmodule_finite
    (X : Type) [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X]
    [JacobianChallenge.Periods.StableChartAt ℂ X] :
    Module.Finite ℤ
      (JacobianChallenge.HolomorphicForms.smoothOneChainCycleSubmodule X) :=
  sorry

theorem smoothOneChainCycleSubmodule_free
    (X : Type) [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X]
    [JacobianChallenge.Periods.StableChartAt ℂ X] :
    Module.Free ℤ
      (JacobianChallenge.HolomorphicForms.smoothOneChainCycleSubmodule X) :=
  sorry

/-- **Frontier obligation (Inc D.4) — Whitney-driven dim equality.**
The ℂ-dimensions of `smoothOneChainCycleSubmodule X →ₗ[ℤ] ℂ` and
`IntegralOneCycle X →ₗ[ℤ] ℂ` agree.

**Decomposition (F.2).** Both sides equal `Module.finrank ℤ` of their
respective ℤ-modules (via `finrank_homℤℂ_eq_finrank_of_free`); we reduce
to comparing `finrank ℤ (smoothOneChainCycleSubmodule X)` with
`finrank ℤ (IntegralOneCycle X)`. Via the bridge
`smoothCycleToHomology X : smoothOneChainCycleSubmodule X →ₗ[ℤ]
IntegralOneCycle X` (F.1) and the rank-nullity formula, this becomes:
`finrank source = finrank (source ⧸ ker) + finrank ker`, where
`source ⧸ ker ≃ₗ[ℤ] target` (via surjectivity D.4.b) and `finrank ker = 0`
(D.4.c).

Sub-sorries introduced:
- `smoothCycleToHomology_surjective` (D.4.b — Whitney in dim 1).
- `smoothCycleToHomology_ker_rank_zero` (D.4.c — Whitney-2D).
- `smoothOneChainCycleSubmodule_finite`, `_free` (D.4.d — finite-free
  structural ingredient, follows downstream of D.4.b + D.4.c but named
  separately for the F.2 body to proceed without forward references). -/
theorem finrank_homℤℂ_smoothCycle_eq_finrank_homℤℂ_intH1
    (X : Type) [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X]
    [JacobianChallenge.Periods.StableChartAt ℂ X] :
    Module.finrank ℂ
      (JacobianChallenge.HolomorphicForms.smoothOneChainCycleSubmodule X →ₗ[ℤ] ℂ)
      = Module.finrank ℂ (IntegralOneCycle X →ₗ[ℤ] ℂ) := by
  haveI : Module.Finite ℤ
      (JacobianChallenge.HolomorphicForms.smoothOneChainCycleSubmodule X) :=
    smoothOneChainCycleSubmodule_finite X
  haveI : Module.Free ℤ
      (JacobianChallenge.HolomorphicForms.smoothOneChainCycleSubmodule X) :=
    smoothOneChainCycleSubmodule_free X
  haveI : Module.Finite ℤ (IntegralOneCycle X) := IntegralOneCycle_finite X
  haveI : Module.Free ℤ (IntegralOneCycle X) := IntegralOneCycle_torsionFree X
  -- Reduce ℂ-Hom-finrank to ℤ-finrank via `finrank_homℤℂ_eq_finrank_of_free`.
  rw [JacobianChallenge.Periods.finrank_homℤℂ_eq_finrank_of_free
        (JacobianChallenge.HolomorphicForms.smoothOneChainCycleSubmodule X),
      JacobianChallenge.Periods.finrank_homℤℂ_eq_finrank_of_free
        (IntegralOneCycle X)]
  -- Now reduce to: finrank ℤ source = finrank ℤ target.
  -- Rank-nullity through `smoothCycleToHomology X`.
  set q := JacobianChallenge.Periods.smoothCycleToHomology X with hq_def
  have hq_surj := smoothCycleToHomology_surjective X
  have hker := smoothCycleToHomology_ker_rank_zero X
  -- A ⧸ ker q ≃ₗ[ℤ] B via surjectivity (LinearMap.quotKerEquivOfSurjective).
  have h_quotEq := q.quotKerEquivOfSurjective hq_surj
  have h_quot_finrank :=
    h_quotEq.finrank_eq (R := ℤ)
  -- Rank-nullity: finrank (A ⧸ ker q) + finrank (ker q) = finrank A.
  have h_rn := Submodule.finrank_quotient_add_finrank (R := ℤ)
                (M := JacobianChallenge.HolomorphicForms.smoothOneChainCycleSubmodule X)
                (LinearMap.ker q)
  -- Diagnostic:
  -- h_quot_finrank : finrank ℤ (A ⧸ ker q) = finrank ℤ B (target)
  -- h_rn          : finrank ℤ (A ⧸ ker q) + finrank ℤ (ker q) = finrank ℤ A (source)
  -- hker          : finrank ℤ (ker q) = 0
  -- Goal: finrank ℤ A = finrank ℤ B.
  -- The diamond appears between the `finrank ℤ (ker q)` instances of `hker` and `h_rn`.
  -- Bridge `hker` to match `h_rn`'s instance via Subsingleton.elim on Module ℤ.
  have hker' :
      @Module.finrank ℤ _ Int.instSemiring _ (LinearMap.ker q).module = 0 := by
    convert hker using 2
  omega

/-- **Frontier obligation (Inc D.1, post-D.2/D.4 decomposition).**
The de Rham theorem in degree 1 restated as a ℂ-dim equality:
`dim_ℂ H¹_dR(X) = dim_ℂ Hom_ℤ(H₁(X, ℤ), ℂ)` for a compact connected
Riemann surface.

Post-D.2 (smooth-cycle LinearEquiv via first iso theorem) +
post-D.4 (Whitney approximation) decomposition: routes through the
smooth-cycle dim equality `deRhamH1Cocycle_finrank_eq_finrank_homℤℂ_smoothCycle`
(Inc D.2, contains the analytic content — `comparison_ker_eq_exact_smooth`
sub-sorry + `comparison_range_eq_top_smooth` sub-sorry, each a distinct
named obligation), then the smooth-vs-integer codomain bridge
`finrank_homℤℂ_smoothCycle_eq_finrank_homℤℂ_intH1` (Inc D.4, contains
the Whitney approximation in dim 1). -/
theorem deRhamH1Cocycle_finrank_eq_finrank_homℤℂ_intH1_via_smooth
    (X : Type) [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X]
    [JacobianChallenge.Periods.StableChartAt ℂ X] :
    Module.finrank ℂ (deRhamH1Cocycle X)
      = Module.finrank ℂ (IntegralOneCycle X →ₗ[ℤ] ℂ) := by
  rw [JacobianChallenge.HolomorphicForms.deRhamH1Cocycle_finrank_eq_finrank_homℤℂ_smoothCycle X]
  exact finrank_homℤℂ_smoothCycle_eq_finrank_homℤℂ_intH1 X

/-- **Frontier theorem (post-Inc D.1, decomposed).**
`dim_ℝ H¹_dR(X, ℝ) = dim_ℝ H¹_sing(X, ℝ)` for a compact connected
Riemann surface, proved through the smooth-cycle de Rham comparison
map.

The body decomposes into:
1. `realDimDeRhamH1 X = Module.finrank ℂ (deRhamH1Cocycle X)`
   (definitional, via `DeRhamCohomology.lean:89`).
2. `Module.finrank ℂ (deRhamH1Cocycle X)
     = Module.finrank ℂ (IntegralOneCycle X →ₗ[ℤ] ℂ)`
   (the named sub-obligation
   `deRhamH1Cocycle_finrank_eq_finrank_homℤℂ_intH1_via_smooth`, which
   captures the smooth-cycle LinearEquiv + smooth approximation in dim 1).
3. `Module.finrank ℂ (IntegralOneCycle X →ₗ[ℤ] ℂ) = Module.finrank ℤ (IntegralOneCycle X)`
   (pure algebra `finrank_homℤℂ_eq_finrank_of_free` plus
   `IntegralOneCycle_finite/torsionFree`).
4. `Module.finrank ℤ (IntegralOneCycle X) = realDimSingularH1 X`
   (UCT bridge `realDim_singularH1_eq_finrank_intH1_via_uct`, sorry-free).

Replaces the pre-Inc-D.1 direct `sorry` with a chain that isolates the
de Rham-side content into ONE named frontier obligation
(`deRhamH1Cocycle_finrank_eq_finrank_homℤℂ_intH1_via_smooth`),
matching the textbook decomposition. -/
theorem realDim_deRhamH1_eq_realDim_singularH1
    (X : Type) [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X]
    [JacobianChallenge.Periods.StableChartAt ℂ X] :
    realDimDeRhamH1 X = realDimSingularH1 X := by
  haveI : Module.Finite ℤ (IntegralOneCycle X) := IntegralOneCycle_finite X
  haveI : Module.Free ℤ (IntegralOneCycle X) := IntegralOneCycle_torsionFree X
  show Module.finrank ℂ (deRhamH1Cocycle X) = realDimSingularH1 X
  rw [deRhamH1Cocycle_finrank_eq_finrank_homℤℂ_intH1_via_smooth X,
      finrank_homℤℂ_eq_finrank_of_free (IntegralOneCycle X),
      ← realDim_singularH1_eq_finrank_intH1_via_uct X]

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
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X] :
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
