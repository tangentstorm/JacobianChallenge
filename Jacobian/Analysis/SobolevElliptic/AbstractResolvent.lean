import Jacobian.Analysis.SobolevElliptic.AbstractFredholmResolvent
import Mathlib.Analysis.InnerProductSpace.Adjoint

/-!
# Phase 3.1 — Abstract resolvent `T = i ∘ i*` and its spectral output

The dispatch plan
(`/root/.claude/plans/okay-let-s-plan-out-shimmering-hearth.md`,
Phase 3) routes the headline `Module.Finite ℝ (ker Δ)` through
the spike-solution shortcut: build `T := (Δ + 1)⁻¹` as a bounded,
self-adjoint, compact operator on `L²(M)`; then `ker(T - 1) =
ker Δ` is finite-dim by `AbstractFredholmResolvent.
moduleFinite_eigenspace_of_compact`.

This file produces the `T` *abstractly*: given two real Hilbert
spaces `V` (think `H¹(M)`) and `H` (think `L²(M)`) with a
continuous linear embedding `i : V →L[ℝ] H`, define `T := i ∘L i†`
and prove

* `T` is self-adjoint (`isSelfAdjoint_resolvent`);
* `T` is non-negative on the diagonal:
  `⟨T x, x⟩ = ‖i† x‖²` (`inner_resolvent_self`);
* if `i` is compact, then `T` is compact
  (`isCompactOperator_resolvent`).

Combining the last point with
`finiteDimensional_eigenspace_of_compact` gives the headline:
`Eigenspace T 1` is finite-dimensional under the compactness
hypothesis on `i`.

**No `sorry`, no `True`-valued bodies.** Every theorem uses real
Mathlib v4.28.0.

## Why `i ∘ i†` is the resolvent

Let `(Δ + 1) : V → H*` be the natural map of the H¹/L² pair.  For
`g ∈ H`, the equation `(Δ + 1) u = g` is solved weakly by `u ∈ V`
satisfying `⟨u, v⟩_V = ⟨g, i v⟩_H` for all `v ∈ V`.  By Riesz,
`u = i† g`, so `(Δ + 1)⁻¹ g = u`.  Embedded back into `H` this
gives `T g := i (i† g) = (Δ + 1)⁻¹ g`.  The eigenvalue equation
`T g = g` then reduces to `Δ g = 0` (assuming `g ∈ V`, which
`T g = g` forces).

## Mathlib hooks used

* `Mathlib/Analysis/InnerProductSpace/Adjoint.lean` —
  `ContinuousLinearMap.adjoint`, `adjoint_adjoint`, `adjoint_comp`,
  `adjoint_inner_left`, `adjoint_inner_right`,
  `IsSelfAdjoint.isSelfAdjoint_iff'`.
* `Mathlib/Analysis/Normed/Operator/Compact.lean` —
  `IsCompactOperator.clm_comp` (compact ∘ bounded is compact).
-/

namespace JacobianChallenge.Analysis.SobolevElliptic

set_option linter.unusedSectionVars false

universe u v

variable {V : Type u} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [CompleteSpace V]
variable {H : Type v} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
  [CompleteSpace H]

/-! ### Definition of the abstract resolvent -/

/-- **Abstract resolvent.**  Given a continuous linear embedding
`i : V →L[ℝ] H`, define `T := i ∘ i† : H →L[ℝ] H`.  This is the
abstract incarnation of `(Δ + 1)⁻¹` when `V := H¹(M)`,
`H := L²(M)`, `i := H¹ ↪ L²`. -/
noncomputable def resolventOfEmbedding (i : V →L[ℝ] H) : H →L[ℝ] H :=
  i ∘L (ContinuousLinearMap.adjoint i)

/-- Pointwise formula for the abstract resolvent. -/
@[simp]
theorem resolventOfEmbedding_apply (i : V →L[ℝ] H) (x : H) :
    resolventOfEmbedding i x = i (ContinuousLinearMap.adjoint i x) := rfl

/-! ### Self-adjointness -/

/-- The abstract resolvent is self-adjoint. -/
theorem isSelfAdjoint_resolventOfEmbedding (i : V →L[ℝ] H) :
    IsSelfAdjoint (resolventOfEmbedding i) := by
  rw [ContinuousLinearMap.isSelfAdjoint_iff']
  unfold resolventOfEmbedding
  rw [ContinuousLinearMap.adjoint_comp,
      ContinuousLinearMap.adjoint_adjoint]

/-! ### Non-negativity on the diagonal -/

open scoped InnerProductSpace

/-- `⟨T x, x⟩_H = ⟨i† x, i† x⟩_V`.  In particular `T` is non-negative:
`⟨T x, x⟩ ≥ 0`. -/
theorem inner_resolventOfEmbedding_self (i : V →L[ℝ] H) (x : H) :
    ⟪resolventOfEmbedding i x, x⟫_ℝ =
      ⟪ContinuousLinearMap.adjoint i x,
        ContinuousLinearMap.adjoint i x⟫_ℝ := by
  -- `T x = i (i† x)`; goal: `⟪i (i† x), x⟫_H = ⟪i† x, i† x⟫_V`.
  -- Use `adjoint_inner_right (A := i)`:
  --     ⟪y, i† z⟫_V = ⟪i y, z⟫_H.
  -- Apply with `y := i† x`, `z := x`:
  --     ⟪i† x, i† x⟫_V = ⟪i (i† x), x⟫_H.
  show ⟪i (ContinuousLinearMap.adjoint i x), x⟫_ℝ = _
  exact (ContinuousLinearMap.adjoint_inner_right i
    (ContinuousLinearMap.adjoint i x) x).symm

/-- The abstract resolvent is non-negative on the diagonal. -/
theorem inner_resolventOfEmbedding_self_nonneg (i : V →L[ℝ] H) (x : H) :
    0 ≤ ⟪resolventOfEmbedding i x, x⟫_ℝ := by
  rw [inner_resolventOfEmbedding_self]
  exact real_inner_self_nonneg

/-! ### Compactness preservation -/

/-- If the embedding `i : V → H` is compact (Rellich-Kondrachov),
then the abstract resolvent `T := i ∘ i†` is compact. -/
theorem isCompactOperator_resolventOfEmbedding
    {i : V →L[ℝ] H} (hi : IsCompactOperator i) :
    IsCompactOperator (resolventOfEmbedding i) := by
  -- `T = i ∘ i†` and `i` is compact ⇒ `T` is compact via
  -- `IsCompactOperator.clm_comp` (precomposition with `i†`).
  -- Postcomposition variant: `IsCompactOperator.comp_clm` would
  -- precompose; here we precompose `i†` to get a compact `i ∘ i†`.
  -- Actually `IsCompactOperator.comp_clm hi g = hi ∘ g` is "g
  -- composed *after* the compact map" -- read carefully.
  -- `comp_clm`: `IsCompactOperator f` + `g : M₁ →SL M₂`
  --   ⇒ `IsCompactOperator (f ∘ g)`.
  -- Here `f = i` (compact), `g = i†`, so `f ∘ g = i ∘ i†` is compact.
  exact hi.comp_clm (ContinuousLinearMap.adjoint i)

/-! ### Spectral consequence: finite-dim eigenspace at any nonzero scalar -/

/-- **Headline (Phase 3.1).**  For a compact embedding
`i : V →L[ℝ] H`, every nonzero-eigenvalue eigenspace of the
abstract resolvent `T := i ∘ i†` is finite-dimensional.

When `V := H¹(M)`, `H := L²(M)`, `i := H¹ ↪ L²`, and `λ := 1`,
this is exactly `Module.Finite ℝ (ker Δ)` — the headline of R10
(`lem:sobolev-elliptic-kernel-finite-dim`,
`JacobianChallenge.Analysis.SobolevElliptic.sobolev_elliptic_overview`).

The remaining gap is supplying the analytic input
`IsCompactOperator i` (Rellich-Kondrachov on a compact manifold).
That input is the irreducible Mathlib gap; the spectral
consequence is here, fully discharged. -/
theorem finiteDimensional_resolvent_eigenspace
    {i : V →L[ℝ] H} (hi : IsCompactOperator i)
    {lam : ℝ} (hlam : lam ≠ 0) :
    FiniteDimensional ℝ (Eigenspace (resolventOfEmbedding i) lam) :=
  finiteDimensional_eigenspace_of_compact
    (isCompactOperator_resolventOfEmbedding hi) hlam

/-- **Module.Finite version of the headline.**  Same as above, in
the form consumed by the R10 statement bank. -/
theorem moduleFinite_resolvent_eigenspace
    {i : V →L[ℝ] H} (hi : IsCompactOperator i)
    {lam : ℝ} (hlam : lam ≠ 0) :
    Module.Finite ℝ (Eigenspace (resolventOfEmbedding i) lam) :=
  moduleFinite_eigenspace_of_compact
    (isCompactOperator_resolventOfEmbedding hi) hlam

end JacobianChallenge.Analysis.SobolevElliptic
