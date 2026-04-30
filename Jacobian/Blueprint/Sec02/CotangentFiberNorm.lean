import Jacobian.HolomorphicForms.CotangentBundle

/-! # Blueprint stub: `def:cotangent-fiber-norm`

Section 2 of `tex/sections/02-holomorphic-forms-and-genus.tex`.

A continuous fiber norm `‖·‖_x` on the cotangent bundle of a complex
1-manifold `X`, obtained chartwise from the canonical norm on
`ℂ →L[ℂ] ℂ` and assembled by a partition of unity.

The cotangent fiber over `x : X` is
`CotangentSpace ℂ X x = TangentSpace 𝓘(ℂ, ℂ) x →L[ℂ] (Bundle.Trivial X ℂ) x`,
which inherits a `NormedAddCommGroup` instance from the operator norm.
This stub records the function `(x, v) ↦ ‖v‖_x` explicitly so the
downstream sup-norm definition has a named handle.

The primary signature `cotangentFiberNorm` takes a single
`Σ x : X, CotangentSpace ℂ X x` argument so it composes cleanly with
total-space-style continuity statements (`Continuous (cotangentFiberNorm X)`).
The convenience `cotangentFiberNormAt X x v` curries the pair for
pointwise sites such as the sup-norm definition and the chart-coefficient
bound.

The downstream worker may either:
* unfold this to the operator norm `‖v‖`, in which case continuity is
  inherited from the bundle topology;
* or take the chart-pulled-back form `|h(z)|` weighted by a partition
  of unity, in which case continuity needs the partition-of-unity glue.

NOTE FOR WORKERS: `CotangentSpace ℂ X x` is a PROJECT-SIDE definition
(not a Mathlib type). Find it at
`Jacobian/HolomorphicForms/CotangentBundle.lean`; its full path is
`JacobianChallenge.HolomorphicForms.CotangentSpace`. Open that
namespace in your file (`open JacobianChallenge.HolomorphicForms`) or
use the fully qualified name. Don't search Mathlib for this — there is
a separate `CotangentSpace` in `RingTheory/Ideal/Cotangent.lean` for
local rings that is unrelated.
-/

namespace JacobianChallenge.Blueprint

open scoped Manifold
open JacobianChallenge.HolomorphicForms

/-- Continuous fiber norm on the cotangent bundle of a complex
1-manifold, viewed as a function on the total space
`Σ x : X, CotangentSpace ℂ X x`. The value at `⟨x, v⟩` is the norm of
the cotangent covector `v` in the fiber over `x`. -/
noncomputable def cotangentFiberNorm
    (X : Type*) [TopologicalSpace X] [T2Space X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X]
    (p : Σ x : X, CotangentSpace ℂ X x) : ℝ := ‖p.2‖

/-- Pointwise convenience accessor: `cotangentFiberNormAt X x v`
unfolds to `cotangentFiberNorm X ⟨x, v⟩`. -/
noncomputable def cotangentFiberNormAt
    (X : Type*) [TopologicalSpace X] [T2Space X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X]
    (x : X) (v : CotangentSpace ℂ X x) : ℝ :=
  cotangentFiberNorm X ⟨x, v⟩

end JacobianChallenge.Blueprint
