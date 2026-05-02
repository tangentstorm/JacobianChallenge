import Mathlib.Geometry.Manifold.IsManifold.Basic
import Mathlib.Analysis.Complex.Basic
import Mathlib.LinearAlgebra.FiniteDimensional.Defs

/-!
# De Rham cohomology dimensions on a smooth manifold (frontier API)

Frontier-layer ℕ-valued surrogates for the dimensions of the de Rham
cohomology groups on a smooth (real or complex) manifold. Mathlib v4.28.0
has neither the de Rham complex on manifolds, nor de Rham cohomology, nor
the de Rham theorem.  Rather than introduce a fresh opaque ℂ-vector-space
type for `H¹_dR(X)` (which would force us to opaquely declare every
needed `AddCommGroup` / `Module` instance), this file exposes the
**dimensions** as opaque ℕ-valued frontier symbols.  Downstream consumers
chain them through named arithmetic identities; landing the actual de
Rham complex in Mathlib will let us replace each opaque ℕ with its real
construction without disturbing callers.

## What this file provides (refinement scaffolding)

* `realDimDeRhamH1` — opaque ℕ, the real dimension of the first de Rham
  cohomology of `X` viewed as a real manifold.
* `complexDimDeRhamH1ℂ` — opaque ℕ, the complex dimension of the first
  de Rham cohomology of `X` viewed as a complex manifold (i.e. with
  ℂ-valued forms).
* `realDimDeRhamH0` / `complexDimDeRhamH0ℂ` — opaque ℕ, the H⁰
  counterparts (used for sanity bookkeeping; equal to the number of
  connected components × 1 over ℝ, and to 1 over ℂ for compact
  connected `X`).
* `realDim_deRhamH1_eq_two_complexDim_deRhamH1ℂ` — frontier theorem
  (sorry): real dim of H¹_dR equals twice the complex dim, since
  ℂ-valued forms are ℝ-valued forms tensored with ℂ.
* `complexDim_deRhamH0ℂ_eq_one_of_compact_connected` — frontier theorem
  (sorry): the global ℂ-valued constant functions exhaust H⁰.

## TOPDOWN role

These declarations are *named opaques* that sit at the bottom of the
top-down chain refining `JacobianChallenge.Periods.hodge_deRham_rank_eq`.
They are the precise points at which Mathlib's eventual de Rham
infrastructure should drop in — each opaque ℕ becomes a `Module.finrank`
of the corresponding cohomology, and each frontier theorem becomes a
real proof.

No file outside `Jacobian/HolomorphicForms/` should reach for these
names directly; the assembly-layer files (`HodgeTheoremRS.lean`,
`HodgeDeRhamRank.lean`) re-export the only identities that downstream
code (e.g. `Jacobian/Periods/PeriodFunctional.lean`) consumes.
-/

namespace JacobianChallenge.HolomorphicForms

open scoped Manifold

/-- **Frontier opaque (ℕ).** Real dimension of the first de Rham
cohomology group of the smooth manifold `X`, with ℝ-valued differential
forms. Mathematically `dim_ℝ H¹_dR(X, ℝ)`. Mathlib gap: no de Rham
complex on manifolds. -/
noncomputable opaque realDimDeRhamH1
    (X : Type) [TopologicalSpace X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X] : ℕ

/-- **Frontier opaque (ℕ).** Complex dimension of the first de Rham
cohomology group of `X` with ℂ-valued differential forms.
Mathematically `dim_ℂ H¹_dR(X, ℂ)`. Equal to `realDimDeRhamH1` for the
real underlying manifold by the universal-coefficient theorem; this
file states the relation as a frontier theorem rather than a
definitional identity. -/
noncomputable opaque complexDimDeRhamH1ℂ
    (X : Type) [TopologicalSpace X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X] : ℕ

/-- **Frontier opaque (ℕ).** Real dimension of the zeroth de Rham
cohomology group of `X` with ℝ-valued forms. Mathematically equals the
number of connected components; for a connected manifold this is `1`. -/
noncomputable opaque realDimDeRhamH0
    (X : Type) [TopologicalSpace X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X] : ℕ

/-- **Frontier opaque (ℕ).** Complex dimension of the zeroth de Rham
cohomology group of `X` with ℂ-valued forms. Equals the ℂ-dimension of
locally constant ℂ-valued functions; for a connected `X` this is `1`. -/
noncomputable opaque complexDimDeRhamH0ℂ
    (X : Type) [TopologicalSpace X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X] : ℕ

/-- **Frontier theorem (sorry).** The real dim of H¹_dR(X, ℝ) equals the
complex dim of H¹_dR(X, ℂ).

Bottom-up content: `H¹_dR(X, ℂ) ≃ H¹_dR(X, ℝ) ⊗_ℝ ℂ` as ℂ-vector
spaces, so the complex dim of the LHS equals the real dim of the
real-coefficient cohomology (`dim_ℂ (V ⊗_ℝ ℂ) = dim_ℝ V`).

This identity moves between the ℝ-valued de Rham picture (which matches
singular cohomology over ℝ) and the ℂ-valued one (which carries Hodge
decomposition). It is equality, **not** doubling — the
`realDimDeRhamH1` is the real dim of the real-coefficient cohomology,
not of the complex one viewed as a real vector space. -/
theorem realDim_deRhamH1_eq_complexDim_deRhamH1ℂ
    (X : Type) [TopologicalSpace X] [T2Space X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X] :
    realDimDeRhamH1 X = complexDimDeRhamH1ℂ X := by
  sorry

/-- **Frontier theorem (sorry).** Connected compact `X` has
`dim_ℂ H⁰_dR(X, ℂ) = 1`.

Bottom-up content: a global ℂ-valued de Rham 0-cocycle is a smooth
function `f : X → ℂ` with `df = 0`, i.e. a locally constant function.
On a connected space, locally constant means constant; the space of
constants is one-dimensional over ℂ.  This factors through Mathlib's
`holomorphic_compact_connected_constant` analogue (already in the
project as `Jacobian.HolomorphicForms.HolomorphicCompactConstant.lean`),
adapted to smooth ℂ-valued functions. -/
theorem complexDim_deRhamH0ℂ_eq_one_of_compact_connected
    (X : Type) [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X] :
    complexDimDeRhamH0ℂ X = 1 := by
  sorry

/-- **Frontier theorem (sorry).** Connected compact `X` has
`dim_ℝ H⁰_dR(X, ℝ) = 1`. The real version of the previous statement;
needed for the universal-coefficient bridge that links `H⁰_dR` over ℝ
to `H₀(X, ℤ) ≅ ℤ`. -/
theorem realDim_deRhamH0_eq_one_of_compact_connected
    (X : Type) [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X] :
    realDimDeRhamH0 X = 1 := by
  sorry

end JacobianChallenge.HolomorphicForms
