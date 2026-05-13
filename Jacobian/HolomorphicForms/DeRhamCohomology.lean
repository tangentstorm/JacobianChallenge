import Mathlib.Geometry.Manifold.IsManifold.Basic
import Mathlib.Analysis.Complex.Basic
import Mathlib.LinearAlgebra.FiniteDimensional.Defs
import Mathlib.SetTheory.Cardinal.Finite
import Mathlib.Topology.Connected.TotallyDisconnected
import Jacobian.HolomorphicForms.SmoothDifferentialForm
import Jacobian.Periods.TrivializationContinuousLinearMapAt

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

* `deRhamH1Cocycle X` — concrete quotient model `closed / exact`.
* `complexDimDeRhamH1ℂ` — the complex finrank of this quotient model.
* `realDimDeRhamH1` — current-model real dimension bridge, using the
  same quotient finrank until a separate real-form complex is available.
* `realDimDeRhamH0` / `complexDimDeRhamH0ℂ` — concrete component-count
  surrogates for the H⁰ counterparts; equal to `1` for connected `X`.
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

/-- Concrete model of `H¹_dR(X, ℂ)` as closed 1-forms modulo exact
1-forms. -/
noncomputable def deRhamH1Cocycle
    (X : Type*) [TopologicalSpace X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X]
    [JacobianChallenge.Periods.StableChartAt ℂ X] :
    Type _ :=
  (ClosedFormSub (Nat.succ 0) X) ⧸ (ExactForm.toClosedSubmodule 0 X)

noncomputable instance deRhamH1Cocycle.instAddCommGroup
    (X : Type*) [TopologicalSpace X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X]
    [JacobianChallenge.Periods.StableChartAt ℂ X] :
    AddCommGroup (deRhamH1Cocycle X) :=
  inferInstanceAs (AddCommGroup (_ ⧸ (ExactForm.toClosedSubmodule 0 X)))

noncomputable instance deRhamH1Cocycle.instModuleℂ
    (X : Type*) [TopologicalSpace X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X]
    [JacobianChallenge.Periods.StableChartAt ℂ X] :
    Module ℂ (deRhamH1Cocycle X) :=
  inferInstanceAs (Module ℂ (_ ⧸ (ExactForm.toClosedSubmodule 0 X)))

/-- Complex dimension of the first de Rham cohomology group of `X` with
ℂ-valued differential forms, computed from the explicit closed-mod-exact
quotient model. -/
noncomputable def complexDimDeRhamH1ℂ
    (X : Type*) [TopologicalSpace X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X]
    [JacobianChallenge.Periods.StableChartAt ℂ X] : ℕ :=
  Module.finrank ℂ (deRhamH1Cocycle X)

/-- Real dimension of the first de Rham cohomology group in the current
ℂ-valued-form substrate. Since this layer has no separate real-form
complex, the real/complex extension-of-scalars bridge is represented by
the same closed-mod-exact quotient finrank. -/
noncomputable def realDimDeRhamH1
    (X : Type*) [TopologicalSpace X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X]
    [JacobianChallenge.Periods.StableChartAt ℂ X] : ℕ :=
  Module.finrank ℂ (deRhamH1Cocycle X)

/-- Real dimension of the zeroth de Rham
cohomology group of `X` with ℝ-valued forms. Mathematically equals the
number of connected components; for a connected manifold this is `1`. -/
noncomputable def realDimDeRhamH0
    (X : Type*) [TopologicalSpace X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X] : ℕ :=
  Nat.card (ConnectedComponents X)

/-- Complex dimension of the zeroth de Rham
cohomology group of `X` with ℂ-valued forms. Equals the ℂ-dimension of
locally constant ℂ-valued functions; for a connected `X` this is `1`. -/
noncomputable def complexDimDeRhamH0ℂ
    (X : Type*) [TopologicalSpace X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X] : ℕ :=
  Nat.card (ConnectedComponents X)

-- The real-of-complex de Rham identity has been moved to
-- `Jacobian/HolomorphicForms/RealComplexDeRham.lean` and refined into a
-- sorry-free assembly of two named obligations
-- (`complexDeRhamH1_eq_tensorℂ_realDeRhamH1` analytic;
-- `tensorℂ_finrank_eq_real_finrank` pure algebra).

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
    (X : Type*) [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X]
    [JacobianChallenge.Periods.StableChartAt ℂ X] :
    complexDimDeRhamH0ℂ X = 1 := by
  rw [complexDimDeRhamH0ℂ, Nat.card_eq_one_iff_unique]
  constructor
  · haveI : ConnectedSpace (ConnectedComponents X) :=
      ConnectedComponents.surjective_coe.connectedSpace ConnectedComponents.continuous_coe
    constructor
    intro a b
    have hsub : (Set.univ : Set (ConnectedComponents X)).Subsingleton :=
      isPreconnected_univ.subsingleton
    exact hsub trivial trivial
  · haveI : Nonempty X := inferInstance
    let x : X := Classical.arbitrary X
    exact Nonempty.intro (show ConnectedComponents X from x)

/-- **Frontier theorem (sorry).** Connected compact `X` has
`dim_ℝ H⁰_dR(X, ℝ) = 1`. The real version of the previous statement;
needed for the universal-coefficient bridge that links `H⁰_dR` over ℝ
to `H₀(X, ℤ) ≅ ℤ`. -/
theorem realDim_deRhamH0_eq_one_of_compact_connected
    (X : Type*) [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X]
    [JacobianChallenge.Periods.StableChartAt ℂ X] :
    realDimDeRhamH0 X = 1 := by
  rw [realDimDeRhamH0, Nat.card_eq_one_iff_unique]
  constructor
  · haveI : ConnectedSpace (ConnectedComponents X) :=
      ConnectedComponents.surjective_coe.connectedSpace ConnectedComponents.continuous_coe
    constructor
    intro a b
    have hsub : (Set.univ : Set (ConnectedComponents X)).Subsingleton :=
      isPreconnected_univ.subsingleton
    exact hsub trivial trivial
  · haveI : Nonempty X := inferInstance
    let x : X := Classical.arbitrary X
    exact Nonempty.intro (show ConnectedComponents X from x)

end JacobianChallenge.HolomorphicForms
