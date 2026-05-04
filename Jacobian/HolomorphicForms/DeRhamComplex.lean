import Jacobian.HolomorphicForms.SmoothDifferentialForm
import Jacobian.HolomorphicForms.DeRhamCohomology
import Jacobian.HolomorphicForms.RealComplexDeRham

/-!
# Bridge between de Rham cohomology dimensions and the explicit complex

`Jacobian/HolomorphicForms/DeRhamCohomology.lean` exposes
`complexDimDeRhamH1ℂ X : ℕ` as an opaque ℕ.  This file connects that
opaque to an **explicit** description: H¹_dR is the quotient of closed
1-forms by exact 1-forms, and its complex dimension is
`Module.finrank ℂ (closed / exact)`.

## What this file provides (round 2 refinement)

* `deRhamH1Cocycle X` — concrete model of `H¹_dR(X, ℂ)` as the quotient
  of closed 1-forms by the image of `d`.
* `deRhamH1Cocycle_finrank_eq_complexDimDeRhamH1ℂ` — frontier identity
  (sorry): the explicit quotient model has the right ℕ dimension.
* `complexDimDeRhamH1ℂ_eq_finrank_quotient` — alternative form of the
  same identity.

## TOPDOWN role

This file makes the previously-opaque `complexDimDeRhamH1ℂ X`
*observable*: a refinement chain ending here can express its leaf
content in terms of concrete quotient `Module.finrank` computations.
-/

namespace JacobianChallenge.HolomorphicForms

open scoped Manifold

/-- **Concrete model.** `H¹_dR(X, ℂ)` realised as the quotient of
closed 1-forms by the image of `d : Ω⁰ → Ω¹` in closed 1-forms.

Defined as a `Submodule.Quotient` to get `AddCommGroup` and `Module ℂ`
instances for free. -/
noncomputable def deRhamH1Cocycle
    (X : Type*) [TopologicalSpace X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X] :
    Type _ :=
  (ClosedFormSub (Nat.succ 0) X) ⧸ (ExactForm.toClosedSubmodule 0 X)

-- Make the AddCommGroup / Module instances visible at use sites.
noncomputable instance deRhamH1Cocycle.instAddCommGroup
    (X : Type*) [TopologicalSpace X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X] :
    AddCommGroup (deRhamH1Cocycle X) :=
  inferInstanceAs (AddCommGroup (_ ⧸ (ExactForm.toClosedSubmodule 0 X)))

noncomputable instance deRhamH1Cocycle.instModuleℂ
    (X : Type*) [TopologicalSpace X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X] :
    Module ℂ (deRhamH1Cocycle X) :=
  inferInstanceAs (Module ℂ (_ ⧸ (ExactForm.toClosedSubmodule 0 X)))

/-- **Frontier identity (sorry).** `complexDimDeRhamH1ℂ X` (the opaque
ℕ) coincides with the ℂ-finrank of the explicit closed-mod-exact
quotient model.

This is the *defining* identity for `complexDimDeRhamH1ℂ X` once the
de Rham complex is in place.  The opacity in `DeRhamCohomology.lean`
exists precisely because the explicit model is missing in Mathlib;
this identity is the bridge. -/
theorem complexDimDeRhamH1ℂ_eq_finrank_cocycle
    (X : Type*) [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X] :
    complexDimDeRhamH1ℂ X = Module.finrank ℂ (deRhamH1Cocycle X) := by
  sorry

/-- **Companion frontier identity (sorry).** Real-coefficient analogue
of the previous identity. Used to match `realDimDeRhamH1` to a concrete
real-coefficient quotient when the real de Rham complex is set up. -/
theorem realDimDeRhamH1_eq_finrank_cocycleℝ
    (X : Type*) [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X] :
    realDimDeRhamH1 X = Module.finrank ℂ (deRhamH1Cocycle X) := by
  rw [realDim_deRhamH1_eq_complexDim_deRhamH1ℂ X,
      complexDimDeRhamH1ℂ_eq_finrank_cocycle X]

end JacobianChallenge.HolomorphicForms
