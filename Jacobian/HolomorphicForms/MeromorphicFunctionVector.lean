import Jacobian.HolomorphicForms.MeromorphicFunction
import Jacobian.HolomorphicForms.VanishingOrder
import Jacobian.HolomorphicForms.Divisor
import Mathlib.Geometry.Manifold.MFDeriv.Basic

/-!
# Meromorphic functions on a complex 1-manifold form a ℂ-vector space

This file provides the additive and scalar action structure for the
field of meromorphic functions `Mer(X)`.

Note: full Field structure requires the inversion of non-zero germs,
which is deferred. This file focuses on the linear-algebraic skeleton
needed for the Riemann-Roch dimension argument.
-/

namespace JacobianChallenge.HolomorphicForms

open scoped Manifold OnePoint
open JacobianChallenge.HolomorphicForms.VanishingOrder

variable {X : Type*} [TopologicalSpace X] [ChartedSpace ℂ X]
  [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X]

namespace MeromorphicFunctionType

/-- Structural axiom (S1a). When the pole divisor is 0, the map
f.toMap never takes the value ∞. -/
def is_holomorphic (f : MeromorphicFunctionType X) : Prop :=
  ∀ x, f.toFun x ≠ ∞

/-- If f is holomorphic, we can project it to ℂ. -/
def toFiniteFun (f : MeromorphicFunctionType X) : X → ℂ :=
  fun x => (f.toFun x).getD 0

/-- The zero meromorphic function. -/
def zero (X : Type*) [TopologicalSpace X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X] :
    MeromorphicFunctionType X :=
  { toFun := fun _ => (0 : ℂ)
    toFun_continuous := continuous_const
    isMeromorphic := fun p => by
      unfold MeromorphicAtX
      have : (fun _ : ℂ => (0 : ℂ)) = (fun q : X => (((0 : ℂ) : OnePoint ℂ).getD 0)) ∘ (extChartAt 𝓘(ℂ) p).symm := by
        ext
        rfl
      rw [← this]
      exact AnalyticAt.meromorphicAt analyticAt_const }

instance : Zero (MeromorphicFunctionType X) := ⟨zero X⟩

/-- Addition of meromorphic functions (axiomatic skeleton). -/
noncomputable axiom add_meromorphic (f g : MeromorphicFunctionType X) : MeromorphicFunctionType X

noncomputable instance : Add (MeromorphicFunctionType X) := ⟨add_meromorphic⟩

/-- The toFun of a sum is the pointwise sum (where both are finite). -/
theorem add_toFun {X : Type*} [TopologicalSpace X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X]
    (f g : MeromorphicFunctionType X) :
    ∀ x, f.toFun x ≠ ∞ → g.toFun x ≠ ∞ →
      (f + g).toFun x = ((f.toFun x).getD 0 + (g.toFun x).getD 0 : ℂ) :=
  sorry

/-- Negation of meromorphic functions (axiomatic skeleton). -/
noncomputable axiom neg_meromorphic (f : MeromorphicFunctionType X) : MeromorphicFunctionType X

noncomputable instance : Neg (MeromorphicFunctionType X) := ⟨neg_meromorphic⟩

/-- The toFun of a negation is the pointwise negation. -/
theorem neg_toFun {X : Type*} [TopologicalSpace X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X]
    (f : MeromorphicFunctionType X) :
    ∀ x, f.toFun x ≠ ∞ → (-f).toFun x = (-(f.toFun x).getD 0 : ℂ) :=
  sorry

/-- Subtraction of meromorphic functions. -/
noncomputable instance : Sub (MeromorphicFunctionType X) := ⟨fun f g => f + (-g)⟩

/-- Scalar multiplication of meromorphic functions (axiomatic skeleton). -/
noncomputable axiom smul_meromorphic (c : ℂ) (f : MeromorphicFunctionType X) : MeromorphicFunctionType X

noncomputable instance : SMul ℂ (MeromorphicFunctionType X) := ⟨smul_meromorphic⟩

/-- The toFun of a scalar multiplication is the pointwise multiplication. -/
theorem smul_toFun {X : Type*} [TopologicalSpace X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X]
    (c : ℂ) (f : MeromorphicFunctionType X) :
    ∀ x, f.toFun x ≠ ∞ → (c • f).toFun x = (c * (f.toFun x).getD 0 : ℂ) :=
  sorry

/-- Constant meromorphic functions. -/
def constant (c : ℂ) : MeromorphicFunctionType X :=
  { toFun := fun _ => (c : OnePoint ℂ)
    toFun_continuous := continuous_const
    isMeromorphic := fun p => by
      unfold MeromorphicAtX
      have : (fun q => ((c : OnePoint ℂ) : OnePoint ℂ).getD 0) ∘
        (extChartAt 𝓘(ℂ) p).symm = fun _ => c := by ext; rfl
      rw [this]
      exact AnalyticAt.meromorphicAt analyticAt_const }

/-- The ℂ-vector space structure on `Mer(X)`. -/
noncomputable instance : AddCommGroup (MeromorphicFunctionType X) :=
  { zero := 0
    add := (· + ·)
    neg := Neg.neg
    nsmul := nsmulRec
    zsmul := zsmulRec
    add_assoc := fun f g h => sorry
    zero_add := fun f => sorry
    add_zero := fun f => sorry
    add_comm := fun f g => sorry
    neg_add_cancel := fun f => sorry }

noncomputable instance : Module ℂ (MeromorphicFunctionType X) :=
  { smul := (· • ·)
    one_smul := fun f => sorry
    mul_smul := fun c d f => sorry
    smul_add := fun c f g => sorry
    smul_zero := fun c => sorry
    add_smul := fun c d f => sorry
    zero_smul := fun f => sorry }

/-- The zero divisor of a meromorphic function. -/
noncomputable def zeros {X : Type*} [TopologicalSpace X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X]
    (f : MeromorphicFunctionType X) : Divisor X :=
  sorry

/-- The pole divisor of a meromorphic function. -/
noncomputable def poles {X : Type*} [TopologicalSpace X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X]
    (f : MeromorphicFunctionType X) : Divisor X :=
  sorry

/-- The principal divisor `(f) = (zeros) - (poles)`. -/
noncomputable def principal {X : Type*} [TopologicalSpace X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X]
    (f : MeromorphicFunctionType X) : Divisor X :=
  f.zeros - f.poles

/-- Structural bridge: if `f.poles = 0`, then `f.toFun` never takes the value `∞`.
This encodes the semantic content of "no poles means no infinities". -/
theorem toFun_ne_infty_of_poles_eq_zero {X : Type*} [TopologicalSpace X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X]
    (f : MeromorphicFunctionType X) (h : f.poles = 0) :
    ∀ x, f.toFun x ≠ ∞ :=
  sorry

/-- Structural bridge: if `f.toFun` never takes the value `∞`, then
`f.toFiniteFun` is `MDifferentiable`. -/
theorem mdifferentiable_toFiniteFun_of_no_infty {X : Type*} [TopologicalSpace X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X]
    (f : MeromorphicFunctionType X) (h : ∀ x, f.toFun x ≠ ∞) :
    MDifferentiable (modelWithCornersSelf ℂ ℂ) (modelWithCornersSelf ℂ ℂ) f.toFiniteFun :=
  sorry

/-- Constant meromorphic functions have no poles. -/
theorem constant_poles {X : Type*} [TopologicalSpace X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X]
    (c : ℂ) : (constant (X := X) c).poles = 0 :=
  sorry

/-- Non-zero constant meromorphic functions have no zeros. -/
theorem constant_zeros {X : Type*} [TopologicalSpace X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X]
    (c : ℂ) (hc : c ≠ 0) : (constant (X := X) c).zeros = 0 :=
  sorry

/-- Membership in the Riemann-Roch space `L(D)`: `f = 0` or `(f) + D ≥ 0`. -/
def MemRiemannRochSpace {X : Type*} [TopologicalSpace X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X]
    (f : MeromorphicFunctionType X) (D : Divisor X) : Prop :=
  f = 0 ∨ Divisor.Effective (f.principal + D)

end MeromorphicFunctionType

end JacobianChallenge.HolomorphicForms
