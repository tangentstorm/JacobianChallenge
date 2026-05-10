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
      show MeromorphicAt ((fun _ => (0 : ℂ)) ∘ (extChartAt 𝓘(ℂ) p).symm) (extChartAt 𝓘(ℂ) p p)
      exact AnalyticAt.meromorphicAt analyticAt_const }

instance : Zero (MeromorphicFunctionType X) := ⟨zero X⟩

/-- Addition of meromorphic functions: pointwise sum on the Riemann sphere. -/
noncomputable def add_meromorphic (f g : MeromorphicFunctionType X) : MeromorphicFunctionType X :=
  { toFun := fun x =>
      match f.toFun x, g.toFun x with
      | some a, some b => ((a + b : ℂ) : OnePoint ℂ)
      | _, _ => ∞
    toFun_continuous := by sorry
    isMeromorphic := by sorry }

noncomputable instance : Add (MeromorphicFunctionType X) := ⟨add_meromorphic⟩

/-- The toFun of a sum is the pointwise sum (where both are finite). -/
theorem add_toFun {X : Type*} [TopologicalSpace X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X]
    (f g : MeromorphicFunctionType X) :
    ∀ x, f.toFun x ≠ ∞ → g.toFun x ≠ ∞ →
      (f + g).toFun x = ((f.toFun x).getD 0 + (g.toFun x).getD 0 : ℂ) := by
  intro x hx_f hx_g
  have h_eq : f.toFun x = some (f.toFiniteFun x) ∧ g.toFun x = some (g.toFiniteFun x) := by
    constructor
    · unfold toFiniteFun; cases h : f.toFun x with | infty => exact absurd h hx_f | coe v => rfl
    · unfold toFiniteFun; cases h : g.toFun x with | infty => exact absurd h hx_g | coe v => rfl
  rw [h_eq.1, h_eq.2]
  simp only [Option.getD_some]
  change (add_meromorphic f g).toFun x = _
  simp only [add_meromorphic, h_eq.1, h_eq.2]

/-- Negation of meromorphic functions. -/
noncomputable def neg_meromorphic (f : MeromorphicFunctionType X) : MeromorphicFunctionType X :=
  { toFun := fun x => OnePoint.map (fun c => -c) (f.toFun x)
    toFun_continuous := sorry
    isMeromorphic := sorry }

noncomputable instance : Neg (MeromorphicFunctionType X) := ⟨neg_meromorphic⟩

/-- The toFun of a negation is the pointwise negation. -/
theorem neg_toFun {X : Type*} [TopologicalSpace X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X]
    (f : MeromorphicFunctionType X) :
    ∀ x, f.toFun x ≠ ∞ → (-f).toFun x = (-(f.toFun x).getD 0 : ℂ) := by
  intro x hx
  show (neg_meromorphic f).toFun x = ↑(-(f.toFun x).getD 0)
  simp only [neg_meromorphic]
  cases h : f.toFun x with
  | infty => exact absurd h hx
  | coe c =>
    simp only [OnePoint.map, Option.getD]
    rfl

/-- Subtraction of meromorphic functions. -/
noncomputable instance : Sub (MeromorphicFunctionType X) := ⟨fun f g => f + (-g)⟩

/-- Scalar multiplication of meromorphic functions. -/
noncomputable def smul_meromorphic (c : ℂ) (f : MeromorphicFunctionType X) : MeromorphicFunctionType X :=
  { toFun := fun x => OnePoint.map (c * ·) (f.toFun x)
    toFun_continuous := sorry
    isMeromorphic := sorry }

noncomputable instance : SMul ℂ (MeromorphicFunctionType X) := ⟨smul_meromorphic⟩

/-- The toFun of a scalar multiplication is the pointwise multiplication. -/
theorem smul_toFun {X : Type*} [TopologicalSpace X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X]
    (c : ℂ) (f : MeromorphicFunctionType X) :
    ∀ x, f.toFun x ≠ ∞ → (c • f).toFun x = (c * (f.toFun x).getD 0 : ℂ) := by
  intro x hx
  show (smul_meromorphic c f).toFun x = ↑(c * Option.getD (f.toFun x) 0)
  simp only [smul_meromorphic]
  cases h : f.toFun x with
  | infty => exact absurd h hx
  | coe z => rfl

/-- Constant meromorphic functions. -/
def constant (c : ℂ) : MeromorphicFunctionType X :=
  { toFun := fun _ => (c : OnePoint ℂ)
    toFun_continuous := continuous_const
    isMeromorphic := fun p => by
      unfold MeromorphicAtX
      show MeromorphicAt ((fun _ => c) ∘ (extChartAt 𝓘(ℂ) p).symm) (extChartAt 𝓘(ℂ) p p)
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

/-! ### Vanishing-order based pole and zero counts -/

/-- The underlying ℂ-valued function obtained by projecting the Riemann sphere
map through `Option.getD 0`. This is the function whose vanishing order we
compute in charts. -/
noncomputable def underlyingFun {X : Type*} [TopologicalSpace X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X]
    (f : MeromorphicFunctionType X) : X → ℂ :=
  fun q => (f.toFun q).getD 0

/-- The pole order of a meromorphic function at a point `p`.

If the vanishing order `ord_p(f)` is a finite negative integer `n < 0`,
the pole order is `(-n) > 0`. Otherwise (non-negative order or `⊤`), 0. -/
noncomputable def poleOrderAt {X : Type*} [TopologicalSpace X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X]
    (f : MeromorphicFunctionType X) (p : X) : ℤ :=
  match orderAt p f.underlyingFun with
  | ⊤ => 0
  | (n : ℤ) => max 0 (-n)

/-- The zero order of a meromorphic function at a point `p`.

If the vanishing order `ord_p(f)` is a finite positive integer `n > 0`,
the zero order is `n`. Otherwise, 0. -/
noncomputable def zeroOrderAt {X : Type*} [TopologicalSpace X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X]
    (f : MeromorphicFunctionType X) (p : X) : ℤ :=
  match orderAt p f.underlyingFun with
  | ⊤ => 0
  | (n : ℤ) => max 0 n

/-- The pole order is always nonnegative. -/
theorem poleOrderAt_nonneg {X : Type*} [TopologicalSpace X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X]
    (f : MeromorphicFunctionType X) (p : X) : 0 ≤ poleOrderAt f p := by
  unfold poleOrderAt
  cases orderAt p f.underlyingFun with
  | top => exact le_refl 0
  | coe n => exact le_max_left 0 (-n)

/-- The zero order is always nonnegative. -/
theorem zeroOrderAt_nonneg {X : Type*} [TopologicalSpace X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X]
    (f : MeromorphicFunctionType X) (p : X) : 0 ≤ zeroOrderAt f p := by
  unfold zeroOrderAt
  cases orderAt p f.underlyingFun with
  | top => exact le_refl 0
  | coe n => exact le_max_left 0 n

/-- **(Existence lemma — proof deferred.)** The set of poles of a
meromorphic function on a compact complex 1-manifold is finite,
i.e. `poleOrderAt f` has finite support. On a compact Riemann surface
this follows from the discreteness of poles plus compactness. -/
theorem poleOrderAt_finite_support {X : Type*} [TopologicalSpace X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X]
    (f : MeromorphicFunctionType X) :
    (Function.support (poleOrderAt f)).Finite := by sorry

/-- **(Existence lemma — proof deferred.)** The set of zeros of a
meromorphic function on a compact complex 1-manifold is finite,
i.e. `zeroOrderAt f` has finite support. -/
theorem zeroOrderAt_finite_support {X : Type*} [TopologicalSpace X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X]
    (f : MeromorphicFunctionType X) :
    (Function.support (zeroOrderAt f)).Finite := by sorry

/-- The pole divisor of a meromorphic function.

Assigns to each point `p` the pole order `max(0, -ord_p(f))`, which is
a nonneg integer that is positive exactly at poles. The resulting function
has finite support (deferred to `poleOrderAt_finite_support`), so it
defines a divisor `X →₀ ℤ`. -/
noncomputable def poles {X : Type*} [TopologicalSpace X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X]
    (f : MeromorphicFunctionType X) : Divisor X :=
  Finsupp.ofSupportFinite (poleOrderAt f) (poleOrderAt_finite_support f)

/-- The zero divisor of a meromorphic function.

Assigns to each point `p` the zero order `max(0, ord_p(f))`, which is
a nonneg integer that is positive exactly at zeros. -/
noncomputable def zeros {X : Type*} [TopologicalSpace X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X]
    (f : MeromorphicFunctionType X) : Divisor X :=
  Finsupp.ofSupportFinite (zeroOrderAt f) (zeroOrderAt_finite_support f)

/-- The principal divisor `(f) = (zeros) - (poles)`. -/
noncomputable def principal {X : Type*} [TopologicalSpace X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X]
    (f : MeromorphicFunctionType X) : Divisor X :=
  f.zeros - f.poles

/-- The pole divisor is effective (all coefficients ≥ 0). -/
theorem poles_effective {X : Type*} [TopologicalSpace X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X]
    (f : MeromorphicFunctionType X) : Divisor.Effective f.poles := by
  intro p
  show poleOrderAt f p ≥ 0
  exact poleOrderAt_nonneg f p

/-- The zero divisor is effective (all coefficients ≥ 0). -/
theorem zeros_effective {X : Type*} [TopologicalSpace X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X]
    (f : MeromorphicFunctionType X) : Divisor.Effective f.zeros := by
  intro p
  show zeroOrderAt f p ≥ 0
  exact zeroOrderAt_nonneg f p

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

/-
Constant meromorphic functions have no poles.
-/
theorem constant_poles {X : Type*} [TopologicalSpace X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X]
    (c : ℂ) : (constant (X := X) c).poles = 0 := by
  ext p
  simp only [poles, Finsupp.ofSupportFinite_coe, Finsupp.coe_zero, Pi.zero_apply]
  unfold poleOrderAt underlyingFun
  -- The constant function has underlying function `fun _ => c`. In any chart, the pullback is the constant function `fun _ => c`, which is analytic. Its meromorphicOrderAt is 0 (if c ≠ 0) or ⊤ (if c = 0). In both cases, poleOrderAt = max(0, -n) where n ≥ 0, so poleOrderAt = 0. Hence, the Finsupp is identically 0.
  simp [constant, orderAt] at *;
  rw [ Function.comp_def ];
  -- Since the constant function is analytic, its meromorphic order is 0.
  have h_const_analytic : AnalyticAt ℂ (fun _ => c) (extChartAt 𝓘(ℂ) p p) := by
    exact analyticAt_const;
  erw [ h_const_analytic.meromorphicOrderAt_eq ];
  rw [ analyticOrderAt ];
  split_ifs <;> simp_all +decide

/-
Non-zero constant meromorphic functions have no zeros.
-/
theorem constant_zeros {X : Type*} [TopologicalSpace X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X]
    (c : ℂ) (hc : c ≠ 0) : (constant (X := X) c).zeros = 0 :=
  by
    ext x;
    erw [ Finsupp.coe_mk ];
    unfold MeromorphicFunctionType.zeroOrderAt;
    unfold orderAt;
    erw [ show ( constant c |> MeromorphicFunctionType.underlyingFun ) ∘ ( extChartAt 𝓘(ℂ, ℂ) x ).symm = fun _ => c from funext fun _ => ?_ ];
    · rw [ show ( fun _ => c ) = ( fun _ => c ) from rfl, meromorphicOrderAt_const ] ; aesop;
    · exact Complex.ext rfl rfl

/-- Membership in the Riemann-Roch space `L(D)`: `f = 0` or `(f) + D ≥ 0`. -/
def MemRiemannRochSpace {X : Type*} [TopologicalSpace X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X]
    (f : MeromorphicFunctionType X) (D : Divisor X) : Prop :=
  f = 0 ∨ Divisor.Effective (f.principal + D)

end MeromorphicFunctionType

end JacobianChallenge.HolomorphicForms