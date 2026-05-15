import Jacobian.HolomorphicForms.MeromorphicFunction
import Jacobian.HolomorphicForms.VanishingOrder
import Jacobian.HolomorphicForms.Divisor
import Mathlib.Geometry.Manifold.MFDeriv.Basic
import Jacobian.Periods.TrivializationContinuousLinearMapAt

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
  [JacobianChallenge.Periods.StableChartAt ℂ X]

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
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X]
    [JacobianChallenge.Periods.StableChartAt ℂ X] :
    MeromorphicFunctionType X :=
  { toFun := fun _ => (0 : ℂ)
    toFun_continuous := continuous_const
    isMeromorphic := fun p => by
      unfold MeromorphicAtX
      show MeromorphicAt ((fun _ => (0 : ℂ)) ∘ (extChartAt 𝓘(ℂ) p).symm) (extChartAt 𝓘(ℂ) p p)
      exact AnalyticAt.meromorphicAt analyticAt_const }

instance : Zero (MeromorphicFunctionType X) := ⟨zero X⟩

/-! ### Helper lemmas for addition of meromorphic functions -/

/-- If `(x : OnePoint ℂ).getD 0 ≠ 0`, then `x ≠ ∞`. -/
private lemma ne_infty_of_getD_ne_zero {x : OnePoint ℂ} (h : x.getD 0 ≠ 0) : x ≠ ∞ := by
  intro hx; subst hx; exact h rfl

/-
On a punctured neighborhood, a meromorphic-typed function's `toFun` is either
eventually finite or eventually `∞`.
-/
omit [JacobianChallenge.Periods.StableChartAt ℂ X] in
private lemma toFun_eventually_finite_or_infty (f : MeromorphicFunctionType X) (p : X) :
    (∀ᶠ z in nhdsWithin (extChartAt 𝓘(ℂ) p p) {extChartAt 𝓘(ℂ) p p}ᶜ,
      f.toFun ((extChartAt 𝓘(ℂ) p).symm z) ≠ ∞) ∨
    (∀ᶠ z in nhdsWithin (extChartAt 𝓘(ℂ) p p) {extChartAt 𝓘(ℂ) p p}ᶜ,
      f.toFun ((extChartAt 𝓘(ℂ) p).symm z) = ∞) := by
  by_cases h : f.toFun p = ∞;
  · have := f.isMeromorphic p;
    obtain h|h := this.eventually_eq_zero_or_eventually_ne_zero;
    · refine' Or.inr _;
      have h_cont : ∀ᶠ z in nhds p, f.toFun z ≠ OnePoint.some 0 := by
        exact f.toFun_continuous.continuousAt.eventually_ne ( by aesop );
      have h_cont : ∀ᶠ z in nhdsWithin (extChartAt 𝓘(ℂ) p p) {extChartAt 𝓘(ℂ) p p}ᶜ, f.toFun ((extChartAt 𝓘(ℂ) p).symm z) ≠ OnePoint.some 0 := by
        have h_cont : Filter.Tendsto (fun z => (extChartAt 𝓘(ℂ) p).symm z) (nhdsWithin (extChartAt 𝓘(ℂ) p p) {extChartAt 𝓘(ℂ) p p}ᶜ) (nhds p) := by
          have h_cont : Filter.Tendsto (fun z => (extChartAt 𝓘(ℂ) p).symm z) (nhds (extChartAt 𝓘(ℂ) p p)) (nhds p) := by
            have h_cont : ContinuousAt (fun z => (extChartAt 𝓘(ℂ) p).symm z) (extChartAt 𝓘(ℂ) p p) := by
              exact continuousAt_extChartAt_symm p;
            convert h_cont.tendsto using 1;
            simp +decide [ extChartAt ];
          exact h_cont.mono_left inf_le_left;
        exact h_cont.eventually ‹_›;
      filter_upwards [ h_cont, h ] with z hz₁ hz₂;
      cases h : f.toFun ( ( extChartAt 𝓘(ℂ) p ).symm z ) <;> aesop;
    · exact Or.inl ( h.mono fun x hx => by contrapose! hx; aesop );
  · left;
    have h_cont : ContinuousAt f.toFun p := by
      exact f.toFun_continuous.continuousAt;
    have h_cont : ContinuousAt (fun z => f.toFun ((extChartAt 𝓘(ℂ) p).symm z)) (extChartAt 𝓘(ℂ) p p) := by
      refine' ContinuousAt.comp _ _;
      · convert h_cont using 1;
        simp +decide [ extChartAt ];
      · refine' ContinuousAt.comp _ _;
        · exact continuousAt_extChartAt_symm p;
        · exact continuousAt_id;
    exact h_cont.eventually_ne ( by simp [ h ] ) |> fun h => h.filter_mono inf_le_left

/-
When `f.toFun` is eventually `∞` on a punctured neighborhood, the `getD 0` of
any match involving `f.toFun` is eventually `0`.
-/
omit [JacobianChallenge.Periods.StableChartAt ℂ X] in
private lemma getD_match_eq_zero_of_infty (f g : MeromorphicFunctionType X) (p : X)
    (hf : ∀ᶠ z in nhdsWithin (extChartAt 𝓘(ℂ) p p) {extChartAt 𝓘(ℂ) p p}ᶜ,
      f.toFun ((extChartAt 𝓘(ℂ) p).symm z) = ∞) :
    ∀ᶠ z in nhdsWithin (extChartAt 𝓘(ℂ) p p) {extChartAt 𝓘(ℂ) p p}ᶜ,
      (match f.toFun ((extChartAt 𝓘(ℂ) p).symm z),
            g.toFun ((extChartAt 𝓘(ℂ) p).symm z) with
        | some a, some b => ((a + b : ℂ) : OnePoint ℂ)
        | _, _ => ∞).getD 0 = 0 := by
  filter_upwards [ hf ] with z hz;
  rw [ hz ];
  cases g.toFun ( ( extChartAt 𝓘(ℂ) p ).symm z ) <;> rfl

/-
When both `f.toFun` and `g.toFun` are finite, the `getD 0` of the match
equals the sum of the `getD 0`'s.
-/
omit [JacobianChallenge.Periods.StableChartAt ℂ X] in
private lemma getD_match_eq_add_of_finite (f g : MeromorphicFunctionType X) (p : X)
    (hf : ∀ᶠ z in nhdsWithin (extChartAt 𝓘(ℂ) p p) {extChartAt 𝓘(ℂ) p p}ᶜ,
      f.toFun ((extChartAt 𝓘(ℂ) p).symm z) ≠ ∞)
    (hg : ∀ᶠ z in nhdsWithin (extChartAt 𝓘(ℂ) p p) {extChartAt 𝓘(ℂ) p p}ᶜ,
      g.toFun ((extChartAt 𝓘(ℂ) p).symm z) ≠ ∞) :
    ∀ᶠ z in nhdsWithin (extChartAt 𝓘(ℂ) p p) {extChartAt 𝓘(ℂ) p p}ᶜ,
      (match f.toFun ((extChartAt 𝓘(ℂ) p).symm z),
            g.toFun ((extChartAt 𝓘(ℂ) p).symm z) with
        | some a, some b => ((a + b : ℂ) : OnePoint ℂ)
        | _, _ => ∞).getD 0 =
      (f.toFun ((extChartAt 𝓘(ℂ) p).symm z)).getD 0 +
      (g.toFun ((extChartAt 𝓘(ℂ) p).symm z)).getD 0 := by
  filter_upwards [ hf, hg ] with z hz₁ hz₂;
  cases h : f.toFun ( ( extChartAt 𝓘(ℂ, ℂ) p ).symm z ) <;> cases h' : g.toFun ( ( extChartAt 𝓘(ℂ, ℂ) p ).symm z ) <;> simp_all +decide [ Option.getD ]

/-
The `isMeromorphic` obligation of `add_meromorphic`: the `getD 0` of the
pointwise sum is meromorphic at every point.
-/
omit [JacobianChallenge.Periods.StableChartAt ℂ X] in
lemma add_meromorphic_isMeromorphic (f g : MeromorphicFunctionType X) (p : X) :
    MeromorphicAtX
      (fun q => (match f.toFun q, g.toFun q with
        | some a, some b => ((a + b : ℂ) : OnePoint ℂ)
        | _, _ => ∞).getD 0) p := by
  -- Apply the lemma that states the sum of two meromorphic functions is meromorphic.
  apply (toFun_eventually_finite_or_infty f p).elim (fun hf => ?_) (fun hg => ?_);
  · apply (toFun_eventually_finite_or_infty g p).elim (fun hg => ?_) (fun hg => ?_);
    · have h_meromorphic : MeromorphicAt (fun z => (f.toFiniteFun ((extChartAt 𝓘(ℂ) p).symm z)) + (g.toFiniteFun ((extChartAt 𝓘(ℂ) p).symm z))) (extChartAt 𝓘(ℂ) p p) := by
        exact MeromorphicAt.add ( f.isMeromorphic p ) ( g.isMeromorphic p );
      have h_eq : ∀ᶠ z in nhdsWithin (extChartAt 𝓘(ℂ) p p) {extChartAt 𝓘(ℂ) p p}ᶜ, (match f.toFun ((extChartAt 𝓘(ℂ) p).symm z), g.toFun ((extChartAt 𝓘(ℂ) p).symm z) with
        | some a, some b => ((a + b : ℂ) : OnePoint ℂ)
        | _, _ => ∞).getD 0 = (f.toFiniteFun ((extChartAt 𝓘(ℂ) p).symm z)) + (g.toFiniteFun ((extChartAt 𝓘(ℂ) p).symm z)) := by
          exact getD_match_eq_add_of_finite f g p hf hg;
      convert h_meromorphic.congr _;
      filter_upwards [ h_eq ] with z hz using hz.symm;
    · refine' ( analyticAt_const.meromorphicAt.congr _ );
      exact 0;
      filter_upwards [ hg ] with z hz using by cases h : f.toFun ( extChartAt 𝓘(ℂ) p |>.symm z ) <;> aesop;
  · have h_zero : ∀ᶠ z in nhdsWithin (extChartAt 𝓘(ℂ) p p) {extChartAt 𝓘(ℂ) p p}ᶜ, (match f.toFun ((extChartAt 𝓘(ℂ) p).symm z), g.toFun ((extChartAt 𝓘(ℂ) p).symm z) with
      | some a, some b => ((a + b : ℂ) : OnePoint ℂ)
      | _, _ => ∞).getD 0 = 0 := by
        filter_upwards [ hg ] with z hz using by rw [ hz ] ; rfl;
    convert ( analyticAt_const.meromorphicAt.congr _ ) using 1;
    exacts [ 0, by filter_upwards [ h_zero ] with z hz; exact hz.symm ]

/-- Addition of meromorphic functions: pointwise sum on the Riemann sphere. -/
noncomputable def add_meromorphic (f g : MeromorphicFunctionType X) : MeromorphicFunctionType X :=
  { toFun := fun x =>
      match f.toFun x, g.toFun x with
      | some a, some b => ((a + b : ℂ) : OnePoint ℂ)
      | _, _ => ∞
    toFun_continuous := by sorry
    isMeromorphic := fun p => add_meromorphic_isMeromorphic f g p }

noncomputable instance : Add (MeromorphicFunctionType X) := ⟨add_meromorphic⟩

/-- The toFun of a sum is the pointwise sum (where both are finite). -/
theorem add_toFun {X : Type*} [TopologicalSpace X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X]
    [JacobianChallenge.Periods.StableChartAt ℂ X]
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
    [JacobianChallenge.Periods.StableChartAt ℂ X]
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
    [JacobianChallenge.Periods.StableChartAt ℂ X]
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

/-- Named blueprint hook for the meromorphic-function vector-space instance. -/
theorem meromorphicFunctionVectorSpace {X : Type*} [TopologicalSpace X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X]
    [JacobianChallenge.Periods.StableChartAt ℂ X] :
    Nonempty (Module ℂ (MeromorphicFunctionType X)) :=
  ⟨inferInstance⟩

/-- Coefficient of the zero divisor at a point. -/
noncomputable def zeros_coeff {X : Type*} [TopologicalSpace X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X]
    [JacobianChallenge.Periods.StableChartAt ℂ X]
    (f : MeromorphicFunctionType X) (p : X) : ℤ :=
  haveI := Classical.propDecidable (f.toFun p = (0 : ℂ))
  if f.toFun p = (0 : ℂ) then (orderAt p (fun q => (f q).getD 0)).untopD 0 else 0

/-- Coefficient of the pole divisor at a point. -/
noncomputable def poles_coeff {X : Type*} [TopologicalSpace X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X]
    [JacobianChallenge.Periods.StableChartAt ℂ X]
    (f : MeromorphicFunctionType X) (p : X) : ℤ :=
  haveI := Classical.propDecidable (f.toFun p = ∞)
  if f.toFun p = ∞ then -(orderAt p (fun q => (f q).getD 0)).untopD 0 else 0

/-- The zero divisor of a meromorphic function.

Defined via the vanishing order: for each point `p`, the coefficient is
`max 0 (orderAt p f.toFiniteFun)` when finite, and `0` otherwise.

Note: the finite-support obligation is deferred; on a compact Riemann
surface, the identity principle guarantees only finitely many zeros. -/
noncomputable def zeros {X : Type*} [TopologicalSpace X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X]
    [JacobianChallenge.Periods.StableChartAt ℂ X]
    (f : MeromorphicFunctionType X) : Divisor X :=
  Finsupp.onFinset (Classical.choice (sorry : Nonempty (Finset X)))
    (zeros_coeff f) (by sorry)

/-- The pole divisor of a meromorphic function. -/
noncomputable def poles {X : Type*} [TopologicalSpace X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X]
    [JacobianChallenge.Periods.StableChartAt ℂ X]
    (f : MeromorphicFunctionType X) : Divisor X :=
  Finsupp.onFinset (Classical.choice (sorry : Nonempty (Finset X)))
    (poles_coeff f) (by sorry)

/-- The principal divisor `(f) = (zeros) - (poles)`. -/
noncomputable def principal {X : Type*} [TopologicalSpace X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X]
    [JacobianChallenge.Periods.StableChartAt ℂ X]
    (f : MeromorphicFunctionType X) : Divisor X :=
  f.zeros - f.poles

/-!
### Blocker analysis for `toFun_ne_infty_of_poles_eq_zero`

**Status (2026-05-12):** sorry — the theorem is currently *unprovable*
as stated, and provably so, because the upstream `poles` definition is
a data-trivial placeholder.

#### The placeholder

`MeromorphicFunctionType.poles` (line 312) is

```
noncomputable def poles (_f : MeromorphicFunctionType X) : Divisor X := 0
```

The `_f` binder is unused: `poles` returns `(0 : Divisor X)` for every
input. Hence `f.poles = 0` reduces to `(0 : Divisor X) = (0 : Divisor X)`,
which is `rfl` and carries no information about `f`.

#### Counterexample to the current statement

The constant-∞ map is a valid `MeromorphicFunctionType X`:

* `toFun := fun _ => (∞ : OnePoint ℂ)` is continuous (constant);
* the ℂ-projection `(toFun q).getD 0` evaluates to `(0 : ℂ)` (because
  `(∞ : OnePoint ℂ).getD 0 = 0`), and the constant-`0` function is
  analytic, hence `MeromorphicAt` at every point.

For this `f`, the hypothesis `h : f.poles = 0` is satisfied (vacuously
by `rfl`), yet the conclusion `∀ x, f.toFun x ≠ ∞` is false — every
point witnesses `f.toFun x = ∞`.

#### Why a non-degenerate proof is blocked

The mission strategy assumes `poles` records pole orders, i.e., that
`(f.poles).point_apply p` (or similar) extracts `-orderAt p f.toFiniteFun`
when the order is negative. With the current placeholder, no such
extraction is possible: `f.poles` literally throws `f` away.

A real definition would set, point-wise,
`(poles f) p = (-orderAt p f.toFiniteFun).toNat.max 0`, but constructing
this as a `Divisor X = X →₀ ℤ` requires *finite support* of
`{p | orderAt p f.toFiniteFun < 0}`, which is **not provable without a
compactness assumption** on `X` (the typeclass context here is only
`TopologicalSpace`, `ChartedSpace ℂ`, and `IsManifold 𝓘(ℂ) ⊤`; there is
no `[CompactSpace X]`).

#### Suggested path forward

Two non-degenerate options, both out of scope for this single-file
proof task per the mission's ANTI-CHEAT CLAUSE:

1. **Widen scope to refine `poles`.** Replace the placeholder with a
   real `VanishingOrder`-based definition. This needs either
   `[CompactSpace X]` added to `MeromorphicFunctionType` (or to `poles`
   specifically) plus a chart-local finiteness lemma routed through
   `MeromorphicOn.isClopen_setOf_meromorphicOrderAt_eq_top` and the
   identity-principle infrastructure already in `VanishingOrder.lean`.
2. **Restate via the existing predicate.** The file already defines
   `is_holomorphic f := ∀ x, f.toFun x ≠ ∞` (line 29). The intended
   structural bridge could be reformulated to take `is_holomorphic f`
   as hypothesis directly, deferring the `poles = 0 ↔ is_holomorphic`
   equivalence to a separate theorem proved *after* `poles` is refined.

Per the ANTI-CHEAT CLAUSE ("If you find a definition is insufficient
for a real proof, STOP and report the issue rather than providing a
degenerate solution"), the `sorry` is preserved unchanged. -/

/-- Structural bridge: if `f.poles = 0`, then `f.toFun` never takes the value `∞`.
This encodes the semantic content of "no poles means no infinities". -/
theorem toFun_ne_infty_of_poles_eq_zero {X : Type*} [TopologicalSpace X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X]
    [JacobianChallenge.Periods.StableChartAt ℂ X]
    (f : MeromorphicFunctionType X) (h : f.poles = 0) :
    ∀ x, f.toFun x ≠ ∞ :=
  sorry

/-- Structural bridge: if `f.toFun` never takes the value `∞`, then
`f.toFiniteFun` is `MDifferentiable`. -/
theorem mdifferentiable_toFiniteFun_of_no_infty {X : Type*} [TopologicalSpace X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X]
    [JacobianChallenge.Periods.StableChartAt ℂ X]
    (f : MeromorphicFunctionType X) (h : ∀ x, f.toFun x ≠ ∞) :
    MDifferentiable (modelWithCornersSelf ℂ ℂ) (modelWithCornersSelf ℂ ℂ) f.toFiniteFun :=
  sorry

/-- Constant meromorphic functions have no poles. -/
theorem constant_poles {X : Type*} [TopologicalSpace X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X]
    [JacobianChallenge.Periods.StableChartAt ℂ X]
    (c : ℂ) : (constant (X := X) c).poles = 0 :=
  sorry

/-- Non-zero constant meromorphic functions have no zeros. -/
theorem constant_zeros {X : Type*} [TopologicalSpace X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X]
    [JacobianChallenge.Periods.StableChartAt ℂ X]
    (c : ℂ) (_hc : c ≠ 0) : (constant (X := X) c).zeros = 0 :=
  sorry

/-- Membership in the Riemann-Roch space `L(D)`: `f = 0` or `(f) + D ≥ 0`. -/
def MemRiemannRochSpace {X : Type*} [TopologicalSpace X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X]
    [JacobianChallenge.Periods.StableChartAt ℂ X]
    (f : MeromorphicFunctionType X) (D : Divisor X) : Prop :=
  f = 0 ∨ Divisor.Effective (f.principal + D)

end MeromorphicFunctionType

end JacobianChallenge.HolomorphicForms
