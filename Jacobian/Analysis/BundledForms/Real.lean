import Mathlib.LinearAlgebra.Alternating.Basic
import Mathlib.Analysis.Calculus.FDeriv.Symmetric

/-!
# R9 — A real type for bundled differential forms (chart-local)

This file is the **first non-placeholder** layer of R9.  In place of
the `Omega := PUnit` skeleton in `Jacobian.StageB.DifferentialForms`,
we expose a concrete carrier:

  `BundledForm E k := E → (E [⋀^Fin k]→ₗ[ℝ] ℝ)`

i.e. a function from the model real Banach space `E` to the alternating
real `k`-multilinear forms on `E`.  This is the *trivialised*
version — it is what `Ω^k(M)` restricts to in any single chart of a
real manifold modelled on `E`.  The fully bundled version (smooth
sections of `Λᵏ T*M`) is the dependency `R9-sub-A` on the missing
alternating-form bundle in Mathlib v4.28.0; the trivialised version
suffices to prove the chart-local algebraic identities (`d² = 0`
on a chart, Leibniz on a chart) that drive the depth-first
refinement of R9 J2.

The module structure is inherited pointwise from
`AlternatingMap`'s `Module` instance over the function space.

## Why two definitions?

The skeleton `Omega := PUnit` lives in `StageB/DifferentialForms.lean`
and is consumed by ~10 downstream files (LaplaceBeltrami,
DeRhamComplex, HarmonicForms, …).  Replacing it in place would break
every downstream proof that currently relies on `Subsingleton (Omega …)`
to discharge a goal.  We therefore introduce `BundledForm` as a
parallel real definition; downstream migration happens incrementally.
-/

namespace JacobianChallenge.Analysis.BundledForms

universe u

variable (E : Type u) [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- **R9 real carrier (chart-local).**  `BundledForm E k` is the
trivialisation of `Ω^k(M)` over a chart of a manifold modelled on `E`:
a function sending each point of `E` to an alternating real
`k`-multilinear form on `E`. -/
def BundledForm (k : ℕ) : Type u :=
  E → (E [⋀^Fin k]→ₗ[ℝ] ℝ)

noncomputable instance (k : ℕ) : AddCommGroup (BundledForm E k) := by
  unfold BundledForm; infer_instance

noncomputable instance (k : ℕ) : Module ℝ (BundledForm E k) := by
  unfold BundledForm; infer_instance

/-! ### Round 2 — `Ω⁰` and the Schwarz-direct `d² = 0` -/

/-- **R9.1.3 (chart-local).**  `Ω⁰(E) ≃ (E → ℝ)`: an alternating
0-multilinear form is just a real number, so a 0-form on a chart is
just a function.  The equivalence is Mathlib's
`AlternatingMap.constLinearEquivOfIsEmpty` lifted pointwise. -/
noncomputable def zeroFormEquiv : BundledForm E 0 ≃ₗ[ℝ] (E → ℝ) where
  toFun ω x := ω x ![]
  invFun f := fun x =>
    AlternatingMap.constLinearEquivOfIsEmpty (R' := ℝ) (M'' := E)
      (N'' := ℝ) (ι := Fin 0) (f x)
  left_inv ω := by
    funext x
    apply AlternatingMap.ext
    intro v
    have hv : v = ![] := by funext i; exact i.elim0
    subst hv
    rfl
  right_inv f := by funext x; rfl
  map_add' ω ω' := by funext x; rfl
  map_smul' c ω := by funext x; rfl

/-- **R9 J2 chart-local for 0-forms (Schwarz-direct form).**
For a `C²` real-valued function `f` on `E` and any pair of tangent
vectors `(v, w)`, the antisymmetric part of the second Fréchet
derivative vanishes:
  `D²f x (v, w) − D²f x (w, v) = 0`.
This is exactly `d²f = 0` evaluated on the pair `(v, w)`, before
the alternating-form bookkeeping. -/
theorem dsq_zero_form_swap_zero
    (f : E → ℝ) (x : E) (hf : ContDiffAt ℝ 2 f x) (v w : E) :
    fderiv ℝ (fderiv ℝ f) x v w - fderiv ℝ (fderiv ℝ f) x w v = 0 := by
  have h : minSmoothness ℝ (2 : WithTop ℕ∞) ≤ (2 : WithTop ℕ∞) := by simp
  have hsymm := (hf.isSymmSndFDerivAt h).eq v w
  linarith

/-! ### Round 3 — `d` on 0-forms as a real linear map -/

/-- **R9.2.1 chart-local (k = 0).**  The exterior derivative of a
0-form is its Fréchet derivative, packaged into the `Fin 1`
alternating-map slot via `AlternatingMap.ofSubsingleton`. -/
noncomputable def exteriorDerivativeZero (f : BundledForm E 0) : BundledForm E 1 :=
  fun x =>
    AlternatingMap.ofSubsingleton ℝ E ℝ (0 : Fin 1)
      (fderiv ℝ (zeroFormEquiv E f) x)

/-- Pointwise unfolding of `exteriorDerivativeZero`. -/
@[simp] lemma exteriorDerivativeZero_apply
    (f : BundledForm E 0) (x : E) (v : Fin 1 → E) :
    exteriorDerivativeZero E f x v = fderiv ℝ (zeroFormEquiv E f) x (v 0) := by
  simp [exteriorDerivativeZero, AlternatingMap.ofSubsingleton]

/-! ### Round 4 — `d²f = 0` for 0-forms in alternating-form form -/

/-- **Auxiliary: differential of `fderiv f y` evaluated at a constant
linear-map argument.**  When `f : E → ℝ` is `C²` at `x`, the function
`y ↦ fderiv ℝ f y w` is differentiable at `x` and its derivative
applied at `v` equals `(fderiv (fderiv f)) x v w`.  This is the
specialisation of `fderiv_clm_apply` to a constant second factor. -/
theorem fderiv_apply_const_arg {f : E → ℝ} {x : E}
    (hf : ContDiffAt ℝ 2 f x) (v w : E) :
    fderiv ℝ (fun y => fderiv ℝ f y w) x v = fderiv ℝ (fderiv ℝ f) x v w := by
  have hdiff_clm : DifferentiableAt ℝ (fderiv ℝ f) x := by
    have h2 : ContDiffAt ℝ 1 (fderiv ℝ f) x := by
      have := (hf.fderiv_right (m := 1) (by norm_num : (1 + 1 : WithTop ℕ∞) ≤ 2))
      simpa using this
    exact h2.differentiableAt one_ne_zero
  have hconst : DifferentiableAt ℝ (fun _ : E => w) x := differentiableAt_const _
  have h := fderiv_clm_apply hdiff_clm hconst
  rw [h]
  simp

/-- **R9 chart-local d² = 0 for 0-forms (alternating form).**  For a
`C²` function `f` on `E` and any pair `(v, w)`, the antisymmetric
derivative of `df` vanishes:
  `Dᵥ (df _ ![w]) − D_w (df _ ![v]) = 0`.
This is the `d²f = 0` identity in the alternating-form formalism,
restricted to 0-forms. -/
theorem dsq_zero_form_alt
    (f : BundledForm E 0) (x : E)
    (hf : ContDiffAt ℝ 2 (zeroFormEquiv E f) x) (v w : E) :
    fderiv ℝ (fun y => exteriorDerivativeZero E f y ![w]) x v
      - fderiv ℝ (fun y => exteriorDerivativeZero E f y ![v]) x w = 0 := by
  have h_lhs :
      (fun y => exteriorDerivativeZero E f y ![w])
        = fun y => fderiv ℝ (zeroFormEquiv E f) y w := by
    funext y; simp
  have h_rhs :
      (fun y => exteriorDerivativeZero E f y ![v])
        = fun y => fderiv ℝ (zeroFormEquiv E f) y v := by
    funext y; simp
  rw [h_lhs, h_rhs, fderiv_apply_const_arg E hf v w,
      fderiv_apply_const_arg E hf w v]
  exact dsq_zero_form_swap_zero E _ x hf v w

/-! ### Round 5 — pullback of 0-forms by smooth maps -/

variable (F : Type u) [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- **R9.4.1 chart-local for 0-forms.**  Pullback of a 0-form along
any function `φ : E → F` is precomposition.  This is the trivialised
analogue of `f^* ω = ω ∘ f` on the function side of `Ω⁰`.  Linearity
in `ω` and naturality (composition of pullbacks) are immediate. -/
noncomputable def pullbackZero (φ : E → F) :
    BundledForm F 0 →ₗ[ℝ] BundledForm E 0 where
  toFun ω := fun x =>
    AlternatingMap.constLinearEquivOfIsEmpty
      (R' := ℝ) (M'' := E) (N'' := ℝ) (ι := Fin 0)
      ((zeroFormEquiv F ω) (φ x))
  map_add' ω ω' := by
    funext x
    apply AlternatingMap.ext; intro v
    have hv : v = ![] := by funext i; exact i.elim0
    subst hv
    show ((ω + ω') (φ x)) ![]
        = AlternatingMap.constOfIsEmpty ℝ E (Fin 0) ((ω (φ x)) ![]) ![]
        + AlternatingMap.constOfIsEmpty ℝ E (Fin 0) ((ω' (φ x)) ![]) ![]
    rw [show (ω + ω') (φ x) = ω (φ x) + ω' (φ x) from rfl,
        AlternatingMap.add_apply]
    simp [AlternatingMap.constOfIsEmpty]
  map_smul' c ω := by
    funext x
    apply AlternatingMap.ext; intro v
    have hv : v = ![] := by funext i; exact i.elim0
    subst hv
    show ((c • ω) (φ x)) ![]
        = c • AlternatingMap.constOfIsEmpty ℝ E (Fin 0) ((ω (φ x)) ![]) ![]
    rw [show (c • ω) (φ x) = c • ω (φ x) from rfl,
        AlternatingMap.smul_apply]
    simp [AlternatingMap.constOfIsEmpty]

/-- Pullback of a 0-form, composed with the `Ω⁰ ≃ (· → ℝ)`
identification, is just precomposition. -/
@[simp] lemma zeroFormEquiv_pullbackZero
    (φ : E → F) (ω : BundledForm F 0) :
    zeroFormEquiv E (pullbackZero E F φ ω) = (zeroFormEquiv F ω) ∘ φ := by
  funext x
  simp [pullbackZero, zeroFormEquiv]

/-- **R9.4.3 chart-local for 0-forms (functoriality).**  Pullbacks
compose contravariantly: `(ψ ∘ φ)^* = φ^* ∘ ψ^*`. -/
theorem pullbackZero_comp
    {G : Type u} [NormedAddCommGroup G] [NormedSpace ℝ G]
    (φ : E → F) (ψ : F → G) (ω : BundledForm G 0) :
    pullbackZero E G (ψ ∘ φ) ω
      = pullbackZero E F φ (pullbackZero F G ψ ω) := by
  funext x
  apply AlternatingMap.ext; intro v
  have hv : v = ![] := by funext i; exact i.elim0
  subst hv
  simp [pullbackZero, zeroFormEquiv]

/-! ### Round 6 — pullback commutes with `d` for 0-forms (chain rule) -/

/-- **R9.4.2 chart-local for 0-forms.**  For a smooth map `φ : E → F`
and a `C¹` 0-form `ω` on `F`, the exterior derivative of the pullback
equals the pullback of the exterior derivative, evaluated on tangent
vectors via `dφ`:
  `d(φ^* ω) x [v] = dω (φ x) [dφ x v]`.
This is exactly the chain rule, lifted into the alternating-form
formalism. -/
theorem exteriorDerivativeZero_pullbackZero
    (φ : E → F) (ω : BundledForm F 0) (x : E) (v : E)
    (hφ : DifferentiableAt ℝ φ x)
    (hω : DifferentiableAt ℝ (zeroFormEquiv F ω) (φ x)) :
    exteriorDerivativeZero E (pullbackZero E F φ ω) x ![v]
      = exteriorDerivativeZero F ω (φ x) ![fderiv ℝ φ x v] := by
  have hcomp :
      zeroFormEquiv E (pullbackZero E F φ ω) = (zeroFormEquiv F ω) ∘ φ :=
    zeroFormEquiv_pullbackZero E F φ ω
  simp only [exteriorDerivativeZero_apply, hcomp,
        fderiv_comp x hω hφ, ContinuousLinearMap.comp_apply,
        Matrix.cons_val_zero]

/-! ### Round 7 — wedge product for 0-forms -/

/-- **R9.3.1 chart-local for 0-forms.**  Wedge of two 0-forms is
pointwise multiplication. -/
noncomputable def wedgeZeroZero (f g : BundledForm E 0) : BundledForm E 0 :=
  fun x => AlternatingMap.constLinearEquivOfIsEmpty
    (R' := ℝ) (M'' := E) (N'' := ℝ) (ι := Fin 0)
    ((zeroFormEquiv E f x) * (zeroFormEquiv E g x))

/-- Pointwise unfolding of the 0-form wedge product. -/
@[simp] lemma zeroFormEquiv_wedgeZeroZero (f g : BundledForm E 0) :
    zeroFormEquiv E (wedgeZeroZero E f g)
      = fun x => zeroFormEquiv E f x * zeroFormEquiv E g x := by
  funext x
  simp [wedgeZeroZero, zeroFormEquiv]

/-- **R9.3.2 chart-local for 0-forms.**  Graded commutativity at
`(p, q) = (0, 0)` is just commutativity of multiplication. -/
theorem wedgeZeroZero_comm (f g : BundledForm E 0) :
    wedgeZeroZero E f g = wedgeZeroZero E g f := by
  apply (zeroFormEquiv E).injective
  rw [zeroFormEquiv_wedgeZeroZero, zeroFormEquiv_wedgeZeroZero]
  funext x
  exact mul_comm _ _

/-- **R9.3.3 chart-local for 0-forms (Leibniz, special case).**
For two `C¹` 0-forms `f` and `g`, the exterior derivative satisfies
the Leibniz product rule:
  `d(f ∧ g) = (df) ∧ g + f ∧ (dg)`,
which on tangent vectors `v` reads
  `D(fg) x v = (Df x v) g(x) + f(x) (Dg x v)`. -/
theorem exteriorDerivativeZero_wedgeZeroZero
    (f g : BundledForm E 0) (x : E) (v : Fin 1 → E)
    (hf : DifferentiableAt ℝ (zeroFormEquiv E f) x)
    (hg : DifferentiableAt ℝ (zeroFormEquiv E g) x) :
    exteriorDerivativeZero E (wedgeZeroZero E f g) x v
      = exteriorDerivativeZero E f x v * zeroFormEquiv E g x
      + zeroFormEquiv E f x * exteriorDerivativeZero E g x v := by
  simp only [exteriorDerivativeZero_apply, zeroFormEquiv_wedgeZeroZero]
  rw [show (fun x => zeroFormEquiv E f x * zeroFormEquiv E g x)
        = (zeroFormEquiv E f * zeroFormEquiv E g) from rfl,
      fderiv_mul hf hg]
  simp [smul_eq_mul, add_comm, mul_comm]

/-! ### Round 8 — pullback commutes with wedge (0,0 case) -/

/-- **Naturality of wedge for 0-forms.**  Pullback is a multiplicative
homomorphism on 0-forms: `φ^* (f ∧ g) = (φ^* f) ∧ (φ^* g)`.
This is the multiplicative analogue of `pullbackZero`'s linearity. -/
theorem pullbackZero_wedge
    (φ : E → F) (f g : BundledForm F 0) :
    pullbackZero E F φ (wedgeZeroZero F f g)
      = wedgeZeroZero E (pullbackZero E F φ f) (pullbackZero E F φ g) := by
  apply (zeroFormEquiv E).injective
  simp [zeroFormEquiv_wedgeZeroZero, zeroFormEquiv_pullbackZero,
        Function.comp_def]

/-- **Restating Round 6 with the wedge-aware lemma.**  Equivalent
to `exteriorDerivativeZero_pullbackZero` but written in the symmetric
``apply to a vector'' form that mirrors the chain-level `f^* ∘ d = d ∘ f^*`
identity. -/
theorem pullbackZero_exteriorDerivative_apply
    (φ : E → F) (ω : BundledForm F 0) (x : E) (v : E)
    (hφ : DifferentiableAt ℝ φ x)
    (hω : DifferentiableAt ℝ (zeroFormEquiv F ω) (φ x)) :
    exteriorDerivativeZero E (pullbackZero E F φ ω) x ![v]
      = exteriorDerivativeZero F ω (φ x) ![fderiv ℝ φ x v] :=
  exteriorDerivativeZero_pullbackZero E F φ ω x v hφ hω

end JacobianChallenge.Analysis.BundledForms
