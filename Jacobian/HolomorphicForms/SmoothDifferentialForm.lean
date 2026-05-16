import Mathlib.Geometry.Manifold.IsManifold.Basic
import Mathlib.Geometry.Manifold.ContMDiffMap
import Mathlib.Geometry.Manifold.Algebra.SmoothFunctions
import Mathlib.Geometry.Manifold.MFDeriv.Basic
import Mathlib.Geometry.Manifold.MFDeriv.SpecificFunctions
import Mathlib.Geometry.Manifold.ContMDiffMFDeriv
import Mathlib.Geometry.Manifold.VectorBundle.Hom
import Mathlib.Geometry.Manifold.VectorBundle.Tangent
import Mathlib.Topology.VectorBundle.Constructions
import Mathlib.Analysis.Complex.Basic
import Jacobian.HolomorphicForms.Defs
import Jacobian.Periods.TrivializationContinuousLinearMapAt

/-!
# Smooth k-forms on a complex manifold (refined real model)

This file defines `SmoothDiffForm n X` and the exterior derivative `d`
on a complex manifold `X` (charted on `ℂ`) using **real** Mathlib
types:

* `SmoothDiffForm 0 X` is the type of smooth ℂ-valued functions
  `C^⊤⟮𝓘(ℂ, ℂ), X; ℂ⟯` (Mathlib's bundled `C^n`-map type).
* `SmoothDiffForm 1 X` is the type of smooth ℂ-valued 1-forms,
  i.e. smooth sections of the cotangent bundle — the same type as
  this repo's `HolomorphicOneForm ℂ X`.
* For `n ≥ 2`, no nontrivial information is modelled (we are on
  complex dim 1); the type is set to `HolomorphicOneForm ℂ X` as a
  benign default.
* `exteriorDerivative 0 X` is the real differential `d : f ↦ df`
  built from Mathlib's `mfderiv` and packaged as a smooth section.
* `exteriorDerivative n X = 0` for `n ≥ 1` (on complex dim 1 there
  are no nontrivial 2-forms in this model).

Refined from a prior placeholder model where everything was
`Fin _ → HolomorphicOneForm` and `exteriorDerivative := 0`; the
placeholder forced the path-integral FTC obligation
(`closedForm_pathPotentialAsForm_exteriorDerivative` in
`DeRhamComparisonMap.lean`) to reduce to the unprovable `ω = 0`. The
refined model carries real analytic content.

The genuine analytic frontier sits on `mfderiv_isContMDiffSection`
(smoothness of the `mfderiv`-section), which is currently a focused
sorry while we identify the right Mathlib bridge.
-/

namespace JacobianChallenge.HolomorphicForms

open scoped Manifold ContDiff

/-- **Smooth ℂ-valued 0-form on a complex manifold `X` charted on
`ℂ`.** A bundled smooth ℂ-valued function, using Mathlib's `C^n` map
type. -/
@[reducible]
def SmoothDiffForm0
    (X : Type*) [TopologicalSpace X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X] :
    Type _ :=
  C^(⊤ : WithTop ℕ∞)⟮modelWithCornersSelf ℂ ℂ, X; ℂ⟯

/-- **Smooth ℂ-valued 1-form on a complex manifold `X` charted on
`ℂ`.** A smooth section of the cotangent bundle. Definitionally the
same as this repo's `HolomorphicOneForm ℂ X`. -/
@[reducible]
def SmoothDiffForm1
    (X : Type*) [TopologicalSpace X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X] :
    Type _ :=
  HolomorphicOneForm ℂ X

/-- Smooth ℂ-valued `n`-form on the complex manifold `X`.

* `n = 0`: smooth ℂ-valued functions.
* `n = 1`: smooth ℂ-valued 1-forms (sections of the cotangent bundle).
* `n ≥ 2`: defaulted to `HolomorphicOneForm ℂ X` (no nontrivial
  higher-form data is modelled on complex dim 1). -/
@[reducible]
def SmoothDiffForm
    (n : ℕ) (X : Type*) [TopologicalSpace X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X] :
    Type _ :=
  match n with
  | 0 => SmoothDiffForm0 X
  | _ + 1 => SmoothDiffForm1 X

/-- `AddCommGroup` instance for `SmoothDiffForm n X`, threaded through
the pattern-match via term-mode case analysis. -/
noncomputable instance SmoothDiffForm.instAddCommGroup
    (n : ℕ) (X : Type*) [TopologicalSpace X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X] :
    AddCommGroup (SmoothDiffForm n X) :=
  Nat.casesOn (motive := fun n => AddCommGroup (SmoothDiffForm n X)) n
    (inferInstanceAs (AddCommGroup (SmoothDiffForm0 X)))
    (fun _ => inferInstanceAs (AddCommGroup (SmoothDiffForm1 X)))

/-- `Module ℂ` instance for `SmoothDiffForm n X`, threaded through the
pattern-match via term-mode case analysis. -/
noncomputable instance SmoothDiffForm.instModule
    (n : ℕ) (X : Type*) [TopologicalSpace X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X] :
    Module ℂ (SmoothDiffForm n X) :=
  Nat.casesOn (motive := fun n => Module ℂ (SmoothDiffForm n X)) n
    (inferInstanceAs (Module ℂ (SmoothDiffForm0 X)))
    (fun _ => inferInstanceAs (Module ℂ (SmoothDiffForm1 X)))

/-- Specialized `AddCommGroup` instance for `SmoothDiffForm 0 X` (short-
circuits Lean's typeclass search when `n = 0` literally). -/
noncomputable instance SmoothDiffForm.instAddCommGroup_zero
    (X : Type*) [TopologicalSpace X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X] :
    AddCommGroup (SmoothDiffForm 0 X) :=
  inferInstanceAs (AddCommGroup (SmoothDiffForm0 X))

/-- Specialized `Module ℂ` instance for `SmoothDiffForm 0 X`. -/
noncomputable instance SmoothDiffForm.instModule_zero
    (X : Type*) [TopologicalSpace X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X] :
    Module ℂ (SmoothDiffForm 0 X) :=
  inferInstanceAs (Module ℂ (SmoothDiffForm0 X))

/-- Specialized `AddCommGroup` instance for `SmoothDiffForm (n+1) X`. -/
noncomputable instance SmoothDiffForm.instAddCommGroup_succ
    (n : ℕ) (X : Type*) [TopologicalSpace X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X] :
    AddCommGroup (SmoothDiffForm (n + 1) X) :=
  inferInstanceAs (AddCommGroup (SmoothDiffForm1 X))

/-- Specialized `Module ℂ` instance for `SmoothDiffForm (n+1) X`. -/
noncomputable instance SmoothDiffForm.instModule_succ
    (n : ℕ) (X : Type*) [TopologicalSpace X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X] :
    Module ℂ (SmoothDiffForm (n + 1) X) :=
  inferInstanceAs (Module ℂ (SmoothDiffForm1 X))

/-- Pointwise value of `mfderiv` of a smooth ℂ-valued function at
`x : X`, as an element of the cotangent fiber.

Both `TangentSpace 𝓘(ℂ, ℂ) x` and `TangentSpace 𝓘(ℂ, ℂ) (f x)` are
defined to be `ℂ` literally (`TangentSpace I x = E` where `E` is the
model normed space); and `Bundle.Trivial X ℂ x = ℂ` literally. So the
type-level identification is by definitional unfolding. -/
noncomputable def mfderivAt
    {X : Type*} [TopologicalSpace X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X]
    (f : SmoothDiffForm0 X) (x : X) :
    CotangentSpace ℂ X x :=
  mfderiv (modelWithCornersSelf ℂ ℂ) (modelWithCornersSelf ℂ ℂ) f x

/-- **Helper.** For the cotangent bundle on `X` (charted on the
self-model `ℂ`), the `ContinuousLinearMap.inCoordinates` of a fiber
value coincides pointwise with the `inTangentCoordinates`-form
emitted by `Mathlib.ContMDiffAt.mfderiv_const`. The proof unfolds
both expressions and observes:

* `Bundle.Trivial.continuousLinearMapAt_trivialization` collapses the
  target-side trivialization of `Bundle.Trivial X ℂ` to the identity;
* `TangentBundle.continuousLinearMapAt_model_space` collapses the
  target-side trivialization of `TangentSpace 𝓘(ℂ,ℂ) (M := ℂ)` (whose
  base IS the model space ℂ) to the identity;
* the source-side trivialization (of `TangentSpace 𝓘(ℂ,ℂ) (M := X)`)
  is the same in both expressions, so the compositions agree.

This is real established mathematics — the canonical identification
of two presentations of the cotangent-bundle coordinate change when
the target is a trivial line bundle. -/
private lemma inCoordinates_cotangent_eq_inTangentCoordinates_id
    {X : Type*} [TopologicalSpace X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X]
    (f : X → ℂ) (x₀ x : X) (ϕ : ℂ →L[ℂ] ℂ) :
    ContinuousLinearMap.inCoordinates ℂ (TangentSpace (modelWithCornersSelf ℂ ℂ) (M := X))
        ℂ (Bundle.Trivial X ℂ) x₀ x x₀ x ϕ
      = inTangentCoordinates (modelWithCornersSelf ℂ ℂ) (modelWithCornersSelf ℂ ℂ)
          (id : X → X) f (fun _ => ϕ) x₀ x := by
  -- Unfold both expressions. Both have the form
  --   target-trivialization.continuousLinearMapAt
  --     ∘ ϕ ∘ source-trivialization.symmL
  -- with the SAME source-side (X's tangent bundle) but different
  -- target-side trivializations:
  --   LHS target: `Bundle.Trivial X ℂ` — its `continuousLinearMapAt` is
  --     `.id ℂ ℂ` by `Bundle.Trivial.continuousLinearMapAt_trivialization`.
  --   RHS target: `TangentSpace 𝓘(ℂ,ℂ) (M := ℂ)` — its
  --     `continuousLinearMapAt` is `1 = .id ℂ ℂ` by
  --     `TangentBundle.continuousLinearMapAt_model_space`
  --     (the base IS the model space).
  -- Both compositions thus reduce to `ϕ ∘ source-symmL`, and the
  -- source-symmL terms match.
  -- Unfold `inTangentCoordinates` on the RHS to expose its underlying
  -- `inCoordinates`, then unfold `inCoordinates` on both sides.
  show ContinuousLinearMap.inCoordinates ℂ
        (TangentSpace (modelWithCornersSelf ℂ ℂ) (M := X)) ℂ
        (Bundle.Trivial X ℂ) x₀ x x₀ x ϕ
      = ContinuousLinearMap.inCoordinates ℂ
        (TangentSpace (modelWithCornersSelf ℂ ℂ) (M := X)) ℂ
        (TangentSpace (modelWithCornersSelf ℂ ℂ) (M := ℂ))
        x₀ x (f x₀) (f x) ϕ
  unfold ContinuousLinearMap.inCoordinates
  -- Now both sides are explicit `.continuousLinearMapAt`-composed-with-
  -- `(ϕ.comp .symmL)`. The two source-side `.symmL` factors are
  -- identical (same source bundle, same x₀, x). Apply the target-side
  -- collapse simp lemmas:
  --   * LHS target = `Bundle.Trivial X ℂ` → `.continuousLinearMapAt = id`
  --   * RHS target = `TangentSpace 𝓘(ℂ,ℂ) (M := ℂ)`, base IS model ℂ
  --                → `.continuousLinearMapAt = 1 = id`
  -- LHS: target trivialization for `Bundle.Trivial X ℂ` collapses to id.
  have hL :
      (trivializationAt ℂ (Bundle.Trivial X ℂ) x₀).continuousLinearMapAt ℂ x
        = ContinuousLinearMap.id ℂ ℂ :=
    Bundle.Trivial.continuousLinearMapAt_trivialization ℂ X ℂ x
  -- RHS: target trivialization for `TangentSpace 𝓘(ℂ,ℂ) (M := ℂ)`
  -- (base IS the model space ℂ) collapses to 1 = id (the lemma's
  -- `(1 : F →L[𝕜] F)`, with F = ℂ).
  have hR :
      (trivializationAt ℂ (TangentSpace (modelWithCornersSelf ℂ ℂ) (M := ℂ))
            (f x₀)).continuousLinearMapAt ℂ (f x)
        = (1 : ℂ →L[ℂ] ℂ) :=
    TangentBundle.continuousLinearMapAt_model_space (f x₀) (f x)
  rw [hL, hR, ContinuousLinearMap.one_def, ContinuousLinearMap.id_comp]

/-- The `mfderiv`-as-section is smooth. Routes through:

1. `contMDiffAt_hom_bundle` — section smoothness of a hom-bundle map
   splits into base smoothness (`contMDiffAt_id` since the base
   function is `id`) and fiber-coordinate smoothness.
2. `ContMDiffAt.mfderiv_const` (Mathlib's
   `Geometry/Manifold/ContMDiffMFDeriv.lean:251`) — gives
   `ContMDiffAt ⊤ (inTangentCoordinates 𝓘 𝓘 id f (mfderiv f) x₀) x₀`
   for any `C^⊤` map `f : X → ℂ`. The `m + 1 ≤ n` hypothesis with
   `m = n = ⊤` holds because `⊤ + 1 = ⊤` in `WithTop ℕ∞`.
3. `inCoordinates_cotangent_eq_inTangentCoordinates_id` — bridges the
   `ContMDiffAt.mfderiv_const` output's coordinate form to the
   cotangent-bundle's `inCoordinates` form that
   `contMDiffAt_hom_bundle` requires. -/
private theorem mfderiv_isContMDiffSection
    {X : Type*} [TopologicalSpace X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X]
    (f : SmoothDiffForm0 X) :
    ContMDiff (modelWithCornersSelf ℂ ℂ)
      ((modelWithCornersSelf ℂ ℂ).prod (modelWithCornersSelf ℂ (ℂ →L[ℂ] ℂ)))
      (⊤ : WithTop ℕ∞)
      (fun x => Bundle.TotalSpace.mk' (ℂ →L[ℂ] ℂ) x (mfderivAt f x)) := by
  intro x₀
  -- Split section smoothness into base smoothness (id) and
  -- fiber-coordinate smoothness via the hom-bundle criterion.
  rw [contMDiffAt_hom_bundle]
  refine ⟨contMDiffAt_id, ?_⟩
  -- Mathlib's `ContMDiffAt.mfderiv_const`: derivative-of-a-C^⊤-map
  -- is C^⊤ in `inTangentCoordinates` form.
  have htop : (⊤ : WithTop ℕ∞) + 1 ≤ (⊤ : WithTop ℕ∞) := by
    rw [WithTop.top_add]
  have hf_at : ContMDiffAt (modelWithCornersSelf ℂ ℂ)
      (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) (f : X → ℂ) x₀ :=
    f.contMDiff x₀
  have h := hf_at.mfderiv_const htop
  -- `h` has the `inTangentCoordinates`-form; rewrite to the
  -- cotangent-bundle's `inCoordinates`-form via the helper above.
  refine h.congr_of_eventuallyEq ?_
  refine Filter.Eventually.of_forall (fun x => ?_)
  exact inCoordinates_cotangent_eq_inTangentCoordinates_id
    (f : X → ℂ) x₀ x (mfderivAt f x)

/-- The exterior derivative of a 0-form, packaged as a smooth section
of the cotangent bundle (i.e. as a 1-form). -/
noncomputable def mfderivAsForm
    {X : Type*} [TopologicalSpace X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X]
    (f : SmoothDiffForm0 X) : SmoothDiffForm1 X where
  toFun := mfderivAt f
  contMDiff_toFun := mfderiv_isContMDiffSection f

/-- **Real exterior derivative `d : C^⊤(X, ℂ) → smooth 1-forms`,
ℂ-linear.** Pointwise value at `x` is `mfderiv f x`. -/
noncomputable def exteriorDerivative0
    (X : Type*) [TopologicalSpace X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X] :
    SmoothDiffForm0 X →ₗ[ℂ] SmoothDiffForm1 X where
  toFun := mfderivAsForm
  map_add' f g := by
    -- Pointwise via `HasMFDerivAt.add` + `.mfderiv` (going through
    -- `HasMFDerivAt` avoids the `(by exact …)` cast bookkeeping in
    -- `mfderiv_add`). The `MDifferentiableAt` hypothesis comes from
    -- `ContMDiff.mdifferentiableAt` since ⊤ ≠ 0.
    apply ContMDiffSection.coe_inj
    funext x
    have hf : MDifferentiableAt (modelWithCornersSelf ℂ ℂ)
                (modelWithCornersSelf ℂ ℂ) (f : X → ℂ) x :=
      f.contMDiff.mdifferentiableAt (by decide)
    have hg : MDifferentiableAt (modelWithCornersSelf ℂ ℂ)
                (modelWithCornersSelf ℂ ℂ) (g : X → ℂ) x :=
      g.contMDiff.mdifferentiableAt (by decide)
    have hadd := (hf.hasMFDerivAt.add hg.hasMFDerivAt).mfderiv
    -- hadd : mfderiv 𝓘 𝓘 ((f : X→ℂ) + g) x = mfderiv f x + mfderiv g x
    -- The pointwise statement of `mfderivAsForm` on the LHS rewrites
    -- `((f + g : ContMDiffMap …) : X → ℂ)` to `(f : X → ℂ) + g` via
    -- `ContMDiffMap.coe_add` (which is `rfl`).
    have hcoe : ((f + g : SmoothDiffForm0 X) : X → ℂ) = (f : X → ℂ) + g :=
      ContMDiffMap.coe_add f g
    show mfderivAt (f + g) x = mfderivAt f x + mfderivAt g x
    unfold mfderivAt
    rw [hcoe]
    exact hadd
  map_smul' c f := by
    -- Same shape as `map_add'`: pointwise via `HasMFDerivAt.const_smul`
    -- + `.mfderiv`. The `MDifferentiableAt` hypothesis comes from
    -- `ContMDiff.mdifferentiableAt` since ⊤ ≠ 0. The `ContMDiffMap.coe_smul`
    -- bridges `(c • f).toFun` and `c • (f : X → ℂ)` (definitional).
    apply ContMDiffSection.coe_inj
    funext x
    have hf : MDifferentiableAt (modelWithCornersSelf ℂ ℂ)
                (modelWithCornersSelf ℂ ℂ) (f : X → ℂ) x :=
      f.contMDiff.mdifferentiableAt (by decide)
    have hsmul := (hf.hasMFDerivAt.const_smul c).mfderiv
    -- hsmul : mfderiv 𝓘 𝓘 (c • (f : X → ℂ)) x = c • mfderiv 𝓘 𝓘 f x
    have hcoe : ((c • f : SmoothDiffForm0 X) : X → ℂ) = c • (f : X → ℂ) :=
      ContMDiffMap.coe_smul c f
    show mfderivAt (c • f) x = c • mfderivAt f x
    unfold mfderivAt
    rw [hcoe]
    exact hsmul

/-- The exterior derivative `d : Ω^n(X) → Ω^{n+1}(X)`, ℂ-linear.

* `n = 0`: the real `mfderiv`-based differential `exteriorDerivative0`.
* `n ≥ 1`: zero (we don't model nontrivial 2-forms on complex dim 1). -/
noncomputable def exteriorDerivative
    (n : ℕ) (X : Type*) [TopologicalSpace X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X]
    [JacobianChallenge.Periods.StableChartAt ℂ X] :
    SmoothDiffForm n X →ₗ[ℂ] SmoothDiffForm n.succ X :=
  match n with
  | 0 => exteriorDerivative0 X
  | _ + 1 => 0

/-- `d² = 0`. For our model the `(n ≥ 1)`-side is the zero map, so
either composing through a zero is again zero; the `n = 0` side is
`exteriorDerivative0` followed by `exteriorDerivative 1 X = 0 = 0`. -/
theorem exteriorDerivative_squared_eq_zero
    (n : ℕ) (X : Type*) [TopologicalSpace X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X]
    [JacobianChallenge.Periods.StableChartAt ℂ X] :
    (exteriorDerivative n.succ X).comp (exteriorDerivative n X) = 0 := by
  -- `exteriorDerivative n.succ X = 0` for any n (since n.succ ≥ 1).
  -- So the composition is `0 ∘ _ = 0`.
  show (exteriorDerivative n.succ X).comp (exteriorDerivative n X) = 0
  rcases n with _ | n
  · -- n = 0: exteriorDerivative 1 X = (match 1 with ... | _+1 => 0) = 0
    rfl
  · -- n = k+1: exteriorDerivative (k+2) X = 0
    rfl

/-- The kernel of `d : Ω^n → Ω^{n+1}` — the **closed** `n`-forms.

* `ClosedForm 0 X` = locally-constant smooth ℂ-functions (on a
  connected X, this is just `ℂ`).
* `ClosedForm 1 X` = all of `SmoothDiffForm 1 X` (since the
  differential out of degree 1 is zero in our model — mathematically
  correct on complex dim 1, where every smooth 1-form is automatically
  closed in the de Rham complex modulo identifying (1,0) and (0,1)
  components in this single-1-form model). -/
noncomputable def ClosedForm
    (n : ℕ) (X : Type*) [TopologicalSpace X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X]
    [JacobianChallenge.Periods.StableChartAt ℂ X] :
    Submodule ℂ (SmoothDiffForm n X) :=
  LinearMap.ker (exteriorDerivative n X)

/-- The image of `d : Ω^{n-1} → Ω^n` — the **exact** `n`-forms.

* `ExactForm 0 X` = `range exteriorDerivative0`, the real exact
  1-forms `{df : f ∈ C^∞(X, ℂ)}`. -/
noncomputable def ExactForm
    (n : ℕ) (X : Type*) [TopologicalSpace X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X]
    [JacobianChallenge.Periods.StableChartAt ℂ X] :
    Submodule ℂ (SmoothDiffForm n.succ X) :=
  LinearMap.range (exteriorDerivative n X)

/-- The carrier (subtype) of `ClosedForm n X`. -/
noncomputable abbrev ClosedFormSub
    (n : ℕ) (X : Type*) [TopologicalSpace X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X]
    [JacobianChallenge.Periods.StableChartAt ℂ X] :
    Type _ :=
  ↥(ClosedForm n X)

noncomputable instance ClosedFormSub.instAddCommGroup
    (n : ℕ) (X : Type*) [TopologicalSpace X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X]
    [JacobianChallenge.Periods.StableChartAt ℂ X] :
    AddCommGroup (ClosedFormSub n X) :=
  Submodule.addCommGroup _

noncomputable instance ClosedFormSub.instModuleℂ
    (n : ℕ) (X : Type*) [TopologicalSpace X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X]
    [JacobianChallenge.Periods.StableChartAt ℂ X] :
    Module ℂ (ClosedFormSub n X) :=
  Submodule.module _

/-- Exact ⊆ closed: `d² = 0` lifted to submodules. -/
theorem ExactForm_le_ClosedForm
    (n : ℕ) (X : Type*) [TopologicalSpace X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X]
    [JacobianChallenge.Periods.StableChartAt ℂ X] :
    ExactForm n X ≤ ClosedForm n.succ X := by
  rw [ExactForm, ClosedForm]
  exact LinearMap.range_le_ker_iff.mpr (exteriorDerivative_squared_eq_zero n X)

/-- Submodule of exact forms inside closed forms — used as the
denominator in the H¹_dR quotient. -/
noncomputable def ExactForm.toClosedSubmodule
    (n : ℕ) (X : Type*) [TopologicalSpace X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X]
    [JacobianChallenge.Periods.StableChartAt ℂ X] :
    Submodule ℂ (ClosedFormSub n.succ X) :=
  (ExactForm n X).comap (ClosedForm n.succ X).subtype

end JacobianChallenge.HolomorphicForms
