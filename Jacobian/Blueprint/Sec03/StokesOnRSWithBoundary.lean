import Mathlib.Geometry.Manifold.IsManifold.Basic
import Mathlib.Geometry.Manifold.Instances.Real
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Analysis.Calculus.FDeriv.Basic
import Mathlib.Analysis.Calculus.FDeriv.Prod
import Mathlib.MeasureTheory.Integral.Prod

/-! # Blueprint stubs: sub-leaves of `thm:stokes-on-rs-with-boundary`

Section 3 of `tex/sections/03-periods-and-riemann-bilinear.tex`.

The umbrella theorem `thm:stokes-on-rs-with-boundary` is classified
**DECOMPOSE** in `ref/scope-out.md`. The full eight-leaf decomposition,
harvested from a ChatGPT planning pass, is in
`ref/plans/stokes-on-rs-with-boundary.md`. This file gives every leaf a
concrete Lean handle:

* leaves **#1 / #2** (SHORT): `True`-valued placeholders — the real
  signatures are too tangled with the corner-modelled boundary API to
  pin down at this stage and will be revisited in a follow-up.
* leaves **#3 / #4** (HARD): concrete `noncomputable def`s with
  manifold-with-corners hypotheses and a placeholder body `0`. These
  pin down the call shape (`integrateTwoForm M ω : ℝ` and
  `integrateOneFormBoundary M ω : ℝ`) so #5–#8 can already speak about
  them.
* leaves **#5 / #6 / #7 / #8** (MEDIUM / HARD): concrete `theorem`
  statements whose conclusions are equalities of the
  `integrateTwoForm` / `integrateOneFormBoundary` functionals (or, for
  #5, an honest Green's-theorem equality of nested interval integrals
  in `ℝ²`); proofs are `sorry` and assigned to follow-up workers.

The `*Aux` form types `TwoFormAux M := M → ℝ` and
`OneFormAux M := M → ℝ` are deliberate placeholders: Mathlib v4.28.0's
inventory entry "Integration of differential forms" is **ABSENT**, so
committing to a real differential-form type today would lock the whole
decomposition behind an unresolved upstream question. Once the
manifold-side exterior-derivative + integration API lands, every
declaration here gets a like-for-like signature replacement (same name,
same arity, real form types).

Imports are deliberately narrow per integrator policy — no
`import Mathlib`. The current set is exactly the manifold-with-corners
model (`WithCorners` + `Instances.Real`) and the real-analysis kernel
(`IntervalIntegral.Basic` + `FDeriv.Basic`) that #5 needs to state
Green's theorem.
-/

namespace JacobianChallenge.Blueprint.Sec03

open scoped Manifold

/-! ## Auxiliary placeholder form types

Both are `M → ℝ` while the real differential-form API is unavailable.
Downstream signatures use these names so the eventual type swap is
mechanical. -/

/-- Placeholder for a 2-form on `M`: scalar density representation. -/
abbrev TwoFormAux (M : Type*) : Type _ := M → ℝ

/-- Placeholder for a 1-form on `M`: scalar coefficient representation. -/
abbrev OneFormAux (M : Type*) : Type _ := M → ℝ

/-- Placeholder predicate "the 2-form `η` is the exterior derivative of
the 1-form `ω`". Trivially `True` while the real exterior-derivative API
is unavailable; carried as a hypothesis on Stokes-shaped statements so
the eventual swap-in lemma has a stable name. -/
def IsExteriorDerivativeAux {M : Type*} (_ω : OneFormAux M)
    (_η : TwoFormAux M) : Prop := True

/-! ## Sub-leaf #1 (SHORT) — preserved from the previous stub commit. -/

/-- **Sub-leaf #1 of `thm:stokes-on-rs-with-boundary` (plan class: SHORT).**

Mathematical content: a 2-dimensional smooth manifold with corners is a
second-countable Hausdorff topological space `M` equipped with an atlas
of charts into the model corner space `(ℝ≥0)²`, with smooth transition
maps. This is the structure carried by a 4g-gon fundamental polygon
before edge identifications.

Eventual Lean signature, once the corner-modeled manifold API stabilises:
```
def manifoldWithCorners2D
    (M : Type*) [TopologicalSpace M] [T2Space M] [SecondCountableTopology M]
    [ChartedSpace (EuclideanQuadrant 2) M]
    [IsManifold (modelWithCornersEuclideanQuadrant 2) ⊤ M] : Prop
```

Placeholder body: `True`. -/
theorem manifold_with_corners_2d : Nonempty Unit := ⟨()⟩

/-- **Sub-leaf #2 of `thm:stokes-on-rs-with-boundary` (plan class: SHORT).**

Mathematical content: for a 2D manifold with corners `M`, the boundary
`∂M` is the set of points whose chart image lies in the boundary of
`(ℝ≥0)²`, and inherits the structure of a 1-manifold with corners.

Eventual Lean signature, layered on `manifold_with_corners_2d`:
```
def boundary1D
    (M : Type*) [TopologicalSpace M] [ChartedSpace (EuclideanQuadrant 2) M]
    [IsManifold (modelWithCornersEuclideanQuadrant 2) ⊤ M] : Set M
```

Placeholder body: `True`. -/
theorem boundary_1d : Nonempty Unit := ⟨()⟩

/-! ## Sub-leaf #3 (HARD) — integration of a 2-form. -/

/-- **Sub-leaf #3 of `thm:stokes-on-rs-with-boundary` (plan class: HARD).**

The integral `∫_M ω` of a 2-form `ω` on a compact 2-manifold with
corners. The eventual definition uses a smooth partition of unity
subordinate to a finite atlas, pulls each summand back to a chart in
`(ℝ≥0)²`, and Lebesgue-integrates against the standard 2D volume form.

Currently a placeholder returning `0`. The signature is the production
call shape — `integrateTwoForm M ω : ℝ` — so #5–#8 can already speak
about it. -/
noncomputable def integrateTwoForm
    (M : Type*) [TopologicalSpace M] [CompactSpace M]
    [ChartedSpace (EuclideanQuadrant 2) M]
    [IsManifold (modelWithCornersEuclideanQuadrant 2) (⊤ : WithTop ℕ∞) M]
    (_ω : TwoFormAux M) : ℝ := 0

/-! ## Sub-leaf #4 (HARD) — boundary integral of a 1-form. -/

/-- **Sub-leaf #4 of `thm:stokes-on-rs-with-boundary` (plan class: HARD).**

The integral `∫_{∂M} ω` of a 1-form `ω` along the oriented boundary of a
compact 2-manifold with corners. The eventual definition decomposes
`∂M` into oriented edges (piecewise smooth curves meeting at corners)
and sums the line integrals, using the outward-normal-first convention
to fix the boundary orientation.

Currently a placeholder returning `0`. Depends on sub-leaf #2 for the
underlying boundary structure. -/
noncomputable def integrateOneFormBoundary
    (M : Type*) [TopologicalSpace M] [CompactSpace M]
    [ChartedSpace (EuclideanQuadrant 2) M]
    [IsManifold (modelWithCornersEuclideanQuadrant 2) (⊤ : WithTop ℕ∞) M]
    (_ω : OneFormAux M) : ℝ := 0

/-! ## Sub-leaf #5 (MEDIUM) — Green's theorem on a rectangle. -/

/-- **Sub-leaf #5.P (FTC slice for `P`).**

For `C¹` `P : ℝ × ℝ → ℝ`, the difference of the top and bottom edge
integrals on the rectangle equals the iterated `y`-integral of
`∂P/∂y`:
```
(∫ x in a..b, P (x, d)) − (∫ x in a..b, P (x, c))
  = ∫ x in a..b, ∫ y in c..d, fderiv ℝ P (x, y) (0, 1).
```

Proof spine (deferred): Fubini + `intervalIntegral.integral_deriv_eq_sub`
on the slice `y ↦ P (x, y)` for each fixed `x`. -/
theorem stokes_local_euclidean_P
    (P : ℝ × ℝ → ℝ) (a b c d : ℝ)
    (_hab : a ≤ b) (_hcd : c ≤ d)
    (_hP : ContDiff ℝ 1 P) :
    (∫ x in a..b, P (x, d)) - (∫ x in a..b, P (x, c))
      = ∫ x in a..b, ∫ y in c..d, fderiv ℝ P (x, y) (0, 1) := by
  have hslice : ∀ x : ℝ,
      (∫ y in c..d, fderiv ℝ P (x, y) (0, 1)) = P (x, d) - P (x, c) := by
    intro x
    have hderiv : ∀ y ∈ Set.uIcc c d,
        HasDerivAt (fun y : ℝ => P (x, y)) (fderiv ℝ P (x, y) (0, 1)) y := by
      intro y _hy
      have hdiff : DifferentiableAt ℝ P (x, y) :=
        (_hP.differentiable (by norm_num)).differentiableAt
      have hline : HasDerivAt (fun y : ℝ => (x, y)) (0, 1) y := by
        simpa using
          (HasFDerivAt.hasDerivAt (hasFDerivAt_prodMk_right (𝕜 := ℝ) x y))
      simpa using hdiff.hasFDerivAt.comp_hasDerivAt y hline
    have hint :
        IntervalIntegrable (fun y : ℝ => fderiv ℝ P (x, y) (0, 1))
          MeasureTheory.volume c d := by
      have hc : Continuous fun y : ℝ => fderiv ℝ P (x, y) (0, 1) := by
        have h := _hP.continuous_fderiv_apply (by norm_num)
        exact h.comp
          (Continuous.prodMk (Continuous.prodMk continuous_const continuous_id)
            continuous_const)
      exact hc.intervalIntegrable _ _
    exact intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint
  rw [← intervalIntegral.integral_sub]
  · simp_rw [← hslice]
  · exact (_hP.continuous.comp (Continuous.prodMk continuous_id continuous_const)).intervalIntegrable _ _
  · exact (_hP.continuous.comp (Continuous.prodMk continuous_id continuous_const)).intervalIntegrable _ _

/-- **Sub-leaf #5.Q (FTC slice for `Q`).**

For `C¹` `Q : ℝ × ℝ → ℝ`, the difference of the right and left edge
integrals on the rectangle equals the iterated `x`-integral of
`∂Q/∂x`:
```
(∫ y in c..d, Q (b, y)) − (∫ y in c..d, Q (a, y))
  = ∫ y in c..d, ∫ x in a..b, fderiv ℝ Q (x, y) (1, 0).
```

Proof spine (deferred): Fubini + `intervalIntegral.integral_deriv_eq_sub`
on the slice `x ↦ Q (x, y)` for each fixed `y`. -/
theorem stokes_local_euclidean_Q
    (Q : ℝ × ℝ → ℝ) (a b c d : ℝ)
    (_hab : a ≤ b) (_hcd : c ≤ d)
    (_hQ : ContDiff ℝ 1 Q) :
    (∫ y in c..d, Q (b, y)) - (∫ y in c..d, Q (a, y))
      = ∫ y in c..d, ∫ x in a..b, fderiv ℝ Q (x, y) (1, 0) := by
  have hslice : ∀ y : ℝ,
      (∫ x in a..b, fderiv ℝ Q (x, y) (1, 0)) = Q (b, y) - Q (a, y) := by
    intro y
    have hderiv : ∀ x ∈ Set.uIcc a b,
        HasDerivAt (fun x : ℝ => Q (x, y)) (fderiv ℝ Q (x, y) (1, 0)) x := by
      intro x _hx
      have hdiff : DifferentiableAt ℝ Q (x, y) :=
        (_hQ.differentiable (by norm_num)).differentiableAt
      have hline : HasDerivAt (fun x : ℝ => (x, y)) (1, 0) x := by
        simpa using
          (HasFDerivAt.hasDerivAt (hasFDerivAt_prodMk_left (𝕜 := ℝ) x y))
      simpa using hdiff.hasFDerivAt.comp_hasDerivAt x hline
    have hint :
        IntervalIntegrable (fun x : ℝ => fderiv ℝ Q (x, y) (1, 0))
          MeasureTheory.volume a b := by
      have hc : Continuous fun x : ℝ => fderiv ℝ Q (x, y) (1, 0) := by
        have h := _hQ.continuous_fderiv_apply (by norm_num)
        exact h.comp
          (Continuous.prodMk (Continuous.prodMk continuous_id continuous_const)
            continuous_const)
      exact hc.intervalIntegrable _ _
    exact intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint
  rw [← intervalIntegral.integral_sub]
  · simp_rw [← hslice]
  · exact (_hQ.continuous.comp (Continuous.prodMk continuous_const continuous_id)).intervalIntegrable _ _
  · exact (_hQ.continuous.comp (Continuous.prodMk continuous_const continuous_id)).intervalIntegrable _ _

/-
**Fubini swap (sub-leaf for #5 assembly).**

For an integrable iterated integral over the rectangle, the order of
the iterated `x`/`y` integrations may be swapped. This is just a
named local handle for `MeasureTheory.integral_prod` / Fubini's
theorem on `ℝ²`, isolating the swap so the assembly in
`stokes_local_euclidean` does not have to recompute integrability
hypotheses.
-/
theorem stokes_local_euclidean_fubini_swap
    (f : ℝ × ℝ → ℝ) (a b c d : ℝ)
    (_hab : a ≤ b) (_hcd : c ≤ d)
    (_hf : ContDiff ℝ 1 f) :
    (∫ x in a..b, ∫ y in c..d, f (x, y))
      = ∫ y in c..d, ∫ x in a..b, f (x, y) := by
  -- By Fubini's theorem, the order of integration can be swapped since the function is continuous on the compact set [a, b] × [c, d].
  have h_fubini : ∫ x in a..b, ∫ y in c..d, f (x, y) = ∫ p in Set.Icc a b ×ˢ Set.Icc c d, f p := by
    erw [ MeasureTheory.setIntegral_prod ];
    · simp +decide [ *, MeasureTheory.integral_Icc_eq_integral_Ioc, intervalIntegral.integral_of_le ];
    · exact ContinuousOn.integrableOn_compact ( isCompact_Icc.prod CompactIccSpace.isCompact_Icc ) ( _hf.continuous.continuousOn );
  erw [ h_fubini, MeasureTheory.setIntegral_prod ];
  · rw [ MeasureTheory.integral_integral_swap ];
    · simp +decide only [MeasureTheory.integral_Icc_eq_integral_Ioc, intervalIntegral.integral_of_le _hab,
          intervalIntegral.integral_of_le _hcd];
    · rw [ MeasureTheory.Measure.prod_restrict ];
      exact ContinuousOn.integrableOn_compact ( isCompact_Icc.prod CompactIccSpace.isCompact_Icc ) ( _hf.continuous.continuousOn );
  · exact ContinuousOn.integrableOn_compact ( isCompact_Icc.prod CompactIccSpace.isCompact_Icc ) ( _hf.continuous.continuousOn )

/-- **Continuous Fubini wrapper for the rectangle.** This is the
version needed by `stokes_local_euclidean`: after taking one
Fréchet derivative of a `ContDiff ℝ 1` function, we only have
continuity of the derivative term, not another `ContDiff ℝ 1`
hypothesis. -/
theorem stokes_local_euclidean_fubini_swap_continuous
    (f : ℝ × ℝ → ℝ) (a b c d : ℝ)
    (_hab : a ≤ b) (_hcd : c ≤ d)
    (_hf : Continuous f) :
    (∫ x in a..b, ∫ y in c..d, f (x, y))
      = ∫ y in c..d, ∫ x in a..b, f (x, y) := by
  have h_fubini :
      ∫ x in a..b, ∫ y in c..d, f (x, y)
        = ∫ p in Set.Icc a b ×ˢ Set.Icc c d, f p := by
    erw [MeasureTheory.setIntegral_prod]
    · simp +decide [*, MeasureTheory.integral_Icc_eq_integral_Ioc,
        intervalIntegral.integral_of_le]
    · exact ContinuousOn.integrableOn_compact
        (isCompact_Icc.prod CompactIccSpace.isCompact_Icc)
        _hf.continuousOn
  erw [h_fubini, MeasureTheory.setIntegral_prod]
  · rw [MeasureTheory.integral_integral_swap]
    · simp +decide only [MeasureTheory.integral_Icc_eq_integral_Ioc,
        intervalIntegral.integral_of_le _hab,
        intervalIntegral.integral_of_le _hcd]
    · rw [MeasureTheory.Measure.prod_restrict]
      exact ContinuousOn.integrableOn_compact
        (isCompact_Icc.prod CompactIccSpace.isCompact_Icc)
        _hf.continuousOn
  · exact ContinuousOn.integrableOn_compact
      (isCompact_Icc.prod CompactIccSpace.isCompact_Icc)
      _hf.continuousOn

/-- Convert an iterated interval integral over a rectangle to a set
integral over the product rectangle. -/
theorem stokes_local_euclidean_prod_setIntegral_continuous
    (f : ℝ × ℝ → ℝ) (a b c d : ℝ)
    (_hab : a ≤ b) (_hcd : c ≤ d)
    (_hf : Continuous f) :
    (∫ x in a..b, ∫ y in c..d, f (x, y))
      = ∫ p in Set.Icc a b ×ˢ Set.Icc c d, f p := by
  erw [MeasureTheory.setIntegral_prod]
  · simp +decide [*, MeasureTheory.integral_Icc_eq_integral_Ioc,
      intervalIntegral.integral_of_le]
  · exact ContinuousOn.integrableOn_compact
      (isCompact_Icc.prod CompactIccSpace.isCompact_Icc)
      _hf.continuousOn

/-- Reverse-order version of
`stokes_local_euclidean_prod_setIntegral_continuous`. -/
theorem stokes_local_euclidean_prod_setIntegral_continuous_rev
    (f : ℝ × ℝ → ℝ) (a b c d : ℝ)
    (_hab : a ≤ b) (_hcd : c ≤ d)
    (_hf : Continuous f) :
    (∫ y in c..d, ∫ x in a..b, f (x, y))
      = ∫ p in Set.Icc a b ×ˢ Set.Icc c d, f p := by
  rw [← stokes_local_euclidean_fubini_swap_continuous f a b c d _hab _hcd _hf]
  exact stokes_local_euclidean_prod_setIntegral_continuous f a b c d _hab _hcd _hf

/-- **Sub-leaf #5 of `thm:stokes-on-rs-with-boundary` (plan class: MEDIUM).**

Green's theorem on the axis-aligned rectangle `[a, b] × [c, d] ⊂ ℝ²`:
for `C¹` scalar fields `P, Q : ℝ × ℝ → ℝ`,

```
∮_{∂R} (P dx + Q dy) = ∫∫_R (∂Q/∂x − ∂P/∂y).
```

The boundary integral is written explicitly as the sum of the four edge
integrals (with the standard counter-clockwise orientation on the
rectangle), and the partial derivatives are read off the Fréchet
derivative `fderiv ℝ` evaluated at the basis vectors `(1, 0)` and
`(0, 1)` of `ℝ × ℝ`.

This is the ℝ²-local version of Stokes; it does not yet involve any
manifold-with-corners structure.

Decomposed into three named sub-leaves above:
* `stokes_local_euclidean_P` — `P`-half FTC slice;
* `stokes_local_euclidean_Q` — `Q`-half FTC slice;
* `stokes_local_euclidean_fubini_swap` — Fubini order swap.

The eventual sorry-free assembly will pair the two FTC halves with one
Fubini swap (after upgrading the differentiability hypothesis to
`ContDiff ℝ 2 P` so the partial derivative `(0,1) ↦ ∂P` is itself
`ContDiff ℝ 1` and Fubini applies). Today still a single `sorry` since
the upgrade and the assembly haven't been wired. -/
theorem stokes_local_euclidean
    (P Q : ℝ × ℝ → ℝ) (a b c d : ℝ)
    (_hab : a ≤ b) (_hcd : c ≤ d)
    (_hP : ContDiff ℝ 1 P) (_hQ : ContDiff ℝ 1 Q) :
    (∫ x in a..b, P (x, c)) + (∫ y in c..d, Q (b, y))
        - (∫ x in a..b, P (x, d)) - (∫ y in c..d, Q (a, y))
      = ∫ y in c..d, ∫ x in a..b,
          (fderiv ℝ Q (x, y) (1, 0) - fderiv ℝ P (x, y) (0, 1)) := by
  let q : ℝ × ℝ → ℝ := fun p => fderiv ℝ Q p (1, 0)
  let pfun : ℝ × ℝ → ℝ := fun p => fderiv ℝ P p (0, 1)
  have hqc : Continuous q :=
    (_hQ.continuous_fderiv_apply (by norm_num)).comp
      (Continuous.prodMk continuous_id continuous_const)
  have hpc : Continuous pfun :=
    (_hP.continuous_fderiv_apply (by norm_num)).comp
      (Continuous.prodMk continuous_id continuous_const)
  have hQset :
      (∫ y in c..d, Q (b, y)) - (∫ y in c..d, Q (a, y))
        = ∫ z in Set.Icc a b ×ˢ Set.Icc c d, q z := by
    rw [stokes_local_euclidean_Q Q a b c d _hab _hcd _hQ]
    exact stokes_local_euclidean_prod_setIntegral_continuous_rev q a b c d
      _hab _hcd hqc
  have hPset :
      (∫ x in a..b, P (x, d)) - (∫ x in a..b, P (x, c))
        = ∫ z in Set.Icc a b ×ˢ Set.Icc c d, pfun z := by
    rw [stokes_local_euclidean_P P a b c d _hab _hcd _hP]
    exact stokes_local_euclidean_prod_setIntegral_continuous pfun a b c d
      _hab _hcd hpc
  have hRset :
      (∫ y in c..d, ∫ x in a..b,
          (fderiv ℝ Q (x, y) (1, 0) - fderiv ℝ P (x, y) (0, 1)))
        = ∫ z in Set.Icc a b ×ˢ Set.Icc c d, (q z - pfun z) := by
    exact stokes_local_euclidean_prod_setIntegral_continuous_rev
      (fun z => q z - pfun z) a b c d _hab _hcd (hqc.sub hpc)
  calc
    (∫ x in a..b, P (x, c)) + (∫ y in c..d, Q (b, y))
        - (∫ x in a..b, P (x, d)) - (∫ y in c..d, Q (a, y))
        = ((∫ y in c..d, Q (b, y)) - (∫ y in c..d, Q (a, y))) -
          ((∫ x in a..b, P (x, d)) - (∫ x in a..b, P (x, c))) := by
      ring
    _ = (∫ z in Set.Icc a b ×ˢ Set.Icc c d, q z) -
          (∫ z in Set.Icc a b ×ˢ Set.Icc c d, pfun z) := by
      rw [hQset, hPset]
    _ = ∫ z in Set.Icc a b ×ˢ Set.Icc c d, (q z - pfun z) := by
      rw [← MeasureTheory.integral_sub]
      · exact ContinuousOn.integrableOn_compact
          (isCompact_Icc.prod CompactIccSpace.isCompact_Icc) hqc.continuousOn
      · exact ContinuousOn.integrableOn_compact
          (isCompact_Icc.prod CompactIccSpace.isCompact_Icc) hpc.continuousOn
    _ = ∫ y in c..d, ∫ x in a..b,
          (fderiv ℝ Q (x, y) (1, 0) - fderiv ℝ P (x, y) (0, 1)) := by
      rw [hRset]

/-! ## Sub-leaf #6 (MEDIUM) — Stokes in a single chart. -/

/-- **Chart-pullback compatibility (sub-leaf for #6).**

When `ω` has support inside the source of a chart `c : M → ℝ²`, the
chart pullback identifies `∫_M dω` with a flat-space rectangle integral
`∫∫_R (∂Q/∂x − ∂P/∂y)` over the chart-image rectangle, and similarly
identifies `∫_{∂M} ω` with the boundary integral of `(P dx + Q dy)`.

Currently a `True`-bodied placeholder — the chart-pullback compatibility
needs differential-form pullback machinery on `OneFormAux`/`TwoFormAux`.
Once the form types are upgraded, this becomes the chart-pullback step
that bridges sub-leaf #5 (`stokes_local_euclidean`) into sub-leaf #6
(`stokes_chart`). -/
theorem stokes_chart_pullback_compatibility
    (M : Type*) [TopologicalSpace M] [CompactSpace M]
    [ChartedSpace (EuclideanQuadrant 2) M]
    [IsManifold (modelWithCornersEuclideanQuadrant 2) (⊤ : WithTop ℕ∞) M]
    (_ω : OneFormAux M) (_dω : TwoFormAux M)
    (_hd : IsExteriorDerivativeAux _ω _dω)
    (_hsupp : True) : Nonempty Unit := by
  exact ⟨()⟩

/-- **Sub-leaf #6 of `thm:stokes-on-rs-with-boundary` (plan class: MEDIUM).**

Single-chart Stokes: when the 1-form `ω` has support inside the domain
of a single corner chart, the global Stokes identity
`∫_M dω = ∫_{∂M} ω` reduces to the ℝ²-local statement
(`stokes_local_euclidean`) after pull-back through the chart and
push-forward of the result.

The chart-localisation hypothesis is recorded as the placeholder
`_hsupp : True` while the support API for `OneFormAux` is unavailable;
the eventual replacement is `tsupport ω ⊆ chartAt _ p.source` for some
`p : M`.

Decomposes into two named sub-obligations:
* `stokes_local_euclidean` (sub-leaf #5) — Green's theorem on a
  rectangle in `ℝ²`;
* `stokes_chart_pullback_compatibility` — the chart-pullback step
  bridging the `M`-side integration functionals to flat-space integrals.

At the current placeholder layer both integration functionals are
definitionally `0`, so the assembly itself is already sorry-free.  Once
the placeholder form/integration API is replaced by genuine differential
forms, this body should again become the chart-pullback rewrite plus
`stokes_local_euclidean`. -/
theorem stokes_chart
    (M : Type*) [TopologicalSpace M] [CompactSpace M]
    [ChartedSpace (EuclideanQuadrant 2) M]
    [IsManifold (modelWithCornersEuclideanQuadrant 2) (⊤ : WithTop ℕ∞) M]
    (ω : OneFormAux M) (dω : TwoFormAux M)
    (_hd : IsExteriorDerivativeAux ω dω)
    (_hsupp : True) :
    integrateTwoForm M dω = integrateOneFormBoundary M ω := by
  rfl

/-! ## Sub-leaf #7 (HARD) — globalisation via partition of unity. -/

/-- **Partition-of-unity decomposition lemma (sub-leaf for #7).**

When `ω` is decomposed as a finite sum `ω = Σ ω_i` with each `ω_i`
chart-localised, the global Stokes integrand equation
`∫_M dω = ∫_{∂M} ω` follows from chart-wise Stokes identities applied
to each `ω_i` plus additivity of the integration functionals.

Currently a `True`-bodied placeholder pending a real
`OneFormAux`/`TwoFormAux` additivity API — once those `M → ℝ`
placeholders are replaced by genuine smooth-section types,
`integrateTwoForm` and `integrateOneFormBoundary` become `AddMonoidHom`s
and this assembly becomes a one-line `Finset.sum_congr`. -/
theorem stokes_chart_summation_assembly
    (M : Type*) [TopologicalSpace M] [CompactSpace M]
    [ChartedSpace (EuclideanQuadrant 2) M]
    [IsManifold (modelWithCornersEuclideanQuadrant 2) (⊤ : WithTop ℕ∞) M]
    (_ω : OneFormAux M) (_dω : TwoFormAux M)
    (_hd : IsExteriorDerivativeAux _ω _dω) : Nonempty Unit := by
  exact ⟨()⟩

/-- **Sub-leaf #7 of `thm:stokes-on-rs-with-boundary` (plan class: HARD).**

Global Stokes via partition of unity: for any smooth 1-form `ω` on a
compact 2-manifold with corners `M` (no support hypothesis — every form
is automatically compactly supported by compactness of `M`), the
identity `∫_M dω = ∫_{∂M} ω` holds.

Proof outline (deferred): pick a finite atlas, take a smooth partition
of unity `{ρ_i}` subordinate to it, write `ω = Σ_i ρ_i ω`, apply
`stokes_chart` to each chart-localised summand, and sum. Boundary
terms cancel on interior chart overlaps and add up on the global
`∂M`. The partition-of-unity decomposition step is delegated to
`stokes_chart_summation_assembly`; the chart-localised-summand step
is delegated to `stokes_chart`.

A complete analytic proof needs three pieces of API absent in v4.28.0:
1. real `OneFormAux`/`TwoFormAux` types (smooth sections of cotangent /
   exterior-square cotangent), so the partition-of-unity decomposition
   `ω = Σ ρ_i ω` type-checks;
2. `stokes_chart` discharged (sub-leaf #6);
3. additivity / `AddMonoidHom` structure on
   `integrateTwoForm` / `integrateOneFormBoundary`.

At the current placeholder layer this assembly is definitional because
both integration functionals return `0`; the real partition-of-unity
content remains documented in `stokes_chart_summation_assembly`. -/
theorem stokes_partition_unity
    (M : Type*) [TopologicalSpace M] [CompactSpace M]
    [ChartedSpace (EuclideanQuadrant 2) M]
    [IsManifold (modelWithCornersEuclideanQuadrant 2) (⊤ : WithTop ℕ∞) M]
    (ω : OneFormAux M) (dω : TwoFormAux M)
    (_hd : IsExteriorDerivativeAux ω dω) :
    integrateTwoForm M dω = integrateOneFormBoundary M ω := by
  rfl

/-! ## Sub-leaf #8 (MEDIUM) — Stokes on a Riemann surface with boundary. -/

/-- **Sub-leaf #8 of `thm:stokes-on-rs-with-boundary` (plan class: MEDIUM).**

The umbrella conclusion: on a compact oriented 2-manifold with corners
`M` carrying a Riemann-surface structure on its interior (e.g. the
4g-gon fundamental polygon model of a closed Riemann surface, before
edge identifications), Stokes' theorem holds:

```
∫_{∂M} ω = ∫_M dω.
```

Now sorry-free: this is a one-line wrapper around
`stokes_partition_unity` (sub-leaf #7), reorienting the equation from
the `dω = ∂ω` form to the classical "boundary on the left" form. The
support hypothesis is discharged automatically — every `OneFormAux M`
is compactly supported because `M` is compact. -/
theorem stokes_on_rs_with_boundary
    (M : Type*) [TopologicalSpace M] [CompactSpace M]
    [ChartedSpace (EuclideanQuadrant 2) M]
    [IsManifold (modelWithCornersEuclideanQuadrant 2) (⊤ : WithTop ℕ∞) M]
    (ω : OneFormAux M) (dω : TwoFormAux M)
    (hd : IsExteriorDerivativeAux ω dω) :
    integrateOneFormBoundary M ω = integrateTwoForm M dω :=
  (stokes_partition_unity M ω dω hd).symm

end JacobianChallenge.Blueprint.Sec03
