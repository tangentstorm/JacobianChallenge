import Jacobian.HolomorphicForms.Defs
import Jacobian.HolomorphicForms.ChartedSpaceComplexPoints
import Jacobian.HolomorphicForms.CompactRiemannSurface
import Jacobian.HolomorphicForms.SectionFiberNorm
import Jacobian.HolomorphicForms.HolomorphicMap
import Jacobian.HolomorphicForms.BranchedCover
import Jacobian.HolomorphicForms.ToFunApplyVec
import Jacobian.HolomorphicForms.PullbackBundled
import Jacobian.TraceDegree.TraceDefinition
import Jacobian.Periods.TrivializationContinuousLinearMapAt
import Jacobian.Blueprint.Sec02.BranchedDegreeFromHolomorphic

/-!
# Trace form specification interface

This file contains the minimal trace object and regular-value
specification needed by both the analytic degree API and the bundled
trace API.  It deliberately does not import `TraceDegree.AnalyticDegree`,
so the degree layer can package trace laws without creating an import
cycle.
-/

namespace JacobianChallenge.HolomorphicForms

open scoped Manifold ContDiff Topology
open JacobianChallenge.HolomorphicForms
open JacobianChallenge.HolomorphicForms.SectionFiberNorm
open JacobianChallenge.Periods

variable {X Y : Type} [TopologicalSpace X] [T2Space X] [CompactSpace X]
  [ConnectedSpace X] [ChartedSpace ℂ X]
  [IsManifold 𝓘(ℂ, ℂ) (⊤ : WithTop ℕ∞) X]
  [StableChartAt ℂ X]
variable {Y : Type} [TopologicalSpace Y] [T2Space Y] [CompactSpace Y]
  [ConnectedSpace Y] [ChartedSpace ℂ Y]
  [IsManifold 𝓘(ℂ, ℂ) (⊤ : WithTop ℕ∞) Y]
  [StableChartAt ℂ Y]

/-- **Trace construction data.** Packages the global bundled trace form
`traceForm` of a holomorphic 1-form `η` along a smooth map `f : X → Y`
between compact Riemann surfaces, together with the two specifications
that determine it:

* `regular_spec` — at every regular value of every compatible
  branched-cover datum, the global form agrees with the finite local
  fiber sum `traceAtRegularValue`;
* `map_zero_spec` — when the input form is zero, the global form is
  zero.

The analytic content of producing such data (holomorphic extension of
the finite local fiber sum across the finite branch locus, plus the
identification at the regular values) is supplied by the single narrow
construction provider `traceFormsConstructionData_provider`. -/
structure TraceFormsConstructionData
    (f : X → Y) (hf : ContMDiff 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) (⊤ : WithTop ℕ∞) f)
    (η : HolomorphicOneForm ℂ X) where
  /-- The global bundled trace form of `η` along `f`. -/
  traceForm : HolomorphicOneForm ℂ Y
  /-- At every regular value of any compatible branched-cover datum on
  `f`, the global form agrees with the finite local fiber sum. -/
  regular_spec :
    ∀ (hbc : BranchedCoverData X Y f) (y : Y) (hy : isRegularValue hbc y),
      traceForm.toFun y = traceAtRegularValue hbc (fun x => η.toFun x) y hy
  /-- The zero input form maps to the zero global form. -/
  map_zero_spec : η = 0 → traceForm = 0

omit [T2Space X] [CompactSpace X] [ConnectedSpace X] [StableChartAt ℂ X]
  [IsManifold 𝓘(ℂ, ℂ) ω X]
  [T2Space Y] [CompactSpace Y] [ConnectedSpace Y]
  [IsManifold 𝓘(ℂ, ℂ) ω Y] [StableChartAt ℂ Y] in
/-- **Helper.** `cotangentPushforward` is zero on the zero cotangent
vector. Sorry-free unfolding of the definition. -/
private theorem cotangentPushforward_zero
    (f : X → Y) (x : X) :
    cotangentPushforward f x (0 : CotangentSpace ℂ X x) = 0 := by
  unfold cotangentPushforward
  by_cases h : Nonempty (IsIso (mfderiv 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) f x))
  · simp only [dif_pos h]
    exact ContinuousLinearMap.zero_comp _
  · simp only [dif_neg h]

omit [T2Space X] [CompactSpace X] [ConnectedSpace X] [StableChartAt ℂ X]
  [IsManifold 𝓘(ℂ, ℂ) ω X]
  [T2Space Y] [CompactSpace Y] [ConnectedSpace Y]
  [IsManifold 𝓘(ℂ, ℂ) ω Y] [StableChartAt ℂ Y] in
/-- **Helper.** The trace sum at a regular value of the zero pointwise
input is zero. Sorry-free reduction to `cotangentPushforward_zero` on
every summand of the finite fiber sum. -/
private theorem traceAtRegularValue_zero
    {f : X → Y} (hbc : BranchedCoverData X Y f)
    (y : Y) (hy : isRegularValue hbc y) :
    traceAtRegularValue hbc (fun _ : X => (0 : CotangentModelFiber ℂ)) y hy = 0 := by
  classical
  unfold traceAtRegularValue
  refine Finset.sum_eq_zero ?_
  rintro ⟨x, _⟩ _
  exact cotangentPushforward_zero f x

/-- **Construction data for the zero input form.** Fully proved.

When `η = 0`, the trace is the zero form on `Y`, and both fields are
immediate:

* `regular_spec` reduces every summand of the finite fiber sum to
  `cotangentPushforward f x 0 = 0`;
* `map_zero_spec` is `rfl` since the global form is already zero.

This is the strictly smaller "zero-input" leaf split out of the original
construction provider. -/
private noncomputable def traceFormsConstructionData_zero
    (f : X → Y) (hf : ContMDiff 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) (⊤ : WithTop ℕ∞) f) :
    TraceFormsConstructionData f hf (0 : HolomorphicOneForm ℂ X) where
  traceForm := 0
  regular_spec := by
    intro hbc y hy
    -- LHS is (0 : HolomorphicOneForm ℂ Y).toFun y = 0
    -- RHS is traceAtRegularValue over (fun x => (0 : HolomorphicOneForm ℂ X).toFun x)
    have hzero_toFun : ∀ x : X, (0 : HolomorphicOneForm ℂ X).toFun x = 0 := by
      intro x
      change ((0 : HolomorphicOneForm ℂ X) : ∀ y, _) x = 0
      simp
    have hLHS : (0 : HolomorphicOneForm ℂ Y).toFun y = 0 := by
      change ((0 : HolomorphicOneForm ℂ Y) : ∀ y, _) y = 0
      simp
    rw [hLHS]
    have hcongr :
        (fun x : X => (0 : HolomorphicOneForm ℂ X).toFun x) =
          (fun _ : X => (0 : CotangentModelFiber ℂ)) := by
      funext x
      exact hzero_toFun x
    rw [hcongr]
    exact (traceAtRegularValue_zero hbc y hy).symm
  map_zero_spec _ := rfl

/-- **Construction data for a constant map.** Fully proved.

For a constant map `f x = y₀`, the trace is the zero form. The
`regular_spec` field is discharged by case-splitting on whether the
target value `y` equals `y₀`:

* If `y ≠ y₀`, then the fiber `f ⁻¹' {y}` is empty, so the finite local
  fiber sum is the empty sum, which is zero;
* If `y = y₀`, the existence of a `BranchedCoverData` at a regular
  value of a constant map contradicts perfectness of the target: by
  `hbc.local_bijective_unramified` at any unramified preimage `x`,
  there are open sets `U ⊆ X`, `V ⊆ Y` with `f` bijective from `U` to
  `V`. But for constant `f` this forces `V = {y₀}`, contradicting
  `IsOpen V` since the target charted ℂ-space `Y` is perfect (no
  isolated points).

This is the strictly smaller "constant-map" leaf split out of the
original construction provider. -/
private noncomputable def traceFormsConstructionData_constant
    (f : X → Y) (hf : ContMDiff 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) (⊤ : WithTop ℕ∞) f)
    (η : HolomorphicOneForm ℂ X) (hconst : ∃ y₀, ∀ x, f x = y₀)
    (hη : η ≠ 0) :
    TraceFormsConstructionData f hf η where
  traceForm := 0
  regular_spec := by
    classical
    intro hbc y hy
    obtain ⟨y₀, hfy₀⟩ := hconst
    have hLHS : (0 : HolomorphicOneForm ℂ Y).toFun y = 0 := by
      change ((0 : HolomorphicOneForm ℂ Y) : ∀ y, _) y = 0
      simp
    rw [hLHS]
    -- Case split on y = y₀.
    by_cases hy_eq : y = y₀
    · -- y = y₀: derive contradiction via local_bijective_unramified.
      exfalso
      -- Pick any x : X (X is nonempty from ConnectedSpace).
      let x : X := Classical.arbitrary X
      have hx_fiber : x ∈ f ⁻¹' {y} := by
        show f x = y
        rw [hy_eq, hfy₀ x]
      have hx_ram : hbc.ramificationIndex x = 1 := hy x hx_fiber
      -- f x = y, so f x is in V; local bijection forces V = {y}.
      obtain ⟨U, V, hUopen, hVopen, hxU, hfxV, hbij⟩ :=
        hbc.local_bijective_unramified x hx_ram
      -- f '' U = V (BijOn) and f is constant equal to y on U.
      have hfU_eq : f '' U = {y} := by
        ext z
        constructor
        · rintro ⟨x', _, rfl⟩
          show f x' = y
          rw [hy_eq, hfy₀ x']
        · intro hz
          refine ⟨x, hxU, ?_⟩
          show f x = z
          rw [Set.mem_singleton_iff.mp hz, hy_eq, hfy₀ x]
      have hV_eq : V = ({y} : Set Y) := hbij.image_eq ▸ hfU_eq
      -- V open and V = {y}: singleton {y} would be open in Y.
      have hV_singleton_open : IsOpen ({y} : Set Y) := hV_eq ▸ hVopen
      -- But Y is perfect: no isolated points.
      rw [isOpen_singleton_iff_punctured_nhds] at hV_singleton_open
      haveI : Nontrivial Y := by
        obtain ⟨p, q, hpq⟩ := exists_two_distinct_points_of_chartedSpaceComplex (X := Y)
        exact ⟨⟨p, q, hpq⟩⟩
      haveI : PerfectSpace Y := inferInstance
      have hY_perfect : (𝓝[≠] y).NeBot := PerfectSpace.not_isolated y
      exact hY_perfect.ne hV_singleton_open
    · -- y ≠ y₀: the fiber is empty, so the sum is zero.
      have hfiber_empty : f ⁻¹' {y} = ∅ := by
        ext x
        simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_empty_iff_false,
          iff_false]
        intro hfx
        apply hy_eq
        rw [← hfx, hfy₀ x]
      show (0 : CotangentSpace ℂ Y y) =
        ((hbc.finite_fiber y).toFinset).attach.sum
          (fun x => cotangentPushforward f x.1 (η.toFun x.1))
      have htoFinset_empty : (hbc.finite_fiber y).toFinset = (∅ : Finset X) := by
        rw [Set.Finite.toFinset_eq_empty]
        exact hfiber_empty
      rw [htoFinset_empty, Finset.attach_empty, Finset.sum_empty]
  map_zero_spec h := absurd h hη

/- The target-side branch locus (image of ramification points) is finite. -/
omit [T2Space X] [CompactSpace X] [ConnectedSpace X] [ChartedSpace ℂ X]
  [IsManifold 𝓘(ℂ, ℂ) ω X] [StableChartAt ℂ X]
  [T2Space Y] [CompactSpace Y] [ConnectedSpace Y] [ChartedSpace ℂ Y]
  [IsManifold 𝓘(ℂ, ℂ) ω Y] [StableChartAt ℂ Y] in
theorem branchLocus_finite
    {f : X → Y} (h : BranchedCoverData X Y f) :
    {y : Y | ¬ isRegularValue h y}.Finite := by
  have hram : {x : X | h.ramificationIndex x ≠ 1}.Finite := h.ramified_finite
  have h_eq : {y : Y | ¬ isRegularValue h y} = f '' {x : X | h.ramificationIndex x ≠ 1} := by
    ext y; constructor
    · intro hy
      simp [isRegularValue] at hy
      obtain ⟨x, hx, hx_ram⟩ := hy
      exact ⟨x, hx_ram, hx⟩
    · rintro ⟨x, hx_ram, rfl⟩
      simp [isRegularValue]
      exact ⟨x, rfl, hx_ram⟩
  rw [h_eq]
  exact hram.image f

theorem dense_compl_of_finite_of_perfect
    {Z : Type*} [TopologicalSpace Z] [T1Space Z] [PerfectSpace Z]
    {s : Set Z} (hs : s.Finite) :
    Dense (sᶜ : Set Z) := by
  classical
  let F := hs.toFinset
  have hF : (F : Set Z) = s := hs.coe_toFinset
  rw [← hF]
  induction F using Finset.induction_on with
  | empty =>
      simp
  | insert a F _ha ih =>
      have hsingle : Dense ({a}ᶜ : Set Z) := dense_compl_singleton a
      have hFopen : IsOpen ((F : Set Z)ᶜ) := F.finite_toSet.isClosed.isOpen_compl
      have hinter : Dense ({a}ᶜ ∩ (F : Set Z)ᶜ : Set Z) :=
        hsingle.inter_of_isOpen_right ih hFopen
      have hset : (insert a (F : Set Z))ᶜ = ({a}ᶜ ∩ (F : Set Z)ᶜ : Set Z) := by
        ext z
        simp
      simpa [Finset.coe_insert, hset] using hinter

/- The regular locus is dense in Y. -/
omit [T2Space X] [CompactSpace X] [ConnectedSpace X] [ChartedSpace ℂ X]
  [IsManifold 𝓘(ℂ, ℂ) ω X] [StableChartAt ℂ X]
  [CompactSpace Y] [IsManifold 𝓘(ℂ, ℂ) ω Y] [StableChartAt ℂ Y] in
theorem regularLocus_dense
    {f : X → Y} (h : BranchedCoverData X Y f) :
    Dense (regularLocus h) := by
  haveI : Nontrivial Y := by
    obtain ⟨p, q, hpq⟩ := exists_two_distinct_points_of_chartedSpaceComplex (X := Y)
    exact ⟨⟨p, q, hpq⟩⟩
  haveI : PerfectSpace Y := inferInstance
  have hbranch : Dense ({y : Y | ¬ isRegularValue h y}ᶜ : Set Y) :=
    dense_compl_of_finite_of_perfect (branchLocus_finite h)
  simpa [regularLocus, Set.compl_setOf] using hbranch

/-! ### Trace-form holomorphic extension providers (Part A)

The narrow analytic frontier under `traceForm_global_extension` is
the classical three-step proof of "the finite local fibre sum
extends to a global holomorphic 1-form":

1. **holomorphicity on the regular locus** — already in the project
   as `localTraceAtRegularValue_holomorphic` (Provider 1);
2. **local boundedness near branch values** — the trace function is
   locally bounded near each branch value (Provider 2);
3. **generic removable singularity → global holomorphic section** —
   Riemann's removable singularity theorem, stated purely about
   `Y`-valued functions defined on a cofinite open set whose finite
   complement is the boundedness set (Provider 3);
4. **BCD-invariance of the local trace** — a set-theoretic fact that
   `traceAtRegularValue hbc … y …` depends only on `f, η, y` (not
   on the BCD chosen), via `Set.Finite.toFinset_inj` (Provider 4).

`traceForm_global_extension` is the sorry-free assembly of these. -/

omit [T2Space X] [CompactSpace X] [StableChartAt ℂ X]
  [T2Space Y] [CompactSpace Y] [ConnectedSpace Y] [StableChartAt ℂ Y] in
/-- **Provider (1).** *Trace holomorphic on the regular locus.* At
every regular value `y` of `hbc`, the local trace function
`localTraceAtRegularValue` (a chart-local realization of the finite
fibre sum, defined in a neighbourhood of `y`) is holomorphic at `y`.

Mathematically: at a regular value `y`, every preimage `x ∈ f⁻¹(y)`
is unramified, so `f` has a holomorphic local inverse near `y`, and
the cotangent pushforward of `η` along this inverse is locally
holomorphic. Summing finitely many holomorphic functions gives a
holomorphic function.

**Sorry-free** via the existing
`localTraceAtRegularValue_holomorphic` lemma in
`TraceDefinition.lean` (specialized to the canonical compatibility
witness for `hbc`). -/
theorem traceAtRegularValue_locally_holomorphic_on_regular_locus
    (f : X → Y) (hf : ContMDiff 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) (⊤ : WithTop ℕ∞) f)
    (η : HolomorphicOneForm ℂ X)
    (hbc : BranchedCoverData X Y f)
    (hcompat : hbc.RamificationIndexCompatible)
    (y : Y) (hy : isRegularValue hbc y) :
    IsHolomorphicAt (localTraceAtRegularValue hbc
      (isHolomorphic_of_contMDiff hf
        (hasLocalKfoldRamification_of_contMDiff hf)) η y hy) y :=
  localTraceAtRegularValue_holomorphic hbc hcompat
    (isHolomorphic_of_contMDiff hf
      (hasLocalKfoldRamification_of_contMDiff hf)) η y hy

/-- **Provider (2).** *Trace locally bounded near branch values.* At
every branch value `y₀` (a non-regular value) of `hbc`, there is a
neighbourhood of `y₀` and a real bound `M` such that the
chart-local finite-fibre sum is bounded by `M` on the neighbourhood
(intersected with the regular locus).

Mathematically: in a chart-local neighbourhood of a branch value
`y₀`, the preimage `f⁻¹(y₀)` is a finite set; each unramified
preimage contributes a locally bounded (in fact holomorphic) term;
each ramified preimage contributes a term whose chart-local
expansion has the form of a holomorphic 1-form pulled back through
a finite-order branched cover, which is bounded because the input
`η` is holomorphic (not meromorphic). The ramified-preimage
contribution is `0` because the cotangent pushforward at a ramified
point is `0` (the `mfderiv` is not an isomorphism there).

The hypotheses are exactly the inputs consumed by Provider (3). -/
theorem traceAtRegularValue_locally_bounded_near_branch_values
    (f : X → Y) (_hf : ContMDiff 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) (⊤ : WithTop ℕ∞) f)
    (η : HolomorphicOneForm ℂ X)
    (hbc : BranchedCoverData X Y f)
    (y₀ : Y) (_hy₀ : ¬ isRegularValue hbc y₀) :
    ∃ (U : Set Y) (M : ℝ), IsOpen U ∧ y₀ ∈ U ∧
      ∀ y ∈ U, ∀ hy : isRegularValue hbc y,
        ‖traceAtRegularValue hbc (fun x => η.toFun x) y hy‖ ≤ M := by
  sorry

omit [ConnectedSpace X] [ChartedSpace ℂ X] [IsManifold (𝓘(ℂ, ℂ)) ω X]
  [StableChartAt ℂ X] in
/-- **Provider (3).** *Generic removable-singularity provider for
holomorphic 1-forms.*

For any function `g : Y → CotangentModelFiber ℂ` that is
* holomorphic at every point of `regular` (an *open* dense subset of
  `Y` whose complement is `finite`), and
* locally bounded near every point of `regularᶜ`,

Riemann's removable singularity theorem produces a global
`HolomorphicOneForm ℂ Y` whose `toFun` agrees with `g` on `regular`.

This is the substantive classical analytic content — pure complex analysis
on `Y`, no reference to the source `X` or to the trace map. The
hypotheses are exactly the data produced by Providers (1) and (2)
when specialized to the trace function. Note that the conclusion
quantifies over a single open set `regular` and does not mention
branched-cover data, so it is strictly smaller than
`traceForm_global_extension` (which quantifies over *all* BCDs).

Allowed to remain a direct sorry: the only ingredient is Mathlib's
`Complex.removable_singularity_of_bounded`, applied chart-locally
at each of the finitely many branch points and glued through the
chart structure. -/
theorem holomorphicOneForm_of_regularLocus_holomorphic_branchLocus_bounded
    (regular : Set Y) (_hOpen : IsOpen regular) (_hDense : Dense regular)
    (_hFiniteCompl : regularᶜ.Finite)
    (g : Y → CotangentModelFiber ℂ)
    (_hHol : ∀ y ∈ regular,
      IsHolomorphicAt (fun y' : Y => g y') y)
    (_hBounded : ∀ y₀ ∈ regularᶜ,
      ∃ (U : Set Y) (M : ℝ), IsOpen U ∧ y₀ ∈ U ∧
        ∀ y ∈ U ∩ regular, ‖g y‖ ≤ M) :
    ∃ τ : HolomorphicOneForm ℂ Y,
      ∀ y ∈ regular, τ.toFun y = g y := by
  sorry

omit [T2Space X] [CompactSpace X] [ConnectedSpace X] [StableChartAt ℂ X]
  [T2Space Y] [CompactSpace Y] [ConnectedSpace Y] [IsManifold 𝓘(ℂ, ℂ) ω Y]
  [StableChartAt ℂ Y] in
/-- **Provider (4).** *BCD-invariance of the local fibre trace.*

The local fibre sum `traceAtRegularValue hbc (fun x => η.toFun x) y hy`
depends only on `f`, `η`, and `y`, not on the choice of `hbc`. This
is purely set-theoretic: the relevant `Finset` is
`(hbc.finite_fiber y).toFinset`, and the witness of finiteness is a
`Subsingleton`, so two different `BranchedCoverData` produce the same
underlying Finset; the cotangent pushforward summands depend only on
the point in the fibre, not on `hbc`.

**Sorry-free** assembly. Strictly smaller than the public leaf
because it concerns only one specific point and does not produce
any global form. -/
theorem traceAtRegularValue_BCD_invariance
    {f : X → Y} (η : HolomorphicOneForm ℂ X)
    (hbc hbc' : BranchedCoverData X Y f) (y : Y)
    (hy : isRegularValue hbc y) (hy' : isRegularValue hbc' y) :
    traceAtRegularValue hbc (fun x => η.toFun x) y hy =
      traceAtRegularValue hbc' (fun x => η.toFun x) y hy' := by
  classical
  unfold traceAtRegularValue
  -- Both `finite_fiber` witnesses are proofs of the same proposition
  -- `(f ⁻¹' {y}).Finite`, hence equal by `Subsingleton`.
  have hsub : hbc.finite_fiber y = hbc'.finite_fiber y :=
    Subsingleton.elim _ _
  congr 1

/-- **Trace-locus pointwise holomorphic auxiliary for Provider (3).**

Provider (1) gives holomorphicity of `localTraceAtRegularValue` (a
chart-local representative). Provider (3) consumes pointwise
holomorphicity of the `dite`-extended global fibre sum. Bridging the
two is the chart-local identification of `localTraceAtRegularValue`
with the global pointwise `traceAtRegularValue`.

The bridge is not a restatement of the leaf — its hypotheses are
about chart-local trace identification, not about producing the
global `HolomorphicOneForm`. Allowed as a direct sorry. -/
theorem regularLocus_dite_trace_holomorphicAt
    (f : X → Y) (_hf : ContMDiff 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) (⊤ : WithTop ℕ∞) f)
    (η : HolomorphicOneForm ℂ X)
    (hbc : BranchedCoverData X Y f)
    (_hcompat : hbc.RamificationIndexCompatible) :
    ∀ y ∈ regularLocus hbc,
      IsHolomorphicAt (fun y' : Y =>
        open Classical in
        if hy' : isRegularValue hbc y' then
          traceAtRegularValue hbc (fun x => η.toFun x) y' hy'
        else (0 : CotangentModelFiber ℂ)) y := by
  sorry

/-- **Per-BCD trace extension (sorry-free intermediate).**

Sorry-free assembly from Providers (1, via
`regularLocus_dite_trace_holomorphicAt`), (2), and (3): for one
fixed BCD `hbc`, the canonical fibre sum extends to a global
`HolomorphicOneForm ℂ Y` agreeing with it on `regularLocus hbc`. The
resulting witness is strictly smaller than `traceForm_global_extension`
because the conclusion is *only* about regular values of `hbc`, not
about all BCDs. -/
private theorem traceForm_extension_per_BCD
    (f : X → Y) (hf : ContMDiff 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) (⊤ : WithTop ℕ∞) f)
    (η : HolomorphicOneForm ℂ X)
    (hbc : BranchedCoverData X Y f)
    (hcompat : hbc.RamificationIndexCompatible) :
    ∃ τ : HolomorphicOneForm ℂ Y,
      ∀ (y : Y) (hy : isRegularValue hbc y),
        τ.toFun y = traceAtRegularValue hbc (fun x => η.toFun x) y hy := by
  classical
  have hOpen : IsOpen (regularLocus hbc) := by
    have hfin : ({y : Y | ¬ isRegularValue hbc y}).Finite :=
      branchLocus_finite hbc
    have hC : IsClosed ({y : Y | ¬ isRegularValue hbc y}) := hfin.isClosed
    have hco : IsOpen ({y : Y | ¬ isRegularValue hbc y}ᶜ) := hC.isOpen_compl
    convert hco using 1
    ext y; simp [regularLocus]
  have hDense : Dense (regularLocus hbc) := regularLocus_dense hbc
  have hCompl : (regularLocus hbc)ᶜ.Finite := by
    have h := branchLocus_finite hbc
    have heq : (regularLocus hbc)ᶜ = ({y : Y | ¬ isRegularValue hbc y}) := by
      ext y; simp [regularLocus]
    rw [heq]; exact h
  let g : Y → CotangentModelFiber ℂ := fun y' =>
    if hy' : isRegularValue hbc y' then
      traceAtRegularValue hbc (fun x => η.toFun x) y' hy'
    else (0 : CotangentModelFiber ℂ)
  have hHol : ∀ y ∈ regularLocus hbc,
      IsHolomorphicAt (fun y' : Y => g y') y :=
    regularLocus_dite_trace_holomorphicAt f hf η hbc hcompat
  have hBdd : ∀ y₀ ∈ (regularLocus hbc)ᶜ,
      ∃ (U : Set Y) (M : ℝ), IsOpen U ∧ y₀ ∈ U ∧
        ∀ y ∈ U ∩ regularLocus hbc, ‖g y‖ ≤ M := by
    intro y₀ hy₀
    have hy₀_branch : ¬ isRegularValue hbc y₀ := by
      have : y₀ ∉ regularLocus hbc := hy₀
      simpa [regularLocus] using this
    obtain ⟨U, M, hU_open, hy₀_in_U, hbound⟩ :=
      traceAtRegularValue_locally_bounded_near_branch_values f hf η hbc y₀ hy₀_branch
    refine ⟨U, M, hU_open, hy₀_in_U, ?_⟩
    rintro y ⟨hyU, hyReg⟩
    have hyReg' : isRegularValue hbc y := hyReg
    have hg : g y = traceAtRegularValue hbc (fun x => η.toFun x) y hyReg' := by
      show (if hy' : isRegularValue hbc y then
              traceAtRegularValue hbc (fun x => η.toFun x) y hy'
            else (0 : CotangentModelFiber ℂ)) = _
      rw [dif_pos hyReg']
    rw [hg]
    exact hbound y hyU hyReg'
  obtain ⟨τ, hτ⟩ :=
    holomorphicOneForm_of_regularLocus_holomorphic_branchLocus_bounded
      (regularLocus hbc) hOpen hDense hCompl g hHol hBdd
  refine ⟨τ, ?_⟩
  intro y hy
  have hyReg : y ∈ regularLocus hbc := hy
  rw [hτ y hyReg]
  show (if hy' : isRegularValue hbc y then
          traceAtRegularValue hbc (fun x => η.toFun x) y hy'
        else (0 : CotangentModelFiber ℂ)) = _
  rw [dif_pos hy]

/-- **Auxiliary (analytic continuation across canonical-BCD branch
values).** If `τ : HolomorphicOneForm ℂ Y` matches the canonical
fibre trace on `regularLocus hbc0`, and if `y` is a branch value of
the canonical BCD `hbc0` but a regular value of some other BCD
`hbc`, then `τ.toFun y = traceAtRegularValue hbc … y …`.

Both sides are continuous functions of `y` on a chart-local
neighbourhood of `y` (for τ, by holomorphicity of the section; for
the right-hand side, by the chart-local trivialisation of the
finite fibre sum at unramified preimages). On the dense joint
regular locus around `y`, they coincide pointwise via Provider (4),
so they coincide at `y` by continuity.

Allowed as a direct sorry: the precise content is one continuity
lemma about the chart-local fibre sum and a single point-evaluation
via density. This is strictly smaller than the public leaf because
it concerns a single point `y` and produces a single equality, not
a global form. -/
theorem traceForm_extension_at_branch_of_canonical_BCD
    (f : X → Y) (_hf : ContMDiff 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) (⊤ : WithTop ℕ∞) f)
    (η : HolomorphicOneForm ℂ X)
    (hbc0 hbc : BranchedCoverData X Y f)
    (y : Y) (_hy0_branch : ¬ isRegularValue hbc0 y)
    (hy_reg : isRegularValue hbc y)
    (τ : HolomorphicOneForm ℂ Y)
    (_hτ : ∀ (y' : Y) (hy' : isRegularValue hbc0 y'),
        τ.toFun y' = traceAtRegularValue hbc0 (fun x => η.toFun x) y' hy') :
    τ.toFun y = traceAtRegularValue hbc (fun x => η.toFun x) y hy_reg := by
  sorry

/-- **Narrow classical leaf: trace-form holomorphic extension.** For a
nonconstant smooth map `f : X → Y` between compact Riemann surfaces
and a nonzero holomorphic 1-form `η` on `X`, there exists a global
holomorphic 1-form `τ` on `Y` whose pointwise values agree with the
finite local fibre sum `traceAtRegularValue` at every regular value
of every compatible branched-cover datum.

**Sorry-free assembly** from the four strictly smaller providers
above:
* Provider (1) — `traceAtRegularValue_locally_holomorphic_on_regular_locus`
  (regular-locus holomorphicity), via the bridge
  `regularLocus_dite_trace_holomorphicAt`;
* Provider (2) — `traceAtRegularValue_locally_bounded_near_branch_values`
  (local boundedness near branch values);
* Provider (3) — `holomorphicOneForm_of_regularLocus_holomorphic_branchLocus_bounded`
  (the generic Riemann removable-singularity assembly);
* Provider (4) — `traceAtRegularValue_BCD_invariance` (set-theoretic
  invariance of the local fibre trace under change of BCD);
* `traceForm_extension_at_branch_of_canonical_BCD` (one-point
  analytic-continuation auxiliary at a branch value of `hbc0`).

The first three are combined in the private helper
`traceForm_extension_per_BCD` to produce a τ tied to the canonical
BCD; the fourth lifts agreement to *all* BCDs at any regular value
of `hbc0`; the auxiliary lifts to regular values not regular for
`hbc0` via analytic continuation. -/
theorem traceForm_global_extension
    (f : X → Y) (hf : ContMDiff 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) (⊤ : WithTop ℕ∞) f)
    (η : HolomorphicOneForm ℂ X) (_hη : η ≠ 0)
    (hnonconst : ¬ ∃ y₀, ∀ x, f x = y₀) :
    ∃ τ : HolomorphicOneForm ℂ Y,
      ∀ (hbc : BranchedCoverData X Y f) (y : Y) (hy : isRegularValue hbc y),
        τ.toFun y = traceAtRegularValue hbc (fun x => η.toFun x) y hy := by
  classical
  set hkfold := hasLocalKfoldRamification_of_contMDiff hf
  set hw := hasWeightedFiberConservation_of_contMDiff hf
  set hHol := isHolomorphic_of_contMDiff hf hkfold
  set hbc0 := JacobianChallenge.Blueprint.branchedCoverData_of_nonconstant_holomorphic
    hHol hw hnonconst with hbc0_def
  have hcompat0 :=
    JacobianChallenge.Blueprint.branchedCoverData_of_nonconstant_holomorphic_compatible
      hHol hw hnonconst
  -- For one fixed BCD `hbc0`, the per-BCD provider gives τ.
  obtain ⟨τ, hτ0⟩ := traceForm_extension_per_BCD f hf η hbc0 hcompat0
  refine ⟨τ, ?_⟩
  intro hbc y hy
  by_cases hy0 : isRegularValue hbc0 y
  · rw [hτ0 y hy0]
    exact (traceAtRegularValue_BCD_invariance η hbc0 hbc y hy0 hy).symm
  · exact traceForm_extension_at_branch_of_canonical_BCD f hf η hbc0 hbc y hy0 hy τ hτ0

/-- **Narrow trace construction provider (nonconstant nonzero case).**

Sorry-free assembly from `traceForm_global_extension`: extract the
witness form `τ` and its regular-value spec; the
`map_zero_spec` field is vacuously satisfied since the hypothesis
`η ≠ 0` rules it out.

The remaining classical content lives entirely inside the strictly
smaller leaf `traceForm_global_extension`. -/
noncomputable def traceFormsConstructionData_nonconstant_nonzero_provider
    (f : X → Y) (hf : ContMDiff 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) (⊤ : WithTop ℕ∞) f)
    (η : HolomorphicOneForm ℂ X) (hη : η ≠ 0)
    (hnonconst : ¬ ∃ y₀, ∀ x, f x = y₀) :
    TraceFormsConstructionData f hf η :=
  let hext := traceForm_global_extension (f := f) (hf := hf) η hη hnonconst
  { traceForm := hext.choose
    regular_spec := hext.choose_spec
    map_zero_spec := fun hzero => (hη hzero).elim }

/-- **The trace construction provider.** Three-way case split:

* `η = 0` — fully proved via `traceFormsConstructionData_zero`;
* `η ≠ 0` and `f` constant — fully proved via
  `traceFormsConstructionData_constant`;
* `η ≠ 0` and `f` nonconstant — delegates to the strictly narrower
  analytic leaf
  `traceFormsConstructionData_nonconstant_nonzero_provider`.

The first two branches are strictly smaller leaves already proved in
this pass; the third branch is the substantive analytic frontier (removable
singularity / holomorphic extension of the finite local fiber sum
across the finite branch locus of a nonconstant holomorphic map). -/
noncomputable def traceFormsConstructionData_provider
    (f : X → Y) (hf : ContMDiff 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) (⊤ : WithTop ℕ∞) f)
    (η : HolomorphicOneForm ℂ X) :
    TraceFormsConstructionData f hf η := by
  classical
  by_cases hη : η = 0
  · -- Zero-input case: fully proved. Cast the η-specialized data back to η.
    cases hη
    exact traceFormsConstructionData_zero f hf
  · by_cases hconst : ∃ y₀, ∀ x, f x = y₀
    · exact traceFormsConstructionData_constant f hf η hconst hη
    · exact traceFormsConstructionData_nonconstant_nonzero_provider f hf η hη hconst

/-- The trace (pushforward) of a holomorphic 1-form along a smooth map.
Sorry-free shim around `traceFormsConstructionData_provider`: the trace
is the `traceForm` field of the construction data. -/
noncomputable def traceFormsBundled
    (f : X → Y) (hf : ContMDiff 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) (⊤ : WithTop ℕ∞) f)
    (η : HolomorphicOneForm ℂ X) : HolomorphicOneForm ℂ Y :=
  (traceFormsConstructionData_provider f hf η).traceForm

-- The linear trace map `traceFormsBundledLM` is defined later in this
-- file, after the identity principle `holomorphicOneForm_ext_on`.

/- **Identity principle for holomorphic 1-forms.**
Two holomorphic 1-forms that agree on a dense set of a connected Riemann
surface are equal everywhere. -/
omit [ConnectedSpace Y] in
theorem holomorphicOneForm_ext_on
    {s : Set Y} (hs : Dense s)
    {ω₁ ω₂ : HolomorphicOneForm ℂ Y} (h : ∀ y ∈ s, ω₁.toFun y = ω₂.toFun y) :
    ω₁ = ω₂ := by
  apply ContMDiffSection.ext
  intro y
  let δ : HolomorphicOneForm ℂ Y := ω₁ - ω₂
  have hcont : Continuous (ContMDiffSection.fiberNorm δ) :=
    holomorphicOneForm_fiberNorm_continuous Y δ
  have hzero_on : Set.EqOn (ContMDiffSection.fiberNorm δ) (fun _ : Y => (0 : ℝ)) s := by
    intro z hz
    have hzfun : δ.toFun z = 0 := by
      dsimp [δ]
      change ((ω₁ - ω₂ : HolomorphicOneForm ℂ Y) : ∀ y, _) z = 0
      rw [ContMDiffSection.coe_sub]
      exact sub_eq_zero.mpr (h z hz)
    simp [ContMDiffSection.fiberNorm, hzfun]
  have hzero_all : ContMDiffSection.fiberNorm δ = fun _ : Y => (0 : ℝ) :=
    Continuous.ext_on hs hcont continuous_const hzero_on
  have hyzero : δ.toFun y = 0 := by
    have hn : ‖δ.toFun y‖ = 0 := by
      simpa [ContMDiffSection.fiberNorm] using congrFun hzero_all y
    exact norm_eq_zero.mp hn
  dsimp [δ] at hyzero
  change ((ω₁ - ω₂ : HolomorphicOneForm ℂ Y) : ∀ y, _) y = 0 at hyzero
  rw [ContMDiffSection.coe_sub] at hyzero
  exact sub_eq_zero.mp hyzero

/-- Minimal trace input used by local linearity and regular-value
assemblies.  This separates the specification needed downstream from
the construction of the global bundled trace form. -/
structure TraceFormsRegularSpec
    (f : X → Y) (hf : ContMDiff 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) (⊤ : WithTop ℕ∞) f) where
  /-- Trace sends the zero form to zero. -/
  map_zero : traceFormsBundled f hf 0 = 0
  /-- At regular values, trace agrees with the finite local fiber sum. -/
  apply_fun_regular :
    ∀ (hbc : BranchedCoverData X Y f) (η : HolomorphicOneForm ℂ X)
      (y : Y) (hy : isRegularValue hbc y),
      (traceFormsBundled f hf η).toFun y =
        traceAtRegularValue hbc (fun x => η.toFun x) y hy

/-- Private helper: in the constant-map case, the construction-data
provider for any input form `η` reduces to
`traceFormsConstructionData_constant` (or
`traceFormsConstructionData_zero` if `η = 0`); in either case, the
resulting `traceForm` is the zero form on `Y`. -/
theorem traceFormsBundled_eq_zero_of_constant
    {f : X → Y} {hf : ContMDiff 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) (⊤ : WithTop ℕ∞) f}
    (η : HolomorphicOneForm ℂ X) (hconst : ∃ y₀, ∀ x, f x = y₀) :
    traceFormsBundled f hf η = 0 := by
  classical
  by_cases hη : η = 0
  · subst hη
    change (traceFormsConstructionData_provider f hf (0 : HolomorphicOneForm ℂ X)).traceForm = 0
    exact (traceFormsConstructionData_provider f hf 0).map_zero_spec rfl
  · change (traceFormsConstructionData_provider f hf η).traceForm = 0
    rw [show traceFormsConstructionData_provider f hf η =
      traceFormsConstructionData_constant f hf η hconst hη from by
        unfold traceFormsConstructionData_provider
        simp [hη, hconst]]
    rfl

/-- The linear trace map on holomorphic 1-forms.

Sorry-free assembly from `traceFormsConstructionData_provider` plus the
identity principle on the regular locus.

Linearity is proved by the standard "dense agreement at regular values"
trick: in the constant-map case both sides are zero
(`traceFormsBundled_eq_zero_of_constant`); in the nonconstant case, the
constructed trace forms agree with `traceAtRegularValue` on the dense
regular locus of the canonical branched-cover datum, and
`traceAtRegularValue` is already linear (via `traceAtRegularValue_add`
and `traceAtRegularValue_smul`). The identity principle
(`holomorphicOneForm_ext_on (regularLocus_dense hbc)`) then promotes
agreement on the regular locus to agreement everywhere. -/
noncomputable def traceFormsBundledLM
    (f : X → Y) (hf : ContMDiff 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) (⊤ : WithTop ℕ∞) f) :
    HolomorphicOneForm ℂ X →ₗ[ℂ] HolomorphicOneForm ℂ Y where
  toFun η := traceFormsBundled f hf η
  map_add' η ζ := by
    classical
    by_cases hconst : ∃ y₀, ∀ x, f x = y₀
    · rw [traceFormsBundled_eq_zero_of_constant η hconst,
          traceFormsBundled_eq_zero_of_constant ζ hconst,
          traceFormsBundled_eq_zero_of_constant (η + ζ) hconst,
          add_zero]
    · set hkfold := hasLocalKfoldRamification_of_contMDiff hf
      set hw := hasWeightedFiberConservation_of_contMDiff hf
      set hHol := isHolomorphic_of_contMDiff hf hkfold
      set hbc := JacobianChallenge.Blueprint.branchedCoverData_of_nonconstant_holomorphic
        hHol hw hconst
      apply holomorphicOneForm_ext_on (regularLocus_dense hbc)
      intro y hy
      have hη_reg := (traceFormsConstructionData_provider f hf η).regular_spec hbc y hy
      have hζ_reg := (traceFormsConstructionData_provider f hf ζ).regular_spec hbc y hy
      have hηζ_reg := (traceFormsConstructionData_provider f hf (η + ζ)).regular_spec hbc y hy
      change (traceFormsConstructionData_provider f hf (η + ζ)).traceForm.toFun y =
        ((traceFormsConstructionData_provider f hf η).traceForm +
          (traceFormsConstructionData_provider f hf ζ).traceForm).toFun y
      rw [hηζ_reg]
      change _ = ((traceFormsConstructionData_provider f hf η).traceForm.toFun +
          (traceFormsConstructionData_provider f hf ζ).traceForm.toFun) y
      simp only [Pi.add_apply]
      rw [hη_reg, hζ_reg]
      have h_eq : (fun x : X => (η + ζ).toFun x) =
          (fun x => η.toFun x + ζ.toFun x) := by
        funext x
        show ((η + ζ : HolomorphicOneForm ℂ X) : ∀ y, _) x = _
        rw [ContMDiffSection.coe_add]
        rfl
      rw [h_eq]
      exact traceAtRegularValue_add hbc (fun x => η.toFun x) (fun x => ζ.toFun x) y hy
  map_smul' k η := by
    classical
    by_cases hconst : ∃ y₀, ∀ x, f x = y₀
    · show traceFormsBundled f hf (k • η) = k • traceFormsBundled f hf η
      rw [traceFormsBundled_eq_zero_of_constant η hconst,
          traceFormsBundled_eq_zero_of_constant (k • η) hconst]
      have h0 : (k • (0 : HolomorphicOneForm ℂ Y)) = 0 := by
        apply ContMDiffSection.ext
        intro y
        change ((k • (0 : HolomorphicOneForm ℂ Y)) : ∀ z, _) y = _
        rw [ContMDiffSection.coe_smul]
        simp
      exact h0.symm
    · set hkfold := hasLocalKfoldRamification_of_contMDiff hf
      set hw := hasWeightedFiberConservation_of_contMDiff hf
      set hHol := isHolomorphic_of_contMDiff hf hkfold
      set hbc := JacobianChallenge.Blueprint.branchedCoverData_of_nonconstant_holomorphic
        hHol hw hconst
      show traceFormsBundled f hf (k • η) = k • traceFormsBundled f hf η
      apply holomorphicOneForm_ext_on (regularLocus_dense hbc)
      intro y hy
      have hη_reg := (traceFormsConstructionData_provider f hf η).regular_spec hbc y hy
      have hkη_reg := (traceFormsConstructionData_provider f hf (k • η)).regular_spec hbc y hy
      change (traceFormsConstructionData_provider f hf (k • η)).traceForm.toFun y =
        (k • (traceFormsConstructionData_provider f hf η).traceForm).toFun y
      rw [hkη_reg]
      change _ = (k • (traceFormsConstructionData_provider f hf η).traceForm.toFun) y
      simp only [Pi.smul_apply]
      rw [hη_reg]
      have h_eq : (fun x : X => (k • η).toFun x) =
          (fun x => k • η.toFun x) := by
        funext x
        show ((k • η : HolomorphicOneForm ℂ X) : ∀ y, _) x = _
        rw [ContMDiffSection.coe_smul]
        rfl
      rw [h_eq]
      exact traceAtRegularValue_smul hbc k (fun x => η.toFun x) y hy

end JacobianChallenge.HolomorphicForms
