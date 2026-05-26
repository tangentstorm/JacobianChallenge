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

/--
**Trace construction data.** Packages the global bundled trace form
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
construction provider `traceFormsConstructionData_provider`.
-/
structure TraceFormsConstructionData
    (f : X → Y) (hf : ContMDiff 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) (⊤ : WithTop ℕ∞) f)
    (η : HolomorphicOneForm ℂ X) where
  /-- The global bundled trace form of `η` along `f`. -/
  traceForm : HolomorphicOneForm ℂ Y
  /--
At every regular value of any compatible branched-cover datum on
  `f`, the global form agrees with the finite local fiber sum.
-/
  regular_spec :
    ∀ (hbc : BranchedCoverData X Y f) (_hcompat : hbc.RamificationIndexCompatible)
      (y : Y) (hy : isRegularValue hbc y),
      traceForm.toFun y = traceAtRegularValue hbc (fun x => η.toFun x) y hy
  /-- The zero input form maps to the zero global form. -/
  map_zero_spec : η = 0 → traceForm = 0

omit [T2Space X] [CompactSpace X] [ConnectedSpace X] [StableChartAt ℂ X]
  [IsManifold 𝓘(ℂ, ℂ) ω X]
  [T2Space Y] [CompactSpace Y] [ConnectedSpace Y]
  [IsManifold 𝓘(ℂ, ℂ) ω Y] [StableChartAt ℂ Y] in

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

private theorem traceAtRegularValue_zero
    {f : X → Y} (hbc : BranchedCoverData X Y f)
    (y : Y) (hy : isRegularValue hbc y) :
    traceAtRegularValue hbc (fun _ : X => (0 : CotangentModelFiber ℂ)) y hy = 0 := by
  classical
  unfold traceAtRegularValue
  refine Finset.sum_eq_zero ?_
  rintro ⟨x, _⟩ _
  exact cotangentPushforward_zero f x

/--
**Construction data for the zero input form.** Fully proved.

When `η = 0`, the trace is the zero form on `Y`, and both fields are
immediate:

* `regular_spec` reduces every summand of the finite fiber sum to
  `cotangentPushforward f x 0 = 0`;
* `map_zero_spec` is `rfl` since the global form is already zero.

This is the strictly smaller "zero-input" leaf split out of the original
construction provider.
-/
private noncomputable def traceFormsConstructionData_zero
    (f : X → Y) (hf : ContMDiff 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) (⊤ : WithTop ℕ∞) f) :
    TraceFormsConstructionData f hf (0 : HolomorphicOneForm ℂ X) where
  traceForm := 0
  regular_spec := by
    intro hbc _hcompat y hy
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

/--
**Construction data for a constant map.** Fully proved.

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
original construction provider.
-/
private noncomputable def traceFormsConstructionData_constant
    (f : X → Y) (hf : ContMDiff 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) (⊤ : WithTop ℕ∞) f)
    (η : HolomorphicOneForm ℂ X) (hconst : ∃ y₀, ∀ x, f x = y₀)
    (hη : η ≠ 0) :
    TraceFormsConstructionData f hf η where
  traceForm := 0
  regular_spec := by
    classical
    intro hbc _hcompat y hy
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

/-!
### Trace-form holomorphic extension providers (Part A)

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
-/

omit [T2Space X] [CompactSpace X] [StableChartAt ℂ X]
  [T2Space Y] [CompactSpace Y] [ConnectedSpace Y] [StableChartAt ℂ Y] in
/--
**Provider (1).** *Trace holomorphic on the regular locus.* At
every regular value `y` of `hbc`, the local trace function
`localTraceAtRegularValue` (a chart-local realization of the finite
fibre sum, defined in a neighbourhood of `y`) is holomorphic at `y`.

Mathematically: at a regular value `y`, every preimage `x ∈ f⁻¹(y)`
is unramified, so `f` has a holomorphic local inverse near `y`, and
the cotangent pushforward of `η` along this inverse is locally
holomorphic. Summing finitely many holomorphic functions gives a
holomorphic function.
-/
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

/--
**Provider (2).** *Trace locally bounded near branch values.* At
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

The hypotheses are exactly the inputs consumed by Provider (3).
-/
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
/--
**Provider (3).** *Generic removable-singularity provider for
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
-/
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
/--
**Provider (4).** *BCD-invariance of the local fibre trace.*

The local fibre sum `traceAtRegularValue hbc (fun x => η.toFun x) y hy`
depends only on `f`, `η`, and `y`, not on the choice of `hbc`. This
is purely set-theoretic: the relevant `Finset` is
`(hbc.finite_fiber y).toFinset`, and the witness of finiteness is a
`Subsingleton`, so two different `BranchedCoverData` produce the same
underlying Finset; the cotangent pushforward summands depend only on
the point in the fibre, not on `hbc`.
-/
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

/--
**Local-inverse preimage of any nhd is a nhd.** The single
continuity-like consequence we need: for any open `W ∋ x`, the preimage
`(h.localInverseAt x hx) ⁻¹' W` is a `𝓝 (f x)`-set.

Proof sketch: the BCD's `localInverseAt` agrees on a neighborhood of `f x`
with an analytic local inverse `analyticInv` (constructed from the
analytic-inverse-function theorem applied to `chartLocalAt f x` whose
derivative at `chartAt ℂ x x` is nonzero because the ramification index
is 1). The analytic local inverse is genuinely continuous at `f x`
because it is the composition `(chartAt x).symm ∘ r ∘ chartAt(f x)`,
where `r` is analytic on a neighborhood of `chartAt(f x)(f x)`. By
combining the Tendsto from analytic continuity with the eventually-equality,
the preimage of any open `W ∋ x` is a neighborhood of `f x`.
-/
private theorem localInverseAt_preimage_mem_nhds
    {f : X → Y} (h : BranchedCoverData X Y f)
    (hcompat : h.RamificationIndexCompatible)
    (hHol : IsHolomorphic f)
    (x : X) (hx : h.ramificationIndex x = 1)
    {W : Set X} (hW_open : IsOpen W) (hxW : x ∈ W) :
    h.localInverseAt x hx ⁻¹' W ∈ 𝓝 (f x) := by
  classical
  obtain ⟨U, V, hUopen, hVopen, hxU, hfxV, hbij, _hright_branch, hleft_branch⟩ :=
    h.localInverse_is_inverse hx
  -- Derive deriv ≠ 0 from compatibility.
  have hramAt : mapAnalyticOrderAt f x = 1 := by
    rw [← h.ramificationIndex_eq_mapAnalyticOrderAt hcompat (hHol.holomorphicAt x)]
    exact hx
  have hderiv : deriv (chartLocalAt f x) (chartAt ℂ x x) ≠ 0 := by
    have h_order : analyticOrderAt
        (fun t => chartLocalAt f x t - chartLocalAt f x (chartAt ℂ x x))
        (chartAt ℂ x x) = 1 := by
      convert hramAt using 1
      unfold mapAnalyticOrderAt
      simp +decide [analyticOrderNatAt]
    have h_deriv_an : AnalyticAt ℂ
        (fun t => chartLocalAt f x t - chartLocalAt f x (chartAt ℂ x x))
        (chartAt ℂ x x) :=
      (hHol.holomorphicAt x).sub analyticAt_const
    have h_deriv_order : analyticOrderAt
        (deriv (fun t => chartLocalAt f x t - chartLocalAt f x (chartAt ℂ x x)))
        (chartAt ℂ x x) = 0 := by
      have := AnalyticAt.analyticOrderAt_deriv_add_one h_deriv_an
      aesop
    rw [analyticOrderAt_eq_zero] at h_deriv_order
    rcases h_deriv_order with hzero | hnezero
    · exfalso; exact hzero (AnalyticAt.deriv h_deriv_an)
    · simpa [deriv_sub_const] using hnezero
  -- Construct the analytic local inverse and prove Tendsto.
  let analyticInv : Y → X := (hHol.holomorphicAt x).localInverse hderiv
  let F : ℂ → ℂ := chartLocalAt f x
  let z₀ : ℂ := chartAt ℂ x x
  let w₀ : ℂ := chartAt ℂ (f x) (f x)
  let r : ℂ → ℂ :=
    (hHol.holomorphicAt x).hasStrictDerivAt.localInverse F
      (deriv F z₀) z₀ hderiv
  have hFz₀ : F z₀ = w₀ := by simp [F, z₀, w₀]
  have hr_z₀ : r w₀ = z₀ := by
    dsimp [r]
    rw [← hFz₀]
    exact (HasStrictDerivAt.eventually_left_inverse
      (f := F) (f' := deriv F z₀) (a := z₀)
      (hf := (hHol.holomorphicAt x).hasStrictDerivAt) (hf' := hderiv)).self_of_nhds
  have hlocalInv_tendsto : Filter.Tendsto analyticInv (𝓝 (f x)) (𝓝 x) := by
    have hr_an : AnalyticAt ℂ r w₀ := by
      dsimp [r, F, z₀, w₀]
      simpa [F, z₀, w₀, hFz₀] using
        (hHol.holomorphicAt x).analyticAt_localInverse hderiv
    have hr_tendsto : Filter.Tendsto r (𝓝 w₀) (𝓝 z₀) := by
      simpa [ContinuousAt, hr_z₀] using hr_an.continuousAt
    have hchart_tendsto : Filter.Tendsto (fun y : Y => chartAt ℂ (f x) y)
        (𝓝 (f x)) (𝓝 w₀) := by
      simpa [w₀] using (chartAt ℂ (f x)).continuousAt (mem_chart_source ℂ (f x))
    have hsymm_tendsto : Filter.Tendsto (fun z => (chartAt ℂ x).symm z)
        (𝓝 z₀) (𝓝 x) := by
      have hcont := (chartAt ℂ x).continuousAt_symm
        ((chartAt ℂ x).map_source (mem_chart_source ℂ x))
      change Filter.Tendsto (fun z => (chartAt ℂ x).symm z) (𝓝 z₀)
        (𝓝 ((chartAt ℂ x).symm z₀)) at hcont
      simpa [z₀, (chartAt ℂ x).left_inv (mem_chart_source ℂ x)] using hcont
    have hcomp := hsymm_tendsto.comp (hr_tendsto.comp hchart_tendsto)
    simpa [analyticInv, IsHolomorphicAt.localInverse, r, F, z₀, w₀] using hcomp
  -- Show analyticInv = localInverseAt x hx eventually near f x.
  have hanalyticInv_mem_U : ∀ᶠ y in 𝓝 (f x), analyticInv y ∈ U :=
    hlocalInv_tendsto.eventually (hUopen.mem_nhds hxU)
  have hanalyticInv_right : ∀ᶠ y in 𝓝 (f x), f (analyticInv y) = y := by
    have hright_z : ∀ᶠ z in 𝓝 w₀, F (r z) = z := by
      dsimp [r]
      simpa [F, z₀, w₀, hFz₀] using
        (HasStrictDerivAt.eventually_right_inverse
          (f := F) (f' := deriv F z₀) (a := z₀)
          (hf := (hHol.holomorphicAt x).hasStrictDerivAt) (hf' := hderiv))
    have hchart_tendsto : Filter.Tendsto (fun y : Y => chartAt ℂ (f x) y)
        (𝓝 (f x)) (𝓝 w₀) := by
      simpa [w₀] using (chartAt ℂ (f x)).continuousAt (mem_chart_source ℂ (f x))
    have hright_y : ∀ᶠ y in 𝓝 (f x), F (r (chartAt ℂ (f x) y)) =
        chartAt ℂ (f x) y :=
      hchart_tendsto.eventually hright_z
    have hy_source : ∀ᶠ y in 𝓝 (f x), y ∈ (chartAt ℂ (f x)).source :=
      (chartAt ℂ (f x)).open_source.mem_nhds (mem_chart_source ℂ (f x))
    have hf_analyticInv_source : ∀ᶠ y in 𝓝 (f x),
        f (analyticInv y) ∈ (chartAt ℂ (f x)).source := by
      have htendsto : Filter.Tendsto (fun y => f (analyticInv y)) (𝓝 (f x)) (𝓝 (f x)) :=
        Filter.Tendsto.comp hHol.continuous.continuousAt hlocalInv_tendsto
      exact htendsto.eventually
        ((chartAt ℂ (f x)).open_source.mem_nhds (mem_chart_source ℂ (f x)))
    filter_upwards [hright_y, hy_source, hf_analyticInv_source] with y hy_eq hy_src hfy_src
    have hchart : chartAt ℂ (f x) (f (analyticInv y)) = chartAt ℂ (f x) y := by
      simpa [analyticInv, IsHolomorphicAt.localInverse, F, r, z₀, w₀] using hy_eq
    exact (chartAt ℂ (f x)).injOn hfy_src hy_src hchart
  -- analyticInv y = h.localInverseAt x hx y eventually.
  have heq : ∀ᶠ y in 𝓝 (f x), analyticInv y = h.localInverseAt x hx y := by
    filter_upwards [hanalyticInv_mem_U, hanalyticInv_right] with y hy_an_U hy_an_right
    have hleft := hleft_branch (analyticInv y) hy_an_U
    rw [hy_an_right] at hleft
    exact hleft.symm
  -- Use Tendsto + eventually-eq to get preimage of W is a nhd.
  have hW_nhd : W ∈ 𝓝 x := hW_open.mem_nhds hxW
  have hanalyticInv_in_W : ∀ᶠ y in 𝓝 (f x), analyticInv y ∈ W :=
    hlocalInv_tendsto.eventually hW_nhd
  filter_upwards [hanalyticInv_in_W, heq] with y hy_an_W hy_eq
  show h.localInverseAt x hx y ∈ W
  rw [← hy_eq]; exact hy_an_W

/--
**Trace-locus pointwise holomorphic auxiliary for Provider (3).**

Provider (1) gives holomorphicity of `localTraceAtRegularValue` (a
chart-local representative). Provider (3) consumes pointwise
holomorphicity of the `dite`-extended global fibre sum. Bridging the
two is the chart-local identification of `localTraceAtRegularValue`
with the global pointwise `traceAtRegularValue`.
-/
theorem regularLocus_dite_trace_holomorphicAt
    (f : X → Y) (hf : ContMDiff 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) (⊤ : WithTop ℕ∞) f)
    (η : HolomorphicOneForm ℂ X)
    (hbc : BranchedCoverData X Y f)
    (hcompat : hbc.RamificationIndexCompatible) :
    ∀ y ∈ regularLocus hbc,
      IsHolomorphicAt (fun y' : Y =>
        open Classical in
        if hy' : isRegularValue hbc y' then
          traceAtRegularValue hbc (fun x => η.toFun x) y' hy'
        else (0 : CotangentModelFiber ℂ)) y := by
  classical
  intro y hy_reg
  have hy : isRegularValue hbc y := hy_reg
  have hHol : IsHolomorphic f :=
    isHolomorphic_of_contMDiff hf (hasLocalKfoldRamification_of_contMDiff hf)
  have hloc_holo : IsHolomorphicAt
      (localTraceAtRegularValue hbc hHol η y hy) y :=
    localTraceAtRegularValue_holomorphic hbc hcompat hHol η y hy
  refine hloc_holo.congr_of_eventuallyEq ?_
  have hRegOpen : IsOpen (regularLocus hbc) := by
    have hfin : ({y : Y | ¬ isRegularValue hbc y}).Finite :=
      branchLocus_finite hbc
    have hC : IsClosed ({y : Y | ¬ isRegularValue hbc y}) := hfin.isClosed
    have hco : IsOpen ({y : Y | ¬ isRegularValue hbc y}ᶜ) := hC.isOpen_compl
    convert hco using 1
    ext z; simp [regularLocus]
  have hReg_mem : regularLocus hbc ∈ 𝓝 y := hRegOpen.mem_nhds hy_reg
  set S : Finset X := (hbc.finite_fiber y).toFinset with hS_def
  have hfiber_eq : ∀ {x : X}, x ∈ S ↔ x ∈ f ⁻¹' {y} := by
    intro x; rw [hS_def, Set.Finite.mem_toFinset]
  -- T2 separation gives raw pairwise disjoint nhds W₀ x.
  have hS_fin : (S : Set X).Finite := S.finite_toSet
  obtain ⟨W₀, hW₀_local, hW₀_disj⟩ := hS_fin.exists_pairwiseDisjoint_open_nhds
  -- For each x ∈ S, ramification index = 1, so the BCD provides U₀ x, V₀ x
  -- with f bijective from U₀ x to V₀ x and inverse identities. Build
  -- `W x := W₀ x ∩ U₀ x`: open, contains x (since x ∈ U₀ x and x ∈ W₀ x),
  -- pairwise disjoint (W₀'s are), and inside U₀ x so `hleft` applies for any
  -- x' ∈ W x giving `localInverseAt x hx_ram (f x') = x'`.
  -- Then use continuity of localInverseAt x at f x = y to find a Y-nhd V₁ x
  -- such that localInverseAt x hx_ram(V₁ x) ⊆ W x.
  have hper_x : ∀ x : X, x ∈ S → ∃ (Wx : Set X) (V₁ : Set Y),
        IsOpen Wx ∧ IsOpen V₁ ∧ x ∈ Wx ∧ y ∈ V₁ ∧
        (∀ x₁ ∈ S, ∀ x₂ ∈ S, x₁ ≠ x₂ → x = x₁ ∨ x = x₂ → True) ∧
        (∀ hx_ram : hbc.ramificationIndex x = 1,
          (∀ z ∈ V₁, f (hbc.localInverseAt x hx_ram z) = z ∧
                      hbc.localInverseAt x hx_ram z ∈ Wx) ∧
          (∀ x' ∈ Wx, hbc.localInverseAt x hx_ram (f x') = x')) ∧
        Wx ⊆ W₀ x := by
    intro x hxS
    have hx_fiber : x ∈ f ⁻¹' {y} := hfiber_eq.mp hxS
    have hx_ram : hbc.ramificationIndex x = 1 := hy x hx_fiber
    obtain ⟨U₀, V₀, hU₀_open, hV₀_open, hxU₀, hfxV₀, _hbij, hright, hleft⟩ :=
      hbc.localInverse_is_inverse hx_ram
    have hfx_eq : f x = y := hx_fiber
    -- Wx := W₀ x ∩ U₀: open, x ∈ Wx, Wx ⊆ U₀, Wx ⊆ W₀ x.
    let Wx : Set X := W₀ x ∩ U₀
    have hWx_open : IsOpen Wx := (hW₀_local x hxS).1.inter hU₀_open
    have hxWx : x ∈ Wx := ⟨(hW₀_local x hxS).2, hxU₀⟩
    have hWx_sub_U₀ : Wx ⊆ U₀ := fun _ h => h.2
    have hWx_sub_W₀ : Wx ⊆ W₀ x := fun _ h => h.1
    have hWx_pre : hbc.localInverseAt x hx_ram ⁻¹' Wx ∈ 𝓝 (f x) :=
      localInverseAt_preimage_mem_nhds hbc hcompat hHol x hx_ram hWx_open hxWx
    -- Get an open V₁'' ⊆ preimage of Wx, containing f x.
    obtain ⟨V₁'', hV₁''_sub, hV₁''_open, hyV₁''⟩ := mem_nhds_iff.mp hWx_pre
    refine ⟨Wx, V₀ ∩ V₁'', hWx_open, hV₀_open.inter hV₁''_open, hxWx, ?_, ?_, ?_, hWx_sub_W₀⟩
    · -- y ∈ V₀ ∩ V₁''
      refine ⟨?_, ?_⟩
      · rw [← hfx_eq]; exact hfxV₀
      · rw [← hfx_eq]; exact hyV₁''
    · intros; trivial
    · intro hx_ram'
      refine ⟨?_, ?_⟩
      · intro z ⟨hz_V₀, hz_V₁''⟩
        have h_eq_ram : hx_ram' = hx_ram := rfl
        refine ⟨?_, ?_⟩
        · rw [h_eq_ram]; exact hright z hz_V₀
        · rw [h_eq_ram]; exact hV₁''_sub hz_V₁''
      · intro x' hx'Wx
        have h_eq_ram : hx_ram' = hx_ram := rfl
        rw [h_eq_ram]
        exact hleft x' (hWx_sub_U₀ hx'Wx)
  -- Choose Wx, V₁ etc.
  choose! Wx V₁ hWx_open hV₁_open hxWx hyV₁ _hdisj_trivial hWx_inv hWx_sub_W₀
    using hper_x
  -- Pairwise disjointness of Wx (using hWx_sub_W₀).
  have hWx_disj : ∀ x₁ ∈ S, ∀ x₂ ∈ S, x₁ ≠ x₂ → Disjoint (Wx x₁) (Wx x₂) := by
    intro x₁ hx₁ x₂ hx₂ hne
    exact (hW₀_disj hx₁ hx₂ hne).mono (hWx_sub_W₀ x₁ hx₁) (hWx_sub_W₀ x₂ hx₂)
  -- V := ⋂ x ∈ S, V₁ x. Open nhd of y.
  have hV_int_nhds : (⋂ x ∈ (S : Set X), V₁ x) ∈ 𝓝 y := by
    refine (Filter.biInter_finset_mem S).mpr ?_
    intro x hxS
    exact (hV₁_open x hxS).mem_nhds (hyV₁ x hxS)
  -- Ω := ⋃ x ∈ S, Wx x. Open set in X containing fiber(y).
  let Ω : Set X := ⋃ x ∈ (S : Set X), Wx x
  have hΩ_open : IsOpen Ω :=
    isOpen_biUnion (fun x hxS => hWx_open x hxS)
  have hFiber_sub_Ω : f ⁻¹' {y} ⊆ Ω := by
    intro x hx_fib
    have hxS : x ∈ S := hfiber_eq.mpr hx_fib
    exact Set.mem_biUnion (Finset.mem_coe.mpr hxS) (hxWx x hxS)
  have hFiber_eventually : ∀ᶠ y' in 𝓝 y, f ⁻¹' {y'} ⊆ Ω :=
    eventually_fiber_subset_of_compact_T2 hHol.continuous hΩ_open hFiber_sub_Ω
  filter_upwards [hFiber_eventually, hV_int_nhds, hReg_mem] with
    y' hy'_fib hy'_V hy'_regset
  have hy'_reg : isRegularValue hbc y' := hy'_regset
  show localTraceAtRegularValue hbc hHol η y hy y' = _
  rw [dif_pos hy'_reg]
  have hx_ram_of_S : ∀ x ∈ S, hbc.ramificationIndex x = 1 := by
    intro x hxS; exact hy x (hfiber_eq.mp hxS)
  -- The local-inverse bijection φ.
  let φ : ∀ x : X, x ∈ S → X := fun x hxS =>
    hbc.localInverseAt x (hx_ram_of_S x hxS) y'
  have hy'_in_V₁ : ∀ x ∈ S, y' ∈ V₁ x := by
    intro x hxS
    exact (Set.mem_iInter₂.mp hy'_V) x (Finset.mem_coe.mpr hxS)
  have hφ_f : ∀ x : X, ∀ hxS : x ∈ S, f (φ x hxS) = y' := by
    intro x hxS
    have := ((hWx_inv x hxS) (hx_ram_of_S x hxS)).1 y' (hy'_in_V₁ x hxS)
    exact this.1
  have hφ_in_Wx : ∀ x : X, ∀ hxS : x ∈ S, φ x hxS ∈ Wx x := by
    intro x hxS
    have := ((hWx_inv x hxS) (hx_ram_of_S x hxS)).1 y' (hy'_in_V₁ x hxS)
    exact this.2
  have hφ_toFinset : ∀ x : X, ∀ hxS : x ∈ S,
      φ x hxS ∈ (hbc.finite_fiber y').toFinset := by
    intro x hxS
    rw [Set.Finite.mem_toFinset]
    exact hφ_f x hxS
  have hφ_inj : ∀ x₁ : X, ∀ hx₁ : x₁ ∈ S, ∀ x₂ : X, ∀ hx₂ : x₂ ∈ S,
      φ x₁ hx₁ = φ x₂ hx₂ → x₁ = x₂ := by
    intro x₁ hx₁ x₂ hx₂ heq
    by_contra hne
    have hdisj : Disjoint (Wx x₁) (Wx x₂) := hWx_disj x₁ hx₁ x₂ hx₂ hne
    have h1 : φ x₁ hx₁ ∈ Wx x₁ := hφ_in_Wx x₁ hx₁
    have h2 : φ x₂ hx₂ ∈ Wx x₂ := hφ_in_Wx x₂ hx₂
    rw [heq] at h1
    exact (Set.disjoint_iff.mp hdisj) ⟨h1, h2⟩
  have hφ_surj : ∀ x' ∈ (hbc.finite_fiber y').toFinset,
      ∃ (x : X) (hxS : x ∈ S), φ x hxS = x' := by
    intro x' hx'
    have hx'_fib : x' ∈ f ⁻¹' {y'} :=
      (Set.Finite.mem_toFinset _).mp hx'
    have hx'_in_Ω : x' ∈ Ω := hy'_fib hx'_fib
    rcases Set.mem_iUnion₂.mp hx'_in_Ω with ⟨x, hxS_coe, hx'_in_Wx⟩
    have hxS : x ∈ S := Finset.mem_coe.mp hxS_coe
    refine ⟨x, hxS, ?_⟩
    -- φ x hxS = localInverseAt x (hx_ram_of_S x hxS) y'.
    -- We need this = x'.  Since x' ∈ Wx x and f x' = y', and (Wx x, V₁ x) is
    -- a "section" pair with the left-inverse identity on Wx x:
    --   localInverseAt x hx_ram (f x') = x'  (from hWx_inv x hxS hx_ram .2).
    -- And f x' = y', so localInverseAt x hx_ram y' = x', as needed.
    have hfx' : f x' = y' := hx'_fib
    have hLI := ((hWx_inv x hxS) (hx_ram_of_S x hxS)).2 x' hx'_in_Wx
    -- hLI : hbc.localInverseAt x (hx_ram_of_S x hxS) (f x') = x'.
    show hbc.localInverseAt x (hx_ram_of_S x hxS) y' = x'
    rw [← hfx']; exact hLI
  -- Use Finset.sum_nbij' with i, j inverses.
  unfold localTraceAtRegularValue traceAtRegularValue
  -- choose: hφ_surj_choice extracts the unique x ∈ S from a fiber-point x'.
  -- For each x' ∈ fiber(y'), pick (xOfFib x', hxOfFib_mem) such that φ xOfFib x' (...) = x'.
  let xOfFib : ∀ x' : X, x' ∈ (hbc.finite_fiber y').toFinset → X :=
    fun x' hx' => (hφ_surj x' hx').choose
  let xOfFib_mem : ∀ x' : X, ∀ hx' : x' ∈ (hbc.finite_fiber y').toFinset,
      xOfFib x' hx' ∈ S := fun x' hx' => (hφ_surj x' hx').choose_spec.choose
  have xOfFib_eq : ∀ x' : X, ∀ hx' : x' ∈ (hbc.finite_fiber y').toFinset,
      φ (xOfFib x' hx') (xOfFib_mem x' hx') = x' :=
    fun x' hx' => (hφ_surj x' hx').choose_spec.choose_spec
  refine Finset.sum_bij'
    (i := fun (z : { x // x ∈ S }) (_ : z ∈ S.attach) =>
      (⟨φ z.1 z.2, hφ_toFinset z.1 z.2⟩ :
        { x // x ∈ (hbc.finite_fiber y').toFinset }))
    (j := fun (z' : { x // x ∈ (hbc.finite_fiber y').toFinset })
        (_ : z' ∈ (hbc.finite_fiber y').toFinset.attach) =>
      (⟨xOfFib z'.1 z'.2, xOfFib_mem z'.1 z'.2⟩ : { x // x ∈ S }))
    ?_ ?_ ?_ ?_ ?_
  · intro z _; exact Finset.mem_attach _ _
  · intro z' _; exact Finset.mem_attach _ _
  · intro z _
    apply Subtype.ext
    show xOfFib (φ z.1 z.2) (hφ_toFinset z.1 z.2) = z.1
    have hee := xOfFib_eq (φ z.1 z.2) (hφ_toFinset z.1 z.2)
    have hxof_S := xOfFib_mem (φ z.1 z.2) (hφ_toFinset z.1 z.2)
    exact hφ_inj _ hxof_S _ z.2 hee
  · intro z' _
    apply Subtype.ext
    show φ (xOfFib z'.1 z'.2) (xOfFib_mem z'.1 z'.2) = z'.1
    exact xOfFib_eq z'.1 z'.2
  · intro z _
    show localPullbackAt hbc hHol η z.1 (hy z.1 ((Set.Finite.mem_toFinset _).mp z.2)) y' =
      cotangentPushforward f (φ z.1 z.2) (η.toFun (φ z.1 z.2))
    unfold localPullbackAt
    rfl


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

omit [T2Space X] [CompactSpace X] [ConnectedSpace X] [StableChartAt ℂ X]
  [T2Space Y] [CompactSpace Y] [ConnectedSpace Y] [StableChartAt ℂ Y] in
/--
**Auxiliary (analytic continuation across canonical-BCD branch
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
-/
theorem traceForm_extension_at_branch_of_canonical_BCD
    (f : X → Y) (hf : ContMDiff 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) (⊤ : WithTop ℕ∞) f)
    (η : HolomorphicOneForm ℂ X)
    (hbc0 hbc : BranchedCoverData X Y f)
    (hcompat0 : hbc0.RamificationIndexCompatible)
    (hcompat : hbc.RamificationIndexCompatible)
    (y : Y) (hy0_branch : ¬ isRegularValue hbc0 y)
    (hy_reg : isRegularValue hbc y)
    (τ : HolomorphicOneForm ℂ Y)
    (_hτ : ∀ (y' : Y) (hy' : isRegularValue hbc0 y'),
        τ.toFun y' = traceAtRegularValue hbc0 (fun x => η.toFun x) y' hy') :
    τ.toFun y = traceAtRegularValue hbc (fun x => η.toFun x) y hy_reg := by
  -- The hypotheses are contradictory: any branch point of hbc0 must be a branch
  -- point of every compatible BCD (both equal mapAnalyticOrderAt f).
  exfalso
  -- Unfold ¬ isRegularValue to extract a ramified preimage.
  unfold isRegularValue at hy0_branch
  push_neg at hy0_branch
  obtain ⟨x, hx_mem, hx_ram⟩ := hy0_branch
  -- IsHolomorphicAt at x, from contMDiff f.
  have hfx : IsHolomorphicAt f x :=
    (isHolomorphicBasic_of_contMDiff hf).holomorphicAt x
  -- Compatibility on both BCDs identifies ramificationIndex with mapAnalyticOrderAt.
  have h0 : hbc0.ramificationIndex x = mapAnalyticOrderAt f x := hcompat0 x hfx
  have h1 : hbc.ramificationIndex x = mapAnalyticOrderAt f x := hcompat x hfx
  -- hy_reg says hbc.ramificationIndex x = 1.
  have hreg : hbc.ramificationIndex x = 1 := hy_reg x hx_mem
  -- Combine: hbc0.ramificationIndex x = 1 but also ≠ 1. Contradiction.
  exact hx_ram (h0.trans (h1.symm.trans hreg))

/--
**Narrow classical leaf: trace-form holomorphic extension.** For a
nonconstant smooth map `f : X → Y` between compact Riemann surfaces
and a nonzero holomorphic 1-form `η` on `X`, there exists a global
holomorphic 1-form `τ` on `Y` whose pointwise values agree with the
finite local fibre sum `traceAtRegularValue` at every regular value
of every compatible branched-cover datum.

The first three are combined in the private helper
`traceForm_extension_per_BCD` to produce a τ tied to the canonical
BCD; the fourth lifts agreement to *all* BCDs at any regular value
of `hbc0`; the auxiliary lifts to regular values not regular for
`hbc0` via analytic continuation.
-/
theorem traceForm_global_extension
    (f : X → Y) (hf : ContMDiff 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) (⊤ : WithTop ℕ∞) f)
    (η : HolomorphicOneForm ℂ X) (_hη : η ≠ 0)
    (hnonconst : ¬ ∃ y₀, ∀ x, f x = y₀) :
    ∃ τ : HolomorphicOneForm ℂ Y,
      ∀ (hbc : BranchedCoverData X Y f) (_hcompat : hbc.RamificationIndexCompatible)
        (y : Y) (hy : isRegularValue hbc y),
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
  intro hbc hcompat y hy
  by_cases hy0 : isRegularValue hbc0 y
  · rw [hτ0 y hy0]
    exact (traceAtRegularValue_BCD_invariance η hbc0 hbc y hy0 hy).symm
  · exact traceForm_extension_at_branch_of_canonical_BCD f hf η hbc0 hbc
      hcompat0 hcompat y hy0 hy τ hτ0

/--
**Narrow trace construction provider (nonconstant nonzero case).**

The remaining classical content lives entirely inside the strictly
smaller leaf `traceForm_global_extension`.
-/
noncomputable def traceFormsConstructionData_nonconstant_nonzero_provider
    (f : X → Y) (hf : ContMDiff 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) (⊤ : WithTop ℕ∞) f)
    (η : HolomorphicOneForm ℂ X) (hη : η ≠ 0)
    (hnonconst : ¬ ∃ y₀, ∀ x, f x = y₀) :
    TraceFormsConstructionData f hf η :=
  let hext := traceForm_global_extension (f := f) (hf := hf) η hη hnonconst
  { traceForm := hext.choose
    regular_spec := hext.choose_spec
    map_zero_spec := fun hzero => (hη hzero).elim }

/--
**The trace construction provider.** Three-way case split:

* `η = 0` — fully proved via `traceFormsConstructionData_zero`;
* `η ≠ 0` and `f` constant — fully proved via
  `traceFormsConstructionData_constant`;
* `η ≠ 0` and `f` nonconstant — delegates to the strictly narrower
  analytic leaf
  `traceFormsConstructionData_nonconstant_nonzero_provider`.
-/
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

/--
Minimal trace input used by local linearity and regular-value
assemblies.  This separates the specification needed downstream from
the construction of the global bundled trace form.
-/
structure TraceFormsRegularSpec
    (f : X → Y) (hf : ContMDiff 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) (⊤ : WithTop ℕ∞) f) where
  /-- Trace sends the zero form to zero. -/
  map_zero : traceFormsBundled f hf 0 = 0
  /-- At regular values, trace agrees with the finite local fiber sum. -/
  apply_fun_regular :
    ∀ (hbc : BranchedCoverData X Y f) (_hcompat : hbc.RamificationIndexCompatible)
      (η : HolomorphicOneForm ℂ X)
      (y : Y) (hy : isRegularValue hbc y),
      (traceFormsBundled f hf η).toFun y =
        traceAtRegularValue hbc (fun x => η.toFun x) y hy

/--
Private helper: in the constant-map case, the construction-data
provider for any input form `η` reduces to
`traceFormsConstructionData_constant` (or
`traceFormsConstructionData_zero` if `η = 0`); in either case, the
resulting `traceForm` is the zero form on `Y`.
-/
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

/--
The linear trace map on holomorphic 1-forms.

Linearity is proved by the standard "dense agreement at regular values"
trick: in the constant-map case both sides are zero
(`traceFormsBundled_eq_zero_of_constant`); in the nonconstant case, the
constructed trace forms agree with `traceAtRegularValue` on the dense
regular locus of the canonical branched-cover datum, and
`traceAtRegularValue` is already linear (via `traceAtRegularValue_add`
and `traceAtRegularValue_smul`). The identity principle
(`holomorphicOneForm_ext_on (regularLocus_dense hbc)`) then promotes
agreement on the regular locus to agreement everywhere.
-/
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
      have hcompat :=
        JacobianChallenge.Blueprint.branchedCoverData_of_nonconstant_holomorphic_compatible
          hHol hw hconst
      apply holomorphicOneForm_ext_on (regularLocus_dense hbc)
      intro y hy
      have hη_reg := (traceFormsConstructionData_provider f hf η).regular_spec hbc hcompat y hy
      have hζ_reg := (traceFormsConstructionData_provider f hf ζ).regular_spec hbc hcompat y hy
      have hηζ_reg := (traceFormsConstructionData_provider f hf (η + ζ)).regular_spec hbc hcompat y hy
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
      have hcompat :=
        JacobianChallenge.Blueprint.branchedCoverData_of_nonconstant_holomorphic_compatible
          hHol hw hconst
      show traceFormsBundled f hf (k • η) = k • traceFormsBundled f hf η
      apply holomorphicOneForm_ext_on (regularLocus_dense hbc)
      intro y hy
      have hη_reg := (traceFormsConstructionData_provider f hf η).regular_spec hbc hcompat y hy
      have hkη_reg := (traceFormsConstructionData_provider f hf (k • η)).regular_spec hbc hcompat y hy
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
