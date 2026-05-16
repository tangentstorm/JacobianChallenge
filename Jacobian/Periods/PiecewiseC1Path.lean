import Jacobian.TraceDegree.PiecewiseC1Def
import Jacobian.Periods.PathLift
import Jacobian.Periods.CurveIntegralSubpath
import Jacobian.Periods.ChartLiftApply

/-!
# Bundled piecewise-C¹ paths

This file defines `PiecewiseC1Path a b X`, a bundled structure carrying
both a continuous path `Path a b` and a witness `IsPiecewiseC1Path γ`
that the path is piecewise-C¹ in chart coordinates with some uniform
derivative bound.

This is Phase 2 of the multi-phase decomposition of the literally-false
`instPiecewiseC1PathRegularity` (see Phase 1 in
`Jacobian/TraceDegree/PiecewiseC1Instance.lean`). The structure provides
the data-carrying analogue that the flagship descent
(`closedForm_pathIntegral_primitive_exists`) needs in order to discharge
`path_contDiffOn_obligation` for the specific paths it constructs (Phase
4, planned for a follow-up session).

Initial API: `cast` (Prop-cast invariance), `refl` (constant path,
trivially piecewise-C¹), `coe` to underlying `Path`. The operators
`.symm` and `.trans` are deferred to a follow-up — they require pulling
in `ContMDiff.piecewise_Iic` from `Mathlib/Geometry/Manifold/Riemannian/PathELength.lean`.
-/

namespace JacobianChallenge.TraceDegree

open Path JacobianChallenge.Periods

variable {X : Type*} [TopologicalSpace X] [ChartedSpace ℂ X]

/-- A continuous path bundled with a piecewise-C¹-in-chart-coordinates
witness. The witness carries the existential `∃ K, ChartLiftPiecewiseC1 γ K`
that future consumers (path-integral additivity, FTC, etc.) need to
discharge their regularity hypotheses. -/
structure PiecewiseC1Path (a b : X) where
  /-- The underlying continuous path. -/
  toPath : Path a b
  /-- Witness that the path is piecewise-C¹ in chart coordinates. -/
  isPiecewiseC1 : IsPiecewiseC1Path toPath

namespace PiecewiseC1Path

/-- Coerce a `PiecewiseC1Path` to its underlying `Path`. -/
instance instCoePath {a b : X} : Coe (PiecewiseC1Path a b) (Path a b) where
  coe γ := γ.toPath

/-- Cast the endpoints of a piecewise-C¹ path through proposition
equalities. The witness is preserved because `ChartLiftPiecewiseC1`
depends only on the path's underlying continuous-map data, which
`Path.cast` leaves unchanged. -/
def cast {a b : X} (γ : PiecewiseC1Path a b) {a' b' : X}
    (ha : a' = a) (hb : b' = b) : PiecewiseC1Path a' b' where
  toPath := γ.toPath.cast ha hb
  isPiecewiseC1 := by
    subst ha
    subst hb
    -- After substituting, γ.toPath.cast rfl rfl = γ.toPath, so the witness
    -- is the same.
    exact γ.isPiecewiseC1

end PiecewiseC1Path

/-- The constant path at `a` is piecewise-C¹: the chart-lifted subpath
(when its range lies in any chart's source) is itself constant in chart
coordinates at `c a`, hence C¹ with zero derivative. The uniform bound
`K = 0` witnesses `ChartLiftPiecewiseC1 (Path.refl a) 0`. -/
theorem isPiecewiseC1Path_refl (a : X) : IsPiecewiseC1Path (Path.refl a) := by
  refine ⟨0, ?_⟩
  intro n hn pickX i h
  -- The chartLift of a constant path at `a` is the constant path at `c a`.
  -- Its `.extend` is `ContinuousMap.const ℝ (c a)`, which coerces to the
  -- constant function and is C¹ with zero derivative on `Icc 0 1`.
  have h_const : (chartLift (chartAt ℂ (pickX i))
      ((Path.refl a).subpath
        (divFinIcc n hn i.val (le_of_lt i.isLt))
        (divFinIcc n hn (i.val + 1) i.isLt)) h).extend =
      ContinuousMap.const ℝ ((chartAt ℂ (pickX i)) a) := rfl
  refine ⟨?_, ?_⟩
  · -- ContDiffOn of the constant function
    rw [h_const]
    exact contDiffOn_const
  · intro t _ht
    -- Derivative bound: derivative of a constant is 0
    rw [h_const]
    show ‖derivWithin
        (fun s => ContinuousMap.const ℝ ((chartAt ℂ (pickX i)) a) s)
        (Set.Icc (0 : ℝ) 1) t‖₊ ≤ 0
    have hderiv : derivWithin
        (fun _ : ℝ => (chartAt ℂ (pickX i)) a)
        (Set.Icc (0 : ℝ) 1) t = 0 := by
      simpa using derivWithin_const (s := Set.Icc (0 : ℝ) 1) (c := (chartAt ℂ (pickX i)) a) t
    show ‖derivWithin (fun _ : ℝ => (chartAt ℂ (pickX i)) a)
        (Set.Icc (0 : ℝ) 1) t‖₊ ≤ 0
    rw [hderiv]
    simp

namespace PiecewiseC1Path

/-- The constant piecewise-C¹ path at `a`. -/
def refl (a : X) : PiecewiseC1Path a a where
  toPath := Path.refl a
  isPiecewiseC1 := isPiecewiseC1Path_refl a

@[simp] theorem coe_refl (a : X) : ((refl a : PiecewiseC1Path a a) : Path a a) = Path.refl a := rfl

@[simp] theorem coe_cast {a b : X} (γ : PiecewiseC1Path a b) {a' b' : X}
    (ha : a' = a) (hb : b' = b) :
    ((γ.cast ha hb : PiecewiseC1Path a' b') : Path a' b') = γ.toPath.cast ha hb := rfl

end PiecewiseC1Path

/-- **Focused residual obligation** (split out from
`connected_smooth_manifold_isPiecewiseC1Joined`).

Given two points on a compact connected smooth complex 1-manifold and
*any* continuous `Path x y` (e.g. one selected via path-connectedness),
this obligation asserts that *some* — not necessarily the given one —
piecewise-C¹ path exists between the same endpoints.

The split exists to isolate the substantive smoothness construction
(chart-chain + linear interpolation + uniform-`K` bound) from the
purely topological step of producing *a* continuous path. The
topological step is discharged in
`connected_smooth_manifold_isPiecewiseC1Joined` below using
`PathConnectedSpace.somePath` (which `ConnectedSpace` +
`LocPathConnectedSpace`, both available for a complex-1 manifold,
provide). What remains is the smoothness refinement.

Math content of the residual: build a finite chart chain along any
continuous path (`IsCompact.elim_finite_subcover` on `range γ`),
straight-line interpolate inside each chart (`(chartAt ℂ p).symm ∘
ContinuousAffineMap.lineMap`), and concatenate via `Path.trans`. The
uniform `K` bound exists because chart-transition derivatives are
bounded on the compact image of the path. Discharge route is laid out
in Mathlib's `Riemannian/PathELength.lean:215-243`
(`riemannianEDist_le_pathELength`, especially the
`ContinuousAffineMap.lineMap` reparametrization) and
`Riemannian/PathELength.lean:340-355`
(`riemannianEDist_triangle`, using `ContMDiff.piecewise_Iic` for
concatenation). -/
theorem piecewiseC1Path_smoothing_obligation
    (X : Type) [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X]
    (x y : X) (_γ₀ : Path x y) :
    ∃ γ : Path x y, IsPiecewiseC1Path γ := by
  -- Focused frontier obligation — Phase 3 chart-chain construction.
  sorry

/-- **Phase 3 existence theorem.** Every two points on a compact
connected smooth complex 1-manifold are joined by a piecewise-C¹ path.

**Proof structure.** Split into two steps:

1. *Topological step* (discharged here): the model space `ℂ` is locally
   path-connected (normed ⇒ locally convex ⇒ locally path-connected).
   `ChartedSpace ℂ X` inherits local path-connectedness from `ℂ` via
   `ChartedSpace.locPathConnectedSpace`. Combined with
   `[ConnectedSpace X]`, `pathConnectedSpace_iff_connectedSpace`
   promotes this to `PathConnectedSpace X`, supplying a continuous
   `Path x y` via `Joined.somePath`.

2. *Smoothness step* (deferred to
   `piecewiseC1Path_smoothing_obligation`): refine to a piecewise-C¹
   path with the same endpoints via chart-chain + straight-line
   interpolation. This is the focused residual obligation. -/
theorem connected_smooth_manifold_isPiecewiseC1Joined
    (X : Type) [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X]
    (x y : X) :
    ∃ γ : Path x y, IsPiecewiseC1Path γ := by
  have hLoc : LocPathConnectedSpace X :=
    ChartedSpace.locPathConnectedSpace (H := ℂ) (M := X)
  have hPath : PathConnectedSpace X := pathConnectedSpace_iff_connectedSpace.mpr ‹_›
  let γ₀ : Path x y := (PathConnectedSpace.joined x y).somePath
  exact piecewiseC1Path_smoothing_obligation X x y γ₀

/-- Bundled existence: the same theorem in `PiecewiseC1Path` form. -/
theorem exists_piecewiseC1Path
    (X : Type) [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X]
    (x y : X) : Nonempty (PiecewiseC1Path x y) := by
  obtain ⟨γ, hγ⟩ := connected_smooth_manifold_isPiecewiseC1Joined X x y
  exact ⟨⟨γ, hγ⟩⟩

/-- **Phase 4 helper.** A chosen piecewise-C¹ path from a basepoint
to a target on a compact connected complex 1-manifold. Replacement
for `manifoldPathFromBasepoint` in the flagship descent: the chosen
path now carries its smoothness witness, so downstream
`path_contDiffOn_obligation` instances become provable. -/
noncomputable def manifoldPiecewiseC1PathFromBasepoint
    {X : Type} [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X]
    (x₀ x : X) : PiecewiseC1Path x₀ x :=
  Classical.choice (exists_piecewiseC1Path X x₀ x)

/-- **Conclusion-form predicate** (the cleanest alternative to
`IsPiecewiseC1Path` for the flagship descent).

`IsChartContDiffPath γ` asserts that the chart-pullback `(chartAt ℂ p) ∘ γ.extend`
is `ContDiffOn ℝ 1` on `γ.extend⁻¹' (chartAt ℂ p).source ∩ Icc 0 1` for
every `p : X`. This is precisely the conclusion of
`path_contDiffOn_obligation`, packaged as a per-path predicate.

By design, the bridge `path_contDiffOn_of_isChartContDiffPath` is
trivial (`hγ p`). The substantive work of producing such a witness is
pushed to Phase 3's existence theorem, where the chart-chain + linear
interpolation construction naturally satisfies this property. -/
abbrev IsChartContDiffPath {X : Type*} [TopologicalSpace X] [ChartedSpace ℂ X]
    {a b : X} (γ : Path a b) : Prop :=
  ∀ p : X, ContDiffOn ℝ 1 ((chartAt ℂ p) ∘ γ.extend)
    (γ.extend ⁻¹' (chartAt ℂ p).source ∩ Set.Icc 0 1)

/-- **Trivial bridge** (per-call discharge of `path_contDiffOn_obligation`).

For a path γ satisfying `IsChartContDiffPath γ`, the chart-pullback is
`C¹` on the preimage by definition. The flagship descent (Phase 4)
uses `manifoldPiecewiseC1PathFromBasepoint`, which produces a path
satisfying this predicate via Phase 3's existence theorem. -/
@[simp] theorem path_contDiffOn_of_isChartContDiffPath
    {X : Type*} [TopologicalSpace X] [ChartedSpace ℂ X]
    {a b : X} {γ : Path a b} (hγ : IsChartContDiffPath γ) (p : X) :
    ContDiffOn ℝ 1 ((chartAt ℂ p) ∘ γ.extend)
      (γ.extend ⁻¹' (chartAt ℂ p).source ∩ Set.Icc 0 1) :=
  hγ p

/-- **Preservation under subpath**: if γ is chart-pulled-back C¹,
so is `γ.subpath t₀ t₁` for any endpoints `t₀, t₁ ∈ unitInterval`.

The subpath's `.extend` agrees with `γ.extend ∘ (affine map from
Icc 0 1 to Icc (min t₀ t₁) (max t₀ t₁))` (via
`subpath_extend_eq_extend_affine`). The affine map is C^∞, so
composition preserves C¹. -/
theorem IsChartContDiffPath.subpath
    {X : Type*} [TopologicalSpace X] [ChartedSpace ℂ X]
    {a b : X} {γ : Path a b} (hγ : IsChartContDiffPath γ)
    (t₀ t₁ : unitInterval) :
    IsChartContDiffPath (γ.subpath t₀ t₁) := by
  intro p
  -- Affine map `g : ℝ → ℝ`, `g s = (1-s) · t₀ + s · t₁`. C^∞.
  set g : ℝ → ℝ := fun s => (1 - s) * (t₀ : ℝ) + s * (t₁ : ℝ) with hg
  have hg_contDiff : ContDiff ℝ 1 g := by
    have h1 : ContDiff ℝ 1 (fun s : ℝ => (1 - s) * (t₀ : ℝ)) :=
      (contDiff_const.sub contDiff_id).mul contDiff_const
    have h2 : ContDiff ℝ 1 (fun s : ℝ => s * (t₁ : ℝ)) :=
      contDiff_id.mul contDiff_const
    exact h1.add h2
  -- Need: g maps Icc 0 1 to Icc 0 1 (so the affine reparam stays in unitInterval).
  have hg_mapsTo_Icc' : ∀ s ∈ Set.Icc (0 : ℝ) 1, g s ∈ Set.Icc (0 : ℝ) 1 := by
    intro s ⟨hs0, hs1⟩
    obtain ⟨ht0_0, ht0_1⟩ := t₀.2
    obtain ⟨ht1_0, ht1_1⟩ := t₁.2
    refine ⟨?_, ?_⟩
    · apply add_nonneg
      · exact mul_nonneg (by linarith) ht0_0
      · exact mul_nonneg hs0 ht1_0
    · have h1 : (1 - s) * (t₀ : ℝ) ≤ (1 - s) := by nlinarith [hs1]
      have h2 : s * (t₁ : ℝ) ≤ s := by nlinarith
      linarith
  -- `(γ.subpath t₀ t₁).extend s = γ.extend (g s)` for `s ∈ Icc 0 1`,
  -- proved directly from Path.subpath's definition (no normed structure needed).
  have hext : ∀ s ∈ Set.Icc (0 : ℝ) 1,
      (γ.subpath t₀ t₁).extend s = γ.extend (g s) := by
    intro s hs
    have hs' : s ∈ unitInterval := hs
    have hgs' : g s ∈ unitInterval := hg_mapsTo_Icc' s hs
    rw [Path.extend_apply _ hs', Path.extend_apply _ hgs']
    -- (γ.subpath t₀ t₁) ⟨s, hs'⟩ = γ (subpathAux t₀ t₁ ⟨s, hs'⟩) = γ ⟨(1-s)·t₀ + s·t₁, _⟩
    rfl
  -- We need ContDiffOn 1 ((chart) ∘ (γ.subpath t₀ t₁).extend) on
  -- the preimage of source intersected with Icc 0 1.
  -- Strategy: use ContDiffOn.congr to substitute (γ.subpath t₀ t₁).extend
  -- with γ.extend ∘ g on Icc 0 1 (where they agree).
  have hcomp_eq_on : Set.EqOn ((chartAt ℂ p) ∘ (γ.subpath t₀ t₁).extend)
      ((chartAt ℂ p) ∘ γ.extend ∘ g) (Set.Icc 0 1) := by
    intro s hs
    show (chartAt ℂ p) ((γ.subpath t₀ t₁).extend s) = (chartAt ℂ p) (γ.extend (g s))
    rw [hext s hs]
  -- The composition with g is C¹ on the appropriate preimage.
  have hg_mapsTo : Set.MapsTo g (Set.Icc 0 1) Set.univ := fun _ _ => Set.mem_univ _
  have hg_contDiffOn : ContDiffOn ℝ 1 g (Set.Icc 0 1) := hg_contDiff.contDiffOn
  -- Define f := (chartAt ℂ p) ∘ γ.extend, with ContDiffOn on preimage.
  -- Compose with g; the preimage adjusts accordingly.
  have hg_mapsTo_Icc : Set.MapsTo g (Set.Icc 0 1) (Set.Icc 0 1) := hg_mapsTo_Icc'
  -- Preimage rewriting via the EqOn identity.
  have hpre_eq : (γ.subpath t₀ t₁).extend ⁻¹' (chartAt ℂ p).source ∩ Set.Icc 0 1 =
      g ⁻¹' (γ.extend ⁻¹' (chartAt ℂ p).source) ∩ Set.Icc 0 1 := by
    ext s
    simp only [Set.mem_inter_iff, Set.mem_preimage]
    constructor
    · rintro ⟨h1, h2⟩
      refine ⟨?_, h2⟩
      rw [← hext s h2]; exact h1
    · rintro ⟨h1, h2⟩
      refine ⟨?_, h2⟩
      rw [hext s h2]; exact h1
  -- Construct the composition's ContDiffOn directly.
  -- Domain for composition: (g⁻¹' preimage_γ) ∩ Icc 0 1.
  have hgmaps_comp : Set.MapsTo g (g ⁻¹' (γ.extend ⁻¹' (chartAt ℂ p).source) ∩ Set.Icc 0 1)
      (γ.extend ⁻¹' (chartAt ℂ p).source ∩ Set.Icc 0 1) := by
    intro s ⟨hg_pre, hg_Icc⟩
    refine ⟨hg_pre, hg_mapsTo_Icc hg_Icc⟩
  -- Compose: ContDiffOn ((chart) ∘ γ.extend ∘ g) on the composed-preimage.
  have hcomp_contDiffOn : ContDiffOn ℝ 1 ((chartAt ℂ p) ∘ γ.extend ∘ g)
      (g ⁻¹' (γ.extend ⁻¹' (chartAt ℂ p).source) ∩ Set.Icc 0 1) :=
    (hγ p).comp (hg_contDiffOn.mono Set.inter_subset_right) hgmaps_comp
  -- Restate via the EqOn substitution and preimage equality.
  rw [hpre_eq]
  -- Now goal: ContDiffOn 1 ((chart) ∘ subpath.extend) (g⁻¹' preimage_γ ∩ Icc 0 1).
  -- Use EqOn to swap subpath.extend for γ.extend ∘ g (on Icc 0 1, which contains the domain).
  refine hcomp_contDiffOn.congr ?_
  -- EqOn: on (g⁻¹' preimage_γ ∩ Icc 0 1), ((chart) ∘ γ.extend ∘ g) = ((chart) ∘ subpath.extend).
  intro s hs
  obtain ⟨_, hs_Icc⟩ := hs
  exact hcomp_eq_on hs_Icc

/-- **Preservation under `Path.cast`**: casting endpoints through
Prop-equalities leaves `extend` unchanged, hence preserves
`IsChartContDiffPath`. -/
theorem IsChartContDiffPath.cast
    {X : Type*} [TopologicalSpace X] [ChartedSpace ℂ X]
    {a b : X} {γ : Path a b} (hγ : IsChartContDiffPath γ)
    {a' b' : X} (ha : a' = a) (hb : b' = b) :
    IsChartContDiffPath (γ.cast ha hb) := by
  intro p
  -- `Path.extend_cast`: `(γ.cast ha hb).extend = γ.extend`.
  show ContDiffOn ℝ 1 ((chartAt ℂ p) ∘ (γ.cast ha hb).extend)
      ((γ.cast ha hb).extend ⁻¹' (chartAt ℂ p).source ∩ Set.Icc 0 1)
  rw [Path.extend_cast]
  exact hγ p

/-- **`IsChartContDiffPath` holds unconditionally for constant paths**:
the constant path `Path.refl a` has extend `fun _ => a` (a constant
function), whose chart pullback is also constant — hence trivially C¹.
The preimage is either empty (if `a ∉ chart.source`) or `Icc 0 1`
(if `a ∈ chart.source`); in both cases `ContDiffOn 1` holds for a
constant function. -/
theorem IsChartContDiffPath.refl
    {X : Type*} [TopologicalSpace X] [ChartedSpace ℂ X]
    (a : X) : IsChartContDiffPath (Path.refl a) := by
  intro p
  -- The chart pullback of a constant path is a constant function.
  have hconst : (chartAt ℂ p) ∘ (Path.refl a).extend = fun _ : ℝ => (chartAt ℂ p) a := by
    funext t
    show (chartAt ℂ p) ((Path.refl a).extend t) = (chartAt ℂ p) a
    rw [Path.refl_extend]
    rfl
  rw [hconst]
  exact contDiffOn_const

/-- **Preservation under path reversal**: `IsChartContDiffPath` is
preserved by `.symm`. The reversed path `γ.symm` has extend
`γ.extend (1 - ·)` on `Icc 0 1` (by `Path.extend_symm_apply`); composing
the chart pullback with the smooth affine map `1 - ·` preserves C¹
regularity on the corresponding preimage.

This is the path-reversal preservation lemma used by Stage III's
`lineIntegral_symm_of_witnesses`. -/
theorem IsChartContDiffPath.symm
    {X : Type*} [TopologicalSpace X] [ChartedSpace ℂ X]
    {a b : X} {γ : Path a b} (hγ : IsChartContDiffPath γ) :
    IsChartContDiffPath γ.symm := by
  intro p
  -- The function `1 - ·` is C^∞ (and in particular C¹).
  have hflip_contDiff : ContDiff ℝ 1 (fun t : ℝ => 1 - t) := by
    exact contDiff_const.sub contDiff_id
  -- The function `1 - ·` maps `Icc 0 1` to `Icc 0 1` (involution).
  have hflip_mapsTo : Set.MapsTo (fun t : ℝ => 1 - t) (Set.Icc 0 1) (Set.Icc 0 1) := by
    intro t ht
    obtain ⟨h0, h1⟩ := ht
    refine ⟨?_, ?_⟩ <;> linarith
  -- `γ.symm.extend = γ.extend ∘ (1 - ·)` (Mathlib `Path.extend_symm`).
  have hextend_symm : γ.symm.extend = (fun t => γ.extend (1 - t)) := by
    funext t
    exact γ.extend_symm_apply t
  -- Substitute the symm-extend equation in the goal.
  have hcomp_eq : (chartAt ℂ p) ∘ γ.symm.extend =
      ((chartAt ℂ p) ∘ γ.extend) ∘ (fun t => 1 - t) := by
    rw [hextend_symm]
    rfl
  rw [hcomp_eq]
  -- Preimage rewriting: `γ.symm.extend ⁻¹' source = (1 - ·) ⁻¹' (γ.extend ⁻¹' source)`.
  have hpre_eq : γ.symm.extend ⁻¹' (chartAt ℂ p).source =
      (fun t : ℝ => 1 - t) ⁻¹' (γ.extend ⁻¹' (chartAt ℂ p).source) := by
    ext t
    simp only [Set.mem_preimage]
    constructor
    · intro h
      rw [hextend_symm] at h
      exact h
    · intro h
      rw [hextend_symm]
      exact h
  rw [hpre_eq]
  -- The intersection with Icc 0 1 also pulls back through `1 - ·` (which preserves Icc 0 1).
  have hint_eq :
      (fun t : ℝ => 1 - t) ⁻¹' (γ.extend ⁻¹' (chartAt ℂ p).source) ∩ Set.Icc 0 1 =
        (fun t : ℝ => 1 - t) ⁻¹'
          (γ.extend ⁻¹' (chartAt ℂ p).source ∩ Set.Icc 0 1) := by
    ext t
    constructor
    · intro ⟨h1, h2⟩
      refine ⟨h1, hflip_mapsTo h2⟩
    · intro ⟨h1, h2⟩
      refine ⟨h1, ?_⟩
      obtain ⟨ha, hb⟩ := h2
      refine ⟨?_, ?_⟩ <;> linarith
  rw [hint_eq]
  -- Compose: `ContDiffOn 1 f S → ContDiff 1 g → ContDiffOn 1 (f ∘ g) (g ⁻¹' S)` (with mapsTo).
  -- We use `ContDiffOn.comp` with `g = 1 - ·` (ContDiff) restricted to its preimage.
  exact (hγ p).comp hflip_contDiff.contDiffOn (Set.mapsTo_preimage _ _)

/-- **`Path.trans` preservation under matching constant joins.**

If `γ : Path a b` is constant at `b` on a non-trivial tail interval
`[1-εL, 1]` and `δ : Path b c` is constant at `b` on a non-trivial head
interval `[0, εR]`, and both are `IsChartContDiffPath`, then so is their
concatenation `γ.trans δ`.

Reason: the join (at `t = 1/2` in the trans path) sits *inside* a
non-trivial open neighbourhood `((1-εL)/2, (1+εR)/2)` on which the trans
path is **constant** at `b`. Outside that neighbourhood, the trans path
reduces to `γ ∘ (2·)` on the left half and `δ ∘ (2· - 1)` on the right
half — both `IsChartContDiffPath` by composition with the smooth scaling.
Gluing via `contDiffOn_of_locally_contDiffOn` produces the chartwise
`ContDiffOn ℝ 1` on `[0, 1]`.

This is the cornerstone preservation lemma that turns "two `IsChartContDiffPath`
paths with matching constant ends" into a single `IsChartContDiffPath`
trans — the bypass for the structurally-false universal `Path.trans`
preservation (which fails when chart-derivatives at the join differ). -/
theorem IsChartContDiffPath.trans_of_constant_join
    {X : Type*} [TopologicalSpace X] [ChartedSpace ℂ X]
    {a b c : X} {γ : Path a b} {δ : Path b c}
    (hγ : IsChartContDiffPath γ) (hδ : IsChartContDiffPath δ)
    {εL : ℝ} (hεL_pos : 0 < εL) (hεL_le : εL ≤ 1)
    (hγ_tail : ∀ t ∈ Set.Icc (1 - εL) (1 : ℝ), γ.extend t = b)
    {εR : ℝ} (hεR_pos : 0 < εR) (hεR_le : εR ≤ 1)
    (hδ_head : ∀ t ∈ Set.Icc (0 : ℝ) εR, δ.extend t = b) :
    IsChartContDiffPath (γ.trans δ) := by
  intro p
  set f : ℝ → ℂ := (chartAt ℂ p) ∘ (γ.trans δ).extend with hf_def
  set S : Set ℝ := (γ.trans δ).extend ⁻¹' (chartAt ℂ p).source ∩ Set.Icc 0 1 with hS_def
  -- Key formula for `Path.trans`'s `.extend` on `unitInterval`:
  -- `(γ.trans δ).extend t = if t ≤ 1/2 then γ.extend (2*t) else δ.extend (2*t - 1)`.
  -- This follows from `Path.trans`'s definition (`toFun := (fun t' => if t' ≤ 1/2 …) ∘ (↑)`)
  -- composed with `Path.extend_extends'`.
  have h_trans_extend_form : ∀ t ∈ unitInterval,
      (γ.trans δ).extend t =
        if t ≤ 1/2 then γ.extend (2*t) else δ.extend (2*t - 1) := by
    intro t ht_unit
    rw [(γ.trans δ).extend_extends' ⟨t, ht_unit⟩]
    show (Path.trans γ δ).toFun ⟨t, ht_unit⟩ = _
    simp [Path.trans]
  -- Constants for the constant-join window: tL := (1 - εL)/2, tR := (1 + εR)/2.
  set tL : ℝ := (1 - εL) / 2 with htL_def
  set tR : ℝ := (1 + εR) / 2 with htR_def
  have htL_lt_half : tL < 1/2 := by rw [htL_def]; linarith
  have hhalf_lt_tR : 1/2 < tR := by rw [htR_def]; linarith
  have htL_lt_tR : tL < tR := htL_lt_half.trans hhalf_lt_tR
  -- The trans path's extend is constant `b` on the open interval (tL, tR).
  have h_trans_const : ∀ t ∈ Set.Ioo tL tR, (γ.trans δ).extend t = b := by
    intro t ⟨ht_gt, ht_lt⟩
    have htL_ge_zero : 0 ≤ tL := by rw [htL_def]; linarith
    have htR_le_one : tR ≤ 1 := by rw [htR_def]; linarith
    have ht_pos : 0 < t := lt_of_le_of_lt htL_ge_zero ht_gt
    have ht_le_one : t ≤ 1 := le_of_lt (ht_lt.trans_le htR_le_one)
    have ht_unit : t ∈ unitInterval := ⟨le_of_lt ht_pos, ht_le_one⟩
    rw [h_trans_extend_form t ht_unit]
    by_cases htle : t ≤ 1/2
    · rw [if_pos htle]
      have h2t_in : 2*t ∈ Set.Icc (1 - εL) (1 : ℝ) := by
        constructor
        · have : (1 - εL) / 2 < t := ht_gt
          linarith
        · linarith
      exact hγ_tail (2*t) h2t_in
    · push_neg at htle
      rw [if_neg (not_le.mpr htle)]
      have h2t1_in : (2*t - 1) ∈ Set.Icc (0 : ℝ) εR := by
        constructor
        · linarith
        · have : t < (1 + εR) / 2 := ht_lt
          linarith
      exact hδ_head (2*t - 1) h2t1_in
  -- Apply contDiffOn_of_locally_contDiffOn: for each t₀ ∈ S, exhibit a
  -- ℝ-open neighbourhood u with ContDiffOn 1 f on S ∩ u.
  -- THREE-WAY case split based on whether t₀ is below 1/2, above 1/2, or in the
  -- open constant window Ioo tL tR (which strictly contains 1/2).
  apply contDiffOn_of_locally_contDiffOn
  intro t₀ ht₀
  by_cases h_mid : t₀ ∈ Set.Ioo tL tR
  · -- Constant window: f is constant chart(b) on S ∩ Ioo tL tR.
    refine ⟨Set.Ioo tL tR, isOpen_Ioo, h_mid, ?_⟩
    refine (contDiffOn_const (c := (chartAt ℂ p) b) (n := (1 : WithTop ℕ∞))
              (s := S ∩ Set.Ioo tL tR)).congr ?_
    intro t ⟨_, ht_in_mid⟩
    show f t = (chartAt ℂ p) b
    show (chartAt ℂ p) ((γ.trans δ).extend t) = (chartAt ℂ p) b
    rw [h_trans_const t ht_in_mid]
  · -- Outside the constant window: either t₀ < 1/2 (use γ-side) or t₀ > 1/2 (use δ-side).
    -- Note: 1/2 ∈ Ioo tL tR, so since t₀ ∉ Ioo tL tR, t₀ ≠ 1/2.
    rcases lt_or_gt_of_ne (show t₀ ≠ 1/2 from fun heq =>
      h_mid (heq ▸ ⟨htL_lt_half, hhalf_lt_tR⟩)) with h_lt | h_gt
    · -- t₀ < 1/2. Take u := Iio (1/2). On S ∩ Iio (1/2), f equals (chart) ∘ γ.extend ∘ (2·).
      refine ⟨Set.Iio (1/2 : ℝ), isOpen_Iio, h_lt, ?_⟩
      have h_scale : ContDiff ℝ (1 : WithTop ℕ∞) (fun t : ℝ => 2 * t) :=
        contDiff_const.mul contDiff_id
      have h_f_eq : Set.EqOn f ((chartAt ℂ p) ∘ γ.extend ∘ (fun t : ℝ => 2 * t))
          (S ∩ Set.Iio (1/2 : ℝ)) := by
        intro t ⟨ht_S, ht_lt⟩
        obtain ⟨_, ht_Icc⟩ := ht_S
        have ht_unit : t ∈ unitInterval := ht_Icc
        show (chartAt ℂ p) ((γ.trans δ).extend t) =
          ((chartAt ℂ p) ∘ γ.extend ∘ (fun s : ℝ => 2 * s)) t
        simp only [Function.comp_apply]
        rw [h_trans_extend_form t ht_unit, if_pos (le_of_lt ht_lt)]
      have h_maps : Set.MapsTo (fun t : ℝ => 2 * t) (S ∩ Set.Iio (1/2 : ℝ))
          (γ.extend ⁻¹' (chartAt ℂ p).source ∩ Set.Icc 0 1) := by
        intro t ⟨⟨ht_pre, ht_Icc⟩, ht_lt⟩
        have ht_unit : t ∈ unitInterval := ht_Icc
        have h0 : (0 : ℝ) ≤ t := ht_unit.1
        have h_lt_half : t < 1/2 := ht_lt
        refine ⟨?_, ?_, ?_⟩
        · show γ.extend (2 * t) ∈ (chartAt ℂ p).source
          have h_eq : γ.extend (2 * t) = (γ.trans δ).extend t := by
            rw [h_trans_extend_form t ht_unit, if_pos (le_of_lt h_lt_half)]
          rw [h_eq]; exact ht_pre
        · linarith
        · linarith
      have h_outer : ContDiffOn ℝ 1 ((chartAt ℂ p) ∘ γ.extend)
          (γ.extend ⁻¹' (chartAt ℂ p).source ∩ Set.Icc 0 1) := hγ p
      have h_inner : ContDiffOn ℝ 1 (fun t : ℝ => 2 * t) (S ∩ Set.Iio (1/2 : ℝ)) :=
        h_scale.contDiffOn
      exact (h_outer.comp h_inner h_maps).congr (fun t ht => h_f_eq ht)
    · -- t₀ > 1/2. Take u := Ioi (1/2). On S ∩ Ioi (1/2), f equals (chart) ∘ δ.extend ∘ (2·-1).
      refine ⟨Set.Ioi (1/2 : ℝ), isOpen_Ioi, h_gt, ?_⟩
      have h_shift : ContDiff ℝ (1 : WithTop ℕ∞) (fun t : ℝ => 2 * t - 1) :=
        (contDiff_const.mul contDiff_id).sub contDiff_const
      have h_f_eq : Set.EqOn f ((chartAt ℂ p) ∘ δ.extend ∘ (fun t : ℝ => 2 * t - 1))
          (S ∩ Set.Ioi (1/2 : ℝ)) := by
        intro t ⟨ht_S, ht_gt'⟩
        obtain ⟨_, ht_Icc⟩ := ht_S
        have ht_unit : t ∈ unitInterval := ht_Icc
        show (chartAt ℂ p) ((γ.trans δ).extend t) =
          ((chartAt ℂ p) ∘ δ.extend ∘ (fun s : ℝ => 2 * s - 1)) t
        simp only [Function.comp_apply]
        rw [h_trans_extend_form t ht_unit, if_neg (not_le.mpr ht_gt')]
      have h_maps : Set.MapsTo (fun t : ℝ => 2 * t - 1) (S ∩ Set.Ioi (1/2 : ℝ))
          (δ.extend ⁻¹' (chartAt ℂ p).source ∩ Set.Icc 0 1) := by
        intro t ⟨⟨ht_pre, ht_Icc⟩, ht_gt'⟩
        have ht_unit : t ∈ unitInterval := ht_Icc
        have h1 : t ≤ (1 : ℝ) := ht_unit.2
        have h_gt_half : (1/2 : ℝ) < t := ht_gt'
        refine ⟨?_, ?_, ?_⟩
        · show δ.extend (2 * t - 1) ∈ (chartAt ℂ p).source
          have h_eq : δ.extend (2 * t - 1) = (γ.trans δ).extend t := by
            rw [h_trans_extend_form t ht_unit, if_neg (not_le.mpr h_gt_half)]
          rw [h_eq]; exact ht_pre
        · linarith
        · linarith
      have h_outer : ContDiffOn ℝ 1 ((chartAt ℂ p) ∘ δ.extend)
          (δ.extend ⁻¹' (chartAt ℂ p).source ∩ Set.Icc 0 1) := hδ p
      have h_inner : ContDiffOn ℝ 1 (fun t : ℝ => 2 * t - 1) (S ∩ Set.Ioi (1/2 : ℝ)) :=
        h_shift.contDiffOn
      exact (h_outer.comp h_inner h_maps).congr (fun t ht => h_f_eq ht)

end JacobianChallenge.TraceDegree
