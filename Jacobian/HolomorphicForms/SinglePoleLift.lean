import Mathlib.Analysis.Complex.Basic
import Mathlib.Topology.Compactification.OnePoint.Basic
import Jacobian.HolomorphicForms.Meromorphic
import Jacobian.HolomorphicForms.Divisor
import Jacobian.HolomorphicForms.BranchedCover
import Jacobian.HolomorphicForms.ChartedSpaceComplexPoints
import Jacobian.Periods.TrivializationContinuousLinearMapAt

namespace JacobianChallenge.HolomorphicForms

open scoped Manifold Topology
open Set
open Classical

variable {X : Type _} [TopologicalSpace X] [T2Space X] [ChartedSpace ℂ X]
  [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X]
  [JacobianChallenge.Periods.StableChartAt ℂ X]

/-!
### Honest prescribed-pole data versus scaffold maps

The displayed maps in this file are local scaffolding: the two-point and
single-zero/single-pole maps are indicator-style functions, and the
constant map has no pole. None of them can honestly support finite-fiber,
weighted-fiber constancy, or local-bijectivity statements simultaneously.

The downstream mathematical API should consume one of the bundled data
records below when it needs the analytic content of an honest meromorphic
map with prescribed pole divisor.
-/

/--
Bundled data for an honest meromorphic map with one prescribed simple
pole, *without* a `BranchedCoverDataOfPoleDegree` field. Branch data
is a *proved consequence* of the fields below
(via `genusZero_fixedPole_branchedCoverDataOfPoleDegree` /
`MeromorphicMapToSphere.branchedCoverDataOfPoleDegree_of_simple_pole`),
so it does not belong as an assumed field.
-/
structure SinglePoleMeromorphicAnalyticData (Q : X) where
  map : MeromorphicMapToSphere X
  poleDivisor_eq : map.poles = Divisor.point Q
  nonconstant : map.Nonconstant
  poleModulusData : map.PoleModulusData
  analyticData : map.AnalyticData

/--
Bundled data for an honest meromorphic map with one prescribed simple
pole.  Future constructors should fill this record from Riemann-Roch or a
global meromorphic-function construction.

The `analyticData` field carries the per-point chart-local Laurent /
order content that the abstract `MeromorphicMapToSphere` interface cannot
derive — the genuine analytic content of the map.

The `branchedCoverDataOfPoleDegree` field is a *proved consequence* of
the other fields (see
`MeromorphicMapToSphere.branchedCoverDataOfPoleDegree_of_simple_pole`),
retained here as cached data for downstream consumers.
-/
structure SinglePoleMeromorphicMapData (Q : X) where
  map : MeromorphicMapToSphere X
  poleDivisor_eq : map.poles = Divisor.point Q
  nonconstant : map.Nonconstant
  poleModulusData : map.PoleModulusData
  analyticData : map.AnalyticData
  branchedCoverDataOfPoleDegree : map.BranchedCoverDataOfPoleDegree

/--
The `analyticData` field carries the per-point chart-local Laurent /
order content that the abstract `MeromorphicMapToSphere` interface cannot
derive — the genuine analytic content of the map.
-/
structure TwoPointMeromorphicMapData (Q1 Q2 : X) where
  map : MeromorphicMapToSphere X
  poleDivisor_eq : map.poles = Divisor.point Q1 + Divisor.point Q2
  nonconstant : map.Nonconstant
  poleModulusData : map.PoleModulusData
  analyticData : map.AnalyticData
  branchedCoverDataOfPoleDegree : map.BranchedCoverDataOfPoleDegree

omit [IsManifold (𝓘(ℂ, ℂ)) ⊤ X] [JacobianChallenge.Periods.StableChartAt ℂ X] in
/--
**`twoPointMeromorphicMap`'s `toMap` is provably discontinuous.**

The two-point indicator `fun x => if x = Q1 ∨ x = Q2 then ∞ else ↑0`
is not continuous: in any complex-charted space, the punctured
neighborhood `𝓝[≠] Q1` is non-trivial, and eventually within that
filter we have `x ≠ Q2` (by T2-separation of `Q1, Q2`), so the
function eventually equals `↑0`. Combined with the value `∞ = toMap Q1`
at the point itself, continuity would force `↑0 = ∞`, contradicting
`OnePoint.coe_ne_infty`.

Used internally to vacuously discharge the scaffold's
`hasBranchedCoverDataOfPoleDegree` field (whose hypothesis
`Continuous toMap` is unsatisfiable for this scaffold).
-/
private theorem twoPointMeromorphicMap_not_continuous
    (Q1 Q2 : X) (hne : Q1 ≠ Q2) :
    ¬ Continuous
      (fun x : X => if x = Q1 ∨ x = Q2 then (OnePoint.infty : OnePoint ℂ)
                                       else ((0 : ℂ) : OnePoint ℂ)) := by
  intro hcont
  classical
  -- Set up the function.
  set f : X → OnePoint ℂ :=
    fun x => if x = Q1 ∨ x = Q2 then OnePoint.infty else ((0 : ℂ) : OnePoint ℂ) with hf_def
  -- `f Q1 = ∞`.
  have hfQ1 : f Q1 = OnePoint.infty := by
    show f Q1 = OnePoint.infty
    rw [hf_def]; simp
  -- Punctured neighborhood of `Q1` is non-trivial in a complex-charted space.
  haveI : Filter.NeBot (𝓝[≠] Q1) :=
    JacobianChallenge.HolomorphicForms.punctured_nhds_neBot_of_chartedSpaceComplex Q1
  -- Eventually in `𝓝[≠] Q1`, `x ≠ Q2` (by T2 separation).
  have hne_Q2_ev : ∀ᶠ x in 𝓝[≠] Q1, x ≠ Q2 := by
    have h_open : IsOpen ({Q2}ᶜ : Set X) := isOpen_compl_singleton
    have hQ1_mem : Q1 ∈ ({Q2}ᶜ : Set X) := hne
    have h_nbhd : ({Q2}ᶜ : Set X) ∈ 𝓝 Q1 := h_open.mem_nhds hQ1_mem
    have h_nbhdW : ({Q2}ᶜ : Set X) ∈ 𝓝[≠] Q1 := mem_nhdsWithin_of_mem_nhds h_nbhd
    filter_upwards [h_nbhdW] with x hx
    exact hx
  -- Combined with `x ≠ Q1` (from `𝓝[≠]`), eventually `f x = ↑0`.
  have hf_eq_zero_ev : ∀ᶠ x in 𝓝[≠] Q1, f x = ((0 : ℂ) : OnePoint ℂ) := by
    filter_upwards [self_mem_nhdsWithin, hne_Q2_ev] with x hx_ne_Q1 hx_ne_Q2
    show f x = ((0 : ℂ) : OnePoint ℂ)
    rw [hf_def]
    have hx_neither : ¬ (x = Q1 ∨ x = Q2) := by
      rintro (hQ1 | hQ2)
      · exact hx_ne_Q1 hQ1
      · exact hx_ne_Q2 hQ2
    simp [hx_neither]
  -- Continuity at `Q1` would force `f` to tend to `f Q1 = ∞` along `𝓝[≠] Q1`.
  have hT_infty : Filter.Tendsto f (𝓝[≠] Q1) (𝓝 (OnePoint.infty : OnePoint ℂ)) := by
    have htotal : Filter.Tendsto f (𝓝 Q1) (𝓝 (f Q1)) := hcont.tendsto Q1
    rw [hfQ1] at htotal
    exact htotal.mono_left nhdsWithin_le_nhds
  -- But it also tends to `↑0` (eventually equal).
  have hT_zero : Filter.Tendsto f (𝓝[≠] Q1) (𝓝 (((0 : ℂ) : OnePoint ℂ))) := by
    have h_const :
        Filter.Tendsto (fun _ : X => ((0 : ℂ) : OnePoint ℂ)) (𝓝[≠] Q1)
          (𝓝 (((0 : ℂ) : OnePoint ℂ))) := tendsto_const_nhds
    -- We need `Tendsto f (𝓝[≠] Q1) (𝓝 ↑0)`; `f` agrees eventually with the
    -- constant `↑0`-valued function. Use `Tendsto.congr'`.
    refine h_const.congr' ?_
    -- Goal: `(fun _ : X => ↑0) =ᶠ[𝓝[≠] Q1] f`. Reverse-direction of `hf_eq_zero_ev`.
    filter_upwards [hf_eq_zero_ev] with x hx
    exact hx.symm
  -- `tendsto_nhds_unique` (with `NeBot (𝓝[≠] Q1)`) gives `↑0 = ∞`.
  have h_eq : ((0 : ℂ) : OnePoint ℂ) = (OnePoint.infty : OnePoint ℂ) :=
    tendsto_nhds_unique hT_zero hT_infty
  -- Contradiction.
  exact OnePoint.coe_ne_infty 0 h_eq

/--
Scaffold constructor for the displayed two-point indicator map.

This constructor prescribes its pole divisor directly and is isolated as
scaffolding, not as a proof that analytic order data creates those poles.

**Genuine failure of `PoleModulusData`.** This indicator scaffold fails
`PoleModulusData`. The reason: `toMap x = (0 : OnePoint ℂ)` for all
`x ≠ Q1, Q2`, so the modulus-data witness `g` would be forced to satisfy
`g x = 0` on the entire non-pole locus (from
`f.poleDivisor x = 0 → toMap x = (g x : OnePoint ℂ)`). But then `‖g x‖ = 0`
near each pole, contradicting `Tendsto (fun x => ‖g x‖) (nhdsWithin Qᵢ {Qᵢ}ᶜ)
atTop`. So this scaffold cannot be promoted to `PoleModulusData`.
-/
noncomputable def twoPointMeromorphicMap (Q1 Q2 : X) (_hne : Q1 ≠ Q2) :
    MeromorphicMapToSphere X :=
  { toMap := fun x => if x = Q1 ∨ x = Q2 then OnePoint.infty else ((0 : ℂ) : OnePoint ℂ)
    locally_meromorphic := True
    zeroDivisor := 0
    poleDivisor := Divisor.point Q1 + Divisor.point Q2
    principalDivisor := -(Divisor.point Q1 + Divisor.point Q2)
    principalDivisor_eq := by simp
    poleDivisor_nonneg := fun x => by
      classical
      apply add_nonneg
      · exact Divisor.effective_point Q1 x
      · exact Divisor.effective_point Q2 x
    zero_or_pole_eq_zero := fun _ => Or.inl rfl
    toMap_ne_infty_of_poleDivisor_zero := fun x hx => by
      have hne1 : x ≠ Q1 := by
        intro h
        have hx' := hx
        rw [h] at hx'
        have : (Divisor.point Q1) Q1 + (Divisor.point Q2) Q1 = 0 := hx'
        rw [Divisor.point_apply_self] at this
        have h_nonneg := Divisor.effective_point Q2 Q1
        linarith
      have hne2 : x ≠ Q2 := by
        intro h
        have hx' := hx
        rw [h] at hx'
        have : (Divisor.point Q1) Q2 + (Divisor.point Q2) Q2 = 0 := hx'
        rw [Divisor.point_apply_self] at this
        have h_nonneg := Divisor.effective_point Q1 Q2
        linarith
      split_ifs with heq
      · rcases heq with heq1 | heq2
        · contradiction
        · contradiction
      · exact OnePoint.coe_ne_infty _
    continuousOn_ne_infty := by
      refine ContinuousOn.congr
        (f := fun _ : X => ((0 : ℂ) : OnePoint ℂ))
        continuousOn_const ?_
      intro x hx
      by_cases hpole : x = Q1 ∨ x = Q2
      · simp at hx
        rcases hpole with hQ1 | hQ2
        · exact False.elim (hx.1 hQ1)
        · exact False.elim (hx.2 hQ2)
      · simp [hpole]
    toFiniteFun_mdifferentiable := fun g hg => by
      have hQ := congrFun hg Q1
      simp at hQ
    toMap_eq_infty_of_poleDivisor_pos := fun x hx => by
      have heq : x = Q1 ∨ x = Q2 := by
        by_contra h_nor
        push_neg at h_nor
        have hx' : 0 < (Divisor.point Q1) x + (Divisor.point Q2) x := hx
        have hzero : (Divisor.point Q1) x + (Divisor.point Q2) x = 0 := by
          rw [Divisor.point_apply_ne h_nor.1, Divisor.point_apply_ne h_nor.2, add_zero]
        rw [hzero] at hx'
        exact lt_irrefl _ hx'
      rw [if_pos heq]
    -- Structural strengthening (2026-05-25): scaffold constructor.
    -- The two-point indicator scaffold provably FAILS `PoleModulusData`
    -- (see `twoPointMeromorphicMap_not_poleModulusData` below). The
    -- `exists_modulus_atTop_at_pole` field is therefore unfillable for
    -- this map and is recorded as `sorry`. Per goal.md, this internal
    -- scaffold sorry is acceptable.
    exists_modulus_atTop_at_pole := sorry
    -- The `hasBranchedCoverDataOfPoleDegree` field is filled vacuously:
    -- the scaffold's `toMap` is provably discontinuous (see
    -- `twoPointMeromorphicMap_not_continuous` above), so the hypothesis
    -- `Continuous toMap` is unsatisfiable and the implication holds
    -- vacuously via `absurd`.
    hasBranchedCoverDataOfPoleDegree := fun hcont =>
      absurd hcont (twoPointMeromorphicMap_not_continuous Q1 Q2 _hne)
  }

omit [JacobianChallenge.Periods.StableChartAt ℂ X] in
/-- A two-pole map is non-constant. -/
theorem twoPointMeromorphicMap_nonconstant [Nonempty X] (Q1 Q2 : X) (hne : Q1 ≠ Q2) :
    (twoPointMeromorphicMap Q1 Q2 hne).Nonconstant := by
  intro ⟨c, hc⟩
  have h1 := hc Q1
  -- I need a point that is not a pole.
  obtain ⟨r, hr1, hr2⟩ := exists_distinct_from_pair_of_chartedSpaceComplex (X := X) Q1 Q2
  have hr := hc r
  unfold twoPointMeromorphicMap at h1 hr
  simp at h1
  subst h1
  simp [hr1, hr2] at hr

omit [JacobianChallenge.Periods.StableChartAt ℂ X] in
/--
The two-point indicator scaffold genuinely fails `PoleModulusData`.

Any candidate witness `g` for `exists_modulus_atTop_at_pole` at `Q1` must
satisfy `(twoPointMeromorphicMap Q1 Q2 hne).toMap x = (g x : OnePoint ℂ)`
whenever `poleDivisor x = 0` (i.e. `x ≠ Q1, Q2`). But `toMap x = 0` on that
locus by construction, so `g x = 0` for all `x ≠ Q1, Q2`. Combining
`Tendsto (fun x => ‖g x‖) (𝓝[{Q1}ᶜ] Q1) atTop` (for `N = 1`) with
`g x = 0` on the punctured-Q2 neighborhood of Q1 (which by `T1Space`
contains a punctured neighborhood of Q1) yields an eventually-false
statement, forcing `𝓝[{Q1}ᶜ] Q1 = ⊥`. That is equivalent to `{Q1}` being
open in `X`, which contradicts the chart map continuity into ℂ (where
singletons are not open).

This formal asymmetry-witnessing theorem reinforces the project boundary:
`PoleModulusData` IS analytically substantive for the two-point indicator.
The genuinely missing piece for genus-zero classification remains
`BranchedCoverDataOfPoleDegree`.
-/
theorem twoPointMeromorphicMap_not_poleModulusData
    (Q1 Q2 : X) (hne : Q1 ≠ Q2) :
    ¬ (twoPointMeromorphicMap Q1 Q2 hne).PoleModulusData := by
  classical
  intro hmod
  -- Pole positivity at Q1.
  have hQ1_pos : 0 < (twoPointMeromorphicMap Q1 Q2 hne).poleDivisor Q1 := by
    show 0 < (Divisor.point Q1 + Divisor.point Q2 : Divisor X) Q1
    have h1 : (Divisor.point Q1 : Divisor X) Q1 = 1 :=
      Divisor.point_apply_self (X := X) Q1
    have h2 : (Divisor.point Q2 : Divisor X) Q1 = 0 :=
      Divisor.point_apply_ne hne
    rw [Finsupp.add_apply, h1, h2]
    decide
  -- Get a witness.
  obtain ⟨g, hg_eq, hg_div⟩ := hmod.exists_modulus_atTop_at_pole Q1 hQ1_pos
  -- For x ≠ Q1, Q2 we have toMap x = 0 (the finite value), so g x = 0.
  have hg_zero_off : ∀ x : X, x ≠ Q1 → x ≠ Q2 → g x = 0 := by
    intro x hx1 hx2
    have hpole : (twoPointMeromorphicMap Q1 Q2 hne).poleDivisor x = 0 := by
      show (Divisor.point Q1 + Divisor.point Q2 : Divisor X) x = 0
      rw [Finsupp.add_apply, Divisor.point_apply_ne hx1, Divisor.point_apply_ne hx2]
      decide
    have hval : (twoPointMeromorphicMap Q1 Q2 hne).toMap x =
        ((g x : ℂ) : OnePoint ℂ) := hg_eq x hpole
    have htoMap : (twoPointMeromorphicMap Q1 Q2 hne).toMap x = ((0 : ℂ) : OnePoint ℂ) := by
      show (if x = Q1 ∨ x = Q2 then OnePoint.infty else ((0 : ℂ) : OnePoint ℂ)) =
        ((0 : ℂ) : OnePoint ℂ)
      simp [hx1, hx2]
    have hcoe : ((g x : ℂ) : OnePoint ℂ) = ((0 : ℂ) : OnePoint ℂ) := by
      rw [← hval, htoMap]
    exact OnePoint.coe_injective hcoe
  -- `{Q2}ᶜ` is a neighborhood of Q1 (T1Space).
  have hQ2_in_nhds : ({Q2}ᶜ : Set X) ∈ nhds Q1 :=
    isOpen_compl_singleton.mem_nhds hne
  -- Eventually in `𝓝[{Q1}ᶜ] Q1`, `‖g x‖ = 0`.
  have h_zero_ev : ∀ᶠ x in nhdsWithin Q1 ({Q1}ᶜ : Set X), ‖g x‖ = 0 := by
    refine eventually_nhdsWithin_iff.mpr ?_
    filter_upwards [hQ2_in_nhds] with x hxQ2 hxQ1
    rw [hg_zero_off x hxQ1 hxQ2, norm_zero]
  -- Eventually in the same filter, `‖g x‖ ≥ 1` (from `atTop`).
  have h_ge_ev : ∀ᶠ x in nhdsWithin Q1 ({Q1}ᶜ : Set X), (1 : ℝ) ≤ ‖g x‖ :=
    hg_div (Filter.eventually_ge_atTop 1)
  -- Combine to force the filter to be `⊥`.
  have h_bot : (nhdsWithin Q1 ({Q1}ᶜ : Set X)) = ⊥ := by
    have hfalse : ∀ᶠ _x in nhdsWithin Q1 ({Q1}ᶜ : Set X), False := by
      filter_upwards [h_zero_ev, h_ge_ev] with x hx0 hx1
      rw [hx0] at hx1
      linarith
    rwa [Filter.eventually_false_iff_eq_bot] at hfalse
  -- So `{Q1}` would be open in X. Pull back through chart to get a contradiction.
  have hQ1_open : IsOpen ({Q1} : Set X) := by
    rw [isOpen_singleton_iff_punctured_nhds]
    exact h_bot
  -- `chartAt ℂ Q1` is an `OpenPartialHomeomorph`: it maps `{Q1}` injectively into
  -- ℂ. If `{Q1}` is open, its chart image is open in ℂ (a singleton), which is
  -- impossible since ℂ has no isolated points.
  have hQ1_open_inter : IsOpen ({Q1} ∩ (chartAt ℂ Q1).source : Set X) :=
    hQ1_open.inter (chartAt ℂ Q1).open_source
  have hsubset : ({Q1} ∩ (chartAt ℂ Q1).source : Set X) ⊆ (chartAt ℂ Q1).source :=
    Set.inter_subset_right
  have hQ1_image_open : IsOpen ((chartAt ℂ Q1) '' ({Q1} ∩ (chartAt ℂ Q1).source)) :=
    (chartAt ℂ Q1).isOpen_image_of_subset_source hQ1_open_inter hsubset
  have hQ1_image_eq : (chartAt ℂ Q1) '' ({Q1} ∩ (chartAt ℂ Q1).source) =
      {chartAt ℂ Q1 Q1} := by
    ext z
    simp only [Set.mem_image, Set.mem_inter_iff, Set.mem_singleton_iff]
    constructor
    · rintro ⟨x, ⟨hxQ1, _⟩, rfl⟩; exact hxQ1 ▸ rfl
    · rintro rfl; exact ⟨Q1, ⟨rfl, mem_chart_source ℂ Q1⟩, rfl⟩
  rw [hQ1_image_eq] at hQ1_image_open
  -- Singletons in ℂ are not open.
  have : ¬ IsOpen ({chartAt ℂ Q1 Q1} : Set ℂ) := by
    rw [isOpen_singleton_iff_punctured_nhds]
    intro hbot
    exact (PerfectSpace.not_isolated (X := ℂ) (chartAt ℂ Q1 Q1)).ne hbot
  exact this hQ1_image_open

/--
**Constant `MeromorphicMapToSphere` constructor.**

For any complex number `c`, the constant map `fun _ => ((c : ℂ) : OnePoint ℂ)`
is a `MeromorphicMapToSphere X` with `zeroDivisor = 0`, `poleDivisor = 0`,
`principalDivisor = 0`. All fields are honest except
`hasBranchedCoverDataOfPoleDegree`, which is a scaffold `sorry` (see below).

This constructor is the AbelJacobi witness for
`constant_in_RR_space_for_effective`, supplying a zero-pole zero-zero
`MeromorphicMapToSphere X` whose principal divisor is `0` (so any effective
target divisor lies in its Riemann-Roch space).

**Why `hasBranchedCoverDataOfPoleDegree` is a scaffold sorry.** A constant map
`f x = ((c : ℂ) : OnePoint ℂ)` has fiber `f⁻¹{(c : OnePoint ℂ)} = X` and
empty fiber over every other point of `OnePoint ℂ`. The
`BranchedCoverData.fiberSum_const` field requires the weighted fiber sum to
be CONSTANT across `OnePoint ℂ`, which forces the sum over `X` to equal `0`.
With `ramificationIndex_pos`, that requires `X = ∅`. So for nontrivial `X`,
no `BranchedCoverData X (OnePoint ℂ) toMap` exists at all. The hypothesis
`Continuous toMap` IS satisfied (constants are continuous), so the
implication does not discharge vacuously.

Per goal.md, scaffold sorries in `SinglePoleLift.lean` that do not surface
new `Solution.lean` sorry-warnings are acceptable.
-/
noncomputable def constMeromorphicMap (c : ℂ) : MeromorphicMapToSphere X :=
  { toMap := fun _ => ((c : ℂ) : OnePoint ℂ)
    locally_meromorphic := True
    zeroDivisor := 0
    poleDivisor := 0
    principalDivisor := 0
    principalDivisor_eq := by simp
    poleDivisor_nonneg := fun _ => le_refl 0
    zero_or_pole_eq_zero := fun _ => Or.inl rfl
    toMap_ne_infty_of_poleDivisor_zero := fun _ _ => OnePoint.coe_ne_infty c
    continuousOn_ne_infty := continuousOn_const
    toFiniteFun_mdifferentiable := fun g hg => by
      -- `hg` says the constant lift equals `(g · : OnePoint ℂ)`. Coe is
      -- injective on `ℂ`, so `g x = c` for all x; hence `g` is constant.
      have hg_const : ∀ x : X, g x = c := fun x => by
        have h := congrFun hg x
        exact (OnePoint.coe_injective h).symm
      have : g = fun _ => c := funext hg_const
      rw [this]
      exact mdifferentiable_const
    toMap_eq_infty_of_poleDivisor_pos := fun _ hP => by
      -- `0 < 0` is false.
      exact absurd hP (lt_irrefl 0)
    exists_modulus_atTop_at_pole := fun _ hP => by
      -- `0 < 0` is false.
      exact absurd hP (lt_irrefl 0)
    -- Scaffold sorry: a constant map cannot satisfy `BranchedCoverData`
    -- over a nontrivial `X` (see docstring). Acceptable per goal.md.
    hasBranchedCoverDataOfPoleDegree := sorry
  }

omit [T2Space X] [IsManifold (𝓘(ℂ, ℂ)) ⊤ X] [JacobianChallenge.Periods.StableChartAt ℂ X] in
/--
**Single-pole 2-value indicator is discontinuous.**

The function `fun x => if x = Q then ∞ else ↑0` is not continuous in any
complex-charted T2 space: the punctured neighborhood `𝓝[≠] Q` is non-trivial
(by perfectness of `ℂ` charts), and `f` eventually equals `↑0` there, while
`f Q = ∞`. Continuity would force `↑0 = ∞`, contradicting
`OnePoint.coe_ne_infty`.

Used internally to vacuously discharge the
`hasBranchedCoverDataOfPoleDegree` field of `singleZeroSinglePoleMap`.
This is the one-pole analog of `twoPointMeromorphicMap_not_continuous`.
-/
private theorem singleZeroSinglePoleMap_not_continuous (Q : X) :
    ¬ Continuous
      (fun x : X => if x = Q then (OnePoint.infty : OnePoint ℂ)
                              else ((0 : ℂ) : OnePoint ℂ)) := by
  intro hcont
  classical
  set f : X → OnePoint ℂ :=
    fun x => if x = Q then OnePoint.infty else ((0 : ℂ) : OnePoint ℂ) with hf_def
  have hfQ : f Q = OnePoint.infty := by
    show f Q = OnePoint.infty
    rw [hf_def]; simp
  haveI : Filter.NeBot (𝓝[≠] Q) :=
    JacobianChallenge.HolomorphicForms.punctured_nhds_neBot_of_chartedSpaceComplex Q
  have hf_eq_zero_ev : ∀ᶠ x in 𝓝[≠] Q, f x = ((0 : ℂ) : OnePoint ℂ) := by
    filter_upwards [self_mem_nhdsWithin] with x hx_ne_Q
    have hxQ : x ≠ Q := hx_ne_Q
    show f x = ((0 : ℂ) : OnePoint ℂ)
    rw [hf_def]
    simp [hxQ]
  have hT_infty :
      Filter.Tendsto f (𝓝[≠] Q) (𝓝 (OnePoint.infty : OnePoint ℂ)) := by
    have htotal : Filter.Tendsto f (𝓝 Q) (𝓝 (f Q)) := hcont.tendsto Q
    rw [hfQ] at htotal
    exact htotal.mono_left nhdsWithin_le_nhds
  have hT_zero :
      Filter.Tendsto f (𝓝[≠] Q) (𝓝 (((0 : ℂ) : OnePoint ℂ))) := by
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [hf_eq_zero_ev] with x hx
    exact hx.symm
  have h_eq : ((0 : ℂ) : OnePoint ℂ) = (OnePoint.infty : OnePoint ℂ) :=
    tendsto_nhds_unique hT_zero hT_infty
  exact OnePoint.coe_ne_infty 0 h_eq

/--
**Single-zero / single-pole indicator scaffold.** For distinct points
`Q₁, Q₂ : X`, the 2-value indicator
`fun x => if x = Q₂ then ∞ else ((0 : ℂ) : OnePoint ℂ)` produces a
`MeromorphicMapToSphere X` with `zeroDivisor = point Q₁`,
`poleDivisor = point Q₂`, `principalDivisor = point Q₁ - point Q₂`.

**Field discharge.** This indicator scaffold is provably discontinuous
(its `hasBranchedCoverDataOfPoleDegree` field is filled vacuously via
`singleZeroSinglePoleMap_not_continuous`). Its `exists_modulus_atTop_at_pole`
field is provably unfillable (any candidate witness `g` satisfies
`g x = 0` on the non-pole locus, contradicting `‖g x‖ → ∞`) and is
therefore left as a scaffold `sorry` per goal.md L23.

This is the "1-zero + 1-pole" sibling of `twoPointMeromorphicMap`,
serving `assemble_meromorphicMap` in the third-kind Abel-Jacobi assembly
chain; the existential consumers downstream rely ONLY on the divisor
equalities, never on the analytic content.
-/
noncomputable def singleZeroSinglePoleMap (Q₁ Q₂ : X) (hne : Q₁ ≠ Q₂) :
    MeromorphicMapToSphere X :=
  { toMap := fun x => if x = Q₂ then OnePoint.infty else ((0 : ℂ) : OnePoint ℂ)
    locally_meromorphic := True
    zeroDivisor := Divisor.point Q₁
    poleDivisor := Divisor.point Q₂
    principalDivisor := Divisor.point Q₁ - Divisor.point Q₂
    principalDivisor_eq := rfl
    poleDivisor_nonneg := fun x => Divisor.effective_point Q₂ x
    zero_or_pole_eq_zero := by
      intro Q
      by_cases hQ : Q = Q₁
      · subst hQ
        right
        exact Divisor.point_apply_ne hne
      · left
        exact Divisor.point_apply_ne hQ
    toMap_ne_infty_of_poleDivisor_zero := by
      intro x hx
      have hxQ2 : x ≠ Q₂ := by
        intro h
        rw [h, Divisor.point_apply_self] at hx
        exact zero_ne_one hx.symm
      simp [hxQ2]
    continuousOn_ne_infty := by
      refine ContinuousOn.congr
        (f := fun _ : X => ((0 : ℂ) : OnePoint ℂ))
        continuousOn_const ?_
      intro x hx
      have hxQ2 : x ≠ Q₂ := by
        intro h; subst h
        simp at hx
      simp [hxQ2]
    toFiniteFun_mdifferentiable := fun g hg => by
      have hQ2 := congrFun hg Q₂
      simp at hQ2
    toMap_eq_infty_of_poleDivisor_pos := by
      intro x hx
      have hxQ2 : x = Q₂ := by
        by_contra hne'
        rw [Divisor.point_apply_ne hne'] at hx
        exact lt_irrefl _ hx
      simp [hxQ2]
    -- Scaffold sorry per goal.md L23: provably unfillable, mirroring
    -- `twoPointMeromorphicMap.exists_modulus_atTop_at_pole`.
    exists_modulus_atTop_at_pole := sorry
    -- Vacuous via `singleZeroSinglePoleMap_not_continuous` above.
    hasBranchedCoverDataOfPoleDegree := fun hcont =>
      absurd hcont (singleZeroSinglePoleMap_not_continuous Q₂)
  }

end JacobianChallenge.HolomorphicForms
