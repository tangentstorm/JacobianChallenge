import Jacobian.Blueprint.Sec02.BranchedDegree
import Jacobian.HolomorphicForms.HolomorphicMap
import Mathlib.Topology.LocallyConstant.Basic

/-! # Blueprint: well-definedness of the branched degree (4-step decomposition)

Section 2 of `tex/sections/02-holomorphic-forms-and-genus.tex`.

This file decomposes the proof of `weightedFiberCard_const` (the
remaining `sorry` in `Sec02/BranchedDegreeFromHolomorphic.lean`) into
four sub-leaves, each stated as a `sorry`-bearing theorem.  Together
they give the well-definedness of the branched degree:

  1. **Branch locus finite** (`mapAnalyticOrderAt_ramified_finite`):
     for a nonconstant holomorphic map between compact preconnected
     complex 1-manifolds, the source-side ramified set
     `{x | mapAnalyticOrderAt f x ≠ 1}` is finite.  Standard proof:
     in each chart, `e_x(f) ≥ 2` is equivalent to vanishing of the
     chart-pulled derivative `(ψ ∘ f ∘ φ⁻¹)'(φ x)`; the derivative is
     itself analytic, so its zero set is discrete by the analytic
     identity principle (`AnalyticAt.eventually_ne` in Mathlib).
     Discrete-in-each-chart + compactness ⇒ finite.

  2. **Local injectivity at unramified points**
     (`IsHolomorphicAt.exists_local_inj_of_unramified`): if
     `mapAnalyticOrderAt f x = 1`, there's an open neighborhood `U`
     of `x` and an open neighborhood `V` of `f x` such that for every
     `y ∈ V`, the set `U ∩ f⁻¹ {y}` is a singleton.  Standard proof:
     order-1 ⇒ chart-local derivative nonzero at chart `x`; Mathlib's
     `AnalyticAt.localInverse` / inverse-function theorem on `ℂ` ⇒
     local biholomorphism; transport back through charts.

  3. **Local k-fold structure at ramified points**
     (`IsHolomorphicAt.exists_local_kfold_of_ramified`): if
     `mapAnalyticOrderAt f x = k` with `k ≥ 1`, there's a neighborhood
     `U` of `x` and a neighborhood `V` of `f x` such that for every
     `y ∈ V` with `y ≠ f x`, the set `U ∩ f⁻¹ {y}` consists of exactly
     `k` distinct unramified preimages.  Standard proof: in suitable
     local chart-coordinates, `f` looks like `t ↦ t^k` near `0`
     (Mathlib's `AnalyticAt.analyticOrderAt_eq_natCast` gives the
     local power-series form `f(t) = t^k · g(t)` with `g(0) ≠ 0`,
     then a holomorphic local change-of-variables flattens `g` to a
     constant).  The map `t ↦ t^k` has exactly `k` simple preimages
     of any nonzero target.

  4. **Local conservation of weighted fibre count**
     (`isHolomorphic_weightedFiberSum_isLocallyConstant`): combining
     leaves 2 and 3, the weighted fibre sum `∑_{x ∈ f⁻¹{y}} e_x(f)`
     is locally constant on `Y`.  Proof: at each `y₀ : Y`, the fibre
     `f⁻¹{y₀}` is finite (by `isHolomorphic_finite_fiber`); choose
     disjoint open neighborhoods of each preimage; each unramified
     preimage contributes `1` to the local count for `y` near `y₀`
     (leaf 2); each ramified preimage of order `k` contributes `k`
     simple preimages (leaf 3) summing to `k` again.  The total
     weighted count at `y` equals the total weighted count at `y₀`.

The final theorem `isHolomorphic_weightedFiberSum_const` follows
from leaf 4 plus `IsLocallyConstant.apply_eq_of_preconnectedSpace`,
and is exactly the field needed to discharge the remaining `sorry`
in `branchedCoverData_of_nonconstant_holomorphic`. -/

namespace JacobianChallenge.Blueprint

open scoped Manifold Topology ContDiff
open Set Filter
open JacobianChallenge.HolomorphicForms.HolomorphicMap

/-! ### Common helper

The next two helpers are used by both sub-leaf A (branch locus
finite) and sub-leaf B (local injectivity at unramified). -/

/-
**Common helper (sorry).** Order = 1 at `x` is equivalent to
the chart-local derivative being nonzero at `chartAt ℂ x x`.

This is a direct re-packaging of Mathlib's
`AnalyticAt.analyticOrderAt_sub_eq_one_of_deriv_ne_zero` plus the
characterisation `analyticOrderNatAt = 1 ↔ analyticOrderAt = 1` on
finite-order analytic functions.
-/
theorem mapAnalyticOrderAt_eq_one_iff_chartLocal_deriv_ne_zero
    {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    [ChartedSpace ℂ X] [ChartedSpace ℂ Y]
    [IsManifold 𝓘(ℂ) ω X] [IsManifold 𝓘(ℂ) ω Y]
    {f : X → Y} {x : X} (_hf : IsHolomorphicAt f x) :
    mapAnalyticOrderAt f x = 1 ↔ deriv (chartLocalAt f x) (chartAt ℂ x x) ≠ 0 := by
  constructor <;> intro h;
  · have h_order : analyticOrderAt (fun t => chartLocalAt f x t - chartLocalAt f x (chartAt ℂ x x)) (chartAt ℂ x x) = 1 := by
      convert h using 1;
      unfold mapAnalyticOrderAt;
      simp +decide [ analyticOrderNatAt ];
    have h_deriv : analyticOrderAt (deriv (fun t => chartLocalAt f x t - chartLocalAt f x (chartAt ℂ x x))) (chartAt ℂ x x) = 0 := by
      have := AnalyticAt.analyticOrderAt_deriv_add_one ( show AnalyticAt ℂ ( fun t => chartLocalAt f x t - chartLocalAt f x ( chartAt ℂ x x ) ) ( chartAt ℂ x x ) from ?_ );
      · aesop;
      · exact _hf.sub ( analyticAt_const );
    rw [ analyticOrderAt_eq_zero ] at h_deriv;
    simp_all +decide [ deriv_sub_const ];
    exact h_deriv.resolve_left fun h => h <| AnalyticAt.deriv _hf;
  · unfold mapAnalyticOrderAt;
    rw [ analyticOrderNatAt ];
    rw [ AnalyticAt.analyticOrderAt_sub_eq_one_of_deriv_ne_zero ] <;> aesop

/-! ### Sub-leaf A: branch locus finite

The decomposition is:

  * A1 = the common helper above (`= 1 ↔ deriv ≠ 0`),
  * A2 `isOpen_setOf_mapAnalyticOrderAt_eq_one` — unramified set is
    open in `X`,
  * A3 `mapAnalyticOrderAt_isolated_at_ramified` — every ramified
    point is isolated in the ramified set,
  * A4 `mapAnalyticOrderAt_ramified_finite` — assembly: closed
    discrete subset of compact ⇒ finite. -/

/-- **A2 (sorry).** The unramified set
`{x : X | mapAnalyticOrderAt f x = 1}` is open in `X`.

Proof sketch: order = 1 at `x` ⇔ chart-local derivative nonzero at
`chartAt ℂ x x` (common helper).  The chart-local derivative is itself
analytic, hence continuous; the set where a continuous function is
nonzero is open in `ℂ`; pull back through the chart to get openness
in `X`. -/
theorem isOpen_setOf_mapAnalyticOrderAt_eq_one
    {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    [ChartedSpace ℂ X] [ChartedSpace ℂ Y]
    [IsManifold 𝓘(ℂ) ω X] [IsManifold 𝓘(ℂ) ω Y]
    {f : X → Y} (_hf : IsHolomorphic f) :
    IsOpen {x : X | mapAnalyticOrderAt f x = 1} := by
  sorry

/-- **A3 (sorry).** Every ramified point is isolated in the ramified
set: at a point `x` with order ≠ 1, there's a neighborhood `U` of `x`
such that every other point in `U` is unramified.

Proof sketch: if `mapAnalyticOrderAt f x = k ≥ 2`, the chart-local
derivative `(chartLocalAt f x)' (z)` vanishes at `z = chartAt ℂ x x`
to order `k - 1 ≥ 1` (subtracting `1` because differentiating drops
the order by one).  Apply Mathlib's `AnalyticAt.eventually_ne` to the
chart-local derivative to obtain a punctured neighborhood of
`chartAt ℂ x x` where the derivative is nonzero, then transport back
through the chart and apply the common helper to identify those
points as having order = 1. -/
theorem mapAnalyticOrderAt_isolated_at_ramified
    {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    [ChartedSpace ℂ X] [ChartedSpace ℂ Y]
    [IsManifold 𝓘(ℂ) ω X] [IsManifold 𝓘(ℂ) ω Y]
    [PreconnectedSpace X] [T2Space Y]
    {f : X → Y} (_hf : IsHolomorphic f)
    (_hnonconst : ¬ ∃ y₀ : Y, ∀ x, f x = y₀) {x : X}
    (_hramx : mapAnalyticOrderAt f x ≠ 1) :
    ∀ᶠ x' in 𝓝[≠] x, mapAnalyticOrderAt f x' = 1 := by
  sorry

/-- **A4 = Sub-leaf 1 (sorry).** For a nonconstant holomorphic map
between compact preconnected complex 1-manifolds, the source-side
ramified set `{x | mapAnalyticOrderAt f x ≠ 1}` is finite.

Proof sketch (assembling A2 + A3):

  * From A2, the ramified set is closed in `X` (complement of an open
    set).  Closed in compact ⇒ compact subspace.
  * From A3, every ramified point is isolated in the ramified set, so
    the subspace topology on the ramified set is discrete.
  * A discrete subset of compact ⇒ finite (Mathlib's
    `DiscreteTopology.finite_of_compact_space` or similar). -/
theorem mapAnalyticOrderAt_ramified_finite
    {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    [ChartedSpace ℂ X] [ChartedSpace ℂ Y]
    [IsManifold 𝓘(ℂ) ω X] [IsManifold 𝓘(ℂ) ω Y]
    [CompactSpace X] [PreconnectedSpace X] [T2Space Y]
    {f : X → Y} (_hf : IsHolomorphic f)
    (_hnonconst : ¬ ∃ y₀ : Y, ∀ x, f x = y₀) :
    {x : X | mapAnalyticOrderAt f x ≠ 1}.Finite := by
  sorry

/-! ### Sub-leaf B: local injectivity at unramified points

Decomposition:

  * B1 = the common helper above (`= 1 ↔ deriv ≠ 0`),
  * B2 `chartLocalAt_localInverse_of_unramified` — at a chart-locally
    unramified point, the chart-local function admits a holomorphic
    local inverse (Mathlib's `AnalyticAt.localInverse`),
  * B3 `IsHolomorphicAt.exists_local_inj_of_unramified` — assembly:
    transport the chart-local inverse to a manifold-level injective
    neighborhood. -/

/-- **B2 (sorry).** At an unramified point `x`, the chart-local
function `chartLocalAt f x` has a holomorphic local inverse.

Proof sketch: from B1 the chart-local derivative is nonzero at
`chartAt ℂ x x`.  Mathlib's analytic inverse function theorem
`AnalyticAt.localInverse` (in `Analysis/Analytic/Inverse.lean`)
produces an analytic local inverse.  Wrap as the existence of an
analytic `g : ℂ → ℂ` with mutual local-inverse equations. -/
theorem chartLocalAt_localInverse_of_unramified
    {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    [ChartedSpace ℂ X] [ChartedSpace ℂ Y]
    [IsManifold 𝓘(ℂ) ω X] [IsManifold 𝓘(ℂ) ω Y]
    {f : X → Y} {x : X} (_hf : IsHolomorphicAt f x)
    (_hramx : mapAnalyticOrderAt f x = 1) :
    ∃ g : ℂ → ℂ, AnalyticAt ℂ g (chartAt ℂ (f x) (f x)) ∧
      g (chartAt ℂ (f x) (f x)) = chartAt ℂ x x ∧
      (∀ᶠ t in 𝓝 (chartAt ℂ x x), g (chartLocalAt f x t) = t) ∧
      (∀ᶠ s in 𝓝 (chartAt ℂ (f x) (f x)),
        chartLocalAt f x (g s) = s) := by
  sorry

/-- **B3 = Sub-leaf 2 (sorry).** Local injectivity at an unramified
point: if `mapAnalyticOrderAt f x = 1`, there is an open neighborhood
pair `(U, V)` such that for every `y ∈ V`, `U ∩ f⁻¹ {y}` is a
singleton.

Proof sketch (assembling B2):

  * Apply B2 to obtain the analytic local inverse `g` near
    `chartAt ℂ (f x) (f x)`.
  * Lift `g` through `chartAt ℂ (f x)` and `chartAt ℂ x` to a
    continuous local inverse `(chartAt ℂ x).symm ∘ g ∘ chartAt ℂ (f x)`
    of `f` on a neighborhood of `f x`.
  * Take `U` and `V` small enough that the chart compositions are
    well-defined and the local inverse lands in the right places. -/
theorem IsHolomorphicAt.exists_local_inj_of_unramified
    {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    [ChartedSpace ℂ X] [ChartedSpace ℂ Y]
    [IsManifold 𝓘(ℂ) ω X] [IsManifold 𝓘(ℂ) ω Y]
    {f : X → Y} (_hf : IsHolomorphic f) {x : X}
    (_hramx : mapAnalyticOrderAt f x = 1) :
    ∃ U : Set X, IsOpen U ∧ x ∈ U ∧
    ∃ V : Set Y, IsOpen V ∧ f x ∈ V ∧
    ∀ y ∈ V, ∃! x' : X, x' ∈ U ∧ f x' = y := by
  sorry

/-! ### Sub-leaf C: local k-fold structure at ramified points

Decomposition:

  * C1 `chartLocalAt_eq_pow_mul_of_order` — local power-series form
    `chartLocalAt(t) - chart(f x) = (t - z₀)^k · g(t)` with
    `g(z₀) ≠ 0`, from Mathlib's `AnalyticAt.analyticOrderAt_eq_natCast`,
  * C2 `analyticAt_kth_root_of_ne_zero` — analytic `k`-th root of a
    locally nonvanishing analytic function (via complex log + cpow,
    or Mathlib's `Complex.cpow` machinery),
  * C3 `chartLocalAt_locally_conjugate_pow` — the substitution
    `s = (t - z₀) · g(t)^{1/k}` flattens the local form to `s ↦ s^k`,
  * C4 `IsHolomorphicAt.exists_local_kfold_of_ramified` — assembly:
    transport through charts to count simple preimages on the
    manifold side. -/

/-- **C1 (sorry).** Local power-series form at a point of order `k`:
the centred chart-local function factors as `(t - z₀)^k · g(t)` for
some analytic `g` with `g(z₀) ≠ 0`, where `z₀ = chartAt ℂ x x`.

Proof sketch: this is Mathlib's
`AnalyticAt.analyticOrderAt_eq_natCast` applied to the centred
chart-local difference `t ↦ chartLocalAt f x t - chartLocalAt f x z₀`
at `z₀`, with `n = k`.  Mathlib gives existence of analytic `g` with
`g(z₀) ≠ 0` such that the centred chart-local difference equals
`(t - z₀)^k • g(t)` near `z₀`. -/
theorem chartLocalAt_eq_pow_mul_of_order
    {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    [ChartedSpace ℂ X] [ChartedSpace ℂ Y]
    {f : X → Y} {x : X} (_hf : IsHolomorphicAt f x)
    {k : ℕ} (_hk : 0 < k) (_hramx : mapAnalyticOrderAt f x = k) :
    ∃ g : ℂ → ℂ, AnalyticAt ℂ g (chartAt ℂ x x) ∧
      g (chartAt ℂ x x) ≠ 0 ∧
      ∀ᶠ t in 𝓝 (chartAt ℂ x x),
        chartLocalAt f x t - chartLocalAt f x (chartAt ℂ x x) =
          (t - chartAt ℂ x x) ^ k * g t := by
  sorry

/-- **C2 (sorry).** Holomorphic `k`-th root of a locally
non-vanishing analytic function: if `g` is analytic at `z₀` with
`g(z₀) ≠ 0` and `k ≥ 1`, there is an analytic `h` near `z₀` with
`h(z)^k = g(z)` locally.

Proof sketch: in a neighborhood of `z₀` where `g` is non-vanishing,
choose a continuous (in fact analytic) branch of `log g` (using
`Complex.log` on a simply-connected nbhd of `g(z₀)` avoiding `0`).
Define `h := exp ((1/k) * log g)`.  Then `h^k = exp(log g) = g`.
Existence of the analytic log branch is `Complex.analyticAt_log` or
similar; the analytic combination gives `h`. -/
theorem analyticAt_kth_root_of_ne_zero
    {g : ℂ → ℂ} {z₀ : ℂ} (_hg : AnalyticAt ℂ g z₀) (_hg_ne : g z₀ ≠ 0)
    {k : ℕ} (_hk : 0 < k) :
    ∃ h : ℂ → ℂ, AnalyticAt ℂ h z₀ ∧ ∀ᶠ z in 𝓝 z₀, h z ^ k = g z := by
  sorry

/-- **C3 (sorry).** Local conjugacy to `s ↦ s^k`: combining C1 and
C2, near `chartAt ℂ x x` the chart-local function satisfies
`chartLocalAt f x t - chart(f x) = ((t - z₀) · h(t))^k` where
`h` is analytic with `h(z₀) ≠ 0`.  The substitution
`s := (t - z₀) · h(t)` is a holomorphic local change of coordinates
(it has nonzero derivative `h(z₀)` at `z₀`), under which
`chartLocalAt - chart(f x) = s^k`.

Proof sketch: take C1 to get `(t - z₀)^k · g(t)`; apply C2 to `g`
to get analytic `h` with `h^k = g`; expand
`(t - z₀)^k · h(t)^k = ((t - z₀) · h(t))^k`. -/
theorem chartLocalAt_locally_conjugate_pow
    {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    [ChartedSpace ℂ X] [ChartedSpace ℂ Y]
    {f : X → Y} {x : X} (_hf : IsHolomorphicAt f x)
    {k : ℕ} (_hk : 0 < k) (_hramx : mapAnalyticOrderAt f x = k) :
    ∃ h : ℂ → ℂ, AnalyticAt ℂ h (chartAt ℂ x x) ∧
      h (chartAt ℂ x x) ≠ 0 ∧
      ∀ᶠ t in 𝓝 (chartAt ℂ x x),
        chartLocalAt f x t - chartLocalAt f x (chartAt ℂ x x) =
          ((t - chartAt ℂ x x) * h t) ^ k := by
  sorry

/-- **C4 = Sub-leaf 3 (sorry).** Local `k`-fold structure at a
ramified point: combining C3 with the fact that `s ↦ s^k` has exactly
`k` simple preimages of any nonzero target, plus chart transport, the
fibre `U ∩ f⁻¹ {y}` near a ramified `x` of order `k` has exactly `k`
elements (all unramified) for every nearby `y ≠ f x`.

Proof sketch: by C3, near `x` (in chart coords) the map
`f - f x` looks like `((t - z₀) · h(t))^k`.  The `k` distinct `k`-th
roots of any nonzero `c` are distinct simple zeros of
`((t - z₀) · h(t))^k - c` (since `(t - z₀) · h(t)` is a local
biholomorphism near `z₀` — derivative `h(z₀) ≠ 0`).  Transport back
through `(chartAt ℂ x).symm` to obtain the `k` preimages on the
manifold side. -/
theorem IsHolomorphicAt.exists_local_kfold_of_ramified
    {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    [ChartedSpace ℂ X] [ChartedSpace ℂ Y]
    [IsManifold 𝓘(ℂ) ω X] [IsManifold 𝓘(ℂ) ω Y]
    {f : X → Y} (_hf : IsHolomorphic f) {x : X}
    {k : ℕ} (_hk_pos : 0 < k) (_hramx : mapAnalyticOrderAt f x = k) :
    ∃ U : Set X, IsOpen U ∧ x ∈ U ∧
    ∃ V : Set Y, IsOpen V ∧ f x ∈ V ∧
    ∀ y ∈ V, y ≠ f x →
    ∃ s : Finset X, s.card = k ∧ ↑s ⊆ U ∧
      (∀ x' ∈ s, f x' = y ∧ mapAnalyticOrderAt f x' = 1) ∧
      (∀ x' ∈ U, f x' = y → x' ∈ s) := by
  sorry

/-! ### Sub-leaf D: weighted fibre sum locally constant

Decomposition:

  * D1 `Set.Finite.exists_pairwiseDisjoint_open_nbhds` — given a
    finite set in a `T2Space`, there exist pairwise-disjoint open
    neighborhoods of each point (probably already in Mathlib),
  * D2 `eventually_fiber_subset_iUnion_nbhds` — properness of a
    continuous map on a compact source: for `y` close to `y₀`, the
    fibre `f⁻¹ {y}` is contained in any open `U ⊇ f⁻¹ {y₀}`,
  * D3 `weightedFiberSum_eventually_eq` — local conservation at a
    single base point `y₀`: there is a neighborhood `V` of `y₀` such
    that the weighted fibre sum is constant on `V`,
  * D4 `isHolomorphic_weightedFiberSum_isLocallyConstant` —
    assembly: D3 holding at every `y₀` is exactly local-constancy. -/

/-
**D1 (likely already in Mathlib).** Pairwise-disjoint open
neighborhoods of a finite set of points in a `T2Space`.  Stated here
as a sub-leaf placeholder; the actual proof should `exact` Mathlib's
`Set.Finite.exists_disjoint_iUnion_open` or similar.
-/
theorem Set.Finite.exists_pairwiseDisjoint_open_nbhds
    {X : Type*} [TopologicalSpace X] [T2Space X]
    {s : Set X} (_hs : s.Finite) :
    ∃ U : X → Set X,
      (∀ x ∈ s, IsOpen (U x) ∧ x ∈ U x) ∧
      Set.Pairwise s (fun x y => Disjoint (U x) (U y)) := by
  obtain ⟨U, hU⟩ := Set.Finite.t2_separation _hs;
  exact ⟨ U, fun x hx => ⟨ hU.1 x |>.2, hU.1 x |>.1 ⟩, hU.2 ⟩

/-- **D2 (sorry).** Properness on a compact source: for any open `U`
containing the fibre `f⁻¹ {y₀}`, there is a neighborhood `V` of `y₀`
such that for every `y ∈ V`, `f⁻¹ {y} ⊆ U`.

Proof sketch: `Uᶜ` is closed, hence compact (closed subset of compact
`X`).  Its image `f(Uᶜ)` is compact, hence closed (in `T2Space Y`),
and does not contain `y₀` (since `f⁻¹ {y₀} ⊆ U` ⇒ `Uᶜ ⊆ f⁻¹ {y₀}ᶜ`).
So `f(Uᶜ)ᶜ` is an open neighborhood of `y₀`; on it,
`y ∉ f(Uᶜ) ⇔ f⁻¹ {y} ∩ Uᶜ = ∅ ⇔ f⁻¹ {y} ⊆ U`. -/
theorem eventually_fiber_subset_of_compact_T2
    {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    [CompactSpace X] [T2Space Y]
    {f : X → Y} (_hf_cont : Continuous f) {y₀ : Y} {U : Set X}
    (_hU_open : IsOpen U) (_hU_fibre : f ⁻¹' {y₀} ⊆ U) :
    ∀ᶠ y in 𝓝 y₀, f ⁻¹' {y} ⊆ U := by
  have h_compact : IsCompact (f '' (Uᶜ)) := by
    exact IsCompact.image (isClosed_compl_iff.mpr _hU_open |> IsClosed.isCompact) _hf_cont
  have := h_compact.isClosed.isOpen_compl.mem_nhds
    (show y₀ ∉ f '' Uᶜ from fun ⟨x, hx, hy⟩ => hx <| _hU_fibre <| hy ▸ rfl)
  filter_upwards [this] with y hy using fun x hx => Classical.not_not.1 fun hx' => hy ⟨x, hx', hx⟩

/-- **D3 (sorry).** Local conservation at a single base point.
Combining D1, D2, sub-leaf B (at unramified preimages) and sub-leaf C
(at ramified preimages), the weighted fibre sum is constant on a
neighborhood of `y₀`.

Proof sketch: pick disjoint open `U_x ∋ x` for each `x ∈ f⁻¹ {y₀}`
(D1); shrink each `U_x` so sub-leaf B (if order = 1) or sub-leaf C
(if order ≥ 2) applies, with associated neighborhoods `V_x` of `y₀`
in `Y`.  Take `V := ⋂ V_x ∩ V'` where `V'` is the neighborhood from
D2 ensuring `f⁻¹ {y} ⊆ ⋃ U_x` for `y ∈ V'`.  On `V`:

  * `f⁻¹ {y}` decomposes as the disjoint union of `U_x ∩ f⁻¹ {y}`
    over `x ∈ f⁻¹ {y₀}`;
  * each `U_x ∩ f⁻¹ {y}` contributes exactly `mapAnalyticOrderAt f x`
    to the weighted sum (`1` for unramified by B, `k` for ramified
    of order `k` by C, regardless of whether `y = y₀` or not — see
    proof of leaf 7 in `BranchedDegree.lean` for the same kind of
    sum-via-Finset.sum bookkeeping).

So `weightedFiberSum y = ∑_{x ∈ f⁻¹ {y₀}} mapAnalyticOrderAt f x =
weightedFiberSum y₀` on `V`. -/
theorem weightedFiberSum_eventually_eq
    {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    [ChartedSpace ℂ X] [ChartedSpace ℂ Y]
    [IsManifold 𝓘(ℂ) ω X] [IsManifold 𝓘(ℂ) ω Y]
    [CompactSpace X] [T2Space X] [PreconnectedSpace X] [T2Space Y]
    {f : X → Y} (hf : IsHolomorphic f)
    (hnonconst : ¬ ∃ y₀ : Y, ∀ x, f x = y₀) (y₀ : Y) :
    ∀ᶠ y in 𝓝 y₀,
      ((isHolomorphic_finite_fiber hf hnonconst y).toFinset).sum
        (mapAnalyticOrderAt f) =
      ((isHolomorphic_finite_fiber hf hnonconst y₀).toFinset).sum
        (mapAnalyticOrderAt f) := by
  sorry

/-- **D4 = Sub-leaf 4 (sorry).** Local conservation: combining
leaves 2 and 3, the weighted fibre sum is locally constant on `Y`.

Proof sketch (assembling D3): apply D3 at every `y₀`; this is
literally the `IsLocallyConstant.iff_eventuallyEq`-form of
local-constancy. -/
theorem isHolomorphic_weightedFiberSum_isLocallyConstant
    {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    [ChartedSpace ℂ X] [ChartedSpace ℂ Y]
    [IsManifold 𝓘(ℂ) ω X] [IsManifold 𝓘(ℂ) ω Y]
    [CompactSpace X] [T2Space X] [PreconnectedSpace X] [T2Space Y]
    {f : X → Y} (hf : IsHolomorphic f)
    (hnonconst : ¬ ∃ y₀ : Y, ∀ x, f x = y₀) :
    IsLocallyConstant (fun y : Y =>
      ((isHolomorphic_finite_fiber hf hnonconst y).toFinset).sum
        (mapAnalyticOrderAt f)) := by
  sorry

/-- **Final assembly.** Combining sub-leaf 4 with preconnectedness of
`Y`: the weighted fibre sum is constant on `Y`. -/
theorem isHolomorphic_weightedFiberSum_const
    {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    [ChartedSpace ℂ X] [ChartedSpace ℂ Y]
    [IsManifold 𝓘(ℂ) ω X] [IsManifold 𝓘(ℂ) ω Y]
    [CompactSpace X] [T2Space X] [PreconnectedSpace X]
    [T2Space Y] [PreconnectedSpace Y]
    {f : X → Y} (hf : IsHolomorphic f)
    (hnonconst : ¬ ∃ y₀ : Y, ∀ x, f x = y₀) (y₁ y₂ : Y) :
    ((isHolomorphic_finite_fiber hf hnonconst y₁).toFinset).sum
      (mapAnalyticOrderAt f) =
    ((isHolomorphic_finite_fiber hf hnonconst y₂).toFinset).sum
      (mapAnalyticOrderAt f) :=
  (isHolomorphic_weightedFiberSum_isLocallyConstant hf hnonconst).apply_eq_of_preconnectedSpace
    y₁ y₂

end JacobianChallenge.Blueprint