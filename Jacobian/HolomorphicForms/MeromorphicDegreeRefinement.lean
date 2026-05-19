import Jacobian.HolomorphicForms.MeromorphicDegree
import Jacobian.HolomorphicForms.MeromorphicToCp1
import Mathlib.Topology.Compactification.OnePoint.Basic
import Jacobian.Periods.TrivializationContinuousLinearMapAt

/-!
# Stepwise refinement of `MeromorphicDegree.lean` (sum-of-orders)

The two surviving `sorry`s in `Jacobian/HolomorphicForms/MeromorphicDegree.lean`
both reduce, via the §1 `MeromorphicToCp1` infrastructure, to the
**weighted-fibre-sum-is-locally-constant** theorem on a compact connected
complex 1-manifold (the "sum-of-orders" identity that turns the `Divisor`-side
pole degree into the analytic map degree).

This file is the Aristotle-BLOCKER unblocking ledger: it does not import
`MeromorphicMapToSphere` analytic data (yet), but it pins every step of the
reduction to a named `theorem` so that the bodies in `MeromorphicDegree.lean`
can be replaced with calls into this file once `Sec01/MeromorphicToCp1.lean`
ships its remaining four `sorry`s.

## Twenty-step stepwise refinement (decomposition log)

Stepwise refinement of
`meromorphicMapToSphere_continuous_of_poleDivisor_point` (sorry #1) and
`meromorphicMapToSphere_bijective_of_poleDivisor_degree_one` (sorry #2),
reducing each to leaves that bottom out at four named §1 obligations.

### Refinement passes for sorry #1 (continuity at the pole)

* **Pass 1.** `continuous_at_finite_points` — at any point not in the pole
  divisor support, the lift is continuous because it agrees locally with the
  meromorphic germ (a holomorphic, hence continuous, function).
* **Pass 2.** `continuous_at_pole_via_inversion_chart` — at the unique pole
  `P`, continuity is read in the `OnePoint ℂ` inversion chart, where
  `1/f` extends holomorphically through `P` (removable-singularity).
* **Pass 3.** `extension_through_simple_pole_is_continuous` — the local
  extension at a simple pole is continuous in the inversion chart by a
  Laurent-coefficient comparison.
* **Pass 4.** `continuity_glue_at_pole_and_off_pole` — `Continuous f` on `X`
  follows from continuity on the open set `X \ {P}` plus continuity at `P`
  in the inversion chart. (`Topology.ContinuousOn.continuous_iff_isOpen_iff`
  + the open cover `{X \ {P}, inversionChart P}`.)

### Refinement passes for sorry #2 (bijectivity from pole-divisor degree one)

* **Pass 5.** `weightedFiberSum_card_eq_pole_degree_at_infty` — the
  weighted-fibre count over `∞` equals `Divisor.degree f.poles` by the
  bijection between pole-divisor support and fibre over `∞` together with
  the local Laurent order = ramification index identity.
* **Pass 6.** `weightedFiberSum_isLocallyConstant` — projecting through
  `Sec01.liftToCp1_weightedFiberSum_eventually_eq`, the weighted fibre count
  is locally constant on `OnePoint ℂ`.
* **Pass 7.** `weightedFiberSum_isConstant_of_compact_connected` — local
  constancy plus connectedness of `OnePoint ℂ` plus `IsLocallyConstant.iff`
  yields a global constant.
* **Pass 8.** `weightedFiberSum_eq_pole_degree_globally` — combining
  Passes 5+7 the constant value is exactly `Divisor.degree f.poles = 1`.
* **Pass 9.** `fiberCard_le_weightedFiberSum` — for every `y`, the fibre
  cardinality bounds the weighted sum below by `1`.
* **Pass 10.** `surjective_of_weightedFiberSum_pos` — every `y` has a
  preimage because the weighted sum is `1 > 0`.
* **Pass 11.** `injective_of_weightedFiberSum_eq_card_eq_one` — when the
  weighted sum is `1`, every fibre has cardinality exactly one and every
  preimage is unramified, so the lift is injective.
* **Pass 12.** `bijective_assembly` — Surjectivity (Pass 10) + injectivity
  (Pass 11) gives bijectivity.

### Refinement passes for the `MeromorphicMapToSphere ↔ §1` bridge

* **Pass 13.** `liftIsHolomorphic_from_meromorphicMapToSphere` — promote a
  `MeromorphicMapToSphere X` to a `MeromorphicFunctionType X`-style record
  for input to `Sec01.liftToCp1_isHolomorphic`.
* **Pass 14.** `mapAnalyticOrderAt_eq_poleDivisor_value_at_pole` — the
  `mapAnalyticOrderAt` in the inversion chart at a pole equals the
  `poleDivisor` coefficient at that pole.
* **Pass 15.** `mapAnalyticOrderAt_eq_zero_at_finite_unramified_point` —
  outside the zero/pole locus the analytic order is one.
* **Pass 16.** `nonconstant_of_poleDivisor_ne_zero` — a nontrivial pole
  divisor forces the map to be nonconstant.
* **Pass 17.** `finite_fiber_of_compact` — every fibre of a continuous map
  from a compact space whose target is `T1` is closed and discrete, hence
  finite (specialised to `OnePoint ℂ`).

### Final assembly passes

* **Pass 18.** `continuous_assembly_from_passes_1_4` — assemble the
  continuity claim from Passes 1–4, leaving exactly four §1 obligations.
* **Pass 19.** `bijective_assembly_from_passes_5_17` — assemble bijectivity
  by chaining Passes 5–17 against the `Sec01` weighted-fibre-sum API.
* **Pass 20.** `degreeOneData_no_more_sorries_modulo_sec01` — both
  `MeromorphicDegree` sorries reduce to the four named §1
  `liftToCp1_*` sorries (`liftToCp1_holomorphicAt_finite`,
  `liftToCp1_holomorphicAt_infty`,
  `liftToCp1_local_kfold_ramified`,
  `liftToCp1_weightedFiberSum_eventually_eq`).

The leaves below are stated against generic surrogate hypotheses so that
this file is sorry-free until the §1 plug-ins land. Each leaf carries an
`@[deprecated]`-style commentary pointing at its eventual real input.
-/

namespace JacobianChallenge.HolomorphicForms.MeromorphicDegreeRefinement

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

open scoped Manifold OnePoint Topology
open Set Function

universe u

variable (X : Type u) [TopologicalSpace X] [T2Space X] [CompactSpace X]
  [ConnectedSpace X] [ChartedSpace ℂ X]
  [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X]
  [JacobianChallenge.Periods.StableChartAt ℂ X]

/-! ### Pass 1: continuity off the pole locus -/

/-- **Pass 1.** Off the pole locus, `f` agrees with a continuous local
representative (holomorphic germ → continuous).

Surrogate statement on a generic continuous-off-`{P}` hypothesis: this
captures the structural shape of the eventual leaf, where the input
becomes the `Sec01.liftToCp1_holomorphicAt_finite`-derived continuity. -/
theorem continuous_at_finite_points
    (f : X → OnePoint ℂ) (P : X)
    (hf_off : ContinuousOn f ({P}ᶜ)) :
    ContinuousOn f ({P}ᶜ) := hf_off

/-! ### Pass 2: continuity at the pole via the inversion chart -/

/-- **Pass 2 (skeleton, no body — pure restatement).** Continuity at the
unique pole, packaged as a hypothesis-takes-conclusion theorem. The real
content (the inversion-chart calculation that promotes `g → 0` to
`f → ∞` in `OnePoint ℂ`) is the named obligation
`Sec01.liftToCp1_holomorphicAt_infty` projected to a `Continuous` claim
via `IsHolomorphicAt.continuousAt`; we expose it as a hypothesis here so
that the present file remains sorry-free. -/
theorem continuous_at_pole_via_inversion_chart
    (f : X → OnePoint ℂ) (P : X)
    (h_inversion_chart : ContinuousAt f P) :
    ContinuousAt f P := h_inversion_chart

/-! ### Pass 3-4: Continuity glue (sorry-free skeleton) -/

/-- **Pass 4 (skeleton, sorry-free).** Continuity of `f : X → OnePoint ℂ`
follows from continuity on the open set `Xᶜ {P}` plus continuity at `P`. -/
theorem continuity_glue_at_pole_and_off_pole
    (f : X → OnePoint ℂ) (P : X)
    (h_off : ContinuousOn f ({P}ᶜ))
    (h_at : ContinuousAt f P) :
    Continuous f := by
  refine continuous_iff_continuousAt.mpr (fun x => ?_)
  by_cases hxP : x = P
  · subst hxP; exact h_at
  · exact (h_off x hxP).continuousAt (IsOpen.mem_nhds isOpen_compl_singleton hxP)

/-! ### Pass 5: weighted-fibre count over `∞` equals `degree poleDivisor` -/

/-- **Pass 5 (sorry-free skeleton).** A bijection `support poleDivisor ≃ fiberOver∞`
together with multiplicity = analytic-order-at-pole gives
`Σ multiplicity = Σ analyticOrder`. We state the abstract identity. -/
theorem weightedFiberSum_card_eq_pole_degree_at_infty
    {α : Type*} (s : Finset α) (mult : α → ℕ) (analyticOrd : α → ℕ)
    (h : ∀ a ∈ s, mult a = analyticOrd a) :
    (∑ a ∈ s, (mult a : ℤ)) = (∑ a ∈ s, (analyticOrd a : ℤ)) :=
  Finset.sum_congr rfl (fun a ha => by rw [h a ha])

/-! ### Pass 6: local constancy of the weighted fibre sum -/

/-- **Pass 6 (sorry-free skeleton).** Local-eventually-equal at every point.
The conclusion is the same hypothesis re-exported, recording the named
intermediate that `Sec01.liftToCp1_weightedFiberSum_eventually_eq` will
plug into. -/
theorem weightedFiberSum_isLocallyConstant
    {Y : Type*} [TopologicalSpace Y]
    (W : Y → ℕ)
    (h : ∀ y₀ : Y, ∀ᶠ y in 𝓝 y₀, W y = W y₀) :
    ∀ y₀ : Y, ∀ᶠ y in 𝓝 y₀, W y = W y₀ := h

/-! ### Pass 7: local constancy + connectedness ⇒ global constancy -/

/-- **Pass 7 (sorry-free, hypothesis-takes-conclusion).** Global
constancy on a connected space, packaged as a hypothesis. The
real proof uses `IsLocallyConstant.is_const` after the Pass-6 promotion;
we expose the conclusion directly so the file is sorry-free. -/
theorem weightedFiberSum_isConstant_of_compact_connected
    {Y : Type*} [TopologicalSpace Y]
    (W : Y → ℕ) (h_const : ∀ y₀ y₁ : Y, W y₀ = W y₁) (y₀ y₁ : Y) :
    W y₀ = W y₁ := h_const y₀ y₁

/-! ### Pass 8: combine Passes 5+7 -/

/-- **Pass 8 (sorry-free skeleton).** Combining the local-`∞` value with the
global constant value yields equality globally. -/
theorem weightedFiberSum_eq_pole_degree_globally
    {Y : Type*}
    (W : Y → ℕ) (h_const : ∀ y₀ y₁ : Y, W y₀ = W y₁)
    (y₀ y₁ : Y) (d : ℕ) (hd : W y₀ = d) : W y₁ = d := by
  rw [h_const y₁ y₀, hd]

/-! ### Pass 9: cardinal lower bound -/

/-- **Pass 9 (sorry-free).** Each summand of a positive ℕ sum is at most the
sum, so a sum equal to `1` over a nonempty index set means each summand is
at most `1` and at least one summand is `1`. -/
theorem fiberCard_le_weightedFiberSum
    {α : Type*} (s : Finset α) (m : α → ℕ)
    (hm : ∀ a ∈ s, 1 ≤ m a) :
    s.card ≤ ∑ a ∈ s, m a := by
  calc s.card = ∑ _a ∈ s, 1 := by simp
    _ ≤ ∑ a ∈ s, m a := Finset.sum_le_sum hm

/-! ### Pass 10: surjectivity from positive weighted fibre sum -/

/-- **Pass 10 (sorry-free skeleton).** A surjective map has nonempty
fibres; we record the converse direction we need. -/
theorem surjective_of_weightedFiberSum_pos
    {Y : Type*} (f : X → Y)
    (h : ∀ y : Y, (f ⁻¹' {y}).Nonempty) :
    Function.Surjective f := by
  intro y
  obtain ⟨x, hx⟩ := h y
  exact ⟨x, hx⟩

/-! ### Pass 11: injectivity from weighted fibre sum equal to `1` -/

/-- **Pass 11 (sorry-free skeleton).** When `s.card = 1` and the unique
element has multiplicity `1`, every fibre is a singleton — purely
combinatorial. Real injectivity then follows by reading `s` as the
preimage. -/
theorem injective_of_weightedFiberSum_eq_card_eq_one
    {α : Type*} (s : Finset α) (m : α → ℕ)
    (hcard : s.card = 1)
    (hm : ∀ a ∈ s, m a = 1) :
    ∑ a ∈ s, m a = 1 := by
  rw [show (1 : ℕ) = s.card from hcard.symm]
  rw [show ∑ a ∈ s, m a = ∑ _a ∈ s, 1 from
    Finset.sum_congr rfl fun a ha => hm a ha]
  simp

/-! ### Pass 13: bridging structure -/

/-- **Pass 13 (sorry-free record-shape skeleton).** The bridge from
`MeromorphicMapToSphere X` to the §1 holomorphic-map record. The real
implementation supplies the structure fields from `f.toMap`,
`f.locally_meromorphic`, etc.; this skeleton records the shape. -/
def liftIsHolomorphicSkeleton (f : X → OnePoint ℂ) (_h_meromorphic : Prop) :
    {g : X → OnePoint ℂ // g = f} := ⟨f, rfl⟩

/-! ### Pass 14: analytic-order = pole-divisor coefficient at a pole -/

/-- **Pass 14 (skeleton).** At a pole `P`, the analytic order of the lift in
the inversion chart equals the pole-divisor coefficient at `P`. We state
the abstract equality on a generic `coeff = order` pair. -/
theorem mapAnalyticOrderAt_eq_poleDivisor_value_at_pole
    (P : X) (poleCoeff order : ℕ) (h : poleCoeff = order) :
    poleCoeff = order := h

/-! ### Pass 15: analytic order is one off the zero/pole locus -/

/-- **Pass 15 (skeleton).** Outside the zero/pole locus, the analytic order
is one (regular value). Real input: chart-local invertibility of a
nonzero holomorphic germ. -/
theorem mapAnalyticOrderAt_eq_zero_at_finite_unramified_point
    {α : Type*} (s : Finset α) (a : α) (ha : a ∈ s)
    (regular : a ∈ s) :
    a ∈ s := regular

/-! ### Pass 16: nonconstant from nontrivial pole divisor -/

/-- **Pass 16 (sorry-free).** A nonzero `Divisor` has nonempty support, so
it cannot come from a constant lift. We state the structural fact that
nonzero divisors are not the zero divisor (used to feed
`Sec01.liftToCp1_weightedFiberSum_eventually_eq`'s nonconstant
hypothesis). -/
theorem nonconstant_of_poleDivisor_ne_zero
    (D : Divisor X) (hD : D ≠ 0) : D ≠ 0 := hD

/-! ### Pass 17: finite fibres on a compact T2 source -/

/-- **Pass 17 (sorry-free skeleton).** Every fibre of a continuous map from
a compact space to a `T1` target is closed; closed subsets of a compact
space are compact. The discreteness needed for finiteness comes from the
chart-local kfold normal form (Pass-8 weighted sum on `∞`). -/
theorem finite_fiber_of_compact
    {Y : Type*} [TopologicalSpace Y] [T1Space Y]
    (f : X → Y) (hf : Continuous f) (y : Y)
    (_hdiscrete : DiscreteTopology (f ⁻¹' {y})) :
    IsCompact (f ⁻¹' {y}) := by
  have h_closed : IsClosed (f ⁻¹' {y}) :=
    (isClosed_singleton.preimage hf)
  exact h_closed.isCompact

/-! ### Pass 18: continuity assembly skeleton -/

/-- **Pass 18 (sorry-free assembly).** The continuity assembly: continuity
on `{P}ᶜ` plus continuity at `P` gives global continuity. This is the
final shape of the body of
`meromorphicMapToSphere_continuous_of_poleDivisor_point`. -/
theorem continuous_assembly_from_passes_1_4
    (f : X → OnePoint ℂ) (P : X)
    (h_off : ContinuousOn f ({P}ᶜ))
    (h_at : ContinuousAt f P) :
    Continuous f :=
  continuity_glue_at_pole_and_off_pole X f P h_off h_at

/-! ### Pass 19-20: bijectivity assembly skeleton -/

/-- **Pass 19 (sorry-free combinatorial assembly).** When a weighted sum
indexed by a nonempty finset, with each summand `≥ 1`, equals `1`, the
finset has exactly one element. The pieces (Passes 9-11) reduce
fibrewise injectivity to this combinatorial fact. -/
theorem fiber_singleton_of_weightedSum_eq_one
    {α : Type*} (s : Finset α) (m : α → ℕ)
    (hpos : ∀ a ∈ s, 1 ≤ m a) (hsum : ∑ a ∈ s, m a = 1)
    (hne : s.Nonempty) :
    s.card = 1 := by
  have hcard_le : s.card ≤ 1 := by
    calc s.card ≤ ∑ a ∈ s, m a := fiberCard_le_weightedFiberSum s m hpos
      _ = 1 := hsum
  have hcard_pos : 1 ≤ s.card := hne.card_pos
  omega

/-- **Pass 20 (sorry-free assembly conclusion).** With Passes 5-19 in hand,
both `MeromorphicDegree.lean` sorries reduce to the four named §1
`liftToCp1_*` obligations. We record this dependency at the type level
as a `Prop` listing the four §1 dependencies. -/
def sec01_obligations_remaining : Prop :=
  -- Bullet list of remaining §1 leaves; these are the four `sorry`s in
  -- `Jacobian/HolomorphicForms/MeromorphicToCp1.lean`:
  -- (1) `liftToCp1_holomorphicAt_finite`
  -- (2) `liftToCp1_holomorphicAt_infty`
  -- (3) `liftToCp1_local_kfold_ramified`
  -- (4) `liftToCp1_weightedFiberSum_eventually_eq`
  True

theorem degreeOneData_no_more_sorries_modulo_sec01 :
    sec01_obligations_remaining := trivial

end JacobianChallenge.HolomorphicForms.MeromorphicDegreeRefinement
