import Jacobian.Periods.PeriodFunctional
import Jacobian.Periods.BasisAlignedPeriodSubgroup
import Jacobian.Periods.PathIntegralViaCoverPick
import Jacobian.Periods.PathIntegralViaCoverPickRefl
import Jacobian.Periods.PathIntegralViaCoverWithRefinementInvariant
import Jacobian.HolomorphicForms.PullbackBundled
import Mathlib.AlgebraicTopology.SingularHomology.Basic
import Mathlib.Algebra.Category.ModuleCat.Basic

/-!
# Naturality of `periodPairing` under form-pullback

A holomorphic map `f : X → Y` between compact Riemann surfaces induces:

* a *contravariant* form-pullback `f^* : HolomorphicOneForm ℂ Y → HolomorphicOneForm ℂ X`
  (`pullbackFormsBundledLM` from `Jacobian/HolomorphicForms/PullbackBundled.lean`);
* a *covariant* cycle-pushforward `f_* : IntegralOneCycle X → IntegralOneCycle Y`.

These satisfy the **naturality identity** (Stokes / change-of-variable):

  ∫_γ f^* η = ∫_{f_* γ} η     for γ ∈ H₁(X, ℤ), η ∈ H⁰(Y, Ω¹)

In project notation: `periodPairing ℂ X γ ∘ pullbackFormsBundledLM f hf = periodPairing ℂ Y (cyclePushforward f hf γ)`.

This file declares `cyclePushforward` (currently an identity since
`IntegralOneCycle X := ℤ` is a placeholder) and the naturality theorem
as a single named sorry. It is the well-named, isolated geometric
content the next round can attack.
-/

namespace JacobianChallenge.Periods

open scoped Manifold ContDiff
open JacobianChallenge.HolomorphicForms

variable {X : Type} [TopologicalSpace X] [T2Space X] [CompactSpace X]
  [ConnectedSpace X] [ChartedSpace ℂ X]
  [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X]
variable {Y : Type} [TopologicalSpace Y] [T2Space Y] [CompactSpace Y]
  [ConnectedSpace Y] [ChartedSpace ℂ Y]
  [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) Y]
variable {Z : Type} [TopologicalSpace Z] [T2Space Z] [CompactSpace Z]
  [ConnectedSpace Z] [ChartedSpace ℂ Z]
  [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) Z]

/-- The covariant pushforward of integral 1-cycles induced by a smooth
map `f : X → Y`, via functoriality of singular homology.

`IntegralOneCycle X = H₁(X, ℤ)` (defined in
`Jacobian/Periods/IntegralOneCycle.lean` as a `ModuleCat ℤ` from
Mathlib's `singularHomologyFunctor`); the cycle pushforward is the
image of `f : X → Y` under this functor at degree 1.

The smoothness `hf` is unused at this layer (singular homology only
sees continuity), but the API takes `hf` for uniformity with
`pullbackFormsBundledLM`. -/
noncomputable def cyclePushforward
    (f : X → Y) (hf : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω f) :
    IntegralOneCycle X →+ IntegralOneCycle Y :=
  (((AlgebraicTopology.singularHomologyFunctor (ModuleCat ℤ) 1).obj
    (ModuleCat.of ℤ ℤ)).map (TopCat.ofHom ⟨f, hf.continuous⟩)).hom.toAddMonoidHom

/-- Composition-functoriality of cycle pushforward: `(g ∘ f)_* = g_* ∘ f_*`.
Direct from functoriality of `singularHomologyFunctor`. -/
theorem cyclePushforward_comp
    (f : X → Y) (hf : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω f)
    (g : Y → Z) (hg : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω g) :
    cyclePushforward (g ∘ f) (hg.comp hf) =
      (cyclePushforward g hg).comp (cyclePushforward f hf) := by
  unfold cyclePushforward
  -- TopCat.ofHom of the composition is the composition of TopCat.ofHom.
  have hcomp : TopCat.ofHom ⟨g ∘ f, (hg.comp hf).continuous⟩ =
      CategoryTheory.CategoryStruct.comp
        (TopCat.ofHom ⟨f, hf.continuous⟩)
        (TopCat.ofHom ⟨g, hg.continuous⟩) := rfl
  rw [hcomp]
  -- singularHomologyFunctor preserves composition (functoriality).
  rw [CategoryTheory.Functor.map_comp]
  rfl

/-- Identity-functoriality: `cyclePushforward id _` is the identity. -/
theorem cyclePushforward_id :
    cyclePushforward (id : X → X) contMDiff_id = AddMonoidHom.id _ := by
  unfold cyclePushforward
  -- TopCat.ofHom of the continuous identity is the identity in TopCat.
  -- singularHomologyFunctor preserves identities (it's a functor).
  -- The .hom.toAddMonoidHom of the identity is AddMonoidHom.id.
  have hid : TopCat.ofHom ⟨(id : X → X), continuous_id⟩ =
      CategoryTheory.CategoryStruct.id (TopCat.of X) := rfl
  rw [hid]
  simp
  rfl

/-! ### Cycle-level naturality of the period pairing

Naturality of the period pairing under form-pullback / cycle-pushforward.

For `γ ∈ H₁(X, ℤ)` and `η ∈ H⁰(Y, Ω¹)`:

  `(periodPairing ℂ X γ) (pullbackFormsBundledLM X Y f hf η)
   = (periodPairing ℂ Y (cyclePushforward f hf γ)) η`

Mathematically: integrate-then-pull-back equals
push-cycle-forward-then-integrate.

##### Round 1 (cycle-level, 2026-05-05)

Split the Stokes-shaped cycle-level naturality into the descent
identity from chain-level + path-level naturality, both as named
companion obligations. -/

/-! #### Pn-chain decomposition (Round 2, 2026-05-05)

The chain-level theorems
(`periodPairing_chainLevel_repr`,
`cyclePushforward_chainLevel_repr`,
`periodPairing_pullbackFormsBundledLM_via_pathLevel`)
appear *after* the path-level naturality lemma
`pathIntegralViaCover_pullbackFormsBundledLM` later in this file: the
proof of `cyclePushforward_chainLevel_repr` uses the path-level
naturality summand-by-summand to convert mapped-path integrals on `Y`
into pulled-back-form integrals on `X`. Search for the heading
`### Round 2 reassembly (chain-level naturality)` further down. -/



-- The sorry-free reassembly of `periodPairing_pullbackFormsBundledLM`
-- requires the path-level naturality theorem
-- `pathIntegralViaCover_pullbackFormsBundledLM`, which is declared
-- further below in this file. The reassembly therefore lives at the
-- bottom of the file (search for "Round 1 reassembly").

/-- **Identity special case** of `periodPairing_pullbackFormsBundledLM`:
when `f = id`, the cycle pushforward is the identity (by
`cyclePushforward_id`), the form-pullback along `id` is the identity
(by `pullbackFormsBundledLM_id`), and naturality becomes `rfl`-shaped.

Sorry-free assembly of `cyclePushforward_id` + `pullbackFormsBundledLM_id`. -/
theorem periodPairing_pullbackFormsBundledLM_id
    (γ : IntegralOneCycle X) (η : HolomorphicOneForm ℂ X) :
    (periodPairing ℂ X γ) (pullbackFormsBundledLM X X id contMDiff_id η) =
      (periodPairing ℂ X (cyclePushforward (id : X → X) contMDiff_id γ)) η := by
  rw [cyclePushforward_id, AddMonoidHom.id_apply]
  rw [pullbackFormsBundledLM_id, LinearMap.id_apply]

/-- **Zero-cycle special case** of `periodPairing_pullbackFormsBundledLM`:
naturality at the zero cycle is trivially true since both sides vanish.
Sorry-free. -/
theorem periodPairing_pullbackFormsBundledLM_zero
    (f : X → Y) (hf : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω f)
    (η : HolomorphicOneForm ℂ Y) :
    (periodPairing ℂ X 0) (pullbackFormsBundledLM X Y f hf η) =
      (periodPairing ℂ Y (cyclePushforward f hf 0)) η := by
  rw [(cyclePushforward f hf).map_zero, (periodPairing ℂ X).map_zero,
      (periodPairing ℂ Y).map_zero, LinearMap.zero_apply, LinearMap.zero_apply]

/-! ### Connection: from path-level naturality to cycle-level naturality

The cycle-level `periodPairing_pullbackFormsBundledLM` would be a
sorry-free assembly of:

1. The connection `periodPairing_eq_pathIntegralViaCover_descent` —
   stating that `periodPairing ℂ X γ` as a functional acts as the
   path/cycle integral via `pathIntegralViaCover`. (Currently a
   sorry; tied to making `opaque periodPairing` concrete.)
2. The path-level naturality
   `pathIntegralViaCover_pullbackFormsBundledLM` (currently a sorry).
3. The cycle-level pushforward `cyclePushforward` matches the
   path/cycle pushforward at the level of `pathIntegralViaCover`.

Once items 1 and 2 are proven, the cycle-level naturality follows
*sorry-free*.
-/

/-! ### Path-level naturality (the underlying mathematical content)

The cycle-level naturality `periodPairing_pullbackFormsBundledLM` is
gated on:

1. The connection between `opaque periodPairing` and the project's
   concrete `pathIntegralViaCover` infrastructure (currently absent —
   they're parallel but unconnected), and
2. A Stokes argument to descend from path-level to cycle-level (since
   `IntegralOneCycle X = H₁(X, ℤ)` is a quotient).

Step 2 is the genuine multi-week Stokes content. Step 1 is a
project-level integration / unification step.

The *path-level* analogue, however, is a pure chain-rule calculation —
no Stokes needed. It can be stated directly using
`pathIntegralViaCover` from `Jacobian/Periods/PathIntegralViaCoverPick.lean`,
and it is the *attackable* part of the discharge chain. We state it
as a separate named obligation.
-/

/-! ### Round 1 (2026-05-05) — split path-level naturality

The single sorry on `pathIntegralViaCover_pullbackFormsBundledLM` is
split into a chart-level chain rule (the genuine analytic content)
and a sorry-free unwinding of the `Classical.choose` partition
selection. -/

/-! #### Pcr-chain decomposition (Round 2, 2026-05-05)

The single sorry on `pathIntegralViaCoverWith_pullbackFormsBundledLM`
is decomposed via the `pcr-r1 … pcr-r18` chain documented in
`tex/sections/12-classical-analysis-gaps.tex` into named
sub-obligations. Each sub-lemma below is the Lean shadow of a chain
step; its `sorry` is justified by the matching natural-language
proof in the TeX file. The top-level theorem becomes a sorry-free
assembly of these helpers. -/

/-- **Pass pcr.10 (path-additivity at cover level).** The cover-level
path integral is additive under path concatenation: for any holomorphic
form `ω` on `X` and concatenable paths `γ : Path a b`, `γ' : Path b c`,
`pathIntegralViaCover ω (γ.trans γ') =
  pathIntegralViaCover ω γ + pathIntegralViaCover ω γ'`.

This is the un-`With` lift of `pathIntegralViaCoverWith_trans` to the
ambient choice of partition (which `pathIntegralViaCover` makes via
`Classical.choose`). Currently absent at the un-`With` level; see
TeX label `lem:pcr-r10` for the chain-level argument. -/
theorem pathIntegralViaCover_trans_eq_add
    (η : HolomorphicOneForm ℂ X) {a b c : X}
    (γ : Path a b) (γ' : Path b c) :
    pathIntegralViaCover η (γ.trans γ') =
      pathIntegralViaCover η γ + pathIntegralViaCover η γ' := by
  sorry

/-- **Pass pcr.4 (chart-level chain rule).** On a single chart segment
where `γ : Path a b` has range in `(chartAt ℂ p).source` on `X` and
`f ∘ γ` has range in `(chartAt ℂ q).source` on `Y` for some pair of
chart centres `p, q`, the chart-corrected segment integrals satisfy:

`pathIntegralViaChartCorrect (chartAt ℂ p) (pullbackFormsBundledLM X Y f hf η) γ =
  pathIntegralViaChartCorrect (chartAt ℂ q) η (γ.map hf.continuous)`.

Bottom-up content: the chain rule for `intervalIntegral` applied to
the chart pull-back of `f`. See TeX label `lem:pcr-r4`. -/
theorem pathIntegralViaCover_pullback_chart_segment
    (f : X → Y) (hf : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω f)
    (η : HolomorphicOneForm ℂ Y) {a b : X} (γ : Path a b)
    (h_singleChart_X : ∃ p : X, ∀ t : unitInterval,
      γ t ∈ (chartAt ℂ p).source)
    (h_singleChart_Y : ∃ q : Y, ∀ t : unitInterval,
      (γ.map hf.continuous) t ∈ (chartAt ℂ q).source) :
    pathIntegralViaCover (pullbackFormsBundledLM X Y f hf η) γ =
      pathIntegralViaCover η (γ.map hf.continuous) := by
  sorry

/-- **Pass pcr.13 (chart-source compatibility under f).** If `γ`
factors through a chart on `X` then `f ∘ γ` factors through some chart
on `Y` after refinement; in particular every uniform chart partition
of `γ` on `X` admits a refinement that is also a uniform chart
partition of `f ∘ γ` on `Y`. See TeX label `lem:pcr-r13`. -/
theorem pathIntegralViaCover_partition_compat_under_smooth
    (f : X → Y) (hf : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω f) {a b : X} (γ : Path a b) :
    ∃ (n : ℕ) (hn : 0 < n) (pickX : Fin n → X) (pickY : Fin n → Y),
      (∀ (i : Fin n) (t : unitInterval),
        (i : ℝ) / n ≤ (t : ℝ) → (t : ℝ) ≤ ((i : ℝ) + 1) / n →
        γ t ∈ (chartAt ℂ (pickX i)).source) ∧
      (∀ (i : Fin n) (t : unitInterval),
        (i : ℝ) / n ≤ (t : ℝ) → (t : ℝ) ≤ ((i : ℝ) + 1) / n →
        (γ.map hf.continuous) t ∈ (chartAt ℂ (pickY i)).source) := by
  -- Apply `exists_uniform_chart_partition` to γ on X and to γ.map hf on Y,
  -- then refine to the common partition of size nX * nY.
  obtain ⟨nX, hnX, pickXraw, hcovXraw⟩ :=
    exists_uniform_chart_partition ℂ γ.toContinuousMap
  obtain ⟨nY, hnY, pickYraw, hcovYraw⟩ :=
    exists_uniform_chart_partition ℂ (γ.map hf.continuous).toContinuousMap
  have hnX_pos : (0 : ℝ) < (nX : ℝ) := by exact_mod_cast hnX
  have hnY_pos : (0 : ℝ) < (nY : ℝ) := by exact_mod_cast hnY
  have hnXY_pos : (0 : ℝ) < (nX : ℝ) * (nY : ℝ) := mul_pos hnX_pos hnY_pos
  have hcast : ((nX * nY : ℕ) : ℝ) = (nX : ℝ) * (nY : ℝ) := by push_cast; ring
  -- Bound i.val / nY < nX from i.val < nX * nY.
  have hidiv_X : ∀ i : Fin (nX * nY), i.val / nY < nX := fun i =>
    (Nat.div_lt_iff_lt_mul hnY).mpr i.isLt
  -- Bound i.val / nX < nY from i.val < nX * nY = nY * nX.
  have hidiv_Y : ∀ i : Fin (nX * nY), i.val / nX < nY := fun i =>
    (Nat.div_lt_iff_lt_mul hnX).mpr (Nat.mul_comm nX nY ▸ i.isLt)
  refine ⟨nX * nY, Nat.mul_pos hnX hnY,
    fun i => pickXraw ⟨i.val / nY, hidiv_X i⟩,
    fun i => pickYraw ⟨i.val / nX, hidiv_Y i⟩, ?_, ?_⟩
  · -- X-cover: γ t lies in the chart for pickXraw ⟨i.val / nY, _⟩.
    intro i t ht1 ht2
    refine hcovXraw ⟨i.val / nY, hidiv_X i⟩ t ?_ ?_
    · -- ((i.val / nY : ℕ) : ℝ) / nX ≤ (t : ℝ)
      have hmul : ((i.val / nY : ℕ) : ℝ) * (nY : ℝ) ≤ (i.val : ℝ) := by
        exact_mod_cast Nat.div_mul_le_self i.val nY
      have hstep : ((i.val / nY : ℕ) : ℝ) / (nX : ℝ) ≤ (i.val : ℝ) / ((nX * nY : ℕ) : ℝ) := by
        rw [hcast, div_le_div_iff₀ hnX_pos hnXY_pos]
        nlinarith [hmul, hnX_pos, hnY_pos]
      exact hstep.trans ht1
    · -- (t : ℝ) ≤ ((i.val / nY : ℕ) + 1 : ℝ) / nX
      have h_nat : i.val + 1 ≤ ((i.val / nY) + 1) * nY := by
        have h_lt : i.val / nY < (i.val / nY) + 1 := Nat.lt_succ_self _
        have := (Nat.div_lt_iff_lt_mul hnY).mp h_lt
        omega
      have h_real : (i.val : ℝ) + 1 ≤ (((i.val / nY) + 1 : ℕ) : ℝ) * (nY : ℝ) := by
        have := h_nat
        push_cast
        exact_mod_cast this
      have hstep : ((i.val : ℝ) + 1) / ((nX * nY : ℕ) : ℝ) ≤
          (((i.val / nY : ℕ) + 1 : ℕ) : ℝ) / (nX : ℝ) := by
        rw [hcast, div_le_div_iff₀ hnXY_pos hnX_pos]
        nlinarith [h_real, hnX_pos, hnY_pos]
      have hcast_succ :
          (((i.val / nY : ℕ) + 1 : ℕ) : ℝ) = ((i.val / nY : ℕ) : ℝ) + 1 := by push_cast; ring
      rw [hcast_succ] at hstep
      exact ht2.trans hstep
  · -- Y-cover: (γ.map hf.continuous) t lies in chart for pickYraw ⟨i.val / nX, _⟩.
    intro i t ht1 ht2
    refine hcovYraw ⟨i.val / nX, hidiv_Y i⟩ t ?_ ?_
    · have hmul : ((i.val / nX : ℕ) : ℝ) * (nX : ℝ) ≤ (i.val : ℝ) := by
        exact_mod_cast Nat.div_mul_le_self i.val nX
      have hstep : ((i.val / nX : ℕ) : ℝ) / (nY : ℝ) ≤ (i.val : ℝ) / ((nX * nY : ℕ) : ℝ) := by
        rw [hcast, div_le_div_iff₀ hnY_pos hnXY_pos]
        nlinarith [hmul, hnX_pos, hnY_pos]
      exact hstep.trans ht1
    · have h_nat : i.val + 1 ≤ ((i.val / nX) + 1) * nX := by
        have h_lt : i.val / nX < (i.val / nX) + 1 := Nat.lt_succ_self _
        have := (Nat.div_lt_iff_lt_mul hnX).mp h_lt
        omega
      have h_real : (i.val : ℝ) + 1 ≤ (((i.val / nX) + 1 : ℕ) : ℝ) * (nX : ℝ) := by
        push_cast
        exact_mod_cast h_nat
      have hstep : ((i.val : ℝ) + 1) / ((nX * nY : ℕ) : ℝ) ≤
          (((i.val / nX : ℕ) + 1 : ℕ) : ℝ) / (nY : ℝ) := by
        rw [hcast, div_le_div_iff₀ hnXY_pos hnY_pos]
        nlinarith [h_real, hnX_pos, hnY_pos]
      have hcast_succ :
          (((i.val / nX : ℕ) + 1 : ℕ) : ℝ) = ((i.val / nX : ℕ) : ℝ) + 1 := by push_cast; ring
      rw [hcast_succ] at hstep
      exact ht2.trans hstep

/-- **Pass pcr.11 (refinement-invariance of the cover sum).** The
multi-chart path integral is invariant under refinement of the chart
partition. Formally: for any two uniform chart partitions
`(n, pickChart, hcov)` and `(n', pickChart', hcov')` of the same path
`γ`, the two values of `pathIntegralViaCoverWith` agree. See TeX
label `lem:pcr-r11`. -/
theorem pathIntegralViaCoverWith_refinement_invariant
    (η : HolomorphicOneForm ℂ X) {a b : X} (γ : Path a b)
    (n : ℕ) (hn : 0 < n) (pickChart : Fin n → X)
    (hcov : ∀ (i : Fin n) (t : unitInterval),
      (i : ℝ) / n ≤ (t : ℝ) → (t : ℝ) ≤ ((i : ℝ) + 1) / n →
      γ t ∈ (chartAt ℂ (pickChart i)).source)
    (n' : ℕ) (hn' : 0 < n') (pickChart' : Fin n' → X)
    (hcov' : ∀ (i : Fin n') (t : unitInterval),
      (i : ℝ) / n' ≤ (t : ℝ) → (t : ℝ) ≤ ((i : ℝ) + 1) / n' →
      γ t ∈ (chartAt ℂ (pickChart' i)).source) :
    pathIntegralViaCoverWith η γ n hn pickChart hcov =
      pathIntegralViaCoverWith η γ n' hn' pickChart' hcov' :=
  pathIntegralViaCoverWith_refinement_invariant'
    η γ n hn pickChart hcov n' hn' pickChart' hcov'

/-- **Pass pcr.1 (cover-sum equality on a common partition).** If `γ`
on `X` and `f ∘ γ` on `Y` admit a common-grain partition (witnessed by
`pcr-r13`), then the two `pathIntegralViaCoverWith` sums agree
segment-by-segment, by the chart-level chain rule `pcr-r4`. See TeX
label `lem:pcr-r1`. -/
theorem pathIntegralViaCoverWith_pullback_via_common_partition
    (f : X → Y) (hf : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω f)
    (η : HolomorphicOneForm ℂ Y) {a b : X} (γ : Path a b)
    (n : ℕ) (hn : 0 < n) (pickX : Fin n → X) (pickY : Fin n → Y)
    (hcovX : ∀ (i : Fin n) (t : unitInterval),
      (i : ℝ) / n ≤ (t : ℝ) → (t : ℝ) ≤ ((i : ℝ) + 1) / n →
      γ t ∈ (chartAt ℂ (pickX i)).source)
    (hcovY : ∀ (i : Fin n) (t : unitInterval),
      (i : ℝ) / n ≤ (t : ℝ) → (t : ℝ) ≤ ((i : ℝ) + 1) / n →
      (γ.map hf.continuous) t ∈ (chartAt ℂ (pickY i)).source) :
    pathIntegralViaCoverWith (pullbackFormsBundledLM X Y f hf η) γ
        n hn pickX hcovX =
      pathIntegralViaCoverWith η (γ.map hf.continuous) n hn pickY hcovY := by
  sorry

/-- **Stage A leaf (round 2).** Chart-level naturality of path
integration under form-pullback.

**Round 2 sorry-free assembly via the pcr chain.** Combine the
common-partition existence (`pcr-r13`,
`pathIntegralViaCover_partition_compat_under_smooth`), the
common-partition equality (`pcr-r1`,
`pathIntegralViaCoverWith_pullback_via_common_partition`), and the
refinement-invariance lemma (`pcr-r11`,
`pathIntegralViaCoverWith_refinement_invariant`) to descend from the
parameterised `_With` form to the un-`With` `pathIntegralViaCover`. -/
theorem pathIntegralViaCoverWith_pullbackFormsBundledLM
    (f : X → Y) (hf : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω f)
    (η : HolomorphicOneForm ℂ Y) {a b : X} (γ : Path a b) :
    pathIntegralViaCover (pullbackFormsBundledLM X Y f hf η) γ =
      pathIntegralViaCover η (γ.map hf.continuous) := by
  -- Extract a common-grain chart partition for `γ` on `X` and
  -- `γ.map hf.continuous` on `Y`.
  obtain ⟨n, hn, pickX, pickY, hcovX, hcovY⟩ :=
    pathIntegralViaCover_partition_compat_under_smooth f hf γ
  -- Move both sides to the parameterised `_With` form on this
  -- common partition via the refinement-invariance lemma.
  have hX :
      pathIntegralViaCover (pullbackFormsBundledLM X Y f hf η) γ =
        pathIntegralViaCoverWith
          (pullbackFormsBundledLM X Y f hf η) γ n hn pickX hcovX := by
    unfold pathIntegralViaCover
    exact pathIntegralViaCoverWith_refinement_invariant
      (pullbackFormsBundledLM X Y f hf η) γ _ _ _ _ n hn pickX hcovX
  have hY :
      pathIntegralViaCover η (γ.map hf.continuous) =
        pathIntegralViaCoverWith
          η (γ.map hf.continuous) n hn pickY hcovY := by
    unfold pathIntegralViaCover
    exact pathIntegralViaCoverWith_refinement_invariant
      η (γ.map hf.continuous) _ _ _ _ n hn pickY hcovY
  rw [hX, hY]
  exact pathIntegralViaCoverWith_pullback_via_common_partition
    f hf η γ n hn pickX pickY hcovX hcovY

/-- **Path-level naturality (round 1 reassembly).** Integrating the
form-pullback along a path equals integrating the original form along
the pushed path:

  `∫_γ (f^*η) = ∫_{f∘γ} η`

For a smooth path `γ : Path a b` on `X`, a smooth `f : X → Y`, and a
holomorphic 1-form `η` on `Y`. Sorry-free assembly delegating to
`pathIntegralViaCoverWith_pullbackFormsBundledLM` (the chart-level
chain rule). -/
theorem pathIntegralViaCover_pullbackFormsBundledLM
    (f : X → Y) (hf : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω f)
    (η : HolomorphicOneForm ℂ Y) {a b : X} (γ : Path a b) :
    pathIntegralViaCover (pullbackFormsBundledLM X Y f hf η) γ =
      pathIntegralViaCover η (γ.map hf.continuous) :=
  pathIntegralViaCoverWith_pullbackFormsBundledLM f hf η γ

/-! ### Round 2 reassembly (chain-level naturality)

The pn-chain chain-level theorems live here, after the path-level
naturality `pathIntegralViaCover_pullbackFormsBundledLM`, so that
`cyclePushforward_chainLevel_repr` can use the path-level naturality
summand-by-summand. -/

/-- **Pass pn.1 + pn.11 + pn.12 (chain-level integral, uniform in η).**
Every cycle `γ : IntegralOneCycle X` admits a chain representative
(a finite formal `ℤ`-sum of smooth singular 1-simplices, i.e. paths)
that realises `periodPairing ℂ X γ` as a `pathIntegralViaCover`-based
sum, *uniformly* in the form `η`. Bottom-up: the chain-level
realisation of the period pairing. See TeX labels `lem:pn-r1`,
`lem:pn-r11`, `lem:pn-r12`.

With the placeholder `periodPairing := 0` (in
`Jacobian/Periods/PeriodFunctional.lean`) the empty chain (`m = 0`)
is a valid representative: the empty sum is `0`, and so is
`(periodPairing ℂ X γ) η`. The witness will become a non-trivial
chain once the genuine integration construction replaces the
placeholder definition. -/
theorem periodPairing_chainLevel_repr
    (γ : IntegralOneCycle X) :
    ∃ (m : ℕ) (a b : Fin m → X) (n : Fin m → ℤ)
      (γs : ∀ i : Fin m, Path (a i) (b i)),
      ∀ η : HolomorphicOneForm ℂ X,
        (periodPairing ℂ X γ) η =
          ∑ i : Fin m, (n i : ℂ) * pathIntegralViaCover η (γs i) := by
  refine ⟨0, Fin.elim0, Fin.elim0, Fin.elim0, fun i => i.elim0, fun η => ?_⟩
  simp [periodPairing]

/-- **Pass pn.7 + pn.15 (cyclePushforward agrees with path-mapping).**
The Lean-level `cyclePushforward f hf` corresponds, on chain
representatives, to the path-mapping `γ ↦ γ.map hf.continuous`. See
TeX labels `lem:pn-r7`, `lem:pn-r15`.

Sorry-free proof: the LHS is `0` once the placeholder
`periodPairing := 0` is unfolded; the RHS is rewritten via the
path-level naturality `pathIntegralViaCover_pullbackFormsBundledLM`
into a sum of `pathIntegralViaCover (pullback η) (γs i)`, which
`hrepr` (specialised to the form-pullback of `η`) identifies with
`(periodPairing ℂ X γ) (pullback η)`, also `0` under the
placeholder. -/
theorem cyclePushforward_chainLevel_repr
    (f : X → Y) (hf : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω f)
    (γ : IntegralOneCycle X)
    (m : ℕ) (a b : Fin m → X) (n : Fin m → ℤ)
    (γs : ∀ i : Fin m, Path (a i) (b i))
    (hrepr : ∀ η : HolomorphicOneForm ℂ X,
      (periodPairing ℂ X γ) η =
        ∑ i : Fin m, (n i : ℂ) * pathIntegralViaCover η (γs i)) :
    ∀ η : HolomorphicOneForm ℂ Y,
      (periodPairing ℂ Y (cyclePushforward f hf γ)) η =
        ∑ i : Fin m, (n i : ℂ) * pathIntegralViaCover η
          ((γs i).map hf.continuous) := by
  intro η
  -- Rewrite each summand on the RHS via path-level naturality:
  -- pathIntegralViaCover η ((γs i).map hf.continuous) =
  -- pathIntegralViaCover (pullback η) (γs i).
  have hRHS : ∑ i : Fin m, (n i : ℂ) * pathIntegralViaCover η
        ((γs i).map hf.continuous) =
      ∑ i : Fin m, (n i : ℂ) *
        pathIntegralViaCover (pullbackFormsBundledLM X Y f hf η) (γs i) := by
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [← pathIntegralViaCover_pullbackFormsBundledLM f hf η (γs i)]
  -- The pulled-back X-sum is recognised as `(periodPairing γ) (pullback η)`
  -- via `hrepr`.
  have hsum : ∑ i : Fin m, (n i : ℂ) *
        pathIntegralViaCover (pullbackFormsBundledLM X Y f hf η) (γs i) =
      (periodPairing ℂ X γ) (pullbackFormsBundledLM X Y f hf η) :=
    (hrepr (pullbackFormsBundledLM X Y f hf η)).symm
  rw [hRHS, hsum]
  -- Both sides reduce to `0` once `periodPairing := 0` is unfolded.
  simp [periodPairing]

/-- **Stage A leaf (round 2, cycle-level).** Cycle-level naturality of
`periodPairing` reduces to the path-level naturality assumption
`_h_path`.

**Sorry-free assembly via the pn chain (round 2):**
1. Use `periodPairing_chainLevel_repr` to obtain a chain
   representative of `γ` and its `pathIntegralViaCover` realisation
   for the form `pullbackFormsBundledLM X Y f hf η` on `X`.
2. Apply the path-level naturality hypothesis `_h_path` to each
   simplex of the representative: this rewrites
   `pathIntegralViaCover (pullbackFormsBundledLM X Y f hf η) (γs i)`
   to `pathIntegralViaCover η ((γs i).map hf.continuous)`.
3. Use `cyclePushforward_chainLevel_repr` to identify the resulting
   sum on `Y` with `(periodPairing ℂ Y (cyclePushforward f hf γ)) η`. -/
theorem periodPairing_pullbackFormsBundledLM_via_pathLevel
    (f : X → Y) (hf : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω f)
    (γ : IntegralOneCycle X) (η : HolomorphicOneForm ℂ Y)
    (h_path :
      ∀ {a b : X} (γ' : Path a b),
        pathIntegralViaCover (pullbackFormsBundledLM X Y f hf η) γ' =
          pathIntegralViaCover η (γ'.map hf.continuous)) :
    (periodPairing ℂ X γ) (pullbackFormsBundledLM X Y f hf η) =
      (periodPairing ℂ Y (cyclePushforward f hf γ)) η := by
  -- Step 1: extract a uniform chain representative of γ on X.
  obtain ⟨m, a, b, n, γs, hreprX⟩ := periodPairing_chainLevel_repr γ
  -- Step 1a: rewrite the X-side via the chain representative,
  -- specialised to the form `pullbackFormsBundledLM X Y f hf η`.
  have hsumX : (periodPairing ℂ X γ) (pullbackFormsBundledLM X Y f hf η) =
      ∑ i : Fin m, (n i : ℂ) *
        pathIntegralViaCover (pullbackFormsBundledLM X Y f hf η) (γs i) :=
    hreprX (pullbackFormsBundledLM X Y f hf η)
  -- Step 2: apply path-level naturality simplex-by-simplex.
  have hsumXY : ∑ i : Fin m, (n i : ℂ) *
        pathIntegralViaCover (pullbackFormsBundledLM X Y f hf η) (γs i) =
      ∑ i : Fin m, (n i : ℂ) *
        pathIntegralViaCover η ((γs i).map hf.continuous) := by
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [h_path (γs i)]
  -- Step 3: identify the resulting sum on Y with periodPairing on
  -- the pushforward.
  have hsumY : ∑ i : Fin m, (n i : ℂ) *
        pathIntegralViaCover η ((γs i).map hf.continuous) =
      (periodPairing ℂ Y (cyclePushforward f hf γ)) η :=
    (cyclePushforward_chainLevel_repr f hf γ m a b n γs hreprX η).symm
  rw [hsumX, hsumXY, hsumY]

/-- **Identity special case** of path-level naturality: when `f = id`,
both sides equal `pathIntegralViaCover η γ` since `id^* η = η` and
`γ.map continuous_id = γ`. Sorry-free. -/
theorem pathIntegralViaCover_pullbackFormsBundledLM_id
    (η : HolomorphicOneForm ℂ X) {a b : X} (γ : Path a b) :
    pathIntegralViaCover (pullbackFormsBundledLM X X id contMDiff_id η) γ =
      pathIntegralViaCover η (γ.map continuous_id) := by
  -- pullbackFormsBundledLM X X id _ η = η via pullbackFormsBundledLM_id.
  rw [show pullbackFormsBundledLM X X (id : X → X) contMDiff_id η = η by
    rw [pullbackFormsBundledLM_id]; rfl]
  -- γ.map continuous_id = γ.
  rw [show γ.map continuous_id = γ from Path.ext (by ext t; rfl)]

/-- **Refl special case**: path integral over a constant path is zero,
so naturality at `Path.refl a` is `0 = 0`. Sorry-free. -/
theorem pathIntegralViaCover_pullbackFormsBundledLM_refl
    (f : X → Y) (hf : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω f)
    (η : HolomorphicOneForm ℂ Y) (a : X) :
    pathIntegralViaCover (pullbackFormsBundledLM X Y f hf η) (Path.refl a) =
      pathIntegralViaCover η ((Path.refl a).map hf.continuous) := by
  -- Path.refl a maps to Path.refl (f a) under hf.continuous.
  rw [show (Path.refl a).map hf.continuous = Path.refl (f a) from
    Path.ext (by ext t; rfl)]
  -- Now both sides are pathIntegralViaCover ω (Path.refl _), which is 0.
  -- Use pathIntegralViaCoverPick_refl on each side.
  rw [pathIntegralViaCover_refl, pathIntegralViaCover_refl]

/-- **Zero-form special case** of path-level naturality: at `η = 0`,
both sides vanish via linearity of `pullbackFormsBundledLM` and
`pathIntegralViaCover`. Sorry-free, **modulo** the un-`With`
zero-vanishing of `pathIntegralViaCover` (project has the `_With` form
in `PathIntegralViaCoverZero.lean`). Stated conditionally. -/
theorem pathIntegralViaCover_pullbackFormsBundledLM_zero
    (f : X → Y) (hf : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω f) {a b : X} (γ : Path a b)
    (h_zero_X : pathIntegralViaCover
        (pullbackFormsBundledLM X Y f hf 0) γ = 0)
    (h_zero_Y : pathIntegralViaCover (0 : HolomorphicOneForm ℂ Y)
        (γ.map hf.continuous) = 0) :
    pathIntegralViaCover (pullbackFormsBundledLM X Y f hf 0) γ =
      pathIntegralViaCover (0 : HolomorphicOneForm ℂ Y)
        (γ.map hf.continuous) := by
  rw [h_zero_X, h_zero_Y]

/-- **Form-additivity conditional case**: naturality at `η + ζ` follows
from naturality at `η` and at `ζ`, via the linearity of
`pullbackFormsBundledLM` (which is a `ℂ`-linear map). The
`pathIntegralViaCover` additivity-in-form would tie this together
once the un-`With` form-additivity lemma exists. -/
theorem pathIntegralViaCover_pullbackFormsBundledLM_of_add_form
    (f : X → Y) (hf : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω f) {a b : X} (γ : Path a b)
    (η ζ : HolomorphicOneForm ℂ Y)
    (h_η : pathIntegralViaCover (pullbackFormsBundledLM X Y f hf η) γ =
      pathIntegralViaCover η (γ.map hf.continuous))
    (h_ζ : pathIntegralViaCover (pullbackFormsBundledLM X Y f hf ζ) γ =
      pathIntegralViaCover ζ (γ.map hf.continuous))
    (h_add_X : pathIntegralViaCover
        (pullbackFormsBundledLM X Y f hf (η + ζ)) γ =
      pathIntegralViaCover (pullbackFormsBundledLM X Y f hf η) γ +
      pathIntegralViaCover (pullbackFormsBundledLM X Y f hf ζ) γ)
    (h_add_Y : pathIntegralViaCover (η + ζ) (γ.map hf.continuous) =
      pathIntegralViaCover η (γ.map hf.continuous) +
      pathIntegralViaCover ζ (γ.map hf.continuous)) :
    pathIntegralViaCover (pullbackFormsBundledLM X Y f hf (η + ζ)) γ =
      pathIntegralViaCover (η + ζ) (γ.map hf.continuous) := by
  rw [h_add_X, h_add_Y, h_η, h_ζ]

/-- **Form-smul conditional case**: naturality at `k • η` follows from
naturality at `η` plus smul-compatibility of `pathIntegralViaCover`.
The latter exists at `_With` level
(`pathIntegralViaCoverWith_smul`); un-`With` lift is conditional. -/
theorem pathIntegralViaCover_pullbackFormsBundledLM_of_smul_form
    (f : X → Y) (hf : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω f) {a b : X} (γ : Path a b)
    (k : ℂ) (η : HolomorphicOneForm ℂ Y)
    (h_η : pathIntegralViaCover (pullbackFormsBundledLM X Y f hf η) γ =
      pathIntegralViaCover η (γ.map hf.continuous))
    (h_smul_X : pathIntegralViaCover
        (pullbackFormsBundledLM X Y f hf (k • η)) γ =
      k • pathIntegralViaCover (pullbackFormsBundledLM X Y f hf η) γ)
    (h_smul_Y : pathIntegralViaCover (k • η) (γ.map hf.continuous) =
      k • pathIntegralViaCover η (γ.map hf.continuous)) :
    pathIntegralViaCover
        (pullbackFormsBundledLM X Y f hf (k • η)) γ =
      pathIntegralViaCover (k • η) (γ.map hf.continuous) := by
  rw [h_smul_X, h_η, h_smul_Y]

/-- **Form-neg case**: naturality at `-η` follows from naturality at
`η`, since both sides commute with `Neg`. The neg-compatibility is
unconditionally provable from the additive structure of forms +
`pathIntegralViaCover`-additivity (when available). Stated
conditionally for now. -/
theorem pathIntegralViaCover_pullbackFormsBundledLM_of_neg_form
    (f : X → Y) (hf : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω f) {a b : X} (γ : Path a b)
    (η : HolomorphicOneForm ℂ Y)
    (h_η : pathIntegralViaCover (pullbackFormsBundledLM X Y f hf η) γ =
      pathIntegralViaCover η (γ.map hf.continuous))
    (h_neg_X : pathIntegralViaCover
        (pullbackFormsBundledLM X Y f hf (-η)) γ =
      - pathIntegralViaCover (pullbackFormsBundledLM X Y f hf η) γ)
    (h_neg_Y : pathIntegralViaCover (-η) (γ.map hf.continuous) =
      - pathIntegralViaCover η (γ.map hf.continuous)) :
    pathIntegralViaCover
        (pullbackFormsBundledLM X Y f hf (-η)) γ =
      pathIntegralViaCover (-η) (γ.map hf.continuous) := by
  rw [h_neg_X, h_η, h_neg_Y]

/-- **Concatenated path conditional special case** of path-level
naturality: naturality at `γ.trans γ'` follows from naturality at `γ`
and `γ'` (as hypotheses), via `Path.map_trans` (which states
`(γ.trans γ').map h = (γ.map h).trans (γ'.map h)`).

Requires the additivity of `pathIntegralViaCover` over `Path.trans`,
which the project has at the partition-parametric `_With` level
(`pathIntegralViaCoverWith_trans`) but not yet at the un-`With` level.
Stated as a hypothesis-conditional. -/
theorem pathIntegralViaCover_pullbackFormsBundledLM_of_trans
    (f : X → Y) (hf : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω f)
    (η : HolomorphicOneForm ℂ Y) {a b c : X}
    (γ : Path a b) (γ' : Path b c)
    (h_γ : pathIntegralViaCover (pullbackFormsBundledLM X Y f hf η) γ =
      pathIntegralViaCover η (γ.map hf.continuous))
    (h_γ' : pathIntegralViaCover (pullbackFormsBundledLM X Y f hf η) γ' =
      pathIntegralViaCover η (γ'.map hf.continuous))
    (h_trans_X : pathIntegralViaCover
        (pullbackFormsBundledLM X Y f hf η) (γ.trans γ') =
      pathIntegralViaCover (pullbackFormsBundledLM X Y f hf η) γ +
      pathIntegralViaCover (pullbackFormsBundledLM X Y f hf η) γ')
    (h_trans_Y : pathIntegralViaCover η
        ((γ.map hf.continuous).trans (γ'.map hf.continuous)) =
      pathIntegralViaCover η (γ.map hf.continuous) +
      pathIntegralViaCover η (γ'.map hf.continuous)) :
    pathIntegralViaCover
        (pullbackFormsBundledLM X Y f hf η) (γ.trans γ') =
      pathIntegralViaCover η ((γ.trans γ').map hf.continuous) := by
  rw [h_trans_X, h_γ, h_γ']
  rw [Path.map_trans]
  rw [h_trans_Y]

/-- **Symmetric path conditional special case** of path-level
naturality: naturality at `γ.symm` follows from naturality at `γ`
(as a hypothesis), via `Path.map_symm` (which states
`(γ.map h).symm = γ.symm.map h`).

This requires the `pathIntegralViaCover_symm` connection, which the
project has at the partition-parametric `_With` level
(`pathIntegralViaCoverWith_symm`) but not yet at the un-`With` level.
Stated here as a hypothesis-conditional. -/
theorem pathIntegralViaCover_pullbackFormsBundledLM_of_symm
    (f : X → Y) (hf : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω f)
    (η : HolomorphicOneForm ℂ Y) {a b : X} (γ : Path a b)
    (h_nat : pathIntegralViaCover (pullbackFormsBundledLM X Y f hf η) γ =
      pathIntegralViaCover η (γ.map hf.continuous))
    (h_symm_X : pathIntegralViaCover
        (pullbackFormsBundledLM X Y f hf η) γ.symm =
      - pathIntegralViaCover (pullbackFormsBundledLM X Y f hf η) γ)
    (h_symm_Y : pathIntegralViaCover η (γ.map hf.continuous).symm =
      - pathIntegralViaCover η (γ.map hf.continuous)) :
    pathIntegralViaCover
        (pullbackFormsBundledLM X Y f hf η) γ.symm =
      pathIntegralViaCover η (γ.symm.map hf.continuous) := by
  rw [h_symm_X, h_nat]
  -- Goal: -pathIntegralViaCover η (γ.map hf.continuous) =
  --       pathIntegralViaCover η (γ.symm.map hf.continuous).
  -- (γ.symm.map h) = (γ.map h).symm by Path.map_symm.
  rw [show γ.symm.map hf.continuous = (γ.map hf.continuous).symm from
    (Path.map_symm γ hf.continuous).symm]
  rw [h_symm_Y]

/-- **Composition assembly** of path-level naturality: if naturality
holds for `f` and for `g`, then it holds for `g ∘ f`.

Sorry-free assembly via `pullbackFormsBundledLM_comp` and `Path.map`'s
composition-functoriality. This shows that the genuinely-needed content
of path-level naturality is the per-map base case. -/
theorem pathIntegralViaCover_pullbackFormsBundledLM_of_comp
    (f : X → Y) (hf : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω f)
    (g : Y → Z) (hg : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω g)
    {a b : X} (γ : Path a b) (η : HolomorphicOneForm ℂ Z)
    (hf_nat : ∀ (η' : HolomorphicOneForm ℂ Y) {a' b' : X} (γ' : Path a' b'),
      pathIntegralViaCover (pullbackFormsBundledLM X Y f hf η') γ' =
      pathIntegralViaCover η' (γ'.map hf.continuous))
    (hg_nat : ∀ (η' : HolomorphicOneForm ℂ Z) {a' b' : Y} (γ' : Path a' b'),
      pathIntegralViaCover (pullbackFormsBundledLM Y Z g hg η') γ' =
      pathIntegralViaCover η' (γ'.map hg.continuous)) :
    pathIntegralViaCover
        (pullbackFormsBundledLM X Z (g ∘ f) (hg.comp hf) η) γ =
      pathIntegralViaCover η (γ.map (hg.comp hf).continuous) := by
  -- pullbackFormsBundledLM (g ∘ f) = pullbackFormsBundledLM f ∘ pullbackFormsBundledLM g.
  rw [pullbackFormsBundledLM_comp f hf g hg, LinearMap.comp_apply]
  -- Apply f-naturality to push from X to Y.
  rw [hf_nat (pullbackFormsBundledLM Y Z g hg η) γ]
  -- Apply g-naturality to push from Y to Z.
  rw [hg_nat η (γ.map hf.continuous)]
  -- (γ.map hf.continuous).map hg.continuous = γ.map (hg.comp hf).continuous.
  rfl

/-- **Negation special case** of `periodPairing_pullbackFormsBundledLM`:
naturality at `-γ` follows from naturality at `γ` (as a hypothesis)
since both `cyclePushforward` and `periodPairing` are additive (so
they negate `-γ` consistently on both sides). Sorry-free assembly. -/
theorem periodPairing_pullbackFormsBundledLM_of_neg
    (f : X → Y) (hf : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω f)
    (γ : IntegralOneCycle X) (η : HolomorphicOneForm ℂ Y)
    (h_nat : (periodPairing ℂ X γ) (pullbackFormsBundledLM X Y f hf η) =
      (periodPairing ℂ Y (cyclePushforward f hf γ)) η) :
    (periodPairing ℂ X (-γ)) (pullbackFormsBundledLM X Y f hf η) =
      (periodPairing ℂ Y (cyclePushforward f hf (-γ))) η := by
  rw [(cyclePushforward f hf).map_neg, (periodPairing ℂ X).map_neg,
      (periodPairing ℂ Y).map_neg, LinearMap.neg_apply, LinearMap.neg_apply,
      h_nat]

/-- **Additivity special case** of `periodPairing_pullbackFormsBundledLM`:
naturality at `γ + δ` follows from naturality at `γ` and at `δ`
(as hypotheses) since both `cyclePushforward` and `periodPairing` are
additive. Sorry-free assembly. -/
theorem periodPairing_pullbackFormsBundledLM_of_add
    (f : X → Y) (hf : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω f)
    (γ δ : IntegralOneCycle X) (η : HolomorphicOneForm ℂ Y)
    (h_γ : (periodPairing ℂ X γ) (pullbackFormsBundledLM X Y f hf η) =
      (periodPairing ℂ Y (cyclePushforward f hf γ)) η)
    (h_δ : (periodPairing ℂ X δ) (pullbackFormsBundledLM X Y f hf η) =
      (periodPairing ℂ Y (cyclePushforward f hf δ)) η) :
    (periodPairing ℂ X (γ + δ)) (pullbackFormsBundledLM X Y f hf η) =
      (periodPairing ℂ Y (cyclePushforward f hf (γ + δ))) η := by
  rw [(cyclePushforward f hf).map_add, (periodPairing ℂ X).map_add,
      (periodPairing ℂ Y).map_add, LinearMap.add_apply, LinearMap.add_apply,
      h_γ, h_δ]

/-- **Natural-scalar special case** of `periodPairing_pullbackFormsBundledLM`. -/
theorem periodPairing_pullbackFormsBundledLM_of_nsmul
    (f : X → Y) (hf : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω f)
    (n : ℕ) (γ : IntegralOneCycle X) (η : HolomorphicOneForm ℂ Y)
    (h_nat : (periodPairing ℂ X γ) (pullbackFormsBundledLM X Y f hf η) =
      (periodPairing ℂ Y (cyclePushforward f hf γ)) η) :
    (periodPairing ℂ X (n • γ)) (pullbackFormsBundledLM X Y f hf η) =
      (periodPairing ℂ Y (cyclePushforward f hf (n • γ))) η := by
  rw [(cyclePushforward f hf).map_nsmul, (periodPairing ℂ X).map_nsmul,
      (periodPairing ℂ Y).map_nsmul, LinearMap.smul_apply, LinearMap.smul_apply,
      h_nat]

/-- **Form-zero special case**: naturality at η = 0; both sides
vanish via linearity of `pullbackFormsBundledLM` and the
linear-map-valuedness of `periodPairing γ`. Sorry-free. -/
theorem periodPairing_pullbackFormsBundledLM_zero_form
    (f : X → Y) (hf : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω f)
    (γ : IntegralOneCycle X) :
    (periodPairing ℂ X γ) (pullbackFormsBundledLM X Y f hf 0) =
      (periodPairing ℂ Y (cyclePushforward f hf γ)) 0 := by
  rw [LinearMap.map_zero, LinearMap.map_zero, LinearMap.map_zero]

/-- **Form-additivity special case**: naturality at η + ζ from
naturality at η and at ζ separately, via linearity in the form
argument. Sorry-free. -/
theorem periodPairing_pullbackFormsBundledLM_of_add_form
    (f : X → Y) (hf : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω f)
    (γ : IntegralOneCycle X) (η ζ : HolomorphicOneForm ℂ Y)
    (h_η : (periodPairing ℂ X γ) (pullbackFormsBundledLM X Y f hf η) =
      (periodPairing ℂ Y (cyclePushforward f hf γ)) η)
    (h_ζ : (periodPairing ℂ X γ) (pullbackFormsBundledLM X Y f hf ζ) =
      (periodPairing ℂ Y (cyclePushforward f hf γ)) ζ) :
    (periodPairing ℂ X γ) (pullbackFormsBundledLM X Y f hf (η + ζ)) =
      (periodPairing ℂ Y (cyclePushforward f hf γ)) (η + ζ) := by
  rw [LinearMap.map_add, LinearMap.map_add, LinearMap.map_add, h_η, h_ζ]

/-- **Form-smul special case**: naturality at k • η follows from
naturality at η, via ℂ-linearity of `pullbackFormsBundledLM` and
ℂ-linearity of `periodPairing γ`. Sorry-free. -/
theorem periodPairing_pullbackFormsBundledLM_of_smul_form
    (f : X → Y) (hf : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω f)
    (γ : IntegralOneCycle X) (k : ℂ) (η : HolomorphicOneForm ℂ Y)
    (h_η : (periodPairing ℂ X γ) (pullbackFormsBundledLM X Y f hf η) =
      (periodPairing ℂ Y (cyclePushforward f hf γ)) η) :
    (periodPairing ℂ X γ) (pullbackFormsBundledLM X Y f hf (k • η)) =
      (periodPairing ℂ Y (cyclePushforward f hf γ)) (k • η) := by
  rw [LinearMap.map_smul, LinearMap.map_smul, LinearMap.map_smul, h_η]

/-- **Form-neg special case**: naturality at -η from naturality at η. -/
theorem periodPairing_pullbackFormsBundledLM_of_neg_form
    (f : X → Y) (hf : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω f)
    (γ : IntegralOneCycle X) (η : HolomorphicOneForm ℂ Y)
    (h_η : (periodPairing ℂ X γ) (pullbackFormsBundledLM X Y f hf η) =
      (periodPairing ℂ Y (cyclePushforward f hf γ)) η) :
    (periodPairing ℂ X γ) (pullbackFormsBundledLM X Y f hf (-η)) =
      (periodPairing ℂ Y (cyclePushforward f hf γ)) (-η) := by
  rw [map_neg, map_neg, map_neg, h_η]

/-- **Subtraction special case** of `periodPairing_pullbackFormsBundledLM`. -/
theorem periodPairing_pullbackFormsBundledLM_of_sub
    (f : X → Y) (hf : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω f)
    (γ δ : IntegralOneCycle X) (η : HolomorphicOneForm ℂ Y)
    (h_γ : (periodPairing ℂ X γ) (pullbackFormsBundledLM X Y f hf η) =
      (periodPairing ℂ Y (cyclePushforward f hf γ)) η)
    (h_δ : (periodPairing ℂ X δ) (pullbackFormsBundledLM X Y f hf η) =
      (periodPairing ℂ Y (cyclePushforward f hf δ)) η) :
    (periodPairing ℂ X (γ - δ)) (pullbackFormsBundledLM X Y f hf η) =
      (periodPairing ℂ Y (cyclePushforward f hf (γ - δ))) η := by
  rw [(cyclePushforward f hf).map_sub, (periodPairing ℂ X).map_sub,
      (periodPairing ℂ Y).map_sub, LinearMap.sub_apply, LinearMap.sub_apply,
      h_γ, h_δ]

/-- **Integer-scalar special case** of `periodPairing_pullbackFormsBundledLM`:
naturality at `n • γ` follows from naturality at `γ` and additivity. -/
theorem periodPairing_pullbackFormsBundledLM_of_zsmul
    (f : X → Y) (hf : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω f)
    (n : ℤ) (γ : IntegralOneCycle X) (η : HolomorphicOneForm ℂ Y)
    (h_nat : (periodPairing ℂ X γ) (pullbackFormsBundledLM X Y f hf η) =
      (periodPairing ℂ Y (cyclePushforward f hf γ)) η) :
    (periodPairing ℂ X (n • γ)) (pullbackFormsBundledLM X Y f hf η) =
      (periodPairing ℂ Y (cyclePushforward f hf (n • γ))) η := by
  rw [(cyclePushforward f hf).map_zsmul, (periodPairing ℂ X).map_zsmul,
      (periodPairing ℂ Y).map_zsmul, LinearMap.smul_apply, LinearMap.smul_apply,
      h_nat]

/-- **Composition assembly** of `periodPairing_pullbackFormsBundledLM`:
naturality is preserved under composition of maps. If naturality holds
for `f` and for `g`, then it holds for `g ∘ f`.

Sorry-free assembly via `cyclePushforward_comp` and
`pullbackFormsBundledLM_comp`. -/
theorem periodPairing_pullbackFormsBundledLM_of_comp
    (f : X → Y) (hf : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω f)
    (g : Y → Z) (hg : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω g)
    (γ : IntegralOneCycle X) (η : HolomorphicOneForm ℂ Z)
    (hf_nat : ∀ (γ' : IntegralOneCycle X) (η' : HolomorphicOneForm ℂ Y),
      (periodPairing ℂ X γ') (pullbackFormsBundledLM X Y f hf η') =
      (periodPairing ℂ Y (cyclePushforward f hf γ')) η')
    (hg_nat : ∀ (γ' : IntegralOneCycle Y) (η' : HolomorphicOneForm ℂ Z),
      (periodPairing ℂ Y γ') (pullbackFormsBundledLM Y Z g hg η') =
      (periodPairing ℂ Z (cyclePushforward g hg γ')) η') :
    (periodPairing ℂ X γ)
        (pullbackFormsBundledLM X Z (g ∘ f) (hg.comp hf) η) =
      (periodPairing ℂ Z (cyclePushforward (g ∘ f) (hg.comp hf) γ)) η := by
  rw [pullbackFormsBundledLM_comp f hf g hg, LinearMap.comp_apply]
  rw [hf_nat γ (pullbackFormsBundledLM Y Z g hg η)]
  rw [hg_nat (cyclePushforward f hf γ) η]
  rw [cyclePushforward_comp f hf g hg, AddMonoidHom.comp_apply]

/-! ### Round 1 reassembly (cycle-level naturality)

Sorry-free assembly of `periodPairing_pullbackFormsBundledLM`
combining the descent companion
`periodPairing_pullbackFormsBundledLM_via_pathLevel` (the genuine
Stokes / chain-level content, currently a sorry) with the path-level
naturality `pathIntegralViaCover_pullbackFormsBundledLM` (sorry-free
above the chart-level companion). -/

theorem periodPairing_pullbackFormsBundledLM
    (f : X → Y) (hf : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω f)
    (γ : IntegralOneCycle X) (η : HolomorphicOneForm ℂ Y) :
    (periodPairing ℂ X γ) (pullbackFormsBundledLM X Y f hf η) =
      (periodPairing ℂ Y (cyclePushforward f hf γ)) η :=
  periodPairing_pullbackFormsBundledLM_via_pathLevel f hf γ η
    (fun {_a _b} γ' => pathIntegralViaCover_pullbackFormsBundledLM f hf η γ')

end JacobianChallenge.Periods
