import Jacobian.Periods.PeriodFunctional
import Jacobian.Periods.BasisAlignedPeriodSubgroup
import Jacobian.Periods.PathIntegralViaCoverPick
import Jacobian.Periods.PathIntegralViaCoverPickRefl
import Jacobian.Periods.PathIntegralViaCoverPickSimp
import Jacobian.Periods.PathIntegralViaCoverPickSmul
import Jacobian.HolomorphicForms.PullbackBundled
import Mathlib.AlgebraicTopology.SingularHomology.Basic
import Mathlib.Algebra.Category.ModuleCat.Basic

set_option linter.unusedSectionVars false

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

/-- Naturality of the period pairing under form-pullback / cycle-pushforward.

For `γ ∈ H₁(X, ℤ)` and `η ∈ H⁰(Y, Ω¹)`:

  `(periodPairing ℂ X γ) (pullbackFormsBundledLM X Y f hf η) = (periodPairing ℂ Y (cyclePushforward f hf γ)) η`

Mathematically: integrate-then-pull-back equals push-cycle-forward-then-integrate.

#### What discharging this sorry requires

Currently `periodPairing` is `opaque` (in `Jacobian/Periods/PeriodFunctional.lean`).
For the general naturality identity, we need *either* of:

1. **A concrete `periodPairing` definition** built from chart-local
   path integration (the project's `Jacobian/Periods/PathIntegral*` work,
   incomplete in v4.28.0). Once concrete, naturality reduces to the
   chain-rule for integration: `∫_γ (f^*η) = ∫_{f∘γ} η`, applied
   simplex-by-simplex, then descended through the H₁ quotient.

2. **A chain-level naturality companion** added alongside the
   `opaque periodPairing`: a separate (smaller, isolated) sorry stating
   that `periodPairing` factors through a *chain-level* pairing
   `chainFormPairing : SingularChain X → ...` for which the chain-level
   naturality is direct. This refactors the file without changing the
   total sorry count, but exposes the chain-level naturality as a
   smaller named obligation.

#### Already-proven special cases (in this file)

* `periodPairing_pullbackFormsBundledLM_id` — naturality at `f = id`
  (identity-functoriality, trivial via `pullbackFormsBundledLM_id` +
  `cyclePushforward_id`).
* `periodPairing_pullbackFormsBundledLM_zero` — naturality at γ = 0
  (additive zero, trivial via `map_zero`).
* `periodPairing_pullbackFormsBundledLM_of_comp` — composition assembly
  (if naturality holds for `f` and `g`, it holds for `g ∘ f`).

These don't reduce the sorry count, but they prove the structural
implications that the general statement *would* have, exposing that
the genuine geometric content is the per-map per-cycle base case
(integration / Stokes). -/
theorem periodPairing_pullbackFormsBundledLM
    (f : X → Y) (hf : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω f)
    (γ : IntegralOneCycle X) (η : HolomorphicOneForm ℂ Y) :
    (periodPairing ℂ X γ) (pullbackFormsBundledLM X Y f hf η) =
      (periodPairing ℂ Y (cyclePushforward f hf γ)) η :=
  sorry

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

/-- **Path-level naturality**: integrating the form-pullback along a
path equals integrating the original form along the pushed path.

Mathematical content: chain rule for path integration. For a smooth
path `γ : Path a b` on `X`, a smooth `f : X → Y`, and a holomorphic
1-form `η` on `Y`:

  `∫_γ (f^*η) = ∫_{f∘γ} η`

Equivalently: `pathIntegralViaCover (pullbackFormsBundledLM X Y f hf η) γ
  = pathIntegralViaCover η (γ.map hf.continuous)`.

This is the simpler, attackable refinement of the Stokes-shaped
cycle-level naturality `periodPairing_pullbackFormsBundledLM`. It does
*not* require Stokes — only the chain rule for `intervalIntegral`
applied chart-by-chart through `pathIntegralViaCoverWith`'s definition.

Bottom-up proof outline:
1. Reduce to `pathIntegralViaCoverWith` form via the `Classical.choose`
   wrapper.
2. For each segment, `pathIntegralViaChartCorrect c (f^*η) γ_i =
   pathIntegralViaChartCorrect (c.transFun f hf) η (γ_i.map hf.continuous)`
   — the chart-level naturality, where `c.transFun f hf` is the
   composed chart on `Y`.
3. The chart-level naturality is a `ChartedFormPullback` calculation
   plus `curveIntegral`'s `congr` with the chart-transition identity.

The work is substantial but stays within the Mathlib-existing
single-variable integration toolbox; no new Mathlib-level analysis
needed. -/
theorem pathIntegralViaCover_pullbackFormsBundledLM
    (f : X → Y) (hf : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω f)
    (η : HolomorphicOneForm ℂ Y) {a b : X} (γ : Path a b) :
    pathIntegralViaCover (pullbackFormsBundledLM X Y f hf η) γ =
      pathIntegralViaCover η (γ.map hf.continuous) :=
  sorry

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
both sides vanish via `LinearMap.map_zero` of `pullbackFormsBundledLM`
and `pathIntegralViaCover_zero` (the unconditional un-`With`
zero-vanishing of `pathIntegralViaCover` in
`Jacobian/Periods/PathIntegralViaCoverPickSimp.lean`). Sorry-free
**unconditionally**. -/
theorem pathIntegralViaCover_pullbackFormsBundledLM_zero
    (f : X → Y) (hf : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω f) {a b : X} (γ : Path a b) :
    pathIntegralViaCover (pullbackFormsBundledLM X Y f hf 0) γ =
      pathIntegralViaCover (0 : HolomorphicOneForm ℂ Y)
        (γ.map hf.continuous) := by
  rw [LinearMap.map_zero, pathIntegralViaCover_zero, pathIntegralViaCover_zero]

/-- **Form-negation independent special case**: the path-pullback of
`-η` along `γ` (without naturality) equals the negation of the path-pullback
of `η`. **Unconditional** via `LinearMap.map_neg` + `pathIntegralViaCover_neg`. -/
theorem pathIntegralViaCover_pullbackFormsBundledLM_neg
    (f : X → Y) (hf : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω f)
    (η : HolomorphicOneForm ℂ Y) {a b : X} (γ : Path a b) :
    pathIntegralViaCover (pullbackFormsBundledLM X Y f hf (-η)) γ =
      - pathIntegralViaCover (pullbackFormsBundledLM X Y f hf η) γ := by
  rw [map_neg, pathIntegralViaCover_neg]

/-- **Form-scalar-mul independent special case**: the path-pullback of
`k • η` along `γ` (without naturality) equals `k`-scalar-times the path-pullback
of `η`. **Unconditional** via `LinearMap.map_smul` + `pathIntegralViaCover_smul`. -/
theorem pathIntegralViaCover_pullbackFormsBundledLM_smul
    (f : X → Y) (hf : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω f)
    (k : ℂ) (η : HolomorphicOneForm ℂ Y) {a b : X} (γ : Path a b) :
    pathIntegralViaCover (pullbackFormsBundledLM X Y f hf (k • η)) γ =
      k • pathIntegralViaCover (pullbackFormsBundledLM X Y f hf η) γ := by
  rw [LinearMap.map_smul, pathIntegralViaCover_smul]

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

/-- **Form-smul case**: naturality at `k • η` follows from naturality
at `η`. **Unconditional** via `LinearMap.map_smul` of
`pullbackFormsBundledLM` and `pathIntegralViaCover_smul` (sorry-free in
`Jacobian/Periods/PathIntegralViaCoverPickSmul.lean`). -/
theorem pathIntegralViaCover_pullbackFormsBundledLM_of_smul_form
    (f : X → Y) (hf : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω f) {a b : X} (γ : Path a b)
    (k : ℂ) (η : HolomorphicOneForm ℂ Y)
    (h_η : pathIntegralViaCover (pullbackFormsBundledLM X Y f hf η) γ =
      pathIntegralViaCover η (γ.map hf.continuous)) :
    pathIntegralViaCover
        (pullbackFormsBundledLM X Y f hf (k • η)) γ =
      pathIntegralViaCover (k • η) (γ.map hf.continuous) := by
  rw [LinearMap.map_smul, pathIntegralViaCover_smul,
      pathIntegralViaCover_smul, h_η]

/-- **Form-neg case**: naturality at `-η` follows from naturality at
`η`, since both sides commute with `Neg`. **Unconditional** via
`map_neg` of `pullbackFormsBundledLM` (a `LinearMap`) and
`pathIntegralViaCover_neg` (sorry-free in
`Jacobian/Periods/PathIntegralViaCoverPickSimp.lean`). -/
theorem pathIntegralViaCover_pullbackFormsBundledLM_of_neg_form
    (f : X → Y) (hf : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω f) {a b : X} (γ : Path a b)
    (η : HolomorphicOneForm ℂ Y)
    (h_η : pathIntegralViaCover (pullbackFormsBundledLM X Y f hf η) γ =
      pathIntegralViaCover η (γ.map hf.continuous)) :
    pathIntegralViaCover
        (pullbackFormsBundledLM X Y f hf (-η)) γ =
      pathIntegralViaCover (-η) (γ.map hf.continuous) := by
  rw [map_neg, pathIntegralViaCover_neg, pathIntegralViaCover_neg, h_η]

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

/-- **Unconditional form-neg side identity**: the cycle-level pullback
applied to `-η` equals the negation of the cycle-level pullback applied
to `η`. This is the LHS-only form version of `_of_neg_form` (no
naturality at `η` required). -/
theorem periodPairing_pullbackFormsBundledLM_neg_form_lhs
    (f : X → Y) (hf : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω f)
    (γ : IntegralOneCycle X) (η : HolomorphicOneForm ℂ Y) :
    (periodPairing ℂ X γ) (pullbackFormsBundledLM X Y f hf (-η)) =
      - (periodPairing ℂ X γ) (pullbackFormsBundledLM X Y f hf η) := by
  rw [map_neg, LinearMap.map_neg]

/-- **Unconditional form-smul side identity**: the cycle-level pullback
applied to `k • η` equals `k`-scalar-times the cycle-level pullback
applied to `η`. -/
theorem periodPairing_pullbackFormsBundledLM_smul_form_lhs
    (f : X → Y) (hf : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω f)
    (γ : IntegralOneCycle X) (k : ℂ) (η : HolomorphicOneForm ℂ Y) :
    (periodPairing ℂ X γ) (pullbackFormsBundledLM X Y f hf (k • η)) =
      k • (periodPairing ℂ X γ) (pullbackFormsBundledLM X Y f hf η) := by
  rw [LinearMap.map_smul, LinearMap.map_smul]

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

end JacobianChallenge.Periods
