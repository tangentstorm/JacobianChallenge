import Jacobian.Periods.PeriodFunctional
import Jacobian.Periods.BasisAlignedPeriodSubgroup
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

/-- Naturality of the period pairing under form-pullback / cycle-pushforward.

For `γ ∈ H₁(X, ℤ)` and `η ∈ H⁰(Y, Ω¹)`:

  `(periodPairing ℂ X γ) (pullbackFormsBundledLM X Y f hf η) = (periodPairing ℂ Y (cyclePushforward f hf γ)) η`

Mathematically: integrate-then-pull-back equals push-cycle-forward-then-integrate.
A change-of-variable / Stokes calculation; the geometric content lives here.

Bottom-up: requires multi-chart path integration and either Stokes
(if cycles are paths) or chain-level naturality (if cycles are
singular chains). Mathlib v4.28.0 has neither for manifolds. -/
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
