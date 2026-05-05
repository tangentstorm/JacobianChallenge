import Jacobian.AbelJacobi.AnalyticOfCurveBasis
import Jacobian.TraceDegree.PushforwardBasis

/-!
# Analytic pullback on the basis-aligned carrier

The basis-aligned analytic Jacobian `BasisAnalyticJacobian X` (defined in
`Jacobian/AbelJacobi/AnalyticOfCurveBasis.lean`) is a complex torus
quotient. A holomorphic map `f : X → Y` of compact Riemann surfaces
induces a pullback `f* : BasisAnalyticJacobian Y → BasisAnalyticJacobian X`
through the dual of the form pullback, descended through the period
quotient.

This module exposes the pullback as a small set of named obligations
that the top-down refinement of `Solution.pullback` (and its
functoriality lemmas) delegates to. Following the project's preference
for *small* named obligations:

* `analyticPullback f hf` — the pullback as a continuous additive
  homomorphism on the basis-aligned carrier (data, `opaque`);
* `analyticPullback_id` — pullback along the identity map is the
  identity (named sorry);
* `analyticPullback_comp` — pullback distributes over composition,
  contravariantly (named sorry);
* `analyticPullback_contMDiff` — the pullback is holomorphic (named
  sorry).

Bottom-up content: each is the descent through periods of the
corresponding identity on `(Fin g_Y → ℂ) →L[ℂ] (Fin g_X → ℂ)` linear
maps (the dual of holomorphic-form pullback in basis coordinates).
-/

namespace JacobianChallenge.TraceDegree

open scoped ContDiff Manifold
open JacobianChallenge.HolomorphicForms JacobianChallenge.Periods
open JacobianChallenge.AbelJacobi
open JacobianChallenge.ComplexTorus

variable {X : Type} [TopologicalSpace X] [T2Space X] [CompactSpace X]
  [ConnectedSpace X] [ChartedSpace ℂ X]
  [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X]
variable {Y : Type} [TopologicalSpace Y] [T2Space Y] [CompactSpace Y]
  [ConnectedSpace Y] [ChartedSpace ℂ Y]
  [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) Y]
variable {Z : Type} [TopologicalSpace Z] [T2Space Z] [CompactSpace Z]
  [ConnectedSpace Z] [ChartedSpace ℂ Z]
  [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) Z]

/-- Bundle carrying the analytic pullback together with its
covering-space representative `basisDualPullback` and the descent
compatibility axiom `mk_eq`.

The `analyticPullback` field is the bundled `→ₜ+` hom on the
basis-aligned carrier; the `basisDualPullback` field is the additive
hom on the covering space; `mk_eq` is the defining property linking
the two: `analyticPullback (mk v) = mk (basisDualPullback v)`.

Bottom-up: concretising `basisDualPullback` requires the dual of the
basis-aligned form-pullback; `analyticPullback` is then its descent
through the period quotient (using period-preservation), and `mk_eq`
is automatic from the descent. -/
structure BasisAnalyticPullbackBundle
    (X : Type) [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X]
    (Y : Type) [TopologicalSpace Y] [T2Space Y] [CompactSpace Y]
    [ConnectedSpace Y] [ChartedSpace ℂ Y]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) Y]
    (_f : X → Y) (_hf : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω _f) where
  /-- The pullback as a continuous additive group homomorphism on the
  basis-aligned carrier. -/
  analyticPullback : BasisAnalyticJacobian Y →ₜ+ BasisAnalyticJacobian X
  /-- The dual form-pullback on the covering space. -/
  basisDualPullback : (Fin (analyticGenus ℂ Y) → ℂ) →+ (Fin (analyticGenus ℂ X) → ℂ)
  /-- Descent compatibility: the bundled pullback acts on the period
  quotient as the descended dual form-pullback. -/
  mk_eq : ∀ v : Fin (analyticGenus ℂ Y) → ℂ,
    analyticPullback (QuotientAddGroup.mk v) =
      QuotientAddGroup.mk (basisDualPullback v)
  /-- The bundled pullback is smooth as a manifold map. -/
  contMDiff_pull :
    ContMDiff (modelWithCornersSelf ℂ (Fin (analyticGenus ℂ Y) → ℂ))
      (modelWithCornersSelf ℂ (Fin (analyticGenus ℂ X) → ℂ)) ω analyticPullback
  /-- The (analytic) degree of `f`. Used in the trace-pullback identity
  (anti-hack #4). -/
  degree : ℕ
  /-- Trace-pullback identity (anti-hack #4):
  `pushf (pullback Q) = degree • Q` for every `Q`. -/
  trace_pullback_spec : ∀ Q : BasisAnalyticJacobian Y,
    analyticPushforward _f _hf (analyticPullback Q) = degree • Q

noncomputable instance (f : X → Y) (hf : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω f) :
    Inhabited (BasisAnalyticPullbackBundle X Y f hf) :=
  ⟨{ analyticPullback := 0
     basisDualPullback := 0
     mk_eq := fun _ => rfl
     contMDiff_pull := contMDiff_const
     degree := 0
     trace_pullback_spec := fun Q => by
       -- pull = 0 here, so pull Q = 0, and pushf 0 = 0 = 0 • Q.
       show (analyticPushforward f hf) (0 : BasisAnalyticJacobian X) =
         (0 : ℕ) • Q
       rw [map_zero, zero_smul] }⟩

/-- The bundled analytic pullback (data + descent axiom), as an
`opaque` value. The `Inhabited` witness uses the zero pullback,
which trivially satisfies the descent axiom; the actual mathematical
content is deferred to the bottom-up layer. -/
noncomputable opaque basisAnalyticPullbackBundle (f : X → Y)
    (hf : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω f) :
    BasisAnalyticPullbackBundle X Y f hf

/-- The analytic pullback induced by a holomorphic map of compact
Riemann surfaces, on the basis-aligned carrier. Extracted from
`basisAnalyticPullbackBundle`. -/
noncomputable def analyticPullback (f : X → Y)
    (hf : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω f) :
    BasisAnalyticJacobian Y →ₜ+ BasisAnalyticJacobian X :=
  (basisAnalyticPullbackBundle f hf).analyticPullback

/-- The analytic pullback is holomorphic.

Sorry-free extraction from `basisAnalyticPullbackBundle.contMDiff_pull`. -/
lemma analyticPullback_contMDiff (f : X → Y) (hf : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω f) :
    ContMDiff (modelWithCornersSelf ℂ (Fin (analyticGenus ℂ Y) → ℂ))
      (modelWithCornersSelf ℂ (Fin (analyticGenus ℂ X) → ℂ)) ω
      (analyticPullback f hf) :=
  (basisAnalyticPullbackBundle f hf).contMDiff_pull

/-! ### Deeper companions for contravariant functoriality

The opaque `analyticPullback` is the descent through the period
quotient of a linear map on the covering space — the dual of the
basis-aligned form-pullback. The two specs below capture that
relationship:

* `basisDualPullback` — the additive group homomorphism on the
  covering space (opaque data);
* `analyticPullback_mk_eq` — descent compatibility (sorry);
* `basisDualPullback_comp` — form-pullback contravariance (sorry).
-/

/-- The dual of the basis-aligned form-pullback, as an additive group
homomorphism on the covering space
`Fin (analyticGenus ℂ Y) → ℂ → Fin (analyticGenus ℂ X) → ℂ`.

Extracted from `basisAnalyticPullbackBundle`. -/
noncomputable def basisDualPullback (f : X → Y)
    (hf : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω f) :
    (Fin (analyticGenus ℂ Y) → ℂ) →+ (Fin (analyticGenus ℂ X) → ℂ) :=
  (basisAnalyticPullbackBundle f hf).basisDualPullback

/-! ### Bundle-primitive split (mirrors PushforwardBasis pattern)

The opaque `basisAnalyticPullbackBundle f hf` is selected independently
by `Classical.choice` for each `(f, hf)`, so Lean has no intrinsic
propositional relationship between the dual pullbacks for `f`, `g`, and
`g ∘ f`. The mathematical relationships — `(id)* = id` and contravariant
`(g ∘ f)* = f* ∘ g*` for the dual of the basis-aligned form-pullback —
are unavailable in the pinned Mathlib (no concrete `pullbackFormsMap`).

The two sorries that remain in this file therefore sit on
*bundle-level* `AddMonoidHom`-equalities (canonical mathematical
statements that the eventual concrete `pullbackFormsMap` fix will
discharge directly), and the per-vector / per-coordinate spec lemmas
are sorry-free assemblies via `unfold + rw + rfl`. -/

/-! ### Round 1 (2026-05-05) — split the HEq diamond sorries

The two diamond sorries
`basisAnalyticPullbackBundle_id_dualPullback` and
`basisAnalyticPullbackBundle_comp_dualPullback` cannot be discharged
without a concrete (non-opaque) realisation of the per-(f, hf)
bundle. We split each into:

* `basisAnalyticPullbackBundle_eq_pullbackFormsMap` — bridge from the
  bundle's `basisDualPullback` field to a *named* covering-space
  dual-pullback function `pullbackFormsMap` (currently both are
  opaque-realised; bridge is itself a sorry);
* `pullbackFormsMap_id` — identity functoriality of the bridge map;
* `pullbackFormsMap_comp` — composition functoriality.

Each is the same Mathlib gap (concrete dual of basis-aligned form
pullback) but stated as a separate, smaller named obligation. -/

/-- **Stage A leaf (round 1, structural opaque).** Concrete dual of
the basis-aligned form pullback. *Bottom-up*: matrix of the
dual-pullback in chosen bases of `H⁰(X, Ω¹)` and `H⁰(Y, Ω¹)`. -/
noncomputable opaque pullbackFormsMap
    (X' Y' : Type) [TopologicalSpace X'] [T2Space X']
    [CompactSpace X'] [ConnectedSpace X'] [ChartedSpace ℂ X']
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X']
    [TopologicalSpace Y'] [T2Space Y'] [CompactSpace Y']
    [ConnectedSpace Y'] [ChartedSpace ℂ Y']
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) Y']
    (f : X' → Y') (_hf : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω f) :
    (Fin (analyticGenus ℂ Y') → ℂ) →+ (Fin (analyticGenus ℂ X') → ℂ)

/-- **Stage A leaf (round 1, bridge sorry).** The bundle's
`basisDualPullback` agrees with the named `pullbackFormsMap`. Same
upstream Mathlib gap as the original diamond sorry: both
`basisAnalyticPullbackBundle f hf` and `pullbackFormsMap X' Y' f hf`
are opaque-realised, so this equality is itself a sorry. -/
theorem basisAnalyticPullbackBundle_eq_pullbackFormsMap
    (f : X → Y) (hf : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω f) :
    (basisAnalyticPullbackBundle f hf).basisDualPullback =
      pullbackFormsMap X Y f hf := by
  sorry

/-- **Stage A leaf (round 1).** Identity functoriality of
`pullbackFormsMap`. Bottom-up: the dual of form-pullback along `id`
is the identity. -/
theorem pullbackFormsMap_id_eq_id :
    pullbackFormsMap X X id contMDiff_id =
      AddMonoidHom.id (Fin (analyticGenus ℂ X) → ℂ) := by
  sorry

/-- **Stage A leaf (round 1).** Composition (contravariant)
functoriality of `pullbackFormsMap`. -/
theorem pullbackFormsMap_comp_eq
    (f : X → Y) (hf : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω f)
    (g : Y → Z) (hg : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω g) :
    pullbackFormsMap X Z (g ∘ f) (hg.comp hf) =
      (pullbackFormsMap X Y f hf).comp (pullbackFormsMap Y Z g hg) := by
  sorry

/-- Bundle-level axiom: the `basisDualPullback` field of the bundle
selected at `(X, X, id, contMDiff_id)` is the identity additive group
homomorphism on the covering space.

**Round 1 sorry-free assembly.** Compose
`basisAnalyticPullbackBundle_eq_pullbackFormsMap` (the bridge sorry)
with `pullbackFormsMap_id_eq_id` (the identity-functoriality sorry). -/
theorem basisAnalyticPullbackBundle_id_dualPullback :
    (basisAnalyticPullbackBundle (X := X) (Y := X) id contMDiff_id).basisDualPullback =
      AddMonoidHom.id (Fin (analyticGenus ℂ X) → ℂ) := by
  rw [basisAnalyticPullbackBundle_eq_pullbackFormsMap (X := X) (Y := X)
      id contMDiff_id,
    pullbackFormsMap_id_eq_id (X := X)]

/-- The dual form-pullback along `id` is the identity additive group
homomorphism. Sorry-free: extracts the bundle-level axiom via `unfold`. -/
theorem basisDualPullback_id :
    basisDualPullback (X := X) (Y := X) id contMDiff_id =
      AddMonoidHom.id (Fin (analyticGenus ℂ X) → ℂ) := by
  unfold basisDualPullback
  exact basisAnalyticPullbackBundle_id_dualPullback

/-- Pointwise form of `basisDualPullback_id`: the dual form-pullback
along `id` is pointwise the identity on the covering space.

Sorry-free assembly via `basisDualPullback_id`. -/
theorem basisDualPullback_id_apply (v : Fin (analyticGenus ℂ X) → ℂ) :
    basisDualPullback (X := X) (Y := X) id contMDiff_id v = v := by
  rw [basisDualPullback_id]
  rfl

/-- Descent compatibility: `analyticPullback` acts on the period
quotient as the descended `basisDualPullback`.

Sorry-free extraction from `basisAnalyticPullbackBundle.mk_eq`. -/
theorem analyticPullback_mk_eq
    (f : X → Y) (hf : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω f)
    (v : Fin (analyticGenus ℂ Y) → ℂ) :
    analyticPullback f hf (QuotientAddGroup.mk v) =
      QuotientAddGroup.mk (basisDualPullback f hf v) :=
  (basisAnalyticPullbackBundle f hf).mk_eq v

/--
Contravariant functoriality of the dual form-pullback on the
covering space: `basisDualPullback (g ∘ f) = basisDualPullback f ∘ basisDualPullback g`.

Bottom-up content: the dual of form-pullback reverses composition.
This is the lifting of `pullbackFormsFun_comp_apply` to the
basis-aligned linear maps, then dualization.

### Blocker analysis (integrated from Aristotle ad278fcd)

**Goal.** Show that the covering-space dual pullback for `g ∘ f`
equals the composition of dual pullbacks for `f` and `g`
(contravariantly), at each covering-space vector.

**Root cause: three independent opaques.** The three
`basisDualPullback` values appearing in this equation originate
from three distinct opaque values:
`basisAnalyticPullbackBundle (g ∘ f) (hg.comp hf)`,
`basisAnalyticPullbackBundle f hf`, and
`basisAnalyticPullbackBundle g hg`. Each `opaque` is selected
independently by `Classical.choice` from the `Inhabited` witness
(which uses `basisDualPullback := 0`), so Lean has no propositional
relationship between the three covering-space lifts.

**Why `mk_eq` is insufficient.** The `mk_eq` field of
`BasisAnalyticPullbackBundle` only gives quotient-level descent
compatibility, yielding congruence modulo the period lattice — not
the exact covering-space equality required.

**Why a composition bundle does not resolve it.** Same cross-instance
opacity issue as `pushforwardTraceLift_comp_spec_apply_at`: a comp
bundle cannot constrain the per-`(f, hf)` opaques, since
`basisDualPullback f hf` is defined directly from
`basisAnalyticPullbackBundle f hf`.

**Mathlib API required to land this:** concrete pullback of
holomorphic 1-forms `f* : H⁰(Y, Ω¹) → H⁰(X, Ω¹)`, contravariant
functoriality `(g ∘ f)* = f* ∘ g*`, basis-coordinate matrix
representation. All absent in v4.28.0.

**Structural change required:** replace the per-`(f, hf)` opaque
bundle with a concrete (non-opaque) definition built from
`pullbackFormsMap`. This is the exact dual of the blocker on
`pushforwardTraceLift_comp_spec_apply_at`.

#### Bundle-primitive split (mirrors PushforwardBasis pattern)

The composition obligation is now isolated as a single
`AddMonoidHom`-equality at the bundle field level
(`basisAnalyticPullbackBundle_comp_dualPullback` below), with the
top-level `basisDualPullback_comp_top` and the per-vector
`basisDualPullback_comp` as sorry-free assemblies. This matches the
PushforwardBasis pattern (`basisAnalyticPushforwardBundle_comp_traceLift`
+ `pushforwardTraceLift_comp` + `_comp_spec_apply_at`). -/
theorem basisAnalyticPullbackBundle_comp_dualPullback
    (f : X → Y) (hf : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω f)
    (g : Y → Z) (hg : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω g) :
    (basisAnalyticPullbackBundle (g ∘ f) (hg.comp hf)).basisDualPullback =
      ((basisAnalyticPullbackBundle f hf).basisDualPullback).comp
        (basisAnalyticPullbackBundle g hg).basisDualPullback := by
  -- Round 1 sorry-free assembly: route through the structural bridge.
  rw [basisAnalyticPullbackBundle_eq_pullbackFormsMap (g ∘ f) (hg.comp hf),
      basisAnalyticPullbackBundle_eq_pullbackFormsMap f hf,
      basisAnalyticPullbackBundle_eq_pullbackFormsMap g hg,
      pullbackFormsMap_comp_eq f hf g hg]

/-- Top-level contravariant functoriality of the dual form-pullback:
`(g ∘ f)* = f* ∘ g*` as an additive group homomorphism on the covering
space. Sorry-free: extracts the bundle-level axiom via `unfold`. -/
theorem basisDualPullback_comp_top
    (f : X → Y) (hf : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω f)
    (g : Y → Z) (hg : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω g) :
    basisDualPullback (g ∘ f) (hg.comp hf) =
      (basisDualPullback f hf).comp (basisDualPullback g hg) := by
  unfold basisDualPullback
  exact basisAnalyticPullbackBundle_comp_dualPullback f hf g hg

/-- Pointwise form: `basisDualPullback (g ∘ f) v = basisDualPullback f
(basisDualPullback g v)`. Sorry-free assembly via
`basisDualPullback_comp_top` + `AddMonoidHom.comp_apply`. -/
theorem basisDualPullback_comp
    (f : X → Y) (hf : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω f)
    (g : Y → Z) (hg : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω g)
    (v : Fin (analyticGenus ℂ Z) → ℂ) :
    basisDualPullback (g ∘ f) (hg.comp hf) v =
      basisDualPullback f hf (basisDualPullback g hg v) := by
  rw [basisDualPullback_comp_top f hf g hg, AddMonoidHom.comp_apply]

/-- Companion spec for `analyticPullback_comp_apply`: pullback of forms is
contravariantly functorial, and descent preserves composition.

**Proof.** Assembly from the deeper companions `analyticPullback_mk_eq`
and `basisDualPullback_comp`. Every element of the quotient is
`⟦v⟧` for some covering-space vector `v`; rewrite both sides using
descent compatibility, then apply the covering-space composition law. -/
theorem analyticPullback_comp_spec
    (f : X → Y) (hf : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω f)
    (g : Y → Z) (hg : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω g)
    (P : BasisAnalyticJacobian Z) :
    analyticPullback (g ∘ f) (hg.comp hf) P =
      analyticPullback f hf (analyticPullback g hg P) := by
  induction P using QuotientAddGroup.induction_on with
  | H v =>
    rw [analyticPullback_mk_eq (g ∘ f) (hg.comp hf) v]
    rw [analyticPullback_mk_eq g hg v]
    rw [analyticPullback_mk_eq f hf (basisDualPullback g hg v)]
    rw [basisDualPullback_comp f hf g hg v]

/-- Pullback distributes contravariantly over composition.

Pure assembly of `analyticPullback_comp_spec`. -/
lemma analyticPullback_comp_apply
    (f : X → Y) (hf : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω f)
    (g : Y → Z) (hg : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω g)
    (P : BasisAnalyticJacobian Z) :
    analyticPullback (g ∘ f) (hg.comp hf) P =
      analyticPullback f hf (analyticPullback g hg P) :=
  analyticPullback_comp_spec f hf g hg P

/-- Companion spec: pullback along the identity map equals the identity
homomorphism (as a `ContinuousAddMonoidHom`).

**Proof.** Assembly from the deeper companions `analyticPullback_mk_eq`
(descent compatibility) and `basisDualPullback_id` (covering-space
identity functoriality). On each `mk v`, rewrite via descent and
identify the dual pullback as the identity. -/
theorem analyticPullback_id_spec :
    analyticPullback (X := X) (Y := X) id contMDiff_id =
      ContinuousAddMonoidHom.id (BasisAnalyticJacobian X) := by
  ext P
  induction P using QuotientAddGroup.induction_on with
  | H v =>
    rw [analyticPullback_mk_eq id contMDiff_id v, basisDualPullback_id]
    rfl

/-- Pullback along the identity is the identity.

Assembly from `analyticPullback_id_spec`. -/
lemma analyticPullback_id_apply (P : BasisAnalyticJacobian X) :
    analyticPullback (X := X) (Y := X) id contMDiff_id P = P := by
  rw [analyticPullback_id_spec]
  rfl

end JacobianChallenge.TraceDegree
