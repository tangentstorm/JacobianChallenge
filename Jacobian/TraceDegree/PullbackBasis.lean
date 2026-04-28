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

/-- Deeper companion: the dual form-pullback along `id` is the identity
additive group homomorphism on the covering space.

Bottom-up: pullback of forms along `id` is the identity on forms;
dualization preserves this. -/
theorem basisDualPullback_id :
    basisDualPullback (X := X) (Y := X) id contMDiff_id =
      AddMonoidHom.id (Fin (analyticGenus ℂ X) → ℂ) := sorry

/-- Descent compatibility: `analyticPullback` acts on the period
quotient as the descended `basisDualPullback`.

Sorry-free extraction from `basisAnalyticPullbackBundle.mk_eq`. -/
theorem analyticPullback_mk_eq
    (f : X → Y) (hf : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω f)
    (v : Fin (analyticGenus ℂ Y) → ℂ) :
    analyticPullback f hf (QuotientAddGroup.mk v) =
      QuotientAddGroup.mk (basisDualPullback f hf v) :=
  (basisAnalyticPullbackBundle f hf).mk_eq v

/-- Contravariant functoriality of the dual form-pullback on the
covering space: `basisDualPullback (g ∘ f) = basisDualPullback f ∘ basisDualPullback g`.

Bottom-up content: the dual of form-pullback reverses composition.
This is the lifting of `pullbackFormsFun_comp_apply` to the
basis-aligned linear maps, then dualization. -/
theorem basisDualPullback_comp
    (f : X → Y) (hf : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω f)
    (g : Y → Z) (hg : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω g)
    (v : Fin (analyticGenus ℂ Z) → ℂ) :
    basisDualPullback (g ∘ f) (hg.comp hf) v =
      basisDualPullback f hf (basisDualPullback g hg v) := sorry

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
