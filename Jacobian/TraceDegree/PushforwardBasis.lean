import Jacobian.AbelJacobi.AnalyticOfCurveBasis

/-!
# Analytic pushforward on the basis-aligned carrier

A holomorphic map `f : X → Y` of compact Riemann surfaces induces a
pushforward `f_* : BasisAnalyticJacobian X → BasisAnalyticJacobian Y`,
typically constructed via the trace map on holomorphic 1-forms (or, in
basis coordinates, the dual of the trace), descended through the
period quotient.

This module mirrors `Jacobian/TraceDegree/PullbackBasis.lean` in the
opposite direction. Named obligations:

* `analyticPushforward f hf` — bundled `→ₜ+` hom on the basis-aligned
  carrier (`opaque`);
* `analyticPushforward_id_apply` — covariant identity functoriality;
* `analyticPushforward_comp_apply` — covariant composition;
* `analyticPushforward_contMDiff` — holomorphicity.

Bottom-up content: descent of the basis-aligned trace map on
`(Fin g_X → ℂ) →L[ℂ] (Fin g_Y → ℂ)` through periods.
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

/-- Bundle carrying the analytic pushforward together with its
covering-space representative `pushforwardTraceLift` and the descent
compatibility axiom `mk_spec`.

Bottom-up: concretising `pushforwardTraceLift` requires the dual of
the trace/norm map on holomorphic 1-forms; `analyticPushforward` is
then its descent through the period quotient (using period-lattice
preservation), and `mk_spec` is automatic from the descent. -/
structure BasisAnalyticPushforwardBundle
    (X : Type) [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X]
    (Y : Type) [TopologicalSpace Y] [T2Space Y] [CompactSpace Y]
    [ConnectedSpace Y] [ChartedSpace ℂ Y]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) Y]
    (_f : X → Y) (_hf : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω _f) where
  /-- The pushforward as a continuous additive group homomorphism on
  the basis-aligned carrier. -/
  analyticPushforward : BasisAnalyticJacobian X →ₜ+ BasisAnalyticJacobian Y
  /-- The trace lift on the covering space. -/
  pushforwardTraceLift : (Fin (analyticGenus ℂ X) → ℂ) →+ (Fin (analyticGenus ℂ Y) → ℂ)
  /-- Descent compatibility: the bundled pushforward acts on the period
  quotient as the descended trace lift. -/
  mk_spec : ∀ v : Fin (analyticGenus ℂ X) → ℂ,
    analyticPushforward (ComplexTorus.mk _ (periodFullComplexLattice X) v) =
      ComplexTorus.mk _ (periodFullComplexLattice Y) (pushforwardTraceLift v)

noncomputable instance (f : X → Y) (hf : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω f) :
    Inhabited (BasisAnalyticPushforwardBundle X Y f hf) :=
  ⟨{ analyticPushforward := 0
     pushforwardTraceLift := 0
     mk_spec := fun _ => rfl }⟩

/-- The bundled analytic pushforward (data + descent axiom), as an
`opaque` value. -/
noncomputable opaque basisAnalyticPushforwardBundle (f : X → Y)
    (hf : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω f) :
    BasisAnalyticPushforwardBundle X Y f hf

/-- The analytic pushforward induced by a holomorphic map of compact
Riemann surfaces, on the basis-aligned carrier. Extracted from
`basisAnalyticPushforwardBundle`. -/
noncomputable def analyticPushforward (f : X → Y)
    (hf : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω f) :
    BasisAnalyticJacobian X →ₜ+ BasisAnalyticJacobian Y :=
  (basisAnalyticPushforwardBundle f hf).analyticPushforward

open JacobianChallenge.ComplexTorus in
/-- Every continuous additive group homomorphism between complex tori
is smooth (`ContMDiff ω`).  This is a standard fact: continuous
homomorphisms between Lie groups are automatically smooth.

Bottom-up obligation.  The proof lifts the continuous homomorphism to a
continuous linear map on the covering spaces (automatically smooth),
then descends through the period-quotient projection (a local
diffeomorphism). -/
theorem contMDiff_continuousAddMonoidHom_complexTorus
    {V W : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V]
    [NormedAddCommGroup W] [NormedSpace ℂ W]
    (ΛV : FullComplexLattice V) (ΛW : FullComplexLattice W)
    (φ : quotient V ΛV →ₜ+ quotient W ΛW) :
    ContMDiff (modelWithCornersSelf ℂ V) (modelWithCornersSelf ℂ W) ω φ := sorry

/-- Companion specification: the analytic pushforward is holomorphic.

Bottom-up obligation. Delegates to
`contMDiff_continuousAddMonoidHom_complexTorus`: the analytic
pushforward is a `ContinuousAddMonoidHom` between complex tori,
and every such homomorphism is smooth. -/
theorem analyticPushforward_contMDiff_spec (f : X → Y)
    (hf : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω f) :
    ContMDiff (modelWithCornersSelf ℂ (Fin (analyticGenus ℂ X) → ℂ))
      (modelWithCornersSelf ℂ (Fin (analyticGenus ℂ Y) → ℂ)) ω
      (analyticPushforward f hf) :=
  contMDiff_continuousAddMonoidHom_complexTorus _ _ (analyticPushforward f hf)

/-- The analytic pushforward is holomorphic.

Top-down obligation. Assembly: delegates to
`analyticPushforward_contMDiff_spec`. -/
lemma analyticPushforward_contMDiff (f : X → Y) (hf : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω f) :
    ContMDiff (modelWithCornersSelf ℂ (Fin (analyticGenus ℂ X) → ℂ))
      (modelWithCornersSelf ℂ (Fin (analyticGenus ℂ Y) → ℂ)) ω
      (analyticPushforward f hf) :=
  analyticPushforward_contMDiff_spec f hf

/-! ### Deeper companions: trace lift on the covering space

The opaque `analyticPushforward` is the descent of a covering-space
linear map.  The companions below capture that decomposition:

* `pushforwardTraceLift` — the additive trace map on covering spaces
  (opaque);
* `pushforwardTraceLift_preserves_lattice` — period-lattice
  preservation (sorry);
* `analyticPushforward_mk_spec` — descent compatibility:
  `analyticPushforward f hf (mk v) = mk (traceLift v)` (sorry);
* `pushforwardTraceLift_comp_spec` — covariant functoriality of
  the trace lift on covering spaces (sorry).

Together with `ComplexTorus.mk_surjective`, these assemble into the
covariant-composition statement `analyticPushforward_comp_spec`. -/

/-- The trace lift on the covering model spaces: the additive map
`(Fin g_X → ℂ) →+ (Fin g_Y → ℂ)`. Extracted from
`basisAnalyticPushforwardBundle`. -/
noncomputable def pushforwardTraceLift (f : X → Y)
    (hf : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω f) :
    (Fin (analyticGenus ℂ X) → ℂ) →+ (Fin (analyticGenus ℂ Y) → ℂ) :=
  (basisAnalyticPushforwardBundle f hf).pushforwardTraceLift

/-- Deeper companion: the trace lift along `id` is the identity additive
group homomorphism on the covering space.

Bottom-up: the trace of the identity branched covering (degree 1) is
the identity on holomorphic 1-forms; dualization preserves this. -/
theorem pushforwardTraceLift_id :
    pushforwardTraceLift (X := X) (Y := X) id contMDiff_id =
      AddMonoidHom.id (Fin (analyticGenus ℂ X) → ℂ) := sorry

/-- The trace lift preserves the period lattice: it sends the period
subgroup of `X` into the period subgroup of `Y`.

Bottom-up obligation. Provable from the fact that the trace/norm map
on holomorphic 1-forms intertwines the period pairings. -/
theorem pushforwardTraceLift_preserves_lattice
    (f : X → Y) (hf : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω f) :
    ∀ v ∈ (periodFullComplexLattice X).subgroup,
      pushforwardTraceLift f hf v ∈ (periodFullComplexLattice Y).subgroup := sorry

/-- Characterization of `analyticPushforward` on the quotient
projection: the pushforward applied to `mk v` equals `mk` of the
trace lift applied to `v`.

Sorry-free extraction from `basisAnalyticPushforwardBundle.mk_spec`. -/
theorem analyticPushforward_mk_spec
    (f : X → Y) (hf : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω f)
    (v : Fin (analyticGenus ℂ X) → ℂ) :
    analyticPushforward f hf
      (ComplexTorus.mk _ (periodFullComplexLattice X) v) =
      ComplexTorus.mk _ (periodFullComplexLattice Y)
        (pushforwardTraceLift f hf v) :=
  (basisAnalyticPushforwardBundle f hf).mk_spec v

/-- The trace lift is covariantly functorial under composition: the
trace lift for `g ∘ f` equals the composition of trace lifts for `g`
and `f`.

Bottom-up obligation. Provable from the multiplicativity of the
trace/norm map on holomorphic 1-forms. -/
theorem pushforwardTraceLift_comp_spec
    (f : X → Y) (hf : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω f)
    (g : Y → Z) (hg : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω g) :
    (pushforwardTraceLift (g ∘ f) (hg.comp hf) : _ →+ _) =
      (pushforwardTraceLift g hg).comp (pushforwardTraceLift f hf) := sorry

/-- Covariant composition specification for the analytic pushforward.

Discharged via the deeper-companion split: uses
`analyticPushforward_mk_spec` (descent compatibility on the covering
space) and `pushforwardTraceLift_comp_spec` (functoriality of the
trace lift) to reduce to a computation on the quotient projection. -/
theorem analyticPushforward_comp_spec
    (f : X → Y) (hf : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω f)
    (g : Y → Z) (hg : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω g)
    (P : BasisAnalyticJacobian X) :
    analyticPushforward (g ∘ f) (hg.comp hf) P =
      analyticPushforward g hg (analyticPushforward f hf P) := by
  obtain ⟨v, rfl⟩ := ComplexTorus.mk_surjective _ (periodFullComplexLattice X) P
  rw [analyticPushforward_mk_spec f hf v,
      analyticPushforward_mk_spec (g ∘ f) (hg.comp hf) v,
      analyticPushforward_mk_spec g hg (pushforwardTraceLift f hf v)]
  congr 1
  exact congr_fun (congr_arg _ (pushforwardTraceLift_comp_spec f hf g hg)) v

/-- Pushforward distributes covariantly over composition.

Top-down obligation. Assembled from `analyticPushforward_comp_spec`. -/
lemma analyticPushforward_comp_apply
    (f : X → Y) (hf : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω f)
    (g : Y → Z) (hg : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω g)
    (P : BasisAnalyticJacobian X) :
    analyticPushforward (g ∘ f) (hg.comp hf) P =
      analyticPushforward g hg (analyticPushforward f hf P) :=
  analyticPushforward_comp_spec f hf g hg P

/-- Deeper companion: the pushforward along the identity map equals
the identity `ContinuousAddMonoidHom`.

**Proof.** Assembly from the deeper companions `analyticPushforward_mk_spec`
(descent compatibility) and `pushforwardTraceLift_id` (covering-space
identity functoriality). On each `mk v`, rewrite via descent and
identify the trace lift as the identity. -/
theorem analyticPushforward_id_eq :
    analyticPushforward (X := X) (Y := X) id contMDiff_id =
      ContinuousAddMonoidHom.id (BasisAnalyticJacobian X) := by
  ext P
  obtain ⟨v, rfl⟩ := ComplexTorus.mk_surjective _ (periodFullComplexLattice X) P
  rw [analyticPushforward_mk_spec id contMDiff_id v, pushforwardTraceLift_id]
  rfl

/-- Specification: the trace of the identity holomorphic map on
holomorphic 1-forms is the identity; descending through the period
quotient preserves this.

Assembly from `analyticPushforward_id_eq`. -/
theorem analyticPushforward_id_spec (P : BasisAnalyticJacobian X) :
    analyticPushforward (X := X) (Y := X) id contMDiff_id P = P := by
  rw [analyticPushforward_id_eq]
  rfl

/-- Pushforward along the identity is the identity.

Top-down obligation. Assembled from `analyticPushforward_id_spec`. -/
lemma analyticPushforward_id_apply (P : BasisAnalyticJacobian X) :
    analyticPushforward (X := X) (Y := X) id contMDiff_id P = P :=
  analyticPushforward_id_spec P

end JacobianChallenge.TraceDegree
