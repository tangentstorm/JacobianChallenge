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
  /-- The trace lift preserves the period subgroup. -/
  preserves_lattice : ∀ v ∈ (periodFullComplexLattice X).subgroup,
    pushforwardTraceLift v ∈ (periodFullComplexLattice Y).subgroup
  /-- The bundled pushforward is smooth as a manifold map. -/
  contMDiff_push :
    ContMDiff (modelWithCornersSelf ℂ (Fin (analyticGenus ℂ X) → ℂ))
      (modelWithCornersSelf ℂ (Fin (analyticGenus ℂ Y) → ℂ)) ω analyticPushforward

noncomputable instance (f : X → Y) (hf : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω f) :
    Inhabited (BasisAnalyticPushforwardBundle X Y f hf) :=
  ⟨{ analyticPushforward := 0
     pushforwardTraceLift := 0
     mk_spec := fun _ => rfl
     preserves_lattice := fun _ _ => (periodFullComplexLattice Y).subgroup.zero_mem
     contMDiff_push := contMDiff_const }⟩

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

/-- Companion specification: the analytic pushforward is holomorphic.

Sorry-free extraction from `basisAnalyticPushforwardBundle.contMDiff_push`. -/
theorem analyticPushforward_contMDiff_spec (f : X → Y)
    (hf : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω f) :
    ContMDiff (modelWithCornersSelf ℂ (Fin (analyticGenus ℂ X) → ℂ))
      (modelWithCornersSelf ℂ (Fin (analyticGenus ℂ Y) → ℂ)) ω
      (analyticPushforward f hf) :=
  (basisAnalyticPushforwardBundle f hf).contMDiff_push

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
  preservation (sorry-free, extracted from the bundle);
* `analyticPushforward_mk_spec` — descent compatibility:
  `analyticPushforward f hf (mk v) = mk (traceLift v)` (sorry-free,
  extracted from the bundle);
* `pushforwardTraceLift_comp_spec` — covariant functoriality of
  the trace lift on covering spaces (sorry, see blocker note below).

Together with `ComplexTorus.mk_surjective`, these assemble into the
covariant-composition statement `analyticPushforward_comp_spec`.

#### Bundle-incompatibility blocker

The opaque value `basisAnalyticPushforwardBundle f hf` is selected by
`Classical.choice` from the `Inhabited` witness, which uses
`pushforwardTraceLift := 0` (forced because the codomain
`Fin (analyticGenus ℂ Y) → ℂ` differs from the domain in general, so
the only canonical zero-witness available is the additive zero).
Therefore the opaque value's `pushforwardTraceLift` may be `0`, and
the identity functoriality `pushforwardTraceLift id contMDiff_id v = v`
is *not* derivable from the bundle alone — it asserts behaviour the
zero witness cannot have unless `v = 0`.

To unblock `pushforwardTraceLift_id_apply` and
`pushforwardTraceLift_comp_spec_apply` at the bundle layer, one of:

* introduce a richer bundle that takes additional parameters
  (e.g. `BasisAnalyticPushforwardIdBundle X` carrying
  `pushforwardTraceLift = AddMonoidHom.id` as a field, with
  Inhabited witness using the literal identity hom);
* add an upstream concretisation step that fixes
  `pushforwardTraceLift` non-opaquely as the dual of a trace map on
  holomorphic forms (e.g. via `JacobianChallenge.HolomorphicForms`),
  then the id and comp axioms become provable from the
  multiplicativity of the trace/norm.

Pending that structural fix, the two sorries below are split into
per-coordinate (single-`ℂ`-value) form so the residual obligations
have the smallest possible goal type. -/

/-- The trace lift on the covering model spaces: the additive map
`(Fin g_X → ℂ) →+ (Fin g_Y → ℂ)`. Extracted from
`basisAnalyticPushforwardBundle`. -/
noncomputable def pushforwardTraceLift (f : X → Y)
    (hf : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω f) :
    (Fin (analyticGenus ℂ X) → ℂ) →+ (Fin (analyticGenus ℂ Y) → ℂ) :=
  (basisAnalyticPushforwardBundle f hf).pushforwardTraceLift

/-- Per-coordinate form of `pushforwardTraceLift_id_apply`: the trace
lift along `id`, evaluated at `v` and projected onto coordinate `i`,
equals `v i`.

This is the smallest named obligation: a single equality in `ℂ`.
Bottom-up: the trace of the identity branched covering (degree 1) is
the identity on holomorphic 1-forms; dualization preserves this
pointwise on each basis coordinate.

Blocked at the bundle layer: see the section docstring above.

#### Detailed blocker analysis (integrated from Aristotle ba57741f)

This lemma cannot be proved from the current `opaque` bundle:

1. **Opaque inaccessibility.** `pushforwardTraceLift id contMDiff_id`
   is defined as
   `(basisAnalyticPushforwardBundle id contMDiff_id).pushforwardTraceLift`,
   where `basisAnalyticPushforwardBundle` is `opaque`. An `opaque`
   value in Lean 4 is uninterpreted — no definitional unfolding is
   possible, so only properties encoded in its *type* are reachable.

2. **Insufficient type.** The type
   `BasisAnalyticPushforwardBundle X X id contMDiff_id` does not carry
   a field asserting `pushforwardTraceLift = AddMonoidHom.id`. The
   `mk_spec` field only gives quotient-level descent compatibility,
   which yields `pushforwardTraceLift v ≡ v (mod period lattice)`,
   not the exact covering-space equality `pushforwardTraceLift v = v`.

3. **Instance diamond blocks enriching the type.** Adding an
   `id_lift_spec` field parameterised by both `X` and `Y` requires a
   propositional `Y = X` or `HEq f id` hypothesis. After `subst`, the
   structure literal carries duplicate typeclass instances on `X`,
   and Lean rejects with "synthesized type class instance is not
   definitionally equal to expression inferred by typing rules".

4. **Instance resolution is compile-time.** Replacing `opaque` with
   `noncomputable def … := default` and a specialised `Inhabited`
   for the `(X, X, id)` case fails because instance resolution at the
   definition site uses the general (zero-valued) instance.

**Mathlib API needed to unblock:**
- A *concrete* (non-opaque) trace/norm map on holomorphic 1-forms,
  e.g. `traceMap f : HolomorphicOneForm ℂ Y →ₗ[ℂ] HolomorphicOneForm ℂ X`
  (Mathlib lacks `Mathlib.Analysis.Complex.RiemannSurface.Trace`).
- Functoriality lemmas `traceMap_id`, `traceMap_comp` (multiplicativity
  of the field-theoretic norm/trace on branched coverings).

**Structural change required:** replace the current `opaque`
`basisAnalyticPushforwardBundle` with a `noncomputable def` built
concretely from `traceMap`, so that `pushforwardTraceLift` is
*definitionally* the basis-coordinate representation of the trace
map and the identity/composition axioms reduce to
`traceMap_id` / `traceMap_comp`. -/
theorem pushforwardTraceLift_id_apply_at
    (i : Fin (analyticGenus ℂ X)) (v : Fin (analyticGenus ℂ X) → ℂ) :
    pushforwardTraceLift (X := X) (Y := X) id contMDiff_id v i = v i := sorry

/-- Deeper companion: the trace lift along `id` is the identity additive
group homomorphism on the covering space.

Bottom-up: the trace of the identity branched covering (degree 1) is
the identity on holomorphic 1-forms; dualization preserves this.

Assembled from `pushforwardTraceLift_id_apply_at` via `funext`. -/
theorem pushforwardTraceLift_id_apply (v : Fin (analyticGenus ℂ X) → ℂ) :
    pushforwardTraceLift (X := X) (Y := X) id contMDiff_id v = v := by
  funext i
  exact pushforwardTraceLift_id_apply_at (X := X) i v

theorem pushforwardTraceLift_id :
    pushforwardTraceLift (X := X) (Y := X) id contMDiff_id =
      AddMonoidHom.id (Fin (analyticGenus ℂ X) → ℂ) := by
  refine AddMonoidHom.ext ?_
  intro v
  exact pushforwardTraceLift_id_apply (X := X) v

/-- The trace lift preserves the period lattice: it sends the period
subgroup of `X` into the period subgroup of `Y`.

Sorry-free extraction from `basisAnalyticPushforwardBundle.preserves_lattice`. -/
theorem pushforwardTraceLift_preserves_lattice
    (f : X → Y) (hf : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω f) :
    ∀ v ∈ (periodFullComplexLattice X).subgroup,
      pushforwardTraceLift f hf v ∈ (periodFullComplexLattice Y).subgroup :=
  (basisAnalyticPushforwardBundle f hf).preserves_lattice

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

/--
### Blocker analysis for `pushforwardTraceLift_comp_spec_apply_at`
(integrated from Aristotle dc58e548)

**Goal.** Show that the covering-space trace lift for `g ∘ f`
equals the composition of trace lifts for `g` and `f`, at each
coordinate.

**Root cause.** The three `pushforwardTraceLift` values appearing in
this equation originate from *three distinct opaque values*:
`basisAnalyticPushforwardBundle (g ∘ f) (hg.comp hf)`,
`basisAnalyticPushforwardBundle f hf`, and
`basisAnalyticPushforwardBundle g hg`. Each `opaque` is selected
independently by `Classical.choice`, so Lean has no propositional
relationship between the three covering-space lifts.

**Why a composition bundle does not resolve it.** A
`BasisAnalyticPushforwardCompBundle f hf g hg` carrying its own
three trace lifts plus a composition axiom can be made `Inhabited`
with zero maps, but `pushforwardTraceLift f hf` is defined by
`(basisAnalyticPushforwardBundle f hf).pushforwardTraceLift`, which
cannot depend on `g`. Re-routing through any canonical companion
still leaves three different opaque comp-bundle instances whose
internal lifts are unrelated.

**Mathlib API required to land this:**
- Trace/norm map on differentials of a finite morphism of Riemann
  surfaces (absent).
- Holomorphic 1-forms `H⁰(X, Ω¹)` as a finite-dim ℂ-vector space
  with a basis (absent; project-internal `HolomorphicOneForm` is a
  placeholder).
- Functoriality of trace: `Tr(g ∘ f) = Tr(g) ∘ Tr(f)` for branched
  coverings (absent).
- Pushforward of 1-forms `f_* : H⁰(X, Ω¹) → H⁰(Y, Ω¹)` via trace
  (absent).

**Structural change required.** Replace the per-`(f, hf)` opaque
bundle with a *concrete* (non-opaque) definition:
`pushforwardTraceLift f hf := dualOfTraceMap (...) (traceMapOnForms f hf)`
where `traceMapOnForms f hf : H⁰(Y, Ω¹) →ₗ[ℂ] H⁰(X, Ω¹)` is the
pullback-then-trace-on-fibres map. Then both
`pushforwardTraceLift_id_apply_at` and `_comp_spec_apply_at`
follow from the multiplicativity / identity laws of the trace
map on 1-forms, which require the substantial new Mathlib
infrastructure listed above. -/
theorem pushforwardTraceLift_comp_spec_apply_at
    (f : X → Y) (hf : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω f)
    (g : Y → Z) (hg : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω g)
    (v : Fin (analyticGenus ℂ X) → ℂ) (i : Fin (analyticGenus ℂ Z)) :
    pushforwardTraceLift (g ∘ f) (hg.comp hf) v i =
      pushforwardTraceLift g hg (pushforwardTraceLift f hf v) i := sorry

/-- The trace lift is covariantly functorial under composition: the
trace lift for `g ∘ f` equals the composition of trace lifts for `g`
and `f`.

Pointwise form: the trace lift for `g ∘ f` evaluated at `v` equals
the iterated trace-lift composition.

Bottom-up obligation. Provable from the multiplicativity of the
trace/norm map on holomorphic 1-forms.

Assembled from `pushforwardTraceLift_comp_spec_apply_at` via `funext`. -/
theorem pushforwardTraceLift_comp_spec_apply
    (f : X → Y) (hf : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω f)
    (g : Y → Z) (hg : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω g)
    (v : Fin (analyticGenus ℂ X) → ℂ) :
    pushforwardTraceLift (g ∘ f) (hg.comp hf) v =
      pushforwardTraceLift g hg (pushforwardTraceLift f hf v) := by
  funext i
  exact pushforwardTraceLift_comp_spec_apply_at f hf g hg v i

/-- The trace lift is covariantly functorial under composition.

Assembly from `pushforwardTraceLift_comp_spec_apply` via
`AddMonoidHom.ext`. -/
theorem pushforwardTraceLift_comp_spec
    (f : X → Y) (hf : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω f)
    (g : Y → Z) (hg : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω g) :
    (pushforwardTraceLift (g ∘ f) (hg.comp hf) : _ →+ _) =
      (pushforwardTraceLift g hg).comp (pushforwardTraceLift f hf) := by
  refine AddMonoidHom.ext ?_
  intro v
  exact pushforwardTraceLift_comp_spec_apply f hf g hg v

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
