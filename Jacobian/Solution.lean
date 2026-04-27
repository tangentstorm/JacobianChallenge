import Mathlib -- compiles with commit 8e3c989104daaa052921bf43de9eef0e1ac9fbf5 (15th April 2026)
import Jacobian.HolomorphicForms.CompactRiemannSurface
import Jacobian.HolomorphicForms.GenusZeroClassification
import Jacobian.Periods.PeriodLattice
import Jacobian.ComplexTorus.ULiftTransport

/-!

# Solution mirror of `Jacobian/Challenge.lean`

This file is the top-down refinement target for the Jacobian challenge,
designed for the [Lean comparator](https://github.com/leanprover/comparator)
workflow.

By comparator convention, this file is **independent** of `Challenge.lean`:
they import the same prelude (`Mathlib`) and define the same declaration
names, but neither imports the other. Comparator verifies kernel-level
declaration equivalence externally.

Top-down refinement strategy: each top-level declaration is replaced
round by round with a real construction in terms of named helper lemmas
in the production modules under `Jacobian/HolomorphicForms/`,
`Jacobian/Periods/`, and `Jacobian/ComplexTorus/`. The expected
trajectory is:

* round-by-round, the count of "top-level" `sorry`s in this file shrinks;
* each removed sorry is replaced by a body that delegates to one or
  more *named* sorries in production modules, each a precise
  mathematical obligation;
* eventually each helper `sorry` is discharged by the bottom-up
  Aristotle / hand-written work and the comparator should accept the
  result.

**Comparator note:** while staged refinement is in progress, the
imported helper modules contain `sorry`. Comparator runs that require
`sorryAx ∉ permitted_axioms` will not accept this file until those
sorries are discharged. See `Jacobian/WorkPackets/TopDown.md`.

## Refinement progress (current rounds)

* **Round 1** ✅ `genus`, `genus_eq_zero_iff_homeo` —
  delegated to `JacobianChallenge.HolomorphicForms.analyticGenus`
  and `analyticGenus_eq_zero_iff_homeomorphic_sphere`.
* **Round 2a** ✅ `Jacobian`, `AddCommGroup`, `TopologicalSpace`,
  `T2Space`, `CompactSpace` — defined as `ULift` of a
  complex-torus quotient by `periodFullComplexLattice`.
* **Round 2b** ✅ `ChartedSpace`, `IsManifold`, `LieAddGroup` —
  ULift transport of complex-torus instances; transport itself
  is the named obligation.

Remaining: Round 3 (`ofCurve` family), Round 4 (`pushforward`,
`pullback`, `degree`, `pushforward_pullback`).

-/

open scoped ContDiff -- for ω notation

open scoped Manifold -- for 𝓘 notation

/-- The genus of a compact Riemann surface.

Refinement (Round 1, top-down): `genus X := analyticGenus ℂ X`, the
ℂ-dimension of the space of holomorphic 1-forms. Finite-dimensionality
is supplied by the global instance
`compactRiemannSurface_finiteDimensionalHolomorphicOneForms`
in `Jacobian.HolomorphicForms.CompactRiemannSurface`. -/
noncomputable def genus (X : Type*) [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X] : ℕ :=
  JacobianChallenge.HolomorphicForms.analyticGenus ℂ X

-- let X be a compact Riemann surface
variable {X : Type*} [TopologicalSpace X] [T2Space X] [CompactSpace X] [ConnectedSpace X]
  [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]

-- this proof avoids the hack answer `∀ X, genus X = 0`
-- Refinement (Round 1, top-down): delegated to the named obligation
-- `analyticGenus_eq_zero_iff_homeomorphic_sphere`.
lemma genus_eq_zero_iff_homeo :
    genus X = 0 ↔ Nonempty (X ≃ₜ (Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1)) :=
  JacobianChallenge.HolomorphicForms.analyticGenus_eq_zero_iff_homeomorphic_sphere X

universe u in
-- data
/-- The Jacobian of a compact Riemann surface.

Refinement (Round 2a, top-down): `Jacobian X := ULift (V ⧸ Λ)` where
`V = Fin (genus X) → ℂ` is the basis-aligned model space and
`Λ = periodFullComplexLattice X` is the period lattice. The `ULift`
brings the analytic quotient (which lives in `Type 0`) up to the
challenge's `Type u`. -/
noncomputable def Jacobian (X : Type u) [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X] : Type u :=
  ULift.{u} (JacobianChallenge.ComplexTorus.quotient
    (Fin (genus X) → ℂ) (JacobianChallenge.Periods.periodFullComplexLattice X))

namespace Jacobian

-- data
/-- The Jacobian of a compact Riemann surface is naturally an additive commutative group. -/
noncomputable instance : AddCommGroup (Jacobian X) :=
  inferInstanceAs (AddCommGroup (ULift _))

-- data
/-- The Jacobian of a compact Riemann surface is naturally a topological space. -/
noncomputable instance : TopologicalSpace (Jacobian X) :=
  inferInstanceAs (TopologicalSpace (ULift _))

-- Prop
instance : T2Space (Jacobian X) := inferInstanceAs (T2Space (ULift _))

-- Prop
instance : CompactSpace (Jacobian X) := inferInstanceAs (CompactSpace (ULift _))

-- data
/-- The Jacobian of a compact Riemann surface is a complex manifold, of dimension
equal to the genus of the surface.
Refinement (Round 2b): ULift transport of `complexTorusChartedSpace`. -/
noncomputable instance : ChartedSpace (Fin (genus X) → ℂ) (Jacobian X) :=
  inferInstanceAs (ChartedSpace (Fin (genus X) → ℂ) (ULift _))

-- Prop
/-- Refinement (Round 2b): ULift transport of `complexTorusIsManifold`. -/
noncomputable instance : IsManifold (modelWithCornersSelf ℂ (Fin (genus X) → ℂ)) ω
    (Jacobian X) :=
  inferInstanceAs (IsManifold (modelWithCornersSelf ℂ (Fin (genus X) → ℂ)) ω
    (ULift _))

-- Prop
/-- Refinement (Round 2b): ULift transport of `lieAddGroup_quotient`. -/
noncomputable instance : LieAddGroup (modelWithCornersSelf ℂ (Fin (genus X) → ℂ)) ω
    (Jacobian X) :=
  inferInstanceAs (LieAddGroup (modelWithCornersSelf ℂ (Fin (genus X) → ℂ)) ω
    (ULift _))

/-- The Abel-Jacobi map from a compact Riemann surface to its Jacobian. -/
def ofCurve (P : X) : X → Jacobian X := sorry

lemma ofCurve_contMDiff (P : X) : ContMDiff 𝓘(ℂ)
    (modelWithCornersSelf ℂ (Fin (genus X) → ℂ)) ω (ofCurve P) := sorry

lemma ofCurve_self (P : X) : ofCurve P P = 0 := sorry

-- this is the lemma which stops the hack answer "J(X)=0 for all X"
lemma ofCurve_inj (P : X) (h : 0 < genus X) : Function.Injective (ofCurve P) := sorry

variable {Y : Type*} [TopologicalSpace Y] [T2Space Y] [CompactSpace Y] [ConnectedSpace Y]
  [ChartedSpace ℂ Y] [IsManifold 𝓘(ℂ) ω Y]

variable (f : X → Y) (hf : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω f)

/-- The pushforward map between Jacobians associated to a map of the underlying curves. -/
def pushforward (f : X → Y)
    (hf : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω f) :
    Jacobian X →ₜ+ Jacobian Y := sorry

-- pushforward is holomorphic
theorem pushforward_contMDiff :
  ContMDiff (modelWithCornersSelf ℂ (Fin (genus X) → ℂ))
  (modelWithCornersSelf ℂ (Fin (genus Y) → ℂ)) ω (pushforward f hf) := sorry

-- functoriality
lemma pushforward_id_apply (P : Jacobian X) : pushforward id contMDiff_id P = P := sorry

variable {Z : Type*} [TopologicalSpace Z] [T2Space Z] [CompactSpace Z] [ConnectedSpace Z]
  [ChartedSpace ℂ Z] [IsManifold 𝓘(ℂ) ω Z]

variable (g : Y → Z) (hg : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω g)

-- functoriality
lemma pushforward_comp_apply (P : Jacobian X) :
    pushforward (g ∘ f) (hg.comp hf) P = pushforward g hg (pushforward f hf P) :=
  sorry

/-- Pullback map between Jacobians associated to a map of the underlying curves.
Equal to the zero map if the map on curves is constant. -/
def pullback (f : X → Y)
    (hf : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω f) :
    Jacobian Y →ₜ+ Jacobian X := sorry

-- pullback is holomorphic
theorem pullback_contMDiff :
    ContMDiff (modelWithCornersSelf ℂ (Fin (genus Y) → ℂ))
      (modelWithCornersSelf ℂ (Fin (genus X) → ℂ)) ω (pullback f hf) := sorry

-- functoriality
lemma pullback_id_apply (P : Jacobian X) : pullback id contMDiff_id P = P := sorry

-- functoriality
lemma pullback_comp_apply (P : Jacobian Z) :
    pullback (g.comp f) (hg.comp hf) P = pullback f hf (pullback g hg P) := sorry

/-- The degree of a holomorphic map between compact Riemann surfaces. Equal to zero
for constant maps, otherwise equal to the usual degree. -/
def _root_.ContMDiff.degree
    (hf : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω f) : ℕ :=
  sorry

lemma pushforward_pullback (P : Jacobian Y) :
  pushforward f hf (pullback f hf P) = (ContMDiff.degree f hf) • P := sorry

end Jacobian
