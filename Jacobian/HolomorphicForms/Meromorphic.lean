import Jacobian.HolomorphicForms.Divisor
import Jacobian.HolomorphicForms.FiniteDimensional
import Jacobian.HolomorphicForms.BranchedCover
import Mathlib.Topology.Compactification.OnePoint.Basic
import Mathlib.Geometry.Manifold.MFDeriv.Basic
import Jacobian.Periods.TrivializationContinuousLinearMapAt

/-!
# Meromorphic maps to the Riemann sphere

This file introduces the production-facing interface used by the genus-zero
classification proof.  It is intentionally narrow: the fields record the
global map together with the divisor data and analytic axioms needed
downstream.  Future bottom-up work can identify these axioms with the local
`MeromorphicAt`/order API.

### Why these fields are present

The structure used to carry only `toMap`, the three divisors, and the
algebraic relation `principalDivisor = zeroDivisor - poleDivisor`. That made
several genuinely-meromorphic facts (poles are effective, zeros and poles
have disjoint support, the map evaluates to `∞` at a pole, the modulus
diverges near a simple pole, etc.) impossible to prove from the structure
alone, so they were carried as `sorry` axioms in `RiemannRoch.lean` and
`MeromorphicDegree.lean`.  Each axiom field below records exactly one such
fact, with a stable docstring naming the analytic content.  Together they
form an axiom layer for "abstract" meromorphic maps; once the project's
`MeromorphicAt`-based bridge is in place, every constructor will discharge
these fields by appealing to that bridge rather than carrying a `sorry`. -/

namespace JacobianChallenge.HolomorphicForms

open scoped Manifold

/-- A meromorphic map from a compact Riemann surface to `OnePoint ℂ`.

The `locally_meromorphic` field is a named placeholder predicate; the
remaining axiom fields capture the structural consequences of being
genuinely meromorphic that the downstream API (Riemann-Roch, degree theory)
relies on. -/
structure MeromorphicMapToSphere
    (X : Type*) [TopologicalSpace X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X] where
  toMap : X → OnePoint ℂ
  locally_meromorphic : Prop
  zeroDivisor : Divisor X
  poleDivisor : Divisor X
  principalDivisor : Divisor X
  principalDivisor_eq : principalDivisor = zeroDivisor - poleDivisor
  /-- The pole divisor of a meromorphic function has nonneg coefficients
  pointwise.  This is the structural fact behind `Divisor.Effective f.poles`. -/
  poleDivisor_nonneg : ∀ P : X, 0 ≤ poleDivisor P
  /-- A point cannot simultaneously be a zero and a pole of a meromorphic
  function.  This expresses the disjoint-support property of the
  zero/pole divisor decomposition. -/
  zero_or_pole_eq_zero : ∀ Q : X, zeroDivisor Q = 0 ∨ poleDivisor Q = 0
  /-- Off the pole locus a meromorphic-map-to-sphere takes finite values
  in `OnePoint ℂ`.  Combined with continuity below, this captures that
  poles are exactly the preimage of `∞`. -/
  toMap_ne_infty_of_poleDivisor_zero :
    ∀ x : X, poleDivisor x = 0 → toMap x ≠ (OnePoint.infty : OnePoint ℂ)
  /-- A meromorphic-map-to-sphere is continuous on the locus of finite
  values (i.e. the complement of its pole set).  This is the
  `OnePoint`-restricted form of the classical "holomorphic away from
  poles ⇒ continuous". -/
  continuousOn_ne_infty :
    ContinuousOn toMap {x : X | toMap x ≠ (OnePoint.infty : OnePoint ℂ)}
  /-- Any global complex-valued lift of `toMap` through the canonical
  inclusion `ℂ → OnePoint ℂ` is `MDifferentiable`.  This implements
  "holomorphic ⇒ smooth" for the lifted map. -/
  toFiniteFun_mdifferentiable :
    ∀ g : X → ℂ,
      toMap = (fun x => ((g x : ℂ) : OnePoint ℂ)) →
      MDifferentiable (modelWithCornersSelf ℂ ℂ) 𝓘(ℂ, ℂ) g
  /-- At a (positive-order) pole of a meromorphic-map-to-sphere, the map
  evaluates to `∞ : OnePoint ℂ`. -/
  toMap_eq_infty_of_poleDivisor_pos :
    ∀ P : X, 0 < poleDivisor P → toMap P = (OnePoint.infty : OnePoint ℂ)

namespace MeromorphicMapToSphere

variable {X : Type*} [TopologicalSpace X] [ChartedSpace ℂ X]
  [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X]
  [JacobianChallenge.Periods.StableChartAt ℂ X]

instance : CoeFun (MeromorphicMapToSphere X) (fun _ => X → OnePoint ℂ) where
  coe f := f.toMap

/-- The zero divisor of a meromorphic map. -/
def zeros (f : MeromorphicMapToSphere X) : Divisor X :=
  f.zeroDivisor

/-- The pole divisor of a meromorphic map. -/
def poles (f : MeromorphicMapToSphere X) : Divisor X :=
  f.poleDivisor

/-- The principal divisor `(f)`, zeros minus poles. -/
def principal (f : MeromorphicMapToSphere X) : Divisor X :=
  f.principalDivisor

/-- A meromorphic map has one simple pole at `P` and no other poles. -/
def HasSimplePoleOnlyAt (f : MeromorphicMapToSphere X) (P : X) : Prop :=
  f.poles = Divisor.point P

/-- A meromorphic map is nonconstant. -/
def Nonconstant (f : MeromorphicMapToSphere X) : Prop :=
  ¬ ∃ c : OnePoint ℂ, ∀ x : X, f.toMap x = c

/-- Membership in the Riemann-Roch space `L(D)`: `(f) + D ≥ 0`.

This is the divisor-theoretic condition that `f` has poles bounded by `D`. -/
def MemRiemannRochSpace (f : MeromorphicMapToSphere X) (D : Divisor X) : Prop :=
  Divisor.Effective (f.principal + D)

/-- A named predicate for continuity of the map to `OnePoint ℂ`.  This is
kept separate from meromorphicity because proving continuity of the extended
map is one of the degree/properness work packets. -/
def ExtendsContinuously (f : MeromorphicMapToSphere X) : Prop :=
  Continuous f.toMap

/-- Additional analytic data for an honest meromorphic map: near a pole,
the map admits a finite lift on the non-pole locus whose modulus tends to
infinity.  This is deliberately separate from `MeromorphicMapToSphere`
because several scaffold maps carry formal divisor data without satisfying
this analytic conclusion. -/
structure PoleModulusData (f : MeromorphicMapToSphere X) where
  exists_modulus_atTop_at_pole :
    ∀ P : X, 0 < f.poleDivisor P →
      ∃ g : X → ℂ,
        (∀ x : X, f.poleDivisor x = 0 →
          f.toMap x = ((g x : ℂ) : OnePoint ℂ)) ∧
        Filter.Tendsto (fun x => ‖g x‖) (nhdsWithin P {P}ᶜ) Filter.atTop

/-- Additional analytic data for an honest nonconstant meromorphic map:
conditional on continuity, it has branched-cover data whose degree is the
degree of the pole divisor.  This is not a field of
`MeromorphicMapToSphere`, since it is false for the cutoff/indicator
scaffolding maps used elsewhere in this file family. -/
structure BranchedCoverDataOfPoleDegree (f : MeromorphicMapToSphere X) where
  hasBranchedCoverDataOfPoleDegree :
    Continuous f.toMap →
    ∃ (h : JacobianChallenge.HolomorphicForms.BranchedCoverData X (OnePoint ℂ) f.toMap),
      JacobianChallenge.HolomorphicForms.branchedDegree h = f.poleDivisor.degree.toNat

omit [Periods.StableChartAt ℂ X] in
@[simp] theorem principal_eq_zeroDivisor_sub_poleDivisor
    (f : MeromorphicMapToSphere X) :
    f.principal = f.zeroDivisor - f.poleDivisor :=
  f.principalDivisor_eq

end MeromorphicMapToSphere

end JacobianChallenge.HolomorphicForms
