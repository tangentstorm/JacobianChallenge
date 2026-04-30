import Jacobian.HolomorphicForms.Divisor
import Jacobian.HolomorphicForms.FiniteDimensional
import Mathlib.Topology.Compactification.OnePoint.Basic

/-!
# Meromorphic maps to the Riemann sphere

This file introduces the production-facing interface used by the genus-zero
classification proof.  It is intentionally narrow: the fields record the
global map and the divisor data needed downstream.  Future bottom-up work can
replace the current theorem leaves by proofs from Mathlib's local
`MeromorphicAt`/order API.
-/

namespace JacobianChallenge.HolomorphicForms

open scoped Manifold

/-- A meromorphic map from a compact Riemann surface to `OnePoint ℂ`.

The `locally_meromorphic` field is currently a named placeholder predicate.
The durable part of the interface is that downstream code consumes its map
and the associated zero/pole divisors. -/
structure MeromorphicMapToSphere
    (X : Type*) [TopologicalSpace X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X] where
  toMap : X → OnePoint ℂ
  locally_meromorphic : Prop
  zeroDivisor : Divisor X
  poleDivisor : Divisor X
  principalDivisor : Divisor X
  principalDivisor_eq : principalDivisor = zeroDivisor - poleDivisor

namespace MeromorphicMapToSphere

variable {X : Type*} [TopologicalSpace X] [ChartedSpace ℂ X]
  [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X]

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

@[simp] theorem principal_eq_zeroDivisor_sub_poleDivisor
    (f : MeromorphicMapToSphere X) :
    f.principal = f.zeroDivisor - f.poleDivisor :=
  f.principalDivisor_eq

end MeromorphicMapToSphere

end JacobianChallenge.HolomorphicForms
