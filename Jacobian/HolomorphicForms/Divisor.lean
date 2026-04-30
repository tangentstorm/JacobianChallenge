import Mathlib.Data.Finsupp.Weight

/-!
# Divisors on compact Riemann surfaces

This module starts the production substrate for the genus-zero
Riemann-Roch route.  A divisor is represented by a finitely supported
integer-valued function on points.  The analytic content that identifies
these divisors with zero/pole data of meromorphic functions is built in
the neighboring meromorphic modules.
-/

namespace JacobianChallenge.HolomorphicForms

noncomputable section

/-- A divisor on `X`: a finite formal integer combination of points. -/
abbrev Divisor (X : Type*) : Type _ :=
  X →₀ ℤ

namespace Divisor

variable {X : Type*}

/-- The degree of a divisor, i.e. the sum of its coefficients. -/
def degree : Divisor X →+ ℤ :=
  Finsupp.degree

/-- The divisor consisting of the point `P` with coefficient `1`. -/
def point (P : X) : Divisor X :=
  Finsupp.single P 1

@[simp] theorem degree_zero : degree (0 : Divisor X) = 0 :=
  rfl

@[simp] theorem point_apply_self [DecidableEq X] (P : X) :
    point P P = 1 := by
  simp [point]

@[simp] theorem point_apply_ne [DecidableEq X] {P Q : X} (h : Q ≠ P) :
    point P Q = 0 := by
  simp [point, h]

@[simp] theorem degree_point (P : X) :
    degree (point P : Divisor X) = 1 := by
  exact Finsupp.degree_single P 1

/-- An effective divisor has nonnegative coefficient at every point. -/
def Effective (D : Divisor X) : Prop :=
  ∀ P, 0 ≤ D P

@[simp] theorem effective_zero : Effective (0 : Divisor X) := by
  intro P
  simp

theorem effective_point [DecidableEq X] (P : X) :
    Effective (point P : Divisor X) := by
  intro Q
  by_cases h : Q = P
  · subst h
    simp [point]
  · simp [point, h]

end Divisor

end

end JacobianChallenge.HolomorphicForms
