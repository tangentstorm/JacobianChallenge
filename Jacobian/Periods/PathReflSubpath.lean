import Mathlib.Topology.Subpath

/-!
# `Path.refl.subpath` is `Path.refl`

A small helper: every subpath of a constant path is itself the same
constant path. Useful for `_refl` lemmas on multi-chart path
integrals.
-/

namespace JacobianChallenge.Periods

variable {X : Type*} [TopologicalSpace X]

/-- Subpath of a constant path equals the constant path. -/
@[simp] theorem refl_subpath (a : X) (t₀ t₁ : unitInterval) :
    (Path.refl a).subpath t₀ t₁ = Path.refl a := by
  apply Path.ext
  rfl

end JacobianChallenge.Periods
