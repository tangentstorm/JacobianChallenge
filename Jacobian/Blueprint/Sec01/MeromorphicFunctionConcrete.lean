import Jacobian.Blueprint.Sec01.MeromorphicFunction

/-! Blueprint: concrete leaves of `def:meromorphic-function` in
`tex/sections/01-compact-riemann-surfaces.tex`.

Stubs for two of the SHORT/TRIVIAL sub-leaves identified in
`ref/plans/meromorphic-function.md`:

* Leaf 1 — `MeromorphicGerm`, the local meromorphic-germ data at a point.
* Leaf 4 — `MeromorphicOn`, the type of meromorphic functions on an open
  subset of the surface.

Leaf 7 (`principalDivisor`) is already covered by
`Jacobian/Blueprint/Sec01/PrincipalDivisor.lean` and is intentionally not
restated here.

The plan's intended Lean signatures depend on a meromorphic-germ /
local-frac-field API that does not yet exist on Riemann surfaces in
Mathlib v4.28.0 (`Mathlib.Analysis.Meromorphic.Basic` and
`Mathlib.Analysis.Meromorphic.Divisor` cover meromorphicity of `ℂ → ℂ`
functions, not the sheaf of meromorphic germs on a manifold). The two
definitions below are therefore placeholder aliases, kept thin enough
that downstream files can refer to the names without committing to a
representation. -/

namespace JacobianChallenge.Blueprint

open scoped Manifold

/-- The type of meromorphic germs at a point `x` of a compact Riemann
surface `X`.

Placeholder. The intended definition is
`FractionRing (HolomorphicGermAt X x)`, but the Mathlib v4.28.0 inventory
does not yet expose a sheaf of holomorphic germs on a Riemann surface or
the local-ring structure required to take its field of fractions. Once
that API lands, swap this alias for the genuine local frac field; current
downstream users only need a `Type*` placeholder. -/
def MeromorphicGerm
    (X : Type*) [TopologicalSpace X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X]
    (_x : X) : Type :=
  Unit

/-- The type of meromorphic functions on an open subset `U ⊆ X` of a
compact Riemann surface.

Placeholder thin wrapper around `MeromorphicFunctionType X`. The intended
definition restricts a global meromorphic function to `U` (or, dually,
takes a section of the meromorphic-function sheaf over `U`); since the
underlying `MeromorphicFunctionType` is itself a placeholder
(`X → OnePoint ℂ`), we currently expose only the global type and ignore
`U`. Refine once the sheaf of meromorphic germs is in place. -/
def MeromorphicOn
    (X : Type*) [TopologicalSpace X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X]
    (_U : Set X) : Type _ :=
  MeromorphicFunctionType X

end JacobianChallenge.Blueprint
