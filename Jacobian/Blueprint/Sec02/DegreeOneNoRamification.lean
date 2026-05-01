import Jacobian.HolomorphicForms.CotangentBundle

/-! # Blueprint stub: `lem:degree-one-no-ramification`

Section 2 of `tex/sections/02-holomorphic-forms-and-genus.tex`.

A degree-one holomorphic map between compact connected Riemann
surfaces is unramified — every fiber is a single point and the local
derivative of the map (in any chart) is nonzero.

This file is a scaffold so the blueprint dep-graph node has a Lean
target via `\lean{}`. The real statement requires the project's
`branched_degree` API (see `ref/plans/branched-degree.md`); until that
lands the body is a placeholder so this file compiles cleanly. -/

namespace JacobianChallenge.Blueprint

open scoped Manifold

/-- Degree-one holomorphic maps are unramified.

PLACEHOLDER STATEMENT: pending the project's `branched_degree` API the
conclusion is recorded as `True`. The intended statement is roughly
"for every `y : Y` the fiber `f ⁻¹' {y}` is a singleton and the chart
derivative of `f` at that point is nonzero". -/
theorem degree_one_no_ramification
    (X Y : Type*) [TopologicalSpace X] [TopologicalSpace Y]
    [ChartedSpace ℂ X] [ChartedSpace ℂ Y]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) Y]
    (_f : X → Y) :
    True := trivial

end JacobianChallenge.Blueprint
