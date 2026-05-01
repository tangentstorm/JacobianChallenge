import Jacobian.HolomorphicForms.CotangentBundle

/-! # Blueprint stub: `thm:degree-one-bijective`

Section 2 of `tex/sections/02-holomorphic-forms-and-genus.tex`.

A degree-one holomorphic map between compact connected Riemann
surfaces is bijective: degree one forces every fiber to have a single
sheet (injectivity), and properness of holomorphic maps from a compact
domain forces surjectivity onto the connected target.

This file is a scaffold so the blueprint dep-graph node has a Lean
target via `\lean{}`. The real statement requires the project's
`branched_degree` API (`ref/plans/branched-degree.md`); until that
lands the body is a placeholder so this file compiles cleanly. -/

namespace JacobianChallenge.Blueprint

open scoped Manifold

/-- Degree-one holomorphic maps between compact connected Riemann
surfaces are bijective.

PLACEHOLDER STATEMENT: pending the project's `branched_degree` API the
conclusion is recorded as `True`. The intended statement is roughly
"`f.Bijective`", with hypotheses pinning down `branchedDegree f = 1`
and connectedness/compactness on `X` and `Y`. -/
theorem degree_one_bijective
    (X Y : Type*) [TopologicalSpace X] [TopologicalSpace Y]
    [ChartedSpace ℂ X] [ChartedSpace ℂ Y]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) Y]
    (_f : X → Y) :
    True := trivial

end JacobianChallenge.Blueprint
