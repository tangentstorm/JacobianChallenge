import Jacobian.Blueprint.Sec01.MeromorphicFunctionConcrete

/-! Blueprint: leaf 3 of `def:meromorphic-function` in
`tex/sections/01-compact-riemann-surfaces.tex`.

The structural shape of a global meromorphic function on a compact Riemann
surface, as identified in `ref/plans/meromorphic-function.md`:

> structure MeromorphicFunction (X : Type*) [RiemannSurface X] where
>   f : ∀ x, MeromorphicGerm X x
>   glue : ∀ x y, …

i.e. a choice of meromorphic germ at every point, satisfying a cocycle /
gluing condition on overlaps. The plan classifies this as MEDIUM because
the genuine glue predicate must compare germ representatives across chart
changes, which in turn requires the meromorphic-germ-sheaf API of
leaf 2. Until that API exists, we record the structural shape with a
placeholder `glue` and document the gap. -/

namespace JacobianChallenge.Blueprint

open scoped Manifold

/-- A global meromorphic function on a compact Riemann surface, recorded
as a per-point choice of meromorphic germ together with a placeholder
gluing predicate.

Placeholder. The intended `glue` field is the cocycle/agreement
condition between germs at distinct points — i.e. that the chosen
representatives extend each other on overlaps of charts. Pinning down
that predicate requires the sheaf of meromorphic germs (leaf 2 of the
plan), which is currently absent from Mathlib v4.28.0. We therefore use
`True` so the structure is trivially inhabited and downstream files can
refer to the type without committing to the gluing API. -/
structure MeromorphicFunction
    (X : Type*) [TopologicalSpace X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X] where
  /-- The chosen meromorphic germ at each point of `X`. -/
  germs : ∀ x : X, MeromorphicGerm X x
  /-- The cocycle / overlap-agreement condition. Currently a placeholder
  `True`; the genuine predicate compares germ representatives on chart
  intersections and depends on the meromorphic-germ sheaf (leaf 2). -/
  glue : True

namespace MeromorphicFunction

variable {X : Type*} [TopologicalSpace X] [ChartedSpace ℂ X]
  [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X]

/-- The trivial meromorphic function with placeholder germs everywhere.
Inhabits `MeromorphicFunction X` while `MeromorphicGerm` is the `Unit`
placeholder. -/
def trivial : MeromorphicFunction X where
  germs := fun _ => (() : MeromorphicGerm X _)
  glue := True.intro

instance : Inhabited (MeromorphicFunction X) := ⟨trivial⟩

end MeromorphicFunction

end JacobianChallenge.Blueprint
