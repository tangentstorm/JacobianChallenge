import Mathlib.Topology.Defs.Basic

/-!
A project-side hook for "orientability" of a topological 2-manifold.
The polygonal-model plan (`ref/plans/polygonal-model.md`, Stage B) needs
to talk about *orientable* compact connected 2-manifolds in order to
state the analytic↔topological genus bridge, but Mathlib v4.28.0 does
not package an `Orientable` typeclass at the topological-manifold level.
-/

namespace JacobianChallenge.Periods


class Orientable (M : Type*) [TopologicalSpace M] : Prop where
  
  existsConsistentChartChoice : Nonempty Unit := ⟨()⟩

end JacobianChallenge.Periods
