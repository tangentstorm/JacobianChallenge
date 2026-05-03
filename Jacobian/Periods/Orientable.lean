import Mathlib.Topology.Defs.Basic

/-!
# Orientable — placeholder typeclass

A project-side hook for "orientability" of a topological 2-manifold.
The polygonal-model plan (`ref/plans/polygonal-model.md`, Stage B) needs
to talk about *orientable* compact connected 2-manifolds in order to
state the analytic↔topological genus bridge, but Mathlib v4.28.0 does
not package an `Orientable` typeclass at the topological-manifold level.

This file introduces a tiny placeholder typeclass that downstream
statements can depend on by name. The current witness (`trivial`) is
deliberately uninformative — it lets the API stabilize while the actual
orientability content is filled in (e.g. via consistent chart choice,
top homology, or volume forms) by a later round.

When that round happens, this `class` is the single point to change:
its callers will continue to compile under `[Orientable M]` regardless
of how the witness is rewired internally.
-/

namespace JacobianChallenge.Periods

/-- Project-side placeholder typeclass for orientable topological
manifolds. The witness will be rewired (consistent chart choice / top
homology / volume form) in a later round; the class name is the stable
API hook. -/
class Orientable (M : Type*) [TopologicalSpace M] : Prop where
  /-- Placeholder witness — to be replaced by a concrete orientability
  statement (consistent chart choice / top-degree homology / volume
  form) once the surrounding infrastructure is built. -/
  existsConsistentChartChoice : Nonempty Unit := ⟨()⟩

end JacobianChallenge.Periods
