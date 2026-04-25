import Mathlib.Algebra.Module.ZLattice.Basic
import Jacobian.WorkPackets.StatementBank

/-!
# Reconnaissance: discreteness packaging for `FullComplexLattice`

Queue B reconnaissance packet. This file is **name-discovery only** —
no proofs required. The goal is to figure out the right discreteness
field for `FullComplexLattice` before the chart-layer packets land.

## Background and the standing trap

A closed cocompact additive subgroup of a finite-dimensional normed
real vector space is **NOT** in general discrete. Concrete
counterexample (in `ℝ²`):

```
  S := { (x, n) | x ∈ ℝ, n ∈ ℤ }   -- = ℝ × ℤ
```

`S` is a closed additive subgroup of `ℝ²`, the quotient `ℝ² / S` is
homeomorphic to a circle and hence compact (so `S` admits a compact
fundamental domain `[0,1] × [0,1]`), yet `S` is not discrete (the
real factor is connected).

So our current `FullComplexLattice` fields — `isClosed`,
`fundamentalDomain`, `fundamentalDomain_isCompact`,
`fundamentalDomain_covers` — together do **not** entail discreteness.
The manifold-layer chart construction needs discreteness as input
(to obtain the isolation-at-zero radius and inject `mk` on small
balls). We must therefore add a discreteness witness to
`FullComplexLattice`.

## Reconnaissance task for Aristotle

Please scan Mathlib (pinned commit `8f9d9cff` / `v4.28.0`) and write
the answers as comments next to each numbered question below. Do not
attempt to prove anything; just record findings.

1. What is the cleanest Mathlib predicate to express "`S : AddSubgroup V`
   is discrete in the subspace topology"?  Candidates: `DiscreteTopology
   S`, `IsClosed S ∧ ...`, `IsClosed S ∧ ProperSpace ...`, etc.
2. Does Mathlib have a lemma of the form "discrete + cocompact + closed
   in finite-dim normed real space ↔ full-rank ZLattice"?  Reference
   names? Statement skeleton?
3. Does `IsZLattice ℝ L` (where `L : Submodule ℤ E`) entail
   `DiscreteTopology L.toAddSubgroup`?  If yes, name the lemma.
4. List the cleanest 2-3 candidate fields to add to
   `FullComplexLattice` to entail discreteness. For each, give a
   one-line pro/con.
5. (Optional, only if you can do it without proof) Sketch in
   pseudocode how `fullComplexLatticeOfZLattice` would supply the
   chosen new discreteness field.

Output expectation: replace each `-- TODO` line below with a short
comment-form answer (one paragraph at most per question). No code
edits needed beyond comments. Do NOT add new declarations or
theorems; this file should only have the namespace declaration and
this docstring/comment block.
-/

namespace JacobianChallenge.ComplexTorus

-- Q1: cleanest discreteness predicate for `AddSubgroup V`?
--
-- `DiscreteTopology S` (where `S : AddSubgroup V` is viewed as a subtype with the
-- induced topology) is the cleanest and most canonical predicate in Mathlib v4.28.0.
-- It means the subspace topology on the carrier of `S` is the discrete topology.
-- This is the predicate used throughout `Mathlib/Topology/Algebra/` — for instance,
-- `AddSubgroup.isClosed_of_discrete` (in `Mathlib/Topology/Algebra/IsUniformGroup/Basic.lean`)
-- has the signature `[DiscreteTopology ↥H] : IsClosed ↑H`, confirming that
-- `DiscreteTopology` on the subtype is the standard Mathlib spelling. There is no
-- dedicated `IsDiscreteAddSubgroup` predicate; `DiscreteTopology ↥S` is the one to use.

-- Q2: discrete + cocompact + closed in finite-dim normed real space ↔ full-rank
-- ZLattice — name and statement?
--
-- No such biconditional equivalence exists in Mathlib v4.28.0. The closest forward
-- direction is `IsZLattice ℝ L` (in `Mathlib/Algebra/Module/ZLattice/Basic.lean`),
-- which is a *class* on `L : Submodule ℤ E` with `[DiscreteTopology ↥L]` as a
-- parameter and a single field `span_top : Submodule.span K ↑L = ⊤`. Given an
-- `IsZLattice ℝ L` instance one can derive closedness (via `AddSubgroup.isClosed_of_discrete`)
-- and cocompactness (via `ZLattice.isAddFundamentalDomain` producing a fundamental domain
-- with `ZSpan.fundamentalDomain_isBounded`, declared in the same file). However, the
-- *reverse* direction — "discrete + cocompact + closed ⇒ isomorphic to a ZLattice" —
-- is not formalized. None found in Mathlib v4.28.0; closest match is `IsZLattice` itself
-- with caveat that it only captures the forward implication.

-- Q3: does `IsZLattice ℝ L` give `DiscreteTopology L.toAddSubgroup`?
--
-- Not directly via a single named lemma. `IsZLattice ℝ L` *requires*
-- `[DiscreteTopology ↥L]` as a class parameter (where `↥L` is the `Submodule ℤ E`
-- coerced to a type). This gives `DiscreteTopology` on the *submodule* carrier, not
-- on `L.toAddSubgroup`. The two types `↥L` and `↥L.toAddSubgroup` have definitionally
-- equal carrier sets but are distinct Lean types, so a small bridge is needed. The
-- project's own `ZLatticeRecon.lean` file provides this bridge as
-- `discreteTopology_toAddSubgroup` using `DiscreteTopology.of_continuous_injective`
-- (from `Mathlib/Topology/Constructions.lean`). No pre-existing Mathlib lemma of the
-- form `Submodule.discreteTopology_toAddSubgroup` was found. In summary: discreteness
-- is an *assumption* of `IsZLattice`, not an *entailment*, and the transfer to
-- `AddSubgroup` requires a one-line bridge that is not yet in Mathlib.

-- Q4: 2-3 candidate fields for `FullComplexLattice`, with one-line pro/con each.
--
-- (a) `isDiscrete : DiscreteTopology Λ.subgroup`
--     Pro: minimal, self-contained, no dependency on `Submodule`/`IsZLattice` machinery;
--          directly usable by chart construction code that needs an isolation radius.
--     Con: makes `FullComplexLattice` carry one more field that is redundant when the
--          lattice originates from `IsZLattice`; slightly lower-level than ideal.
--
-- (b) Replace `subgroup : AddSubgroup V` with `submodule : Submodule ℤ V` plus
--     `[DiscreteTopology submodule]` and `[IsZLattice ℝ submodule]`.
--     Pro: maximally integrated with Mathlib's ZLattice API; discreteness, closedness,
--          and fundamental-domain existence all follow from existing lemmas.
--     Con: invasive refactor — every downstream reference to `Λ.subgroup` must change
--          to `Λ.submodule.toAddSubgroup`; also forces `NormedSpace ℝ V` and
--          `FiniteDimensional ℝ V` into scope, coupling the structure to real scalars.
--
-- (c) `isolationRadius : ℝ` with `isolationRadius_pos : 0 < isolationRadius` and
--     `isolated : ∀ x ∈ Λ.subgroup, x ≠ 0 → isolationRadius ≤ ‖x‖`.
--     Pro: gives an explicit numerical witness that chart construction can use directly
--          (ball of radius `isolationRadius / 2` injects under `mk`); implies
--          `DiscreteTopology` via `DiscreteTopology.of_forall_le_norm'`
--          (in `Mathlib/Analysis/Normed/Group/Basic.lean`).
--     Con: slightly more data than needed (the exact radius is not canonical); must be
--          extracted from `IsZLattice` via a compactness argument on the unit ball.
--
-- Recommendation: option (a) is the best balance of simplicity and compatibility. It
-- is easy to supply from `IsZLattice` (via the bridge in `ZLatticeRecon.lean`), does
-- not force a structural refactor, and is directly consumable by chart-layer code.

-- Q5 (optional): sketch the supply path in `fullComplexLatticeOfZLattice`.
--
-- `fullComplexLatticeOfZLattice` (in `ZLatticeRecon.lean`) already demonstrates this.
-- Pseudocode for supplying option (a)'s `isDiscrete` field:
--
--   isDiscrete := by
--     -- We have `[DiscreteTopology ↥L]` from the `IsZLattice` class parameter.
--     -- Transfer to `L.toAddSubgroup` via `DiscreteTopology.of_continuous_injective`:
--     --   the map `↥L.toAddSubgroup → ↥L` sending `⟨x, hx⟩ ↦ ⟨x, hx⟩` is
--     --   continuous (both carry the subspace topology from `V`) and injective.
--     exact discreteTopology_toAddSubgroup L
--
-- This is exactly what `ZLatticeRecon.lean` does for the `isClosed` field (which
-- first obtains `DiscreteTopology L.toAddSubgroup` and then applies
-- `AddSubgroup.isClosed_of_discrete`). With option (a), the same
-- `discreteTopology_toAddSubgroup` bridge lemma is reused directly as the field value.

end JacobianChallenge.ComplexTorus
