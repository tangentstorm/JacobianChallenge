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

-- TODO Q1: cleanest discreteness predicate for `AddSubgroup V`?

-- TODO Q2: discrete + cocompact + closed in finite-dim normed real
-- space ↔ full-rank ZLattice — name and statement?

-- TODO Q3: does `IsZLattice ℝ L` give `DiscreteTopology L.toAddSubgroup`?

-- TODO Q4: 2-3 candidate fields for `FullComplexLattice`, with
-- one-line pro/con each.

-- TODO Q5 (optional): sketch the supply path in
-- `fullComplexLatticeOfZLattice`.

end JacobianChallenge.ComplexTorus
