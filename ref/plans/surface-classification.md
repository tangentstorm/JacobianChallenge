# Plan: Surface classification (Stage A of `thm:polygonal-model`)

Parent plan: `ref/plans/polygonal-model.md` §4 Stage A.
Status: **DECOMPOSE**. Mathlib v4.28.0 has none of the four classical
ingredients packaged; this plan breaks the gap into reachable leaves.

## 1. Mathematical target

Every compact connected oriented topological 2-manifold `M` is
homeomorphic to the standard fundamental polygon
`JacobianChallenge.Periods.Polygon4g g'` for a unique `g' : ℕ` (the
topological genus). This is the classical *closed-surface
classification theorem*.

The *output* of Stage A is the umbrella:

```
theorem compact_orientable_surface_classification
    (M : Type*) [TopologicalSpace M] [CompactSpace M] [T2Space M]
    [ConnectedSpace M] [Orientable M] [SmoothReal2Manifold M] :
    ∃ g' : ℕ, Nonempty (M ≃ₜ Polygon4g g')
```

(`Orientable` is the project-side placeholder typeclass shipped this
session in `Jacobian/Periods/Orientable.lean`; `SmoothReal2Manifold` is
the bundled smooth-real-2-manifold structure shipped in
`Jacobian/Periods/SmoothRealStructure.lean` as `SmoothReal2Structure`.)

## 2. Three-route comparison

Before decomposing, name the candidate proof routes so the chosen one
is visible later when an Aristotle leaf hits a wall.

**Route 1 — Radó + combinatorial reduction (CLASSICAL).**

> Every compact 2-manifold admits a finite triangulation (Radó);
> orientable triangulated 2-manifolds reduce to standard-form polygon
> words by a finite sequence of Tietze-like moves.

This is the textbook proof (Massey, *Algebraic Topology: An
Introduction*, ch. 1; Seifert-Threlfall §38–§43). It splits into
combinatorics + a single hard topological input (Radó). **Recommended
route — best fits Mathlib's incremental style.**

**Route 2 — Morse-theoretic handle decomposition.**

> Pick a Morse function on `M`; its handle decomposition gives the
> CW-cell counts; standard-form follows from cell rearrangement.

This route is shorter on paper but requires Morse theory on
2-manifolds, which Mathlib v4.28.0 has nothing of. Skipped.

**Route 3 — Combinatorial-only via simplicial complexes.**

> Skip Radó: just *assume* `M` comes pre-triangulated (state the
> classification for triangulated surfaces), then drop the
> Radó-equivalence as a separate axiom-statement leaf.

Ugly but tractable: defers the genuinely-hard topology (Radó) into
its own stand-alone axiom-style placeholder while letting the
combinatorial classification (the bulk of the work) land first.
Useful as a fallback if Aristotle keeps stalling on Radó leaves.

**Adopted: Route 1.** Falls back to Route 3 only if A1 (Radó) proves
intractable; the rest of the decomposition is unchanged either way.

## 3. Mathlib v4.28.0 inventory (Stage A specific)

| prerequisite                                         | status   | path / note                                                                                  |
|------------------------------------------------------|----------|----------------------------------------------------------------------------------------------|
| Triangulation / simplicial complex on top spaces     | PARTIAL  | `Mathlib.AlgebraicTopology.SimplicialSet` (abstract); no "geometric realisation = M" lemma  |
| CW-complex API                                       | PARTIAL  | `Mathlib.Topology.CWComplex.Basic` exists; no closed-2-manifold structure theorem            |
| `Polygon4g g` quotient                               | PRESENT  | `Jacobian/Periods/Polygon4g.lean`, sorry-free, 164 LOC                                        |
| Project `Orientable` typeclass                       | PRESENT  | `Jacobian/Periods/Orientable.lean`, placeholder witness                                       |
| Connected-sum of 2-manifolds                         | ABSENT   | needed for Route 1's classification-by-induction                                              |
| Edge-pairing words / fundamental polygon abstraction | ABSENT   | needed for A2; project-side `EdgeWord` type would be the natural API hook                     |
| Tietze-style word reductions                         | ABSENT   | the combinatorial heart of A2                                                                 |
| Radó's theorem (∃ triangulation)                     | ABSENT   | the hardest single Mathlib gap                                                                |
| Singular homology `H₁`                               | PRESENT  | `Mathlib.AlgebraicTopology.SingularHomology.Basic` (used elsewhere this session)              |
| Genus-zero classification (`M ≃ₜ S²` if `H₁ = 0`)    | ABSENT   | needed for the `g = 0` base case of an inductive A2                                           |

## 4. Decomposition into Aristotle-reachable leaves

### A1 — Triangulation existence (Radó-style)

Hardest leaf. Even decomposed:

| #   | Lean handle                                         | Class | Sketch                                                                                                                                                                                                                                  | Dep                  |
|-----|-----------------------------------------------------|-------|------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------|----------------------|
| A1.1 | `compact_2manifold_has_finite_chart_cover`         | SHORT | A compact `[ChartedSpace (EuclideanSpace ℝ (Fin 2))]` admits a finite atlas with each chart's source covering a precompact open in `ℝ²`. Compactness + chart-source openness + finite-subcover.                                          | smooth atlas         |
| A1.2 | `chart_admits_triangulation`                       | MEDIUM| Each open Euclidean chart's image admits a triangulation refining the chart boundary. Mathlib has `Polytope` machinery; combine with bary-subdivision.                                                                                  | A1.1                 |
| A1.3 | `triangulation_compatibility_on_overlap`           | MEDIUM| On chart overlaps, two chart-local triangulations admit a common refinement. Standard simplicial-mesh argument.                                                                                                                          | A1.2                 |
| A1.4 | `compact_2manifold_admits_triangulation` (umbrella)| HARD  | Assemble A1.1 + A1.2 + A1.3 into a global triangulation. Likely needs project-side `Triangulation M` data type + glue.                                                                                                                  | A1.1, A1.2, A1.3     |

Estimated LOC: ~1500–2500 just for A1. **A1 is the single biggest
risk in the whole plan.** If Aristotle stalls on A1.4, retreat to
Route 3 (state the umbrella as a postulate-style leaf and continue
with A2).

### A2 — Combinatorial classification of triangulated orientable 2-manifolds

Given a triangulation, reduce its boundary word to standard form. This
is purely combinatorial and is the intellectual core of the classical
proof.

| #    | Lean handle                                                | Class  | Sketch                                                                                                                                                          | Dep                |
|------|------------------------------------------------------------|--------|----------------------------------------------------------------------------------------------------------------------------------------------------------------|--------------------|
| A2.1 | `EdgeWord` (project-side type)                             | SHORT  | `inductive EdgeWord` carrying letters `a_i`, `b_i`, inverses, with normal-form predicate. Plus `wordQuotient : EdgeWord → TopCat` via a polygon quotient.       | none               |
| A2.2 | `triangulated_surface_to_edge_word`                        | MEDIUM | Cut a triangulated 2-manifold along a spanning tree of the dual graph, flatten to a polygon, read off the edge-pairing word.                                   | A1.4, A2.1         |
| A2.3 | `tietze_swap_lemma`                                        | SHORT  | `xy⁻¹y⁻¹x → ε` and `xyxy → x²y²` style equivalences, each as a hom in the wordQuotient.                                                                         | A2.1               |
| A2.4 | `tietze_handle_swap_lemma`                                 | MEDIUM | One full handle (`xyx⁻¹y⁻¹`) commutes with adjacent letters / can be moved to the front.                                                                        | A2.3               |
| A2.5 | `orientable_word_reduces_to_standard`                      | HARD   | Inductive: any orientable edge word reduces to `a₁b₁a₁⁻¹b₁⁻¹⋯a_gb_ga_g⁻¹b_g⁻¹` via finitely many A2.3/A2.4 moves. Genus is invariant under these moves.        | A2.3, A2.4         |
| A2.6 | `triangulated_orientable_surface_word` (umbrella)          | SHORT  | Compose A2.2 + A2.5: any triangulated orientable closed surface has a polygon word in standard form.                                                            | A2.2, A2.5         |

Estimated LOC: ~1000–1500 for A2. The combinatorics is mechanical
once `EdgeWord` exists; A2.5 is the inductive heart.

### A3 — Polygon word ↔ `Polygon4g g`

| #   | Lean handle                              | Class | Sketch                                                                                                                                                              | Dep         |
|-----|------------------------------------------|-------|----------------------------------------------------------------------------------------------------------------------------------------------------------------------|-------------|
| A3.1 | `polygon4g_eq_standard_word_quotient`   | SHORT | Show `Polygon4g g` (our project-local quotient of the closed disk) equals the `wordQuotient` of the standard `4g`-gon word. Direct identification of relations.   | A2.1        |
| A3.2 | `polygon4g_homeo_word_quotient`         | MEDIUM| Lift A3.1 to a `Homeomorph`. Direct from quotient-topology identification.                                                                                          | A3.1        |

Estimated LOC: ~150 for A3. Pure bookkeeping once A2.1's `EdgeWord`
is correct.

### A4 — Umbrella

```
theorem compact_orientable_surface_classification
    (M : Type*) [TopologicalSpace M] [CompactSpace M] [T2Space M]
    [ConnectedSpace M] [Orientable M] [SmoothReal2Manifold M] :
    ∃ g' : ℕ, Nonempty (M ≃ₜ Polygon4g g') := by
  obtain ⟨T, hT⟩ := compact_2manifold_admits_triangulation M
  obtain ⟨g', w, hw⟩ := triangulated_orientable_surface_word T
  exact ⟨g', polygon4g_homeo_word_quotient.symm.trans (...) ⟩  -- glue
```

Estimated LOC: ~30–50 for A4 (pure assembly).

## 5. LOC + risk summary

| Stage | Marginal LOC | Risk    | Aristotle-suitable?                         |
|-------|--------------|---------|---------------------------------------------|
| A1    | 1500–2500    | HIGH    | Only A1.1 + maybe A1.2; A1.3/A1.4 too big   |
| A2    | 1000–1500    | MEDIUM  | A2.1, A2.3, A2.6 yes; A2.2/A2.4/A2.5 marginal|
| A3    | 150          | LOW     | Both leaves yes                             |
| A4    | 30–50        | LOW     | Yes (pure assembly)                         |
| Total | 2700–4200    |         |                                             |

## 6. Suggested first-tick ralph/Aristotle seeds

Sized for codex/Aristotle's per-iter capacity, ranked by risk:

1. **A2.1 — `EdgeWord` type** (~80 LOC). Pure inductive type + normal
   form predicate + a `wordQuotient` definition via a partial-order
   relation. No proofs beyond `rfl`. Aristotle should one-shot this.
2. **A1.1 — `compact_2manifold_has_finite_chart_cover`** (~50 LOC).
   Pure Mathlib finite-subcover argument.
3. **A3.1 — `polygon4g_eq_standard_word_quotient`** (depends on A2.1).
   A relation-equality proof; medium-easy once A2.1 exists.
4. **A2.3 — `tietze_swap_lemma`** (depends on A2.1). Each individual
   swap is a 5–10 LOC `Quotient.sound` invocation.

These four leaves alone would unblock ~25% of Stage A's LOC budget at
low risk and create concrete handles for A2.5 / A1.4 to depend on.

## 7. What is genuinely unsolvable today

**Radó's theorem itself (A1.4 umbrella) is the hard wall.** Even with
A1.1–A1.3 landed, gluing chart-local triangulations into a global
triangulation requires either:

- a full simplicial-complex API on a topological space (Mathlib has the
  abstract simplicial set machinery but no "geometric realisation =
  this manifold" theorem), or
- a CW-complex-on-2-manifold structure theorem (also absent).

**Falling back to Route 3 (state Radó as a placeholder leaf) is the
realistic Plan B** if A1.4 stalls for >2 weeks of Aristotle attempts.
The combinatorial heart of the proof (A2) lands either way; only the
"every compact 2-manifold has a triangulation" preamble is at risk.

## 8. Sequencing

1. Land A2.1 (`EdgeWord`) first — unblocks A2.3/A2.4/A2.5 + A3.1.
2. Land A1.1, A1.2 in parallel with A2.1.
3. Build A3 once A2.1 is done.
4. Build A2.3, A2.4, A2.5 in sequence.
5. Attempt A1.3 + A1.4. If stuck, postulate-shape A1.4 (Route 3) and
   continue.
6. Land A4 as final assembly.

This sequencing means **the project gets a real `EdgeWord` API and
the start of polygon-word combinatorics without waiting on Radó**,
which is the right tradeoff for keeping motion.
