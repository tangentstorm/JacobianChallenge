# R2 — Tietze normal form for orientable surface words

**Headline.** Every edge word arising from a polygonal presentation
of a compact connected orientable 2-manifold of genus `g` is
Tietze-equivalent to the standard relator
`a₁ b₁ a₁⁻¹ b₁⁻¹ ⋯ a_g b_g a_g⁻¹ b_g⁻¹`.

**Lean target.** `JacobianChallenge.Analysis.Tietze.tietze_overview`
in `Overview.lean`; full realisation will replace
`StageA.orientable_edgeWord_tietzeEq_standardWord`.

**Build.** `lake build Jacobian.Analysis.Tietze`

## Classical proof (4 phases)

1. **Cyclic reduction.** Cancel `ℓ ℓ⁻¹` adjacencies, including across
   the cyclic seam; result is cyclically reduced.
2. **Handle separation.** In an orientable word, every letter
   appears with both signs; the Brahana handle-creation trick slides
   four interleaved letters into a contiguous handle block
   `a b a⁻¹ b⁻¹`.
3. **Orientability flag preservation.** Each Tietze move preserves
   orientability; orientable cyclically-reduced words are concatenations
   of handle blocks.
4. **Induction on length.** Strip one handle off the front, recurse
   on the shorter remainder.

Brahana 1921, Seifert–Threlfall 1934 (often presented in modern
textbooks following Massey).

## Lean plan (sub-leaves under `Overview.lean`)

| Sub-leaf | Phase | Status |
|---|---|---|
| `tietze_inverse_cancel_move` | 1 | placeholder |
| `tietze_cyclic_reduction` | 1 | placeholder |
| `tietze_handle_block_rotation` | 2 | placeholder |
| `tietze_handle_swap_move` | 2 | placeholder |
| `tietze_brahana_handle_creation` | 2 | placeholder |
| `tietze_moves_preserve_orientability` | 3 | placeholder |
| `tietze_orientable_is_handle_concat` | 3 | placeholder |
| `tietze_base_case_length_zero` | 4 | placeholder |
| `tietze_strip_one_handle` | 4 | placeholder |
| `tietze_inductive_assembly` | 4 | placeholder |

Existing edge-word algebra and the Tietze relation are sorry-free in
`Jacobian/Periods/EdgeWord.lean`; the reduction theorem itself is
sorry.

## Recursive sub-gaps

* **R2-sub-A.** Free-group surface presentation API on a finite
  alphabet.  ~200 LOC.
* **R2-sub-B.** Cyclic-word equivalence on `List` (cancellation
  closure beyond `List.IsRotated`).  ~80 LOC.
* **R2-sub-C.** Brahana handle-creation lemma.  ~150 LOC, single
  trickiest combinatorial step.

## Plain-English

Cut a surface open along loops; trace its boundary; you read off a
sequence of letters.  Tietze normal form says: this sequence
simplifies, by a finite chain of trivial moves (cancel `ℓ ℓ⁻¹`,
permute handle blocks), to one canonical pattern.  The proof is
induction on length: cancel until cyclically reduced, slide one
handle to the front via Brahana's trick, strip it off, recurse.

## See also

* Blueprint section `subsec:gap-R2-tietze` in
  `tex/sections/12-classical-analysis-gaps.tex`.
* Bottom-up sketch `Jacobian/StageA/EdgeWordTietze.lean`.
* Project-side reduction `Jacobian/Periods/TietzeReduction.lean`.

**Estimated full LOC** (R2 + sub-A + sub-B + sub-C): 900–1100.
