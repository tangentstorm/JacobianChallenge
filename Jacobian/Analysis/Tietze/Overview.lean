/-!
# R2 — Tietze normal form for orientable surface words

Headline statement:

> Every edge word arising from a polygonal presentation of a compact
> connected orientable 2-manifold of genus `g` is Tietze-equivalent to
> the standard relator
> `a₁ b₁ a₁⁻¹ b₁⁻¹ ⋯ a_g b_g a_g⁻¹ b_g⁻¹`.

This is the combinatorial heart of the topological-classification
theorem (Brahana 1921, Seifert–Threlfall 1934).  Independent build
target for the R2 classical-analysis gap.

The pre-existing bottom-up scaffolding lives at
`Jacobian/StageA/EdgeWordTietze.lean` (sketch) and the project-side
combinatorial reduction at `Jacobian/Periods/TietzeReduction.lean`.

**Status.** Every name below is a `True` placeholder; the headline
realisation in `StageA.orientable_edgeWord_tietzeEq_standardWord`
remains `sorry`.
-/

namespace JacobianChallenge.Analysis.Tietze

/-! ### Headline -/

/-- **R2 headline (placeholder type).**  Tietze normal form for the
edge word of a compact connected orientable triangulated 2-manifold. -/
theorem tietze_overview : True := trivial

/-! ### Sub-leaves — Phase 1: cyclic reduction -/

/-- **R2.1.1.** Inverse-pair cancellation is a Tietze move: removing
`ℓ ℓ⁻¹` from anywhere in a word produces a Tietze-equivalent word. -/
theorem tietze_inverse_cancel_move : True := trivial

/-- **R2.1.2.** Iterated inverse-pair cancellation reduces every word to
a *cyclically reduced* form (no immediate inverse adjacencies, even
across the cyclic seam). -/
theorem tietze_cyclic_reduction : True := trivial

/-! ### Sub-leaves — Phase 2: handle separation -/

/-- **R2.2.1.** A handle pair `a b a⁻¹ b⁻¹` can be cyclically rotated
to a canonical four-letter block at any position. -/
theorem tietze_handle_block_rotation : True := trivial

/-- **R2.2.2.** Two complete handle blocks may be permuted within the
word (the *handle-swap* Tietze move). -/
theorem tietze_handle_swap_move : True := trivial

/-- **R2.2.3.** A pair of generators that occurs in the *non-standard*
order (e.g. `a a` or `a⁻¹ a⁻¹` adjacent to mixed material) is reduced
to a handle block by the *Brahana handle-creation* trick. -/
theorem tietze_brahana_handle_creation : True := trivial

/-! ### Sub-leaves — Phase 3: orientability flag preservation -/

/-- **R2.3.1.** Tietze moves preserve orientability of the underlying
surface (every move acts on a presentation of the same fundamental
group up to a controlled HNN extension). -/
theorem tietze_moves_preserve_orientability : True := trivial

/-- **R2.3.2.** An orientable cyclically reduced word is a concatenation
of handle blocks (no `a a` blocks, no `a⁻¹ a⁻¹` blocks, all letters
appear with one positive and one negative occurrence). -/
theorem tietze_orientable_is_handle_concat : True := trivial

/-! ### Sub-leaves — Phase 4: induction on length -/

/-- **R2.4.1.** A word of length 0 is trivially equal to the genus-0
standard word (the empty word). -/
theorem tietze_base_case_length_zero : True := trivial

/-- **R2.4.2.** A cyclically reduced orientable word of length `4(g+1)`
strips off one handle block to a length-`4g` word, on which the IH
applies. -/
theorem tietze_strip_one_handle : True := trivial

/-- **R2.4.3.** Inductive assembly: by R2.1.2 + R2.3.2 + R2.4.2,
every orientable surface word reduces to the standard relator. -/
theorem tietze_inductive_assembly : True := trivial

/-! ### Recursive sub-gaps surfaced

* **R2-sub-A.** Free-group presentation API on a finite alphabet.
  Mathlib has `FreeGroup` but not the surface-presentation
  `Presentation.{Sphere, Torus, Surface}` infrastructure.  Tracked
  in `Jacobian/Periods/EdgeWord.lean` (project-side).
* **R2-sub-B.** Cyclic-word equivalence on `List`.  Mathlib has
  `List.IsRotated`; not the cyclic-cancellation closure.
* **R2-sub-C.** Brahana–Seifert–Threlfall handle-creation lemma.
  Pure combinatorics on `List Letter`; ~40 LOC of routine work but
  needs the cyclic-rotation API of R2-sub-B. -/

theorem tietze_subgap_free_group_surface_presentation : True := trivial
theorem tietze_subgap_cyclic_word_equivalence : True := trivial
theorem tietze_subgap_brahana_handle_creation : True := trivial

end JacobianChallenge.Analysis.Tietze
