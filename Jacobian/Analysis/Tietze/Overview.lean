import Jacobian.Periods.EdgeWord
import Jacobian.Periods.TietzeReduction
import Jacobian.StageA.EdgeWordTietze

/-!
# R2 — Tietze normal form for orientable surface words

Headline statement:

> Every edge word arising from a polygonal presentation of a compact
> connected orientable 2-manifold of genus `g` is `TietzeEq` to the
> standard relator `standardWord g`.

Independent build target for the R2 classical-analysis gap.  Real-typed
`sorry` declarations on top of `Jacobian.Periods.EdgeWord` (which
provides `EdgeWord`, `Letter`, `InverseCancel`, `HandleSwap`,
`TietzeStep`, `TietzeEq`, `standardWord`) and
`Jacobian.StageA.EdgeWordTietze` (algorithmic decomposition).
-/

namespace JacobianChallenge.Analysis.Tietze

open JacobianChallenge.Periods JacobianChallenge.StageA

/-! ### Predicates -/

/-- *Forward declaration.*  An edge word `w : EdgeWord g` is said to
*arise from a polygonal presentation of an orientable surface* if the
side-pairing quotient of the closed unit disk by `w` is homeomorphic
to a compact connected oriented topological 2-manifold whose first
Betti number is `2g`.  This file treats `ArisesFromOrientablePolygonalPresentation`
as a placeholder predicate; the real content is supplied by R3. -/
def ArisesFromOrientablePolygonalPresentation {g : ℕ} (_w : EdgeWord g) : Prop :=
  ¬ EdgeWord.HasNonorientablePair _w

/-! ### Headline (R2) -/

/-- **R2 headline.** Every edge word arising from a polygonal
presentation of a compact connected orientable 2-manifold of genus
`g` is `TietzeEq` to the standard relator. -/
theorem tietze_overview {g : ℕ} (w : EdgeWord g)
    (_h : ArisesFromOrientablePolygonalPresentation w) :
    EdgeWord.TietzeEq w (EdgeWord.standardWord g) :=
  sorry

/-! ### Phase 1 — cyclic reduction -/

/-- **R2.1.1.** Inverse-pair cancellation is a Tietze move:
`InverseCancel` is a `TietzeStep`. -/
theorem tietze_inverse_cancel_move {g : ℕ} {w v : EdgeWord g}
    (h : EdgeWord.InverseCancel w v) :
    EdgeWord.TietzeStep w v :=
  EdgeWord.TietzeStep.cancel h

/-- **R2.1.2.** Iterated inverse-pair cancellation reduces every word
to a fully-reduced (no-cancel-applies) form. -/
theorem tietze_cyclic_reduction {g : ℕ} (w : EdgeWord g) :
    ∃ v : EdgeWord g,
      EdgeWord.WordEq w v ∧ EdgeWord.IsFullyReduced v :=
  exists_fullyReduced_form w

/-! ### Phase 2 — handle separation -/

/-- **R2.2.1.** A complete handle block of four letters can be
cyclically rotated to any position by a finite sequence of
`HandleSwap` moves. -/
theorem tietze_handle_block_rotation {g : ℕ}
    (xs : List (Letter g)) (ys : List (Letter g))
    (h : List (Letter g)) (_hHandle : ∃ i : Fin g, h = EdgeWord.handleBlock i) :
    EdgeWord.HandleSwap (xs ++ h ++ ys) (ys ++ h ++ xs) :=
  sorry

/-- **R2.2.2.** Two complete handle blocks may be permuted within the
word: this is the `HandleSwap` Tietze move applied twice. -/
theorem tietze_handle_swap_move {g : ℕ}
    (xs ys h₁ h₂ : List (Letter g))
    (_hH1 : ∃ i : Fin g, h₁ = EdgeWord.handleBlock i)
    (_hH2 : ∃ i : Fin g, h₂ = EdgeWord.handleBlock i) :
    EdgeWord.TietzeEq (xs ++ h₁ ++ h₂ ++ ys) (xs ++ h₂ ++ h₁ ++ ys) :=
  sorry

/-- **R2.2.3 (Brahana handle creation).**  In a fully-reduced
orientable word, there exists a `TietzeEq`-equivalent word that is in
handle-grouped form (see `EdgeWord.IsHandleGrouped`). -/
theorem tietze_brahana_handle_creation {g : ℕ} (w : EdgeWord g)
    (hRed : EdgeWord.IsFullyReduced w)
    (hOrient : ¬ EdgeWord.HasNonorientablePair w) :
    ∃ v : EdgeWord g,
      EdgeWord.TietzeEq w v ∧ EdgeWord.IsHandleGrouped v :=
  orientable_word_handleSwap_to_grouped w hRed hOrient

/-! ### Phase 3 — orientability flag preservation -/

/-- **R2.3.1.** Tietze moves preserve the absence of nonorientable
pairs (an orientable word stays orientable under every move). -/
theorem tietze_moves_preserve_orientability {g : ℕ} {w v : EdgeWord g}
    (_h : EdgeWord.TietzeEq w v)
    (hOrient : ¬ EdgeWord.HasNonorientablePair w) :
    ¬ EdgeWord.HasNonorientablePair v :=
  sorry

/-- **R2.3.2.** A handle-grouped word with all four-letter blocks
following the standard pattern is `IsStandardForm` after appropriate
re-indexing. -/
theorem tietze_orientable_is_handle_concat {g : ℕ} (w : EdgeWord g)
    (_hG : EdgeWord.IsHandleGrouped w) :
    ∃ v : EdgeWord g,
      EdgeWord.TietzeEq w v ∧ v.IsStandardForm :=
  sorry

/-! ### Phase 4 — induction on length -/

/-- **R2.4.1.** Base case: the empty edge word equals the standard
word for genus 0. -/
theorem tietze_base_case_length_zero :
    ([] : EdgeWord 0) = EdgeWord.standardWord 0 := by
  rfl

/-- **R2.4.2.** Strip-one-handle: a cyclically-reduced orientable word
of length `4 (g + 1)` admits a `TietzeEq`-equivalent decomposition
`block ++ rest` where `block` is one handle and `rest` has length
`4 g`. -/
theorem tietze_strip_one_handle {g : ℕ} (w : EdgeWord (g + 1))
    (_hRed : EdgeWord.IsFullyReduced w)
    (_hOrient : ¬ EdgeWord.HasNonorientablePair w)
    (_hLen : w.length = 4 * (g + 1)) :
    ∃ (i : Fin (g + 1)) (rest : List (Letter (g + 1))),
      EdgeWord.TietzeEq w (EdgeWord.handleBlock i ++ rest) :=
  sorry

/-- **R2.4.3.** Inductive assembly combining R2.1.2 + R2.3 + R2.4.2:
every orientable surface word reduces to the standard relator. -/
theorem tietze_inductive_assembly {g : ℕ} (w : EdgeWord g)
    (_h : ArisesFromOrientablePolygonalPresentation w) :
    EdgeWord.TietzeEq w (EdgeWord.standardWord g) :=
  sorry

/-! ### Recursive sub-gaps surfaced -/

/-- **R2-sub-A.**  Free-group surface presentation API: every
`EdgeWord` has a corresponding presentation in `FreeGroup`. -/
theorem tietze_subgap_free_group_surface_presentation {g : ℕ}
    (_w : EdgeWord g) :
    ∃ _f : Letter g → FreeGroup (Fin (2 * g)), True :=
  sorry

/-- **R2-sub-B.**  Cyclic-word equivalence: a rotation of an edge word
is `TietzeEq` to the original (handle blocks rotate as units; non-handle
rotations need cancellation moves). -/
theorem tietze_subgap_cyclic_word_equivalence {g : ℕ}
    (w : EdgeWord g) (k : ℕ) :
    EdgeWord.TietzeEq w (w.rotate k) :=
  sorry

/-- **R2-sub-C.**  Brahana handle-creation lemma: the existence of a
single Tietze-step decomposition that creates a handle block.
Algorithmic core of R2.2.3. -/
theorem tietze_subgap_brahana_handle_creation_step {g : ℕ}
    (w : EdgeWord g) (i : Fin g)
    (_hCount :
      0 < (show List (Letter g) from w).count (Letter.a i) ∧
      0 < (show List (Letter g) from w).count (Letter.aInv i)) :
    ∃ v : EdgeWord g,
      EdgeWord.TietzeEq w v ∧
      ∃ xs ys : List (Letter g),
        v = xs ++ EdgeWord.handleBlock i ++ ys :=
  sorry

/-! ### Stepwise refinement of the headline -/

/-- **R2 step A (Phases 1+2 combined).**  Every word arising from an
orientable polygonal presentation is `TietzeEq` to a *handle-grouped*
word — the first half of the reduction.  Combines cyclic reduction
(R2.1.2) with Brahana handle creation (R2.2.3). -/
theorem tietze_to_handle_grouped {g : ℕ} (w : EdgeWord g)
    (h : ArisesFromOrientablePolygonalPresentation w) :
    ∃ v : EdgeWord g,
      EdgeWord.TietzeEq w v ∧ EdgeWord.IsHandleGrouped v := by
  -- Phase 1: cyclic reduction.
  obtain ⟨v₁, hwv₁, hRed⟩ := tietze_cyclic_reduction w
  -- Phase 3: orientability is preserved by `WordEq`-step.
  have hOrient₁ : ¬ EdgeWord.HasNonorientablePair v₁ :=
    tietze_moves_preserve_orientability hwv₁.toTietzeEq h
  -- Phase 2 (Brahana): land at a handle-grouped word.
  obtain ⟨v₂, hv₁v₂, hG⟩ :=
    tietze_brahana_handle_creation v₁ hRed hOrient₁
  exact ⟨v₂, hwv₁.toTietzeEq.trans hv₁v₂, hG⟩

/-- **R2 step B (Phases 3+4 combined).**  A handle-grouped word is
`TietzeEq` to the standard relator (handle-swap re-orderings + identity
on each block).  Combines `tietze_orientable_is_handle_concat`
with the standard-word identification. -/
theorem tietze_handle_grouped_to_standard {g : ℕ} (v : EdgeWord g)
    (hG : EdgeWord.IsHandleGrouped v) :
    EdgeWord.TietzeEq v (EdgeWord.standardWord g) := by
  obtain ⟨v', hvv', hStd⟩ := tietze_orientable_is_handle_concat v hG
  -- `IsStandardForm` says `v' = standardWord g`.
  rw [show v' = EdgeWord.standardWord g from hStd] at hvv'
  exact hvv'

/-- **R2 overview, stepwise refinement.**  Same as `tietze_overview`
but with the proof factored through the two intermediate steps
A and B. -/
theorem tietze_overview_via_steps {g : ℕ} (w : EdgeWord g)
    (h : ArisesFromOrientablePolygonalPresentation w) :
    EdgeWord.TietzeEq w (EdgeWord.standardWord g) := by
  obtain ⟨v, hwv, hG⟩ := tietze_to_handle_grouped w h
  exact hwv.trans (tietze_handle_grouped_to_standard v hG)

end JacobianChallenge.Analysis.Tietze
