/-
Copyright (c) 2026 Jacobian Challenge contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.Data.Finset.Sort
import Mathlib.Data.List.Sort

/-!
# Helper lemmas: `Finset.sort` and `Finset.orderEmbOfFin` interact with `Finset.erase`

These pure-Mathlib lemmas bridge `Finset.orderEmbOfFin` evaluation through
`Finset.erase` to the underlying `List.eraseIdx`. They are used in
`Jacobian/StageA/CellularSingular.lean` to discharge the simplicial
`∂² = 0` identity for the cellular chain complex of an abstract
simplicial complex.

## Main results

* `Finset.sort_erase` — the sort of `s.erase v` equals the sort of `s`
  with `v` removed (as a list).
* `Finset.orderEmbOfFin_erase_lt` — `(s.erase v_p).orderEmbOfFin h k =
  s.orderEmbOfFin h ⟨k, _⟩` for `k < p`.
* `Finset.orderEmbOfFin_erase_ge` — `(s.erase v_p).orderEmbOfFin h k =
  s.orderEmbOfFin h ⟨k+1, _⟩` for `k ≥ p`.

## Mathlib gap

Mathlib v4.28.0 has `Finset.orderEmbOfFin` (in `Mathlib/Data/Finset/Sort.lean`)
but no lemmas relating it to `Finset.erase`. The bridge through
`List.getElem_eraseIdx` (Lean stdlib) was developed for this purpose.
-/

namespace Finset

variable {α : Type*} [LinearOrder α] [DecidableEq α]

/-- The sort of `s.erase v` equals the sort of `s` with `v` erased
(as a list). -/
theorem sort_erase (s : Finset α) (v : α) (hv : v ∈ s) :
    (s.erase v).sort (· ≤ ·) = (s.sort (· ≤ ·)).erase v := by
  apply List.Perm.eq_of_pairwise (le := (· ≤ ·))
    (fun _ _ _ _ => le_antisymm)
    ((s.erase v).sort_sorted (· ≤ ·))
    ((s.sort_sorted (· ≤ ·)).sublist (List.erase_sublist (a := v)))
  -- Show the two lists are permutations: same multiset.
  apply (Multiset.coe_eq_coe).mp
  rw [Finset.sort_eq, ← Multiset.coe_erase, Finset.sort_eq, Finset.erase_val]

/-- The sort of `s.erase v` equals `(s.sort).eraseIdx p` when `v` is the
`p`-th element of `s.sort` (i.e., `v = s.orderEmbOfFin _ p`). -/
private theorem sort_erase_eq_eraseIdx
    (s : Finset α) {n : ℕ} (h : s.card = n + 1) (p : Fin (n + 1)) :
    (s.erase (s.orderEmbOfFin h p)).sort (· ≤ ·) =
      (s.sort (· ≤ ·)).eraseIdx p.val := by
  have hv_mem : s.orderEmbOfFin h p ∈ s := Finset.orderEmbOfFin_mem _ _ _
  rw [sort_erase _ _ hv_mem]
  -- Use Nodup.erase_getElem to convert erase to eraseIdx.
  have hndp : (s.sort (· ≤ ·)).Nodup := s.sort_nodup _
  have hp_lt : p.val < (s.sort (· ≤ ·)).length := by
    rw [Finset.length_sort]; rw [h]; exact p.isLt
  have hgetElem : (s.sort (· ≤ ·))[p.val]'hp_lt = s.orderEmbOfFin h p := by
    rw [Finset.orderEmbOfFin_apply]
    simp [Fin.getElem_fin]
  rw [← hgetElem, hndp.erase_getElem p.val hp_lt]

/-- For `k < p`, the `k`-th sorted vertex of `s.erase (s.orderEmbOfFin h p)`
equals `s.orderEmbOfFin h ⟨k.val, _⟩` (no shift).

The proof routes through `List.getElem_eraseIdx_of_lt`. The bound-proof
bookkeeping for `Finset.orderEmbOfFin` versus `(s.sort).eraseIdx` indexing
hits a `motive`-correctness issue with `rw`; left as `sorry`. -/
theorem orderEmbOfFin_erase_lt
    (s : Finset α) {n : ℕ} (h : s.card = n + 1) (p : Fin (n + 1))
    (k : Fin n)
    (hcard : (s.erase (s.orderEmbOfFin h p)).card = n)
    (hk : k.val < p.val) :
    (s.erase (s.orderEmbOfFin h p)).orderEmbOfFin hcard k =
      s.orderEmbOfFin h ⟨k.val, by have := p.isLt; omega⟩ := by
  sorry

/-- For `k ≥ p`, the `k`-th sorted vertex of `s.erase (s.orderEmbOfFin h p)`
equals `s.orderEmbOfFin h ⟨k.val + 1, _⟩` (shift by 1).

Routes through `List.getElem_eraseIdx_of_ge`. Same `motive`-correctness
issue as the `_lt` companion. -/
theorem orderEmbOfFin_erase_ge
    (s : Finset α) {n : ℕ} (h : s.card = n + 1) (p : Fin (n + 1))
    (k : Fin n)
    (hcard : (s.erase (s.orderEmbOfFin h p)).card = n)
    (hk : p.val ≤ k.val) :
    (s.erase (s.orderEmbOfFin h p)).orderEmbOfFin hcard k =
      s.orderEmbOfFin h ⟨k.val + 1, by have := k.isLt; omega⟩ := by
  sorry

end Finset
