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
theorem sort_erase (s : Finset α) (v : α) :
    (s.erase v).sort (· ≤ ·) = (s.sort (· ≤ ·)).erase v := by
  apply List.Perm.eq_of_pairwise (le := (· ≤ ·))
    (fun _ _ _ _ => le_antisymm)
    ((s.erase v).pairwise_sort (· ≤ ·))
    ((s.pairwise_sort (· ≤ ·)).sublist (List.erase_sublist (a := v)))
  -- Show the two lists are permutations: same multiset.
  apply (Multiset.coe_eq_coe).mp
  rw [Finset.sort_eq, ← Multiset.coe_erase, Finset.sort_eq, Finset.erase_val]

/-- The sort of `s.erase v` equals `(s.sort).eraseIdx p` when `v` is the
`p`-th element of `s.sort` (i.e., `v = s.orderEmbOfFin _ p`). -/
private theorem sort_erase_eq_eraseIdx
    (s : Finset α) {n : ℕ} (h : s.card = n + 1) (p : Fin (n + 1)) :
    (s.erase (s.orderEmbOfFin h p)).sort (· ≤ ·) =
      (s.sort (· ≤ ·)).eraseIdx p.val := by
  rw [sort_erase _ _]
  have hndp : (s.sort (· ≤ ·)).Nodup := s.sort_nodup _
  have hp_lt : p.val < (s.sort (· ≤ ·)).length := by
    rw [Finset.length_sort]; rw [h]; exact p.isLt
  have hgetElem : (s.sort (· ≤ ·))[p.val]'hp_lt = s.orderEmbOfFin h p := by
    rw [Finset.orderEmbOfFin_apply]
    simp [Fin.getElem_fin]
  rw [← hgetElem, hndp.erase_getElem p.val hp_lt]

/-- Helper: pure-list-level form of `orderEmbOfFin_erase_lt`. -/
private theorem orderEmbOfFin_erase_lt_aux
    (s : Finset α) {n : ℕ} (h : s.card = n + 1) (p : Fin (n + 1))
    (k : Fin n) (hk : k.val < p.val) :
    ∀ (h₁ : k.val < ((s.erase (s.orderEmbOfFin h p)).sort (· ≤ ·)).length)
      (h₂ : k.val < (s.sort (· ≤ ·)).length),
    ((s.erase (s.orderEmbOfFin h p)).sort (· ≤ ·))[k.val]'h₁ =
    (s.sort (· ≤ ·))[k.val]'h₂ := by
  intro h₁ h₂
  -- Re-introduce h₁ after rewriting via hsort: this forces Lean to
  -- elaborate the bound proof in the rewritten form.
  have hsort := sort_erase_eq_eraseIdx s h p
  revert h₁
  rw [hsort]
  intro h₁
  exact List.getElem_eraseIdx_of_lt _ hk

/-- Helper: pure-list-level form of `orderEmbOfFin_erase_ge`. -/
private theorem orderEmbOfFin_erase_ge_aux
    (s : Finset α) {n : ℕ} (h : s.card = n + 1) (p : Fin (n + 1))
    (k : Fin n) (hk : p.val ≤ k.val) :
    ∀ (h₁ : k.val < ((s.erase (s.orderEmbOfFin h p)).sort (· ≤ ·)).length)
      (h₂ : k.val + 1 < (s.sort (· ≤ ·)).length),
    ((s.erase (s.orderEmbOfFin h p)).sort (· ≤ ·))[k.val]'h₁ =
    (s.sort (· ≤ ·))[k.val + 1]'h₂ := by
  intro h₁ h₂
  have hsort := sort_erase_eq_eraseIdx s h p
  revert h₁
  rw [hsort]
  intro h₁
  exact List.getElem_eraseIdx_of_ge _ hk

/-- For `k < p`, the `k`-th sorted vertex of `s.erase (s.orderEmbOfFin h p)`
equals `s.orderEmbOfFin h ⟨k.val, _⟩` (no shift). -/
theorem orderEmbOfFin_erase_lt
    (s : Finset α) {n : ℕ} (h : s.card = n + 1) (p : Fin (n + 1))
    (k : Fin n)
    (hcard : (s.erase (s.orderEmbOfFin h p)).card = n)
    (hk : k.val < p.val) :
    (s.erase (s.orderEmbOfFin h p)).orderEmbOfFin hcard k =
      s.orderEmbOfFin h ⟨k.val, by have := p.isLt; omega⟩ := by
  -- `orderEmbOfFin_apply` is `rfl`; reduce both sides to list element accesses
  -- via `change`, then bridge `Fin`-getElem to `Nat`-getElem and apply the
  -- list-level helper.
  show ((s.erase (s.orderEmbOfFin h p)).sort (· ≤ ·))[k]'(by
        rw [Finset.length_sort, hcard]; exact k.isLt) =
      (s.sort (· ≤ ·))[(⟨k.val, by have := p.isLt; omega⟩ : Fin (n + 1))]'(by
        rw [Finset.length_sort, h]; have := p.isLt; omega)
  rw [Fin.getElem_fin, Fin.getElem_fin]
  exact orderEmbOfFin_erase_lt_aux s h p k hk _ _

/-- For `k ≥ p`, the `k`-th sorted vertex of `s.erase (s.orderEmbOfFin h p)`
equals `s.orderEmbOfFin h ⟨k.val + 1, _⟩` (shift by 1). -/
theorem orderEmbOfFin_erase_ge
    (s : Finset α) {n : ℕ} (h : s.card = n + 1) (p : Fin (n + 1))
    (k : Fin n)
    (hcard : (s.erase (s.orderEmbOfFin h p)).card = n)
    (hk : p.val ≤ k.val) :
    (s.erase (s.orderEmbOfFin h p)).orderEmbOfFin hcard k =
      s.orderEmbOfFin h ⟨k.val + 1, by have := k.isLt; omega⟩ := by
  show ((s.erase (s.orderEmbOfFin h p)).sort (· ≤ ·))[k]'(by
        rw [Finset.length_sort, hcard]; exact k.isLt) =
      (s.sort (· ≤ ·))[(⟨k.val + 1, by have := k.isLt; omega⟩ : Fin (n + 1))]'(by
        rw [Finset.length_sort, h]; have := k.isLt; omega)
  rw [Fin.getElem_fin, Fin.getElem_fin]
  exact orderEmbOfFin_erase_ge_aux s h p k hk _ _

end Finset
