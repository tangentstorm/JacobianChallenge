SUGGEST: Milestone C2b: Prove orientable_handleSwap_grouping

# Worker 2 (jc2) - Task Ledger

## Goal
Honestly close the surface-classification sub-chain in `Jacobian/Periods/TietzeReduction.lean` + `Jacobian/Periods/HandleSwapHomeo.lean`.

## Targets
- `Jacobian/Periods/TietzeReduction.lean`

## Current Step (Milestone C2b.1)
- [x] Isolate the narrow provider `orientable_handleBlock_collection`.
- [x] Prove `orientable_handleSwap_grouping` from it.
- [x] Verify `lake build Jacobian.Periods.TietzeReduction` compiles.
- [x] Update `sorries.jsonl` and commit.

## Logs
- Milestone B has been accepted.
- Milestone C2a (`handleSwap_index_ordering`) has been successfully proven and committed!
- Moving to the next decomposition lemma for `brahana_orientable_core`.

---

## MANAGER TRIAGE — UNBLOCKED (resume work; do NOT stay BLOCKED)

**Verdict:** This is NOT a valid wholesale block. "Massive Mathematical
Formalization Required" is true *as one lemma*, but per `proving-guide.md` /
`unblock-guide.md` the resolution is to **decompose `orientable_handleSwap_grouping`
into a local scaffold with one narrow named provider** — not to declare the whole
Brahana step blocked. You may not declare BLOCKED on raw difficulty; only on a
true cross-group gate or a Mathlib gap, neither of which applies here.

**Also: you set `BLOCKED:` without filing a Detailed Blocker Triage Report at the
bottom of this `task.md`.** That alone is a protocol miss — a bare BLOCKED with no
triage report is not actionable. Going forward, if you ever block, the report is
mandatory.

### Why this is decomposable, not blocked
You already own everything downstream of the grouping step:
- `handleSwap_index_ordering` (line 154) — PROVEN sorry-free: takes the
  `∃ perm, v = (finRange g).flatMap (handleBlock ∘ perm)` shape to
  `TietzeEq v (standardWord g)`.
- `TietzeEq_swap_adj` (line 99) and `TietzeEq_of_Perm_handleBlocks` /
  `..._context` (lines 131/148) — PROVEN sorry-free: arbitrary permutation of
  adjacent handle blocks via `HandleSwap` + `rotate` Tietze moves.

So the genuine remaining gap is purely: **a reduced, inverse-paired orientable
word can be brought, via `HandleSwap`/Tietze moves, into a `flatMap handleBlock`
normal form over SOME index list.** The permutation-to-standard tail is already done.

### Concrete decomposition (this becomes your next 2–3 commits)

**C2b.1 — isolate the narrow provider (1 commit, moves the frontier, no net new sorry).**
Replace the single broad `sorry` at line 91 with one strictly-narrower named
provider that captures only the genuine combinatorial heart, e.g.:

```lean
/-- Classical Brahana handle-collection: a reduced, inverse-paired word over the
genus-`g` alphabet is `TietzeEq` to a concatenation of complete handle blocks
listed in some order `l : List (Fin g)`. This is the genuine geometric input;
re-indexing to `standardWord` is handled downstream by the proven Perm lemmas. -/
theorem orientable_handleBlock_collection
    {g : ℕ} (w : EdgeWord g)
    (hPairs : ∀ ℓ : Letter g, ℓ ∈ w → ℓ.inv ∈ w)
    (hReduced : ∀ x : EdgeWord g, ¬ EdgeWord.InverseCancel w x) :
    ∃ l : List (Fin g),
      EdgeWord.TietzeEq w (l.flatMap EdgeWord.handleBlock) := by
  sorry
```

Then prove `orientable_handleSwap_grouping` sorry-free FROM it: obtain `l`, set
`v := (finRange g).flatMap (handleBlock ∘ perm)` where `perm` realizes `l` as a
permutation of `finRange g` — for the orientable closed surface `l` is a
permutation of `finRange g` (each handle index occurs exactly once because the
word is the full genus-`g` relator). Bridge `l.flatMap handleBlock` to the
`perm`-indexed form with `List.flatMap_map` + `TietzeEq_of_Perm_handleBlocks`
(both already available). If proving "`l` is a permutation of `finRange g`"
needs its own fact, expose THAT as a second tiny lemma rather than widening the
provider.

This commit should leave exactly ONE direct `sorry` (the new
`orientable_handleBlock_collection`) where there was one before — net-zero new
reachable sorries, frontier renamed to the precise geometric statement.

**C2b.2 — discharge the collection provider by induction (the real work, 1+ commits).**
Prove `orientable_handleBlock_collection` by strong induction on `w.length`
using your existing `HandleSwap`/`rotate` toolkit:
- An inverse-paired reduced word that is non-empty contains some letter `a i`
  (or symmetric); locate its partner `aInv i` and the `b i`/`bInv i` of the same
  handle, and use `HandleSwap.move` + `rotate` (exactly the moves you already
  packaged in `TietzeEq_swap_adj`) to bring that handle's four letters together
  as `handleBlock i` at the front.
- Peel `handleBlock i`, apply the induction hypothesis to the (shorter, still
  reduced & inverse-paired) remainder, prepend `i` to `l`.
If a single sub-step (e.g. "the four letters of a handle can be collected
adjacently") is itself heavy, isolate IT as the next narrow provider and prove
the peel/recursion on top — same discipline, one level down.

### Guardrails
- Do NOT widen: keep the public `orientable_handleSwap_grouping` signature
  exactly as is (line 91); it stays sorry-free on top of the provider.
- Do NOT touch `EdgeWord.lean` definitions, `Jacobian/Challenge.lean`, or other
  workers' files. New helpers go in `TietzeReduction.lean` (or a new local file
  under `Jacobian/Periods/`).
- No `axiom`/`unsafe`. `#print axioms orientable_handleSwap_grouping` after C2b.1
  must show only the new provider's `sorryAx`, nothing else.
- `orientable_letterPair_opposite_orientation` (line 84) is a SEPARATE remaining
  sorry — leave it for its own milestone; do not fold it in here.

**Action:** clear the `BLOCKED:` status, take C2b.1 as your next commit-sized
step, and proceed. Re-enter planning mode and rewrite the Current Step above to
the C2b.1 provider-isolation task.
