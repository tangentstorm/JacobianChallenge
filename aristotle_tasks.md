# Aristotle Task Index

This file indexes the Lean statement bank in
`Jacobian/WorkPackets/StatementBank.lean`.

Claude should treat each queue below as a source of small Aristotle jobs. Before
submitting, Claude should copy the relevant declarations into a narrower target
file and ask Aristotle to work only on that file.

The Aristotle account is shared with other projects; job IDs from
`aristotle list` may belong to FourColor or other unrelated work. Record every
JacobianChallenge submission in `aristotle_jobs.jsonl` so future ticks can
identify our jobs without inspecting tarballs.

## Live Status (2026-04-27 12:32 EDT)

- Active jobs (ours): 0/5. Backend healthy. No new submissions
  this tick — packets still queued for prep.
- **Integrated this tick (local Claude-owned, 4 lemmas, 1 new file):**
  - NEW `Jacobian/TraceDegree/PullbackFormsLinearMapSmulNegApplyVec.lean`:
    vec-applied versions of smul/neg combined identities:
      - `pullbackFormsLinearMap_smul_neg_apply_vec`
      - `pullbackFormsLinearMap_neg_smul_apply_vec`
      - `pullbackFormsLinearMap_neg_add_apply_vec`
      - `pullbackFormsLinearMap_add_neg_apply_vec`
    Each forwards via the function-level identity in
    `PullbackFormsLinearMapSmulNeg` plus `rfl`. All `@[simp]`.
- **Strategic note (carried forward):**
  Backend awake, queue empty. Continuing 4-lemma local cadence
  in parallel; Aristotle packet preparation still queued.

## Earlier (now stale; kept for context only)
## Stale Live Status (2026-04-27 12:29 EDT)

- Active jobs (ours): 1/5; canary `09cd85dd` QUEUED ~15h.
  Not waiting per user.
- **Integrated this tick (local Claude-owned, 4 lemmas, 1 new file):**
  - NEW `Jacobian/TraceDegree/PullbackFunIdEvalVecExtra.lean`:
      - `pullbackFormsFun_id_apply_sub_vec`
      - `pullbackFormsFun_id_apply_nsmul_vec`
      - `pullbackFormsFun_id_apply_zsmul_vec`
      - `pullbackFormsFun_id_apply_neg_neg_vec`

## Earlier (now stale; kept for context only)
## Stale Live Status (2026-04-27 09:41 EDT)

- Active jobs (ours): 1/5; canary `09cd85dd` QUEUED ~15h.
  Not waiting per user.
- **Integrated this tick (local Claude-owned, 4 lemmas, 1 new file):**
  - NEW `Jacobian/TraceDegree/PullbackFunIdEvalVec.lean`:
      - `pullbackFormsFun_id_apply_zero_vec`
      - `pullbackFormsFun_id_apply_add_vec`
      - `pullbackFormsFun_id_apply_neg_vec`
      - `pullbackFormsFun_id_apply_smul_vec`

## Earlier (now stale; kept for context only)
## Stale Live Status (2026-04-27 09:35 EDT)

- Active jobs (ours): 1/5; canary `09cd85dd` QUEUED ~15h.
  Not waiting per user.
- **Integrated this tick (local Claude-owned, 4 lemmas, 1 new file):**
  - NEW `Jacobian/TraceDegree/PullbackFunIdEvalSmul.lean`:
      - `pullbackFormsFun_id_smul_apply_vec`
      - `pullbackFormsFun_id_nsmul_apply_vec`
      - `pullbackFormsFun_id_zsmul_apply_vec`
      - `pullbackFormsFun_id_neg_zero_apply_vec`

## Earlier (now stale; kept for context only)
## Stale Live Status (2026-04-27 09:30 EDT)

- Active jobs (ours): 1/5; canary `09cd85dd` QUEUED ~15h.
  Not waiting per user.
- **Integrated this tick (local Claude-owned, 4 lemmas, 1 new file):**
  - NEW `Jacobian/TraceDegree/PullbackFunIdEvalDist.lean`:
      - `pullbackFormsFun_id_zero_apply_vec`
      - `pullbackFormsFun_id_add_apply_vec`
      - `pullbackFormsFun_id_neg_apply_vec`
      - `pullbackFormsFun_id_sub_apply_vec`

## Earlier (now stale; kept for context only)
## Stale Live Status (2026-04-27 09:27 EDT)

- Active jobs (ours): 1/5; canary `09cd85dd` QUEUED ~15h.
  Not waiting per user.
- **Integrated this tick (local Claude-owned, 4 lemmas, 1 new file):**
  - NEW `Jacobian/AbelJacobi/Symmetry.lean`:
      - `witnessAbelJacobi_neg_vec_eq_neg`
      - `evalJacobianClass_neg_vec_at_endpoint`
      - `witnessAbelJacobi_two_smul_vec`
      - `witnessAbelJacobi_eq_zero_of_evalLinearMap_eq`

## Earlier (now stale; kept for context only)
## Stale Live Status (2026-04-27 09:23 EDT)

- Active jobs (ours): 1/5; canary `09cd85dd` QUEUED ~15h.
  Not waiting per user.
- **Integrated this tick (local Claude-owned, 4 lemmas, 1 new file):**
  - NEW `Jacobian/TraceDegree/PullbackFunIdEval.lean`:
      - `pullbackFormsFun_id_apply_vec_eq_evalLinearMap'`
      - `pullbackFormsFun_id_eq_zero_iff_evalLinearMap_eq_zero`
      - `pullbackFormsFun_id_eq_iff_evalLinearMap_eq`
      - `pullbackFormsFun_id_factor_evalLinearMap`

## Earlier (now stale; kept for context only)
## Stale Live Status (2026-04-27 09:18 EDT)

- Active jobs (ours): 1/5; canary `09cd85dd` QUEUED ~15h.
  Not waiting per user.
- **Integrated this tick (local Claude-owned, 4 lemmas, 1 new file):**
  - NEW `Jacobian/AbelJacobi/WitnessMk.lean`:
      - `witnessAbelJacobi_eq_mk_sub`
      - `witnessAbelJacobi_eq_mk_evalLinearMap_sub`
      - `witnessAbelJacobi_eq_mk_neg_basePoint_add_endpoint`
      - `witnessAbelJacobi_eq_zero_iff_endpoint_diff_mem`

## Earlier (now stale; kept for context only)
## Stale Live Status (2026-04-27 09:13 EDT)

- Active jobs (ours): 1/5; canary `09cd85dd` QUEUED ~15h.
  Not waiting per user.
- **Integrated this tick (local Claude-owned, 4 lemmas, 1 new file):**
  - NEW `Jacobian/AnalyticJacobian/EvalJacobianClassPeriodPairing.lean`:
      - `evalJacobianClass_eq_mk_of_evalLinearMap_eq_add_periodPairing`
      - `evalJacobianClass_eq_mk_of_evalLinearMap_eq_sub_periodPairing`
      - `evalJacobianClass_eq_zero_of_evalLinearMap_eq_periodPairing`
      - `evalJacobianClass_eq_zero_of_evalLinearMap_eq_zsmul_periodPairing`

## Earlier (now stale; kept for context only)
## Stale Live Status (2026-04-27 09:09 EDT)

- Active jobs (ours): 1/5; canary `09cd85dd` QUEUED ~15h.
  Not waiting per user.
- **Integrated this tick (local Claude-owned, 4 lemmas, 1 new file):**
  - NEW `Jacobian/AnalyticJacobian/MkPeriodPairingSmul.lean`:
      - `mk_nsmul_periodPairing`
      - `mk_zsmul_periodPairing`
      - `mk_add_nsmul_periodPairing`
      - `mk_add_zsmul_periodPairing`

## Earlier (now stale; kept for context only)
## Stale Live Status (2026-04-27 09:05 EDT)

- Active jobs (ours): 1/5; canary `09cd85dd` QUEUED ~14h.
  Not waiting per user.
- **Integrated this tick (local Claude-owned, 4 lemmas, 1 new file):**
  - NEW `Jacobian/AnalyticJacobian/MkPeriodPairing.lean`:
      - `mk_add_periodPairing`
      - `mk_periodPairing_add`
      - `mk_sub_periodPairing`
      - `mk_neg_periodPairing`

## Earlier (now stale; kept for context only)
## Stale Live Status (2026-04-27 09:01 EDT)

- Active jobs (ours): 1/5; canary `09cd85dd` QUEUED ~14h.
  Not waiting per user.
- **Integrated this tick (local Claude-owned, 4 lemmas, 1 new file):**
  - NEW `Jacobian/AnalyticJacobian/MkArith.lean`:
      - `mk_eq_neg_iff_add_mem`
      - `neg_mk_eq_iff_add_mem`
      - `mk_add_eq`
      - `zero_eq_mk_zero`

## Earlier (now stale; kept for context only)
## Stale Live Status (2026-04-27 08:57 EDT)

- Active jobs (ours): 1/5; canary `09cd85dd` QUEUED ~14h.
  Not waiting per user.
- **Integrated this tick (local Claude-owned, 4 lemmas, 1 new file):**
  - NEW `Jacobian/HolomorphicForms/EvalLinearMapNeg.lean`:
      - `evalLinearMap_neg_neg_form`
      - `evalLinearMap_neg_neg_result`
      - `evalLinearMap_neg_form_eq_neg`
      - `evalLinearMap_neg_form_swap`

## Earlier (now stale; kept for context only)
## Stale Live Status (2026-04-27 08:54 EDT)

- Active jobs (ours): 1/5; canary `09cd85dd` QUEUED ~14h.
  Not waiting per user.
- **Integrated this tick (local Claude-owned, 4 lemmas, 1 new file):**
  - NEW `Jacobian/HolomorphicForms/ToFunNeg.lean`:
      - `neg_neg_toFun_apply`
      - `neg_neg_toFun_apply_vec`
      - `toFun_neg_apply_swap`
      - `toFun_neg_apply_vec_swap`

## Earlier (now stale; kept for context only)
## Stale Live Status (2026-04-27 08:48 EDT)

- Active jobs (ours): 1/5; canary `09cd85dd` QUEUED ~14h.
  Not waiting per user.
- **Integrated this tick (local Claude-owned, 4 lemmas, 1 new file):**
  - NEW `Jacobian/AbelJacobi/Specialize.lean`:
      - `witnessAbelJacobi_eq_endpoint_of_basePoint_class_zero`
      - `witnessAbelJacobi_eq_zero_of_both_classes_zero`
      - `witnessAbelJacobi_eq_zero_of_both_evalLinearMap_mem`
      - `witnessAbelJacobi_eq_zero_of_both_evalLinearMap_zero`

## Earlier (now stale; kept for context only)
## Stale Live Status (2026-04-27 08:45 EDT)

- Active jobs (ours): 1/5; canary `09cd85dd` QUEUED ~14h.
  Not waiting per user.
- **Integrated this tick (local Claude-owned, 4 lemmas, 1 new file):**
  - NEW `Jacobian/AnalyticJacobian/EvalJacobianClassMember.lean`:
      - `evalJacobianClass_eq_zero_of_evalLinearMap_mem_periodSubgroup`
      - `evalJacobianClass_eq_zero_of_evalLinearMap_zero`
      - `evalJacobianClass_eq_evalJacobianClass_iff_sub_mem`
      - `mk_evalLinearMap_eq_zero_iff`

## Earlier (now stale; kept for context only)
## Stale Live Status (2026-04-27 08:41 EDT)

- Active jobs (ours): 1/5; canary `09cd85dd` QUEUED ~14h.
  Not waiting per user.
- **Integrated this tick (local Claude-owned, 4 lemmas, 1 new file):**
  - NEW `Jacobian/AnalyticJacobian/MkMembership.lean`:
      - `mk_eq_zero_of_mem_periodSubgroup`
      - `mk_eq_zero_iff_mem_periodSubgroup`
      - `mk_periodPairing_eq_zero`
      - `mk_eq_mk_iff_sub_mem`

## Earlier (now stale; kept for context only)
## Stale Live Status (2026-04-27 08:37 EDT)

- Active jobs (ours): 1/5; canary `09cd85dd` QUEUED ~14h.
  Not waiting per user.
- **Integrated this tick (local Claude-owned, 4 lemmas, 1 new file):**
  - NEW `Jacobian/AbelJacobi/GenusWitness.lean`:
      - `genus_pos_and_nontrivial_jacobian_of_witness_ne_zero`
      - `genus_pos_of_witness_ne_zero`
      - `nontrivial_jacobian_of_witness_ne_zero`
      - `witness_eq_zero_of_subsingleton_jacobian`

## Earlier (now stale; kept for context only)
## Stale Live Status (2026-04-27 08:31 EDT)

- Active jobs (ours): 1/5; canary `09cd85dd` QUEUED ~14h.
  Not waiting per user.
- **Integrated this tick (local Claude-owned, 4 lemmas, 1 new file):**
  - NEW `Jacobian/AbelJacobi/Nontrivial.lean`:
      - `nontrivial_analyticJacobian_of_witness_ne_zero`
      - `evalJacobianClass_ne_of_witness_ne_zero`
      - `evalLinearMap_diff_notMem_of_witness_ne_zero`
      - `witness_zero_iff_evalJacobianClass_eq`

## Earlier (now stale; kept for context only)
## Stale Live Status (2026-04-27 08:25 EDT)

- Active jobs (ours): 1/5; canary `09cd85dd` QUEUED ~14h.
  Not waiting per user.
- **Integrated this tick (local Claude-owned, 4 lemmas, 1 new file):**
  - NEW `Jacobian/Periods/PeriodSubgroupExt.lean`:
      - `periodSubgroup_carrier_eq_range`
      - `range_periodPairing_subset_periodSubgroup`
      - `neg_periodPairing_mem_periodSubgroup`
      - `periodPairing_add_mem_periodSubgroup`

## Earlier (now stale; kept for context only)
## Stale Live Status (2026-04-27 08:19 EDT)

- Active jobs (ours): 1/5; canary `09cd85dd` QUEUED ~14h.
  Not waiting per user.
- **Integrated this tick (local Claude-owned, 4 lemmas, 1 new file):**
  - NEW `Jacobian/AbelJacobi/Sum.lean`:
      - `witnessAbelJacobi_sum_range`
      - `witnessAbelJacobi_sum_range_loop`
      - `witnessAbelJacobi_sum_range_const`
      - `witnessAbelJacobi_sum_range_split`

## Earlier (now stale; kept for context only)
## Stale Live Status (2026-04-27 08:15 EDT)

- Active jobs (ours): 1/5; canary `09cd85dd` QUEUED ~14h.
  Not waiting per user.
- **Integrated this tick (local Claude-owned, 4 lemmas, 1 new file):**
  - NEW `Jacobian/AbelJacobi/Telescoping.lean`:
      - `witnessAbelJacobi_chain_four`
      - `witnessAbelJacobi_telescope_pair`
      - `witnessAbelJacobi_telescope_loop`
      - `witnessAbelJacobi_eq_iff_swap_eq_zero`

## Earlier (now stale; kept for context only)
## Stale Live Status (2026-04-27 08:11 EDT)

- Active jobs (ours): 1/5; canary `09cd85dd` QUEUED ~14h.
  Not waiting per user.
- **Integrated this tick (local Claude-owned, 4 lemmas, 1 new file):**
  - NEW `Jacobian/AbelJacobi/Coset.lean`:
      - `witnessAbelJacobi_eq_zero_iff_class_eq`
      - `witnessAbelJacobi_add_swap_eq_zero`
      - `witnessAbelJacobi_endpoint_diff`
      - `witnessAbelJacobi_base_change_eq`

## Earlier (now stale; kept for context only)
## Stale Live Status (2026-04-27 08:08 EDT)

- Active jobs (ours): 1/5; canary `09cd85dd` QUEUED ~14h.
  Not waiting per user.
- **Integrated this tick (local Claude-owned, 4 lemmas, 1 new file):**
  - NEW `Jacobian/AbelJacobi/Identities.lean`:
      - `witnessAbelJacobi_add_basePoint_class`
      - `basePoint_class_add_witness`
      - `witnessAbelJacobi_chain_shift`
      - `witnessAbelJacobi_left_self_eq_zero`

## Earlier (now stale; kept for context only)
## Stale Live Status (2026-04-27 08:05 EDT)

- Active jobs (ours): 1/5; canary `09cd85dd` QUEUED ~13h.
  Not waiting per user.
- **Integrated this tick (local Claude-owned, 4 lemmas, 1 new file):**
  - NEW `Jacobian/AbelJacobi/BaseChange.lean`:
      - `witnessAbelJacobi_base_change`
      - `witnessAbelJacobi_chain_three`
      - `witnessAbelJacobi_eq_iff_class_eq`
      - `witnessAbelJacobi_swap_eq_zero_iff`

## Earlier (now stale; kept for context only)
## Stale Live Status (2026-04-27 08:01 EDT)

- Active jobs (ours): 1/5; canary `09cd85dd` QUEUED ~13h.
  Not waiting per user.
- **Integrated this tick (local Claude-owned, 4 lemmas, 1 new file):**
  - NEW `Jacobian/AbelJacobi/Smul.lean`:
      - `witnessAbelJacobi_sub_vec`
      - `witnessAbelJacobi_nsmul_vec`
      - `witnessAbelJacobi_zsmul_vec`
      - `witnessAbelJacobi_eq_zero_iff`

## Earlier (now stale; kept for context only)
## Stale Live Status (2026-04-27 07:57 EDT)

- Active jobs (ours): 1/5; canary `09cd85dd` QUEUED ~13h.
  Not waiting per user.
- **Integrated this tick (local Claude-owned, 4 lemmas, 1 new file):**
  - NEW `Jacobian/AbelJacobi/Composition.lean`:
      - `witnessAbelJacobi_chain`
      - `witnessAbelJacobi_zero_vec`
      - `witnessAbelJacobi_add_vec`
      - `witnessAbelJacobi_neg_vec`

## Earlier (now stale; kept for context only)
## Stale Live Status (2026-04-27 07:48 EDT)

- Active jobs (ours): 1/5; canary `09cd85dd` QUEUED ~13h.
  Not waiting per user.
- **Integrated this tick (local Claude-owned, 4 items, 2 new files):**
  - NEW `Jacobian/AbelJacobi/Defs.lean`:
      - `witnessAbelJacobi`
      - `witnessAbelJacobi_self`
      - `witnessAbelJacobi_swap`
      - `witnessAbelJacobi_diag`
  - NEW `Jacobian/AbelJacobi.lean` umbrella.

## Earlier (now stale; kept for context only)
## Stale Live Status (2026-04-27 07:43 EDT)

- Active jobs (ours): 1/5; canary `09cd85dd` QUEUED ~13h.
  Not waiting per user.
- **Integrated this tick (local Claude-owned, 4 lemmas, 1 new file):**
  - NEW `Jacobian/AnalyticJacobian/NontrivialWitness.lean`:
      - `evalJacobianClass_ne_zero`
      - `nontrivial_analyticJacobianGroup_of_evalLinearMap_ne_periodSubgroup`
      - `evalLinearMap_notMem_of_evalJacobianClass_ne_zero`
      - `evalLinearMap_notMem_iff_evalJacobianClass_ne_zero`

## Earlier (now stale; kept for context only)
## Stale Live Status (2026-04-27 07:40 EDT)

- Active jobs (ours): 1/5; canary `09cd85dd` QUEUED ~13h.
  Not waiting per user.
- **Integrated this tick (local Claude-owned, 4 lemmas, 1 new file):**
  - NEW `Jacobian/AnalyticJacobian/EvalJacobianClassZero.lean`:
      - `evalJacobianClass_eq_zero_iff`
      - `evalJacobianClass_zero_of_mem_periodSubgroup`
      - `evalJacobianClass_zero_of_evalLinearMap_eq_zero`
      - `evalJacobianClass_eq_iff`

## Earlier (now stale; kept for context only)
## Stale Live Status (2026-04-27 07:36 EDT)

- Active jobs (ours): 1/5; canary `09cd85dd` QUEUED ~13h.
  Not waiting per user.
- **Integrated this tick (local Claude-owned, 4 lemmas, 1 new file):**
  - NEW `Jacobian/AnalyticJacobian/EvalJacobianClassSmul.lean`:
      - `evalLinearMap_vec_nsmul`
      - `evalLinearMap_vec_zsmul`
      - `evalJacobianClass_nsmul_vec`
      - `evalJacobianClass_zsmul_vec`

## Earlier (now stale; kept for context only)
## Stale Live Status (2026-04-27 07:33 EDT)

- Active jobs (ours): 1/5; canary `09cd85dd` QUEUED ~13h.
  Not waiting per user.
- **Integrated this tick (local Claude-owned, 4 lemmas, 1 new file):**
  - NEW `Jacobian/AnalyticJacobian/EvalJacobianClassOps.lean`:
      - `evalLinearMap_vec_neg`
      - `evalLinearMap_vec_sub`
      - `evalJacobianClass_neg_vec`
      - `evalJacobianClass_sub_vec`

## Earlier (now stale; kept for context only)
## Stale Live Status (2026-04-27 07:29 EDT)

- Active jobs (ours): 1/5; canary `09cd85dd` QUEUED ~13h.
  Not waiting per user.
- **Integrated this tick (local Claude-owned, 4 lemmas, 1 new file):**
  - NEW `Jacobian/AnalyticJacobian/EvalJacobianClass.lean`:
      - `evalLinearMap_vec_add`
      - `evalLinearMap_vec_zero`
      - `evalJacobianClass_zero_vec`
      - `evalJacobianClass_add_vec`

## Earlier (now stale; kept for context only)
## Stale Live Status (2026-04-27 07:25 EDT)

- Active jobs (ours): 1/5; canary `09cd85dd` QUEUED ~13h.
  Not waiting per user.
- **Integrated this tick (local Claude-owned, 4 lemmas, 1 new file):**
  - NEW `Jacobian/AnalyticJacobian/MkExt.lean`:
      - `mk_surjective`
      - `mk_eq_mk_iff`
      - `evalJacobianClass`
      - `evalJacobianClass_def`

## Earlier (now stale; kept for context only)
## Stale Live Status (2026-04-27 07:20 EDT)

- Active jobs (ours): 1/5; canary `09cd85dd` QUEUED ~13h.
  Not waiting per user.
- **Integrated this tick (local Claude-owned, 4 lemmas, 1 new file):**
  - NEW `Jacobian/AnalyticJacobian/MkOps.lean`:
      - `mk_neg`
      - `mk_sub`
      - `mk_nsmul`
      - `mk_zsmul`

## Earlier (now stale; kept for context only)
## Stale Live Status (2026-04-27 07:14 EDT)

- Active jobs (ours): 1/5; canary `09cd85dd` QUEUED ~13h.
  Not waiting per user.
- **Integrated this tick (local Claude-owned, 4 lemmas, 1 new file):**
  - NEW `Jacobian/AnalyticJacobian/Mk.lean`:
      - `mk`
      - `mk_zero`
      - `mk_add`
      - `mk_eq_zero_iff`

## Earlier (now stale; kept for context only)
## Stale Live Status (2026-04-27 07:09 EDT)

- Active jobs (ours): 1/5; canary `09cd85dd` QUEUED ~12h.
  Not waiting per user.
- **Integrated this tick (local Claude-owned, 4 lemmas, 1 new file):**
  - NEW `Jacobian/Periods/PeriodSubgroupClosure.lean`:
      - `add_mem_periodSubgroup`
      - `sub_mem_periodSubgroup`
      - `nsmul_mem_periodSubgroup`
      - `zsmul_mem_periodSubgroup`

## Earlier (now stale; kept for context only)
## Stale Live Status (2026-04-27 07:01 EDT)

- Active jobs (ours): 1/5; canary `09cd85dd` QUEUED ~12h.
  Not waiting per user.
- **Integrated this tick (local Claude-owned, 4 lemmas, 1 new file):**
  - NEW `Jacobian/Periods/PeriodSubgroupApi.lean`:
      - `periodPairing_sub`
      - `mem_periodSubgroup_iff`
      - `periodPairing_mem_periodSubgroup`
      - `neg_mem_periodSubgroup`

## Earlier (now stale; kept for context only)
## Stale Live Status (2026-04-27 06:52 EDT)

- Active jobs (ours): 1/5; canary `09cd85dd` QUEUED ~12h.
  Not waiting per user.
- **Integrated this tick (local Claude-owned, 4 lemmas, 1 new file):**
  - NEW `Jacobian/Periods/PeriodFunctionalApi.lean`:
      - `periodPairing_zero`
      - `periodPairing_add`
      - `periodPairing_neg`
      - `zero_mem_periodSubgroup`

## Earlier (now stale; kept for context only)
## Stale Live Status (2026-04-27 06:47 EDT)

- Active jobs (ours): 1/5; canary `09cd85dd` QUEUED ~12h.
  Not waiting per user.
- **Integrated this tick (local Claude-owned, 4 lemmas, 1 new file):**
  - NEW `Jacobian/HolomorphicForms/AnalyticGenusOrder.lean`:
      - `analyticGenus_le_iff_finrank_le`
      - `analyticGenus_lt_iff_finrank_lt`
      - `analyticGenus_eq_iff_finrank_eq`
      - `analyticGenus_ge_iff_finrank_ge`

## Earlier (now stale; kept for context only)
## Stale Live Status (2026-04-27 06:43 EDT)

- Active jobs (ours): 1/5; canary `09cd85dd` QUEUED ~12h.
  Not waiting per user.
- **Integrated this tick (local Claude-owned, 4 lemmas, 1 new file):**
  - NEW `Jacobian/HolomorphicForms/EvalLinearMapVecExtra.lean`:
      - `evalLinearMap_sub_vec`
      - `evalLinearMap_nsmul_vec`
      - `evalLinearMap_zsmul_vec`
      - `toFun_apply_add_vec`

## Earlier (now stale; kept for context only)
## Stale Live Status (2026-04-27 06:39 EDT)

- Active jobs (ours): 1/5; canary `09cd85dd` QUEUED ~12h.
  Not waiting per user.
- **Integrated this tick (local Claude-owned, 4 lemmas, 1 new file):**
  - NEW `Jacobian/HolomorphicForms/EvalLinearMapVec.lean`:
      - `evalLinearMap_zero_vec`
      - `evalLinearMap_add_vec`
      - `evalLinearMap_smul_vec`
      - `evalLinearMap_neg_vec`

## Earlier (now stale; kept for context only)
## Stale Live Status (2026-04-27 06:35 EDT)

- Active jobs (ours): 1/5; canary `09cd85dd` QUEUED ~12h.
  Not waiting per user.
- **Integrated this tick (local Claude-owned, 4 lemmas, 1 new file):**
  - NEW `Jacobian/HolomorphicForms/AnalyticGenusWitness.lean`:
      - `analyticGenus_pos_of_evalLinearMap_ne_zero`
      - `analyticGenus_ne_zero_of_evalLinearMap_ne_zero`
      - `analyticGenus_pos_of_toFun_ne_zero`
      - `nontrivial_holomorphicOneForm_of_evalLinearMap_ne_zero`

## Earlier (now stale; kept for context only)
## Stale Live Status (2026-04-27 06:32 EDT)

- Active jobs (ours): 1/5; canary `09cd85dd` QUEUED ~12h.
  Not waiting per user.
- **Integrated this tick (local Claude-owned, 4 lemmas, 1 new file):**
  - NEW `Jacobian/HolomorphicForms/ExtEvalLinearMap.lean`:
      - `ext_evalLinearMap_iff`
      - `ext_evalLinearMap`
      - `eq_zero_iff_evalLinearMap_eq_zero`
      - `ne_zero_of_evalLinearMap_ne_zero`

## Earlier (now stale; kept for context only)
## Stale Live Status (2026-04-27 06:28 EDT)

- Active jobs (ours): 1/5; canary `09cd85dd` QUEUED ~12h.
  Not waiting per user.
- **Integrated this tick (local Claude-owned, 4 lemmas, 1 new file):**
  - NEW `Jacobian/HolomorphicForms/Ext.lean`:
      - `ext_toFun_iff`
      - `ext_toFun`
      - `ext_toFun_apply_iff`
      - `ext_toFun_apply`

## Earlier (now stale; kept for context only)
## Stale Live Status (2026-04-27 06:24 EDT)

- Active jobs (ours): 1/5; canary `09cd85dd` QUEUED ~12h.
  Not waiting per user.
- **Integrated this tick (local Claude-owned, 4 lemmas, 1 new file):**
  - NEW `Jacobian/HolomorphicForms/EvalLinearMapZsmul.lean`:
      - `evalLinearMap_zsmul`
      - `evalLinearMap_natCast_smul`
      - `evalLinearMap_neg_neg`
      - `zsmul_toFun_apply`

## Earlier (now stale; kept for context only)
## Stale Live Status (2026-04-27 06:14 EDT)

- Active jobs (ours): 1/5; canary `09cd85dd` QUEUED ~12h.
  Not waiting per user.
- **Integrated this tick (local Claude-owned, 4 lemmas, 1 new file):**
  - NEW `Jacobian/TraceDegree/PullbackFunEvalLinearMap.lean`:
      - `pullbackFormsFun_apply_eq_comp`
      - `pullbackFormsFun_id_apply_eq_toFun`
      - `pullbackFormsFun_id_apply_vec_eq_evalLinearMap`
      - `pullbackFormsFun_apply_vec_add'`

## Earlier (now stale; kept for context only)
## Stale Live Status (2026-04-27 06:08 EDT)

- Active jobs (ours): 1/5; canary `09cd85dd` QUEUED ~12h.
  Not waiting per user.
- **Integrated this tick (local Claude-owned, 4 lemmas, 1 new file):**
  - NEW `Jacobian/HolomorphicForms/EvalLinearMapApi.lean`:
      - `evalLinearMap_neg`
      - `evalLinearMap_sub`
      - `evalLinearMap_smul`
      - `evalLinearMap_nsmul`

## Earlier (now stale; kept for context only)
## Stale Live Status (2026-04-27 06:04 EDT)

- Active jobs (ours): 1/5; canary `09cd85dd` QUEUED ~11h.
  Not waiting per user.
- **Integrated this tick (local Claude-owned, 4 lemmas, 1 new file):**
  - NEW `Jacobian/HolomorphicForms/EvalLinearMap.lean`:
      - `evalLinearMap`
      - `evalLinearMap_apply`
      - `evalLinearMap_zero`
      - `evalLinearMap_add`

## Earlier (now stale; kept for context only)
## Stale Live Status (2026-04-27 06:01 EDT)

- Active jobs (ours): 1/5; canary `09cd85dd` QUEUED ~11h.
  Not waiting per user.
- **Integrated this tick (local Claude-owned, 4 lemmas, 1 new file):**
  - NEW `Jacobian/HolomorphicForms/ToFunApplyVecExtra.lean`:
      - `sub_toFun_apply_vec`
      - `smul_toFun_apply_vec`
      - `nsmul_toFun_apply`
      - `nsmul_toFun_apply_vec`

## Earlier (now stale; kept for context only)
## Stale Live Status (2026-04-27 05:57 EDT)

- Active jobs (ours): 1/5; canary `09cd85dd` QUEUED ~11h.
  Not waiting per user.
- **Integrated this tick (local Claude-owned, 4 lemmas, 1 new file):**
  - NEW `Jacobian/HolomorphicForms/ToFunApplyVec.lean`:
      - `smul_toFun_apply`
      - `zero_toFun_apply_vec`
      - `neg_toFun_apply_vec`
      - `add_toFun_apply_vec`

## Earlier (now stale; kept for context only)
## Stale Live Status (2026-04-27 05:51 EDT)

- Active jobs (ours): 1/5; canary `09cd85dd` QUEUED ~11h.
  Not waiting per user.
- **Integrated this tick (local Claude-owned, 4 lemmas, 1 new file):**
  - NEW `Jacobian/HolomorphicForms/ToFunApply.lean`:
      - `zero_toFun_apply`
      - `neg_toFun_apply`
      - `add_toFun_apply`
      - `sub_toFun_apply`

## Earlier (now stale; kept for context only)
## Stale Live Status (2026-04-27 05:46 EDT)

- Active jobs (ours): 1/5; canary `09cd85dd` QUEUED ~11h.
  Not waiting per user.
- **Integrated this tick (local Claude-owned, 4 lemmas, 1 new file):**
  - NEW `Jacobian/HolomorphicForms/AnalyticGenusPos.lean`:
      - `analyticGenus_pos_iff_nontrivial`
      - `analyticGenus_ne_zero_iff_nontrivial`
      - `analyticGenus_pos_of_exists_ne_zero`
      - `subsingleton_of_analyticGenus_eq_zero`

## Earlier (now stale; kept for context only)
## Stale Live Status (2026-04-27 05:43 EDT)

- Active jobs (ours): 1/5; canary `09cd85dd` QUEUED ~11h.
  Not waiting per user.
- **Integrated this tick (local Claude-owned, 4 lemmas, 1 new file):**
  - NEW `Jacobian/HolomorphicForms/AnalyticGenus.lean`:
      - `analyticGenus_def`
      - `analyticGenus_eq_zero_iff_finrank_zero`
      - `analyticGenus_eq_zero_iff_subsingleton`
      - `analyticGenus_eq_zero_of_subsingleton`

## Earlier (now stale; kept for context only)
## Stale Live Status (2026-04-27 05:37 EDT)

- Active jobs (ours): 1/5; canary `09cd85dd` QUEUED ~11h.
  Not waiting per user.
- **Integrated this tick (local Claude-owned, 4 lemmas, 1 new file):**
  - NEW `Jacobian/TraceDegree/PullbackFunIdComposeId.lean`:
    closes the trivial corner of the composition matrix where both
    factors are `id`:
      - `pullbackFormsFun_id_id`
      - `pullbackFormsFun_id_id_apply`
      - `pullbackFormsFun_id_id_apply_vec`
      - `pullbackFormsLinearMap_id_id_apply`
    All collapse to `pullbackFormsFun_id` since `id ∘ id = id` rfl.

## Earlier (now stale; kept for context only)
## Stale Live Status (2026-04-27 05:32 EDT)

- Active jobs (ours): 1/5; canary `09cd85dd` QUEUED ~11h.
  Not waiting per user.
- **Integrated this tick (local Claude-owned, 4 lemmas, 1 new file):**
  - NEW `Jacobian/TraceDegree/PullbackFormsLinearMapMixedConstId.lean`:
    bundled-LinearMap apply / vec-apply forms of last tick's mixed
    compositions, closing the const/id matrix at the bundled level:
      - `pullbackFormsLinearMap_id_comp_const_apply`
      - `pullbackFormsLinearMap_id_comp_const_apply_vec`
      - `pullbackFormsLinearMap_const_comp_id_apply`
      - `pullbackFormsLinearMap_const_comp_id_apply_vec`
    All zero. Wired into TraceDegree umbrella.

## Earlier (now stale; kept for context only)
## Stale Live Status (2026-04-27 05:28 EDT)

- Active jobs (ours): 1/5; canary `09cd85dd` QUEUED ~11h.
  Not waiting per user.
- **Integrated this tick (local Claude-owned, 4 lemmas, 1 new file):**
  - NEW `Jacobian/TraceDegree/PullbackFunMixedConstIdApply.lean`:
    apply and vec-apply forms of last tick's mixed compositions:
      - `pullbackFormsFun_id_comp_const_apply`
      - `pullbackFormsFun_id_comp_const_apply_vec`
      - `pullbackFormsFun_const_comp_id_apply`
      - `pullbackFormsFun_const_comp_id_apply_vec`
    All zero. Wired into TraceDegree umbrella.

## Earlier (now stale; kept for context only)
## Stale Live Status (2026-04-27 05:23 EDT)

- Active jobs (ours): 1/5; canary `09cd85dd` QUEUED ~11h.
  Not waiting per user.
- **Integrated this tick (local Claude-owned, 4 lemmas, 1 new file):**
  - NEW `Jacobian/TraceDegree/PullbackFunConstCompConstBundled.lean`:
    completes the const-comp-const matrix and adds two mixed
    `id ∘ const` / `const ∘ id` zero simps:
      - `pullbackFormsLinearMap_const_comp_const`
      - `pullbackFormsLinearMap_const_comp_const_apply_vec`
      - `pullbackFormsFun_id_comp_const`
      - `pullbackFormsFun_const_comp_id`
    Wired into TraceDegree umbrella.

## Earlier (now stale; kept for context only)
## Stale Live Status (2026-04-27 05:14 EDT)

- Active jobs (ours): 1/5; canary `09cd85dd` QUEUED ~11h.
  Not waiting per user.
- **Integrated this tick (local Claude-owned, 4 lemmas, 1 new file):**
  - NEW `Jacobian/TraceDegree/PullbackFunConstCompConst.lean`:
    pullback along the doubly-constant composition
    `Function.const Y z ∘ Function.const X y`, in four forms:
      - `pullbackFormsFun_const_comp_const`
      - `pullbackFormsFun_const_comp_const_apply`
      - `pullbackFormsFun_const_comp_const_apply_vec`
      - `pullbackFormsLinearMap_const_comp_const_apply`
    All zero via `pullbackFormsFun_const_comp` + `rfl`. Wired
    into TraceDegree umbrella.

## Earlier (now stale; kept for context only)
## Stale Live Status (2026-04-27 05:09 EDT)

- Active jobs (ours): 1/5; canary `09cd85dd` QUEUED ~11h.
  Not waiting per user.
- **Integrated this tick (local Claude-owned, 4 lemmas, 1 new file):**
  - NEW `Jacobian/TraceDegree/PullbackFormsLinearMapCompIdApply.lean`:
    pointwise apply / vec-apply forms of the bundled-LinearMap
    comp-id pair:
      - `pullbackFormsLinearMap_id_comp_apply`
      - `pullbackFormsLinearMap_comp_id_apply`
      - `pullbackFormsLinearMap_id_comp_apply_vec`
      - `pullbackFormsLinearMap_comp_id_apply_vec`
    All `rfl`. Wired into TraceDegree umbrella.

## Earlier (now stale; kept for context only)
## Stale Live Status (2026-04-27 05:03 EDT)

- Active jobs (ours): 1/5; canary `09cd85dd` QUEUED ~10h.
  Not waiting per user.
- **Integrated this tick (local Claude-owned, 8 lemmas, 2 new files):**
  - NEW `Jacobian/TraceDegree/PullbackFunCompConstApply.lean`:
    four apply / vec-apply forms of the comp-const lemmas:
      - `pullbackFormsFun_comp_const_apply`
      - `pullbackFormsFun_comp_const_apply_vec`
      - `pullbackFormsFun_const_comp_apply`
      - `pullbackFormsFun_const_comp_apply_vec`
    All `rw [pullbackFormsFun_(comp|const)_(const|comp)]; rfl`.
  - NEW `Jacobian/TraceDegree/PullbackFormsLinearMapCompConstApplyVec.lean`:
    four bundled-LinearMap forms (function-equality + vec-apply):
      - `pullbackFormsLinearMap_comp_const`
      - `pullbackFormsLinearMap_const_comp`
      - `pullbackFormsLinearMap_comp_const_apply_vec`
      - `pullbackFormsLinearMap_const_comp_apply_vec`
    Build green; both wired into TraceDegree umbrella.

## Earlier (now stale; kept for context only)
## Stale Live Status (2026-04-27 04:54 EDT)

- Active jobs (ours): 1/5; canary `09cd85dd` QUEUED ~10h.
  Not waiting per user.
- **Integrated this tick (local Claude-owned, 4 lemmas):**
  - EXTENDED `Jacobian/TraceDegree/PullbackFunCompId.lean` with
    four apply / vector-apply simp variants of the comp-id
    function-equality lemmas:
      - `pullbackFormsFun_id_comp_apply`
      - `pullbackFormsFun_comp_id_apply`
      - `pullbackFormsFun_id_comp_apply_vec`
      - `pullbackFormsFun_comp_id_apply_vec`
    All four `rfl`. Build green.

## Earlier (now stale; kept for context only)
## Stale Live Status (2026-04-27 04:49 EDT)

- Active jobs (ours): 1/5; canary `09cd85dd` QUEUED ~10h.
  Per user, NOT waiting for Aristotle to wake.
- **Integrated this tick (local Claude-owned, 4 lemmas, 2 new files):**
  - NEW `Jacobian/TraceDegree/PullbackFunCompId.lean` with two
    function-level rfl simps:
      - `pullbackFormsFun_id_comp`: `pullbackFormsFun (id ∘ f) η =
        pullbackFormsFun f η`.
      - `pullbackFormsFun_comp_id`: `pullbackFormsFun (f ∘ id) η =
        pullbackFormsFun f η`.
  - NEW `Jacobian/TraceDegree/PullbackFormsLinearMapCompId.lean`
    mirrors at the bundled-LinearMap level:
      - `pullbackFormsLinearMap_id_comp`
      - `pullbackFormsLinearMap_comp_id`
    Both also rfl.
  Branched into TraceDegree (was at 17%) per "don't wait for
  Aristotle" directive. Build green; bumped progress bar to 19%.

## Earlier (now stale; kept for context only)
## Stale Live Status (2026-04-27 04:42 EDT)

- Active jobs (ours): 1/5; canary `09cd85dd` QUEUED ~10h —
  `submitted-redundant`, kept as wake detector.
- **Integrated this tick (local Claude-owned, 3 lemmas):**
  - EXTENDED `Jacobian/Periods/TranslationChart.lean` with three
    pointwise translation-zero simp lemmas:
      - `chartedForm_translationChart_zero_apply`:
        `chartedForm (translationChart 0) ω e = ω.toFun e`.
      - `chartedFormPullback_translationChart_zero_apply`:
        `chartedFormPullback (translationChart 0) ω e = ω.toFun e`.
      - `chartLift_translationChart_zero_apply`:
        `chartLift (translationChart 0) γ h t = γ t`.
    Pointwise/applied versions of last tick's collapse simps —
    useful for downstream `simp` chains. Build green (8189 jobs).
- **Strategic note (carried forward):**
  Pushing Path integration/periods to 100% requires substantive
  infrastructure (Packet F, partition independence, Stokes), not
  small simps. Continuing micro-lemma work per user's "3-4 per
  tick" directive.

## Earlier (now stale; kept for context only)
## Stale Live Status (2026-04-27 04:35 EDT)

- Active jobs (ours): 1/5; canary `09cd85dd` QUEUED ~10h —
  `submitted-redundant`, kept as wake detector.
- **Integrated this tick (local Claude-owned, 3 lemmas):**
  - EXTENDED `Jacobian/Periods/TranslationChart.lean` with three
    more zero-translation chart-form collapses:
      - `chartedFormPullback_translationChart_zero`:
        `chartedFormPullback (translationChart 0) ω = ω.toFun`.
      - `chartedFormLinearMap_translationChart_zero`:
        bundled provisional version, equals `ω.toFun`.
      - `chartedFormPullbackLinearMap_translationChart_zero`:
        bundled corrected version, equals `ω.toFun`.
    All proofs reduce via `translationChart_zero` to the refl
    chart formula or directly delegate. Build green (8189 jobs).
- **Strategic note (carried forward from previous tick):**
  Pushing Path integration/periods to 100% requires substantive
  infrastructure (Packet F, partition independence, Stokes), not
  small simps. See previous tick's strategic note in commit
  `005b4d9`.

## Earlier (now stale; kept for context only)
## Stale Live Status (2026-04-27 04:26 EDT)

- Active jobs (ours): 1/5; canary `09cd85dd` QUEUED ~10h —
  `submitted-redundant`, kept as wake detector.
- **Integrated this tick (local Claude-owned):**
  - EXTENDED `Jacobian/Periods/TranslationChart.lean` with two
    degenerate-zero results (and dropped two attempts):
      - `pathIntegralInChartCorrect_translationChart_zero`:
        `pathIntegralInChartCorrect (translationChart 0) ω γ =
        curveIntegral ω.toFun γ`. Proof: rewrite via the corrected
        translation formula + `neg_zero; add_zero`.
      - `chartedForm_translationChart_zero`:
        `chartedForm (translationChart 0) ω = ω.toFun`. Proof:
        `rw [translationChart_zero]` + `chartedForm_refl_eq_toFun`.
    Two via-chart zero variants (provisional and corrected) hit a
    dependent-type rewrite blocker — `rw [translationChart_zero]`
    on a hypothesis whose type depends on the chart fails to
    propagate the change to a `pathIntegralViaChart` argument.
    Left for a later tick with a different proof strategy.
    Build green (8189 jobs).
- **Strategic note (in response to user "can you push to 100%?"):**
  No — the remaining 35% on Path integration/periods is
  substantive infrastructure, not many small simps:
    - Packet F (full curveIntegrability for chartedFormPullback)
      is a real analysis proof depending on Mathlib's continuity
      stack.
    - Cover-with `_add` becoming unconditional needs Packet F.
    - Partition independence / well-definedness of
      `pathIntegralViaCover` is a substantial chart-transition
      theorem.
    - Stokes / homotopy invariance is a major theorem.
  Each is multi-tick to multi-day work. The ladder of small simps
  extending the bridge has hit diminishing returns and should be
  paused; resuming progress on the remaining 35% requires either
  Aristotle-scale jobs or larger Claude-owned packets, neither of
  which can land in a 5-minute tick.

## Earlier (now stale; kept for context only)
## Stale Live Status (2026-04-27 04:13 EDT)

- Active jobs (ours): 1/5; canary `09cd85dd` QUEUED ~10h —
  `submitted-redundant`, kept as wake detector.
- **Integrated this tick (local Claude-owned):**
  - EXTENDED `Jacobian/Periods/TranslationChart.lean` with
    `pathIntegralInChartCorrect_translationChart_zero`: corrected
    variant of last-tick's degenerate-case lemma.
    `pathIntegralInChartCorrect (translationChart 0) ω γ =
    curveIntegral ω.toFun γ`. Proof: rewrite via the corrected
    translation formula, then `congr 1; funext; neg_zero, add_zero`.
    Build green (8189 jobs).

## Earlier (now stale; kept for context only)
## Stale Live Status (2026-04-27 04:05 EDT)

- Active jobs (ours): 1/5; canary `09cd85dd` QUEUED ~9h —
  `submitted-redundant`, kept as wake detector.
- **Integrated this tick (local Claude-owned):**
  - EXTENDED `Jacobian/Periods/TranslationChart.lean` with
    `pathIntegralInChart_translationChart_zero`: degenerate case
    `translationChart 0` reduces the in-chart integral to
    `curveIntegral ω.toFun γ` (matching the refl-chart formula).
    Proof: rewrite via the general translation formula, then
    `congr 1; funext` + `neg_zero, add_zero`. Build green
    (8189 jobs).

## Earlier (now stale; kept for context only)
## Stale Live Status (2026-04-27 03:59 EDT)

- Active jobs (ours): 1/5; canary `09cd85dd` QUEUED ~9h —
  `submitted-redundant`, kept as wake detector.
- **Integrated this tick (local Claude-owned):**
  - EXTENDED `Jacobian/Periods/PathIntegralReflChart.lean` with
    `chartedFormLinearMap_refl_apply_eq_toFun`: provisional
    bundled-LinearMap version. `chartedFormLinearMap (refl E) ω =
    ω.toFun`.
  - EXTENDED `Jacobian/Periods/TranslationChart.lean` with
    `chartedFormLinearMap_translationChart_apply_eq_shifted`:
    `chartedFormLinearMap (translationChart v) ω =
    fun e => ω.toFun (e + (-v))`.
  Both reduce directly to the corresponding chartedForm function-
  equality forms (via the bundled `_apply` rfl). Now both chart
  instances have bundled-LinearMap formulas at both corrected and
  provisional layers. Build green (8189 jobs).

## Earlier (now stale; kept for context only)
## Stale Live Status (2026-04-27 03:52 EDT)

- Active jobs (ours): 1/5; canary `09cd85dd` QUEUED ~9h —
  `submitted-redundant`, kept as wake detector.
- **Integrated this tick (local Claude-owned):**
  - EXTENDED `Jacobian/Periods/TranslationChart.lean` with
    `chartedFormPullbackLinearMap_translationChart_apply_eq_shifted`:
    bundled-LinearMap version of the translation-chart pullback
    formula. `chartedFormPullbackLinearMap (translationChart v) ω =
    fun e : E => ω.toFun (e + (-v))`. Companion to last tick's refl
    variant. Both chart instances now have bundled-LinearMap
    pullback formulas. Build green (8189 jobs).

## Earlier (now stale; kept for context only)
## Stale Live Status (2026-04-27 03:46 EDT)

- Active jobs (ours): 1/5; canary `09cd85dd` QUEUED ~9h —
  `submitted-redundant`, kept as wake detector.
- **Integrated this tick (local Claude-owned):**
  - EXTENDED `Jacobian/Periods/PathIntegralReflChart.lean` with
    `chartedFormPullbackLinearMap_refl_apply_eq_toFun`: the
    bundled-LinearMap version of the refl-chart pullback formula.
    `chartedFormPullbackLinearMap (refl E) ω = ω.toFun`. Reduces
    to the unbundled `chartedFormPullback_refl_eq_toFun` (since the
    bundled `_apply` is rfl). Bundled callers can now identify the
    refl-chart pullback directly as `ω.toFun`. Build green
    (8189 jobs).

## Earlier (now stale; kept for context only)
## Stale Live Status (2026-04-27 03:39 EDT)

- Active jobs (ours): 1/5; canary `09cd85dd` QUEUED ~9h —
  `submitted-redundant`, kept as wake detector.
- **Integrated this tick (local Claude-owned):**
  - EXTENDED `Jacobian/Periods/TranslationChart.lean` with two
    function-equality forms:
      - `chartedForm_translationChart_eq_shifted`: rfl
        `chartedForm (translationChart v) ω =
        fun e : E => ω.toFun (e + (-v))`.
      - `chartedFormPullback_translationChart_eq_shifted`:
        `chartedFormPullback (translationChart v) ω =
        fun e : E => ω.toFun (e + (-v))` as functions
        (proof: `funext` + `chartedFormPullback_translationChart_apply`).
    Companion to last-tick's refl variants — both chart instances
    now have function-level chartedForm/chartedFormPullback
    formulas. Build green (8189 jobs).

## Earlier (now stale; kept for context only)
## Stale Live Status (2026-04-27 03:33 EDT)

- Active jobs (ours): 1/5; canary `09cd85dd` QUEUED ~9h —
  `submitted-redundant`, kept as wake detector.
- **Integrated this tick (local Claude-owned):**
  - EXTENDED `Jacobian/Periods/PathIntegralReflChart.lean` with
    two function-equality forms:
      - `chartedForm_refl_eq_toFun`: rfl
        `chartedForm (refl E) ω = ω.toFun` as functions.
      - `chartedFormPullback_refl_eq_toFun`:
        `chartedFormPullback (refl E) ω = ω.toFun` as functions
        (proof: `funext` + `chartedFormPullback_refl_apply`).
    Function-level statements rather than pointwise — useful for
    `congr`-style rewriting without an explicit `funext`. Build
    green (8189 jobs).

## Earlier (now stale; kept for context only)
## Stale Live Status (2026-04-27 03:26 EDT)

- Active jobs (ours): 1/5; canary `09cd85dd` QUEUED ~9h —
  `submitted-redundant`, kept as wake detector.
- **Integrated this tick (local Claude-owned):**
  - EXTENDED `Jacobian/Periods/PathIntegralReflCover.lean` with
    `pathIntegralViaCoverWith_self_eq_sum_curveIntegral`: cover-with
    (explicit-partition) variant of last tick's Pick-layer
    reduction. Theorem: for `chartedSpaceSelf E`,
    `pathIntegralViaCoverWith ω γ n hn pickChart hcov =
    ∑ i, curveIntegral ω.toFun (γ.subpath_i)`. Proof: unfold
    `pathIntegralViaCoverWith` + `Finset.sum_congr` +
    `pathIntegralViaChartCorrect_reflChart` per summand —
    going through the corrected layer directly without bouncing
    off the bridge. Build green (8189 jobs).

## Earlier (now stale; kept for context only)
## Stale Live Status (2026-04-27 03:18 EDT)

- Active jobs (ours): 1/5; canary `09cd85dd` QUEUED ~9h —
  `submitted-redundant`, kept as wake detector.
- **Integrated this tick (local Claude-owned):**
  - EXTENDED `Jacobian/Periods/PathIntegralReflCover.lean` with
    `pathIntegralViaCover_self_eq_sum_curveIntegral`: for
    `chartedSpaceSelf E`, the user-facing multi-chart integral
    `pathIntegralViaCover ω γ` reduces to a plain
    `∑ i, curveIntegral ω.toFun (γ.subpath_i)`. Proof: rewrite via
    `_self_eq_sum_provisional` (existing), then `Finset.sum_congr`
    + `pathIntegralViaChart_reflChart` per summand. Most reduced
    cover-layer formula — `pathIntegralViaCover` now hooks directly
    into Mathlib's `curveIntegral` for `chartedSpaceSelf E`. Build
    green (8189 jobs).

## Earlier (now stale; kept for context only)
## Stale Live Status (2026-04-27 03:07 EDT)

- Active jobs (ours): 1/5; canary `09cd85dd` QUEUED ~8h —
  `submitted-redundant`, kept as wake detector.
- **Integrated this tick (local Claude-owned):**
  - EXTENDED `Jacobian/Periods/PathIntegralReflChart.lean` with
    `pathIntegralViaChartCorrect_reflChart`:
    `pathIntegralViaChartCorrect (refl E) ω γ h =
    curveIntegral ω.toFun γ`.
  - EXTENDED `Jacobian/Periods/TranslationChart.lean` with
    `pathIntegralViaChartCorrect_translationChart`:
    `pathIntegralViaChartCorrect (translationChart v) ω γ h =
    curveIntegral (fun e => ω.toFun (e + (-v)))
    (chartLift (translationChart v) γ h)`.
  Both proofs combine the chart-specific via-chart bridge with
  last-tick's provisional via-chart formulas. Both chart instances
  now have end-to-end direct `curveIntegral` simps spanning
  corrected and provisional layers. Build green (8189 jobs).

## Earlier (now stale; kept for context only)
## Stale Live Status (2026-04-27 02:59 EDT)

- Active jobs (ours): 1/5; canary `09cd85dd` QUEUED ~8h —
  `submitted-redundant`, kept as wake detector.
- **Integrated this tick (local Claude-owned):**
  - EXTENDED `Jacobian/Periods/PathIntegralReflChart.lean` with
    `pathIntegralInChartCorrect_reflChart`:
    `pathIntegralInChartCorrect (refl E) ω γ =
    curveIntegral ω.toFun γ`.
  - EXTENDED `Jacobian/Periods/TranslationChart.lean` with
    `pathIntegralInChartCorrect_translationChart`:
    `pathIntegralInChartCorrect (translationChart v) ω γ =
    curveIntegral (fun e => ω.toFun (e + (-v))) γ`.
  Both proofs combine the bridge `pathIntegralInChartCorrect_..._eq_
  pathIntegralInChart` with the provisional `_chart` formula.
  Both refl and translation instances now have corrected in-chart
  formulas hooking directly into Mathlib's `curveIntegral`. Build
  green (8189 jobs).

## Earlier (now stale; kept for context only)
## Stale Live Status (2026-04-27 02:52 EDT)

- Active jobs (ours): 1/5; canary `09cd85dd` QUEUED ~8h —
  `submitted-redundant`, kept as wake detector.
- **Integrated this tick (local Claude-owned):**
  - EXTENDED `Jacobian/Periods/TranslationChart.lean` with
    `pathIntegralViaChart_translationChart`: via-chart variant of
    last tick's in-chart integral simp. Theorem:
    `pathIntegralViaChart (translationChart v) ω γ h =
    curveIntegral (fun e => ω.toFun (e + (-v)))
    (chartLift (translationChart v) γ h)`. Proof: unfold via-chart
    definition + apply the in-chart variant. Build green (8189
    jobs).

## Earlier (now stale; kept for context only)
## Stale Live Status (2026-04-27 02:46 EDT)

- Active jobs (ours): 1/5; canary `09cd85dd` QUEUED ~8h —
  `submitted-redundant`, kept as wake detector.
- **Integrated this tick (local Claude-owned):**
  - EXTENDED `Jacobian/Periods/TranslationChart.lean` with
    `pathIntegralInChart_translationChart`: theorem
    `pathIntegralInChart (translationChart v) ω γ =
    curveIntegral (fun e => ω.toFun (e + (-v))) γ`. Hooks the
    in-chart integral on a translation chart directly into Mathlib's
    `curveIntegral`. Companion to last-tick's
    `pathIntegralInChart_reflChart`. Build green (8189 jobs).

## Earlier (now stale; kept for context only)
## Stale Live Status (2026-04-27 02:41 EDT)

- Active jobs (ours): 1/5; canary `09cd85dd` QUEUED ~8h —
  `submitted-redundant`, kept as wake detector.
- **Integrated this tick (local Claude-owned):**
  - EXTENDED `Jacobian/Periods/PathIntegralReflChart.lean` with
    `pathIntegralViaChart_reflChart`: via-chart analogue of last
    tick's `pathIntegralInChart_reflChart`. Theorem:
    `pathIntegralViaChart (OpenPartialHomeomorph.refl E) ω γ h =
    curveIntegral ω.toFun γ`. Proof: unfold via-chart definition
    and apply the in-chart variant — the chart-lift through refl
    is the path itself. Build green (8189 jobs).

## Earlier (now stale; kept for context only)
## Stale Live Status (2026-04-27 02:35 EDT)

- Active jobs (ours): 1/5; canary `09cd85dd` QUEUED ~8h —
  `submitted-redundant`, kept as wake detector.
- **Integrated this tick (local Claude-owned):**
  - EXTENDED `Jacobian/Periods/PathIntegralReflChart.lean` with
    `pathIntegralInChart_reflChart`: the provisional in-chart
    integral on `OpenPartialHomeomorph.refl E` reduces to the
    direct `curveIntegral ω.toFun γ`. Hooks the refl chart into
    Mathlib's `curveIntegral` directly. Renamed (with `Chart`
    suffix) to avoid clash with the existing `pathIntegralInChart_refl`
    (for constant paths). Build green (8189 jobs).

## Earlier (now stale; kept for context only)
## Stale Live Status (2026-04-27 02:27 EDT)

- Active jobs (ours): 1/5; canary `09cd85dd` QUEUED ~8h —
  `submitted-redundant`, kept as wake detector.
- **Integrated this tick (local Claude-owned):**
  - Stocktake/progress-report adjustment in `README.md`: Path
    integration/periods bar bumped from 55% to 65%, and the
    explanatory note updated to describe the bridge-ladder maturity
    plus the concrete refl/translationChart instances. No source
    code changes this tick.

## Earlier (now stale; kept for context only)
## Stale Live Status (2026-04-27 02:25 EDT)

- Active jobs (ours): 1/5; canary `09cd85dd` QUEUED ~8h —
  `submitted-redundant`, kept as wake detector.
- **Integrated this tick (local Claude-owned):**
  - EXTENDED `Jacobian/Periods/PathIntegralReflChart.lean` with
    two refl-chart pointwise formulas:
      - `chartedForm_refl_apply`: rfl
        `chartedForm (refl E) ω e = ω.toFun e`.
      - `chartedFormPullback_refl_apply`: corrected chart-pullback
        on the refl chart equals `ω.toFun e` — proof combines the
        refl bridge with `chartedForm_refl_apply`.
    Companion to last-tick's translation-chart pointwise formulas.
    Build green (8189 jobs).

## Earlier (now stale; kept for context only)
## Stale Live Status (2026-04-27 02:19 EDT)

- Active jobs (ours): 1/5; canary `09cd85dd` QUEUED ~8h —
  `submitted-redundant`, kept as wake detector.
- **Integrated this tick (local Claude-owned):**
  - EXTENDED `Jacobian/Periods/TranslationChart.lean` with
    `chartedFormPullback_translationChart_apply`: explicit
    pointwise formula
    `chartedFormPullback (translationChart v) ω e =
    ω.toFun (e + (-v))`. Proof: combine the bridge instance
    `chartedFormPullback_translationChart_eq_chartedForm` with
    last-tick's `chartedForm_translationChart_apply`. The corrected
    chart-pullback on a translation chart reduces to the simple
    shifted form. Build green (8189 jobs).

## Earlier (now stale; kept for context only)
## Stale Live Status (2026-04-27 02:14 EDT)

- Active jobs (ours): 1/5; canary `09cd85dd` QUEUED ~8h —
  `submitted-redundant`, kept as wake detector.
- **Integrated this tick (local Claude-owned):**
  - EXTENDED `Jacobian/Periods/TranslationChart.lean` with
    `chartedForm_translationChart_apply`: rfl identity
    `chartedForm (translationChart v) ω e = ω.toFun (e + (-v))`.
    Names the explicit pointwise formula for the provisional
    chart-form on a translation chart — useful for downstream
    callers who want to compute integrals through translation
    charts. Build green (8189 jobs).

## Earlier (now stale; kept for context only)
## Stale Live Status (2026-04-27 02:09 EDT)

- Active jobs (ours): 1/5; canary `09cd85dd` QUEUED ~7h —
  `submitted-redundant`, kept as wake detector.
- **Integrated this tick (local Claude-owned):**
  - EXTENDED `Jacobian/Periods/PathIntegralReflChart.lean` with
    `chartLift_refl_apply`: rfl simp lemma
    `chartLift (OpenPartialHomeomorph.refl E) γ h t = γ t`.
    Companion to last tick's `chartLift_translationChart_apply` —
    `simp` now unfolds the chart-lift through both the refl chart
    and any translation chart. Build green (8189 jobs).

## Earlier (now stale; kept for context only)
## Stale Live Status (2026-04-27 02:02 EDT)

- Active jobs (ours): 1/5; canary `09cd85dd` QUEUED ~7h —
  `submitted-redundant`, kept as wake detector.
- **Integrated this tick (local Claude-owned):**
  - EXTENDED `Jacobian/Periods/TranslationChart.lean` with
    `chartLift_translationChart_apply`: rfl simp lemma
    `chartLift (translationChart v) γ h t = γ t + v`. Lets `simp`
    unfold the chart-lift of a path through a translation chart to
    the explicit pointwise translation. Useful for downstream
    callers that need the lifted path's pointwise behavior. Build
    green (8189 jobs).

## Earlier (now stale; kept for context only)
## Stale Live Status (2026-04-27 01:56 EDT)

- Active jobs (ours): 1/5; canary `09cd85dd` QUEUED ~7h —
  `submitted-redundant`, kept as wake detector.
- **Integrated this tick (local Claude-owned):**
  - EXTENDED `Jacobian/Periods/PathIntegralReflChart.lean` with
    `mfderiv_chartAt_self_symm_eq_id`: for `chartedSpaceSelf E`,
    the manifold derivative of `(chartAt E x).symm` at any `e` is
    `ContinuousLinearMap.id`. Direct corollary of the existing
    `mfderiv_refl_symm_eq_id` since `chartAt E x = refl E`
    definitionally for `chartedSpaceSelf`. Ties the bridge
    witness directly to Mathlib's `chartAt` typeclass interface,
    avoiding the need for callers to unfold the chartedSpace
    instance. Build green (8189 jobs).

## Earlier (now stale; kept for context only)
## Stale Live Status (2026-04-27 01:50 EDT)

- Active jobs (ours): 1/5; canary `09cd85dd` QUEUED ~7h —
  `submitted-redundant`, kept as wake detector.
- **Integrated this tick (local Claude-owned):**
  - EXTENDED `Jacobian/Periods/TranslationChart.lean` with two
    function-level cancellation simp lemmas:
      - `translationChart_neg_apply_translationChart_apply`:
        `translationChart (-v) (translationChart v x) = x`
        (proof: `add_neg_cancel_right`).
      - `translationChart_apply_translationChart_neg_apply`:
        `translationChart v (translationChart (-v) x) = x`
        (proof: `neg_add_cancel_right`).
    Cancellation laws — `simp` automatically closes any nested
    `translationChart v / translationChart (-v)` composition.
    Build green (8189 jobs).

## Earlier (now stale; kept for context only)
## Stale Live Status (2026-04-27 01:44 EDT)

- Active jobs (ours): 1/5; canary `09cd85dd` QUEUED ~7h —
  `submitted-redundant`, kept as wake detector.
- **Integrated this tick (local Claude-owned):**
  - EXTENDED `Jacobian/Periods/TranslationChart.lean` with
    `translationChart_zero`: structure-level equality
    `translationChart (0 : E) = OpenPartialHomeomorph.refl E`.
    Proof: `OpenPartialHomeomorph.ext` + `add_zero` /
    `neg_zero` + `add_zero` on each direction. Confirms the
    translation atlas contains the identity chart. Combined with
    last-tick's `translationChart_symm`, the translation chart
    family has both identity (`0`) and inverses (`-v`) at the
    OpenPartialHomeomorph structure level. Build green (8189 jobs).

## Earlier (now stale; kept for context only)
## Stale Live Status (2026-04-27 01:40 EDT)

- Active jobs (ours): 1/5; canary `09cd85dd` QUEUED ~7h —
  `submitted-redundant`, kept as wake detector.
- **Integrated this tick (local Claude-owned):**
  - EXTENDED `Jacobian/Periods/TranslationChart.lean` with
    `translationChart_symm`: structure-level equality
    `(translationChart v).symm = translationChart (-v)` as
    `OpenPartialHomeomorph`s. Proof: `OpenPartialHomeomorph.ext`
    with rfl on forward, `neg_neg` rewrite on the inverse. Now the
    translation-chart involution is available at the
    OpenPartialHomeomorph layer, not just the function level.
    Build green (8189 jobs).

## Earlier (now stale; kept for context only)
## Stale Live Status (2026-04-27 01:32 EDT)

- Active jobs (ours): 1/5; canary `09cd85dd` QUEUED ~7h —
  `submitted-redundant`, kept as wake detector.
- **Integrated this tick (local Claude-owned):**
  - EXTENDED `Jacobian/Periods/ChartedFormPullbackEqChartedFormOfMfderivId.lean`
    with primed function-equality form
    `chartedFormPullback_eq_chartedForm_of_mfderiv_id'`: under the
    global mfderiv-identity hypothesis,
    `chartedFormPullback c ω = chartedForm c ω` as functions
    (proof: `funext` + per-point bridge). Lets downstream callers
    use the function-level equality directly without an explicit
    `funext`. Build green (8189 jobs).

## Earlier (now stale; kept for context only)
## Stale Live Status (2026-04-27 01:21 EDT)

- Active jobs (ours): 1/5; canary `09cd85dd` QUEUED ~7h —
  `submitted-redundant`, kept as wake detector.
- **Integrated this tick (local Claude-owned):**
  - NEW `Jacobian/Periods/ChartedFormPullbackEqOnOfMfderivId.lean`:
    set-restricted bridge. Theorem
    `chartedFormPullback_eqOn_chartedForm_of_mfderiv_id`: if
    `mfderiv c.symm = id` for every `e ∈ s`, then
    `EqOn (chartedFormPullback c ω) (chartedForm c ω) s`. Natural
    intermediate between the per-point and global bridges —
    matches the "agrees on `c.target` only" pattern of partial
    chart inverses. Proof: just unfold `EqOn` and apply the
    per-point bridge. Build green (8189 jobs).

## Earlier (now stale; kept for context only)
## Stale Live Status (2026-04-27 01:15 EDT)

- Active jobs (ours): 1/5; canary `09cd85dd` QUEUED ~7h —
  `submitted-redundant`, kept as wake detector.
- **Integrated this tick (local Claude-owned):**
  - EXTENDED `Jacobian/Periods/TranslationChart.lean` with
    `translationChart_source` and `translationChart_target` simp
    lemmas: both equal `Set.univ` (rfl). Discharges the
    `range γ ⊆ source` precondition trivially for downstream
    callers using translation charts — `simp` handles it. Build
    green (8188 jobs).

## Earlier (now stale; kept for context only)
## Stale Live Status (2026-04-27 01:10 EDT)

- Active jobs (ours): 1/5; canary `09cd85dd` QUEUED ~7h —
  `submitted-redundant`, kept as wake detector.
- **Integrated this tick (local Claude-owned):**
  - EXTENDED `Jacobian/Periods/TranslationChart.lean` with
    `translationChart_symm_apply_eq_translationChart_neg_apply`:
    rfl-level identity stating `(translationChart v).symm x =
    translationChart (-v) x` as functions. Both reduce to `x + (-v)`
    definitionally. Establishes the involution structure of
    translation charts (chart-symm = chart at negated translation).
    Build green (8188 jobs).

## Earlier (now stale; kept for context only)
## Stale Live Status (2026-04-27 01:03 EDT)

- Active jobs (ours): 1/5; canary `09cd85dd` QUEUED ~6h —
  `submitted-redundant`, kept as wake detector.
- **Integrated this tick (local Claude-owned):**
  - EXTENDED `Jacobian/Periods/TranslationChart.lean` with chart-
    transition simp lemmas:
      - `translationChart_apply_translationChart_symm_apply`:
        `translationChart v ((translationChart u).symm x) = x + (-u) + v`
      - `translationChart_symm_apply_translationChart_apply`:
        `(translationChart u).symm (translationChart v x) = (x + v) + (-u)`
    Both proved by `rfl`. This is the geometric content showing
    translation atlases close under chart transitions — the
    composition of two translations is a translation. Foundational
    for translation-only manifolds (e.g. complex torus). Build
    green (8188 jobs).

## Earlier (now stale; kept for context only)
## Stale Live Status (2026-04-27 00:58 EDT)

- Active jobs (ours): 1/5; canary `09cd85dd` QUEUED ~6h —
  `submitted-redundant`, kept as wake detector.
- **Integrated this tick (local Claude-owned):**
  - EXTENDED `Jacobian/Periods/TranslationChart.lean` with
    integration-tower lifts:
      - `pathIntegralInChartCorrect_translationChart_eq_pathIntegralInChart`
      - `pathIntegralViaChartCorrect_translationChart_eq_pathIntegralViaChart`
    Both unconditional. Translation-chart pipeline now at parity
    with refl-chart pipeline through via-chart for the concrete
    `translationChart v` instance. Build green (8188 jobs, no new
    module).

## Earlier (now stale; kept for context only)
## Stale Live Status (2026-04-27 00:53 EDT)

- Active jobs (ours): 1/5; canary `09cd85dd` QUEUED ~6h —
  `submitted-redundant`, kept as wake detector.
- **Integrated this tick (local Claude-owned):**
  - NEW `Jacobian/Periods/TranslationChart.lean`: concrete
    `translationChart v : OpenPartialHomeomorph E E` built from
    `Homeomorph.addRight v`. Three theorems:
      - `translationChart_apply v x = x + v` (rfl simp)
      - `translationChart_symm_apply v x = x + (-v)` (rfl simp)
      - `chartedFormPullback_translationChart_eq_chartedForm`:
        the bridge fires unconditionally for translation charts.
    Concrete named witness — anyone building chart constructions
    based on translations now has a ready-to-use chart with the
    bridge already proven. Build green (8188 jobs).

## Earlier (now stale; kept for context only)
## Stale Live Status (2026-04-27 00:45 EDT)

- Active jobs (ours): 1/5; canary `09cd85dd` QUEUED ~6h —
  `submitted-redundant`, kept as wake detector.
- **Integrated this tick (local Claude-owned):**
  - NEW `Jacobian/Periods/ChartedFormPullbackLinearMapEqOfMfderivId.lean`:
    bundled-LinearMap bridge. Theorem:
    `chartedFormPullbackLinearMap c = chartedFormLinearMap c`
    whenever `mfderiv c.symm = id` everywhere. Proof:
    `LinearMap.ext` + `funext` + the unbundled pointwise bridge.
    The corrected and provisional bundled chart-form LinearMaps
    coincide as a single equation under the same hypothesis used
    at every other layer of the bridge ladder. Build green
    (8187 jobs).

## Earlier (now stale; kept for context only)
## Stale Live Status (2026-04-27 00:40 EDT)

- Active jobs (ours): 1/5; canary `09cd85dd` QUEUED ~6h —
  `submitted-redundant`, kept as wake detector.
- **Integrated this tick (local Claude-owned):**
  - EXTENDED `Jacobian/Periods/ChartedFormPullbackTranslationChart.lean`
    with EventuallyEq variants of all three translation bridges:
      - `_of_symm_eventuallyEq_add_const`
      - `_of_symm_eventuallyEq_const_add`
      - `_of_symm_eventuallyEq_sub_const`
    Weaker hypothesis (`c.symm =ᶠ[𝓝 e] translation`) suffices since
    `mfderiv` is local at `e`. Proof: reduce to `_of_mfderiv_id` via
    `Filter.EventuallyEq.mfderiv_eq` + the corresponding
    `mfderiv_*_const_self`. Useful for charts that agree with a
    translation only in a neighborhood of `e` (typical of partial
    chart inverses). Build green (8186 jobs, no new module).

## Earlier (now stale; kept for context only)
## Stale Live Status (2026-04-27 00:34 EDT)

- Active jobs (ours): 1/5; canary `09cd85dd` QUEUED ~6h —
  `submitted-redundant`, kept as wake detector.
- **Integrated this tick (local Claude-owned):**
  - EXTENDED `Jacobian/Periods/PathIntegralTranslationChart.lean`
    with subtraction-translation tower lifts:
      - `pathIntegralInChartCorrect_eq_pathIntegralInChart_of_symm_eq_sub_const`
      - `pathIntegralViaChartCorrect_eq_pathIntegralViaChart_of_symm_eq_sub_const`
    Each feeds `mfderiv_sub_const_self` into the layer-wise
    `_of_mfderiv_id` bridge. Translation pipeline now covers all
    three forms (`x + v`, `v + x`, `x - v`) at chartedForm,
    in-chart, and via-chart layers. Build green (8186 jobs, no new
    module — extension of existing file).

## Earlier (now stale; kept for context only)
## Stale Live Status (2026-04-27 00:28 EDT)

- Active jobs (ours): 1/5; canary `09cd85dd` QUEUED ~6h —
  `submitted-redundant`, kept as wake detector.
- **Integrated this tick (local Claude-owned):**
  - EXTENDED `Jacobian/Periods/MfderivTranslation.lean` with
    `mfderiv_sub_const_self`: manifold derivative of `x ↦ x - v` is
    `id`. Proof: rewrite `x - v = x + (-v)` then specialize
    `mfderiv_add_const_self`.
  - EXTENDED `Jacobian/Periods/ChartedFormPullbackTranslationChart.lean`
    with `chartedFormPullback_eq_chartedForm_of_symm_eq_sub_const`:
    bridge fires when `c.symm = x ↦ x - v`. Useful because charts
    `c : x ↦ x + v` have `c.symm : x ↦ x - v`. Build green
    (8186 jobs, two extensions, no new modules).

## Earlier (now stale; kept for context only)
## Stale Live Status (2026-04-27 00:20 EDT)

- Active jobs (ours): 1/5; canary `09cd85dd` QUEUED ~6h —
  `submitted-redundant`, kept as wake detector.
- **Integrated this tick (local Claude-owned):**
  - EXTENDED `Jacobian/Periods/PathIntegralTranslationChart.lean`
    with the left-translation variants:
      - `pathIntegralInChartCorrect_eq_pathIntegralInChart_of_symm_eq_const_add`
      - `pathIntegralViaChartCorrect_eq_pathIntegralViaChart_of_symm_eq_const_add`
    Each feeds `mfderiv_const_add_self` into the layer-wise
    `_of_mfderiv_id` bridge. Translation pipeline now covers both
    `c.symm = x ↦ x + v` and `c.symm = x ↦ v + x` at in-chart and
    via-chart layers, all unconditional. Build green (8186 jobs,
    no new module — extension of existing file).

## Earlier (now stale; kept for context only)
## Stale Live Status (2026-04-27 00:15 EDT)

- Active jobs (ours): 1/5; canary `09cd85dd` QUEUED ~6h —
  `submitted-redundant`, kept as wake detector.
- **Integrated this tick (local Claude-owned):**
  - NEW `Jacobian/Periods/PathIntegralTranslationChart.lean`:
    lifts the translation-chart bridge up the integration tower.
    Two theorems for a self-chart `c : OpenPartialHomeomorph E E`
    with `c.symm = fun x => x + v`:
      - `pathIntegralInChartCorrect_eq_pathIntegralInChart_of_symm_eq_add_const`:
        in-chart corrected = provisional unconditionally.
      - `pathIntegralViaChartCorrect_eq_pathIntegralViaChart_of_symm_eq_add_const`:
        via-chart corrected = provisional unconditionally.
    Each proof feeds `mfderiv_add_const_self` into the existing
    layer-wise `_of_mfderiv_id` bridges. Translation pipeline now
    at parity with refl through via-chart. Build green (8186 jobs).

## Earlier (now stale; kept for context only)
## Stale Live Status (2026-04-27 00:10 EDT)

- Active jobs (ours): 1/5; canary `09cd85dd` QUEUED ~6h —
  `submitted-redundant`, kept as wake detector.
- **Integrated this tick (local Claude-owned):**
  - NEW `Jacobian/Periods/ChartedFormPullbackTranslationChart.lean`:
    translation-chart bridge instance using last-tick's
    `MfderivTranslation` building blocks. Two theorems:
      - `chartedFormPullback_eq_chartedForm_of_symm_eq_add_const`:
        if `c.symm = fun x => x + v`, the corrected pullback equals
        the provisional chart-form unconditionally.
      - `chartedFormPullback_eq_chartedForm_of_symm_eq_const_add`:
        same with left translation `c.symm = fun x => v + x`.
    Proof: rewrite `c.symm` as the explicit translation, then
    `mfderiv_{add,const}_const_self`. Second concrete bridge
    instance after refl, directly relevant to torus transition
    charts. Build green (8185 jobs).

## Earlier (now stale; kept for context only)
## Stale Live Status (2026-04-27 00:02 EDT)

- Active jobs (ours): 1/5; canary `09cd85dd` QUEUED ~6h —
  `submitted-redundant`, kept as wake detector.
- **Integrated this tick (local Claude-owned):**
  - NEW `Jacobian/Periods/MfderivTranslation.lean`: building
    blocks for translation-chart bridge instances. Two theorems:
      - `mfderiv_add_const_self v e`: manifold derivative of
        `x ↦ x + v` at any `e` is `id`.
      - `mfderiv_const_add_self v e`: manifold derivative of
        `x ↦ v + x` at any `e` is `id`.
    Both proofs reduce to `fderiv` via `mfderiv_eq_fderiv`, then
    `fderiv_add_const` (or `fderiv_const_add`) + `fderiv_id`. Sets
    up future translation-chart bridge instances — torus
    transition charts are translations by lattice elements.
    Build green (8184 jobs).

## Earlier (now stale; kept for context only)
## Stale Live Status (2026-04-26 23:53 EDT)

- Active jobs (ours): 1/5; canary `09cd85dd` QUEUED ~5h —
  `submitted-redundant`, kept as wake detector.
- **Integrated this tick (local Claude-owned):**
  - NEW `Jacobian/Periods/PathIntegralReflCover.lean`: tops out
    the refl-chart pipeline at the cover-with and Pick layers.
    Two theorems for `chartedSpaceSelf E`:
      - `pathIntegralViaCoverWith_self_eq_sum_provisional`:
        cover-with multi-chart integral = ∑ provisional via-chart
        integrals on each segment, unconditionally.
      - `pathIntegralViaCover_self_eq_sum_provisional`:
        same identity at the user-facing Pick wrapper.
    Both proofs feed the refl witness `mfderiv_refl_symm_eq_id`
    into the existing `_of_mfderiv_id` cover-with / Pick bridges.
    End-to-end refl pipeline now complete: chartedForm → in-chart
    → via-chart → cover-with → Pick. Build green (8183 jobs).

## Earlier (now stale; kept for context only)
## Stale Live Status (2026-04-26 23:45 EDT)

- Active jobs (ours): 1/5; canary `09cd85dd` QUEUED ~5h —
  `submitted-redundant`, kept as wake detector.
- **Integrated this tick (local Claude-owned):**
  - NEW `Jacobian/Periods/PathIntegralReflChart.lean`: lifts the
    previous-tick refl-chart bridge up the integration tower.
    Packages `mfderiv_refl_symm_eq_id` as a reusable global witness
    (proof: rewrite `(refl E).symm` as the identity function via
    `funext` + `refl_symm` simp, then `mfderiv_id`). Then derives
    two unconditional corollaries via the existing layer-wise
    bridges:
      - `pathIntegralInChartCorrect_refl_eq_pathIntegralInChart_refl`
      - `pathIntegralViaChartCorrect_refl_eq_pathIntegralViaChart_refl`
    The refl chart now has a fully concrete corrected ↔ provisional
    pipeline at every layer up to via-chart. Build green
    (8182 jobs).

## Earlier (now stale; kept for context only)
## Stale Live Status (2026-04-26 23:39 EDT)

- Active jobs (ours): 1/5; canary `09cd85dd` QUEUED ~5h —
  `submitted-redundant`, kept as wake detector.
- **Integrated this tick (local Claude-owned):**
  - NEW `Jacobian/Periods/ChartedFormPullbackRefl.lean`:
    concrete-instance corollary of the bridge.
    `chartedFormPullback (OpenPartialHomeomorph.refl E) ω e =
    chartedForm (OpenPartialHomeomorph.refl E) ω e`
    unconditionally. First concrete witness that the bridge
    ladder fires on a real chart instance. Proof: apply the
    EventuallyEq variant — the witness `(refl E).symm = id` is
    direct from `OpenPartialHomeomorph.refl_symm`. Build green
    (8181 jobs).

## Earlier (now stale; kept for context only)
## Stale Live Status (2026-04-26 23:31 EDT)

- Active jobs (ours): 1/5; canary `09cd85dd` QUEUED ~5h —
  `submitted-redundant`, kept as wake detector.
- **Integrated this tick (local Claude-owned):**
  - NEW `Jacobian/Periods/ChartedFormPullbackEqChartedFormOfSymmEventuallyEqId.lean`:
    weaker sufficient condition for the chartedForm bridge. For a
    self-chart `c : OpenPartialHomeomorph E E`, the hypothesis
    `c.symm =ᶠ[𝓝 e] id` (i.e. `c.symm` agrees with the identity in
    a neighborhood of `e`) suffices. Proof: reduce to the previous
    `_of_mfderiv_id` bridge via `Filter.EventuallyEq.mfderiv_eq` +
    `mfderiv_id`. Useful instance for translation charts on the
    model space `ℂ` itself (the torus example). Build green
    (8180 jobs).

## Earlier (now stale; kept for context only)
## Stale Live Status (2026-04-26 23:16 EDT)

- Active jobs (ours): 1/5; canary `09cd85dd` QUEUED ~5h —
  `submitted-redundant`, kept as wake detector.
- **Integrated this tick (local Claude-owned):**
  - NEW `Jacobian/Periods/PathIntegralViaCoverEqOfMfderivId.lean`:
    Pick-layer bridge — the user-facing
    `pathIntegralViaCover ω γ` reduces to a sum of provisional
    via-chart integrals on the `Classical.choose`-picked partition,
    under the global hypothesis
    `∀ (x : X) (e : E), mfderiv (chartAt E x).symm e = id`. Proof:
    `unfold` + apply the cover-with bridge with the universal
    hypothesis adapted to each segment chart. **Bridge ladder fully
    closed: chartedForm ✓ in-chart ✓ via-chart ✓ cover-with ✓
    Pick ✓.** All 5 layers now have a named bridge from corrected
    to provisional under one global hypothesis. Apt for
    translation-only manifolds (e.g. complex tori). Build green
    (8179 jobs).

## Earlier (now stale; kept for context only)
## Stale Live Status (2026-04-26 23:09 EDT)

- Active jobs (ours): 1/5; canary `09cd85dd` QUEUED ~5h —
  `submitted-redundant`, kept as wake detector.
- **Integrated this tick (local Claude-owned):**
  - NEW `Jacobian/Periods/CoverSegmentSubpathRange.lean`:
    extracts a reusable named version of the inline range-subset
    proof embedded in `pathIntegralViaCoverWith` (the cover-with
    definition). Useful infrastructure for any cover-with theorem
    that needs to talk about the i-th segment's range.
  - NEW `Jacobian/Periods/PathIntegralViaCoverWithEqOfMfderivId.lean`:
    cover-with bridge under `mfderiv c.symm = id`. Theorem:
    `pathIntegralViaCoverWith ω γ n hn pickChart hcov =
    ∑ i, pathIntegralViaChart (chartAt E (pickChart i)) ω
    (γ.subpath …) (cover_segment_subpath_range …)` whenever each
    chart's `mfderiv c.symm = id` everywhere. Proof: `unfold` then
    `Finset.sum_congr` + per-segment via-chart bridge. Bridge
    ladder: chartedForm ✓, in-chart ✓, via-chart ✓, cover-with ✓ —
    only Pick layer remains. Build green (8178 jobs).

## Earlier (now stale; kept for context only)
## Stale Live Status (2026-04-26 22:53 EDT)

- Active jobs (ours): 1/5; canary `09cd85dd` QUEUED ~4h —
  `submitted-redundant`, kept as wake detector.
- **Integrated this tick (local Claude-owned):**
  - NEW `Jacobian/Periods/PathIntegralViaChartCorrectEqOfMfderivId.lean`:
    lifts the in-chart bridge to the from-`X` via-chart layer.
    `pathIntegralViaChartCorrect c ω γ h =
    pathIntegralViaChart c ω γ h` under the same `mfderiv c.symm =
    id` hypothesis. Proof: `unfold` + apply the in-chart bridge to
    the chart-lifted path. Bridge ladder so far: chartedForm ✓,
    in-chart ✓, via-chart ✓; cover layers next. Build green
    (8176 jobs).

## Earlier (now stale; kept for context only)
## Stale Live Status (2026-04-26 22:48 EDT)

- Active jobs (ours): 1/5; canary `09cd85dd` QUEUED ~4h —
  `submitted-redundant`, kept as wake detector.
- **Integrated this tick (local Claude-owned):**
  - NEW `Jacobian/Periods/PathIntegralInChartCorrectEqOfMfderivId.lean`:
    lifts the previous-tick chartedForm bridge to integrals.
    Theorem: `pathIntegralInChartCorrect c ω γ =
    pathIntegralInChart c ω γ` whenever `mfderiv c.symm` is the
    identity everywhere on `E`. Proof: `congr` under `curveIntegral`
    + `funext` + the CLM-level bridge. The provisional integration
    layer now coincides exactly with the corrected one under a
    single named global hypothesis. Build green (8175 jobs).

## Earlier (now stale; kept for context only)
## Stale Live Status (2026-04-26 22:42 EDT)

- Active jobs (ours): 1/5; canary `09cd85dd` QUEUED ~4h —
  `submitted-redundant`, kept as wake detector.
- **Integrated this tick (local Claude-owned):**
  - NEW `Jacobian/Periods/ChartedFormPullbackEqChartedFormOfMfderivId.lean`:
    conditional bridge — when `mfderiv c.symm e =
    ContinuousLinearMap.id`, the corrected chart-pullback coincides
    with the provisional chart-form (both at the CLM level and the
    tangent-vec apply level). This is the precise hypothesis for
    when the provisional layer is exactly correct (translation
    transition charts; e.g. the torus example). Build green (8174
    jobs).

## Earlier (now stale; kept for context only)
## Stale Live Status (2026-04-26 22:36 EDT)

- Active jobs (ours): 1/5; canary `09cd85dd` QUEUED ~4h —
  `submitted-redundant`, kept as wake detector.
- **Integrated this tick (local Claude-owned):**
  - NEW `Jacobian/Periods/ChartedFormPullbackEqChartedFormCompMfderiv.lean`:
    the `rfl` bridge between the corrected and provisional
    chart-form towers. Names
    `chartedFormPullback c ω e = (chartedForm c ω e).comp
    (mfderiv c.symm e)` plus its tangent-vec apply form. Makes the
    `mfderiv`-factor difference explicit and reusable. Build green
    (8173 jobs).

## Earlier (now stale; kept for context only)
## Stale Live Status (2026-04-26 22:29 EDT)

- Active jobs (ours): 1/5; canary `09cd85dd` QUEUED ~4h —
  now `submitted-redundant` (proof discharged locally this tick)
  but kept running as wake detector.
- **Integrated this tick (local Claude-owned):**
  - DISCHARGED sorry in
    `Jacobian/Periods/PathIntegralViaChartTrans.lean`:
    `pathIntegralViaChart_trans_of_curveIntegrable` proven directly
    (`unfold + chartLift_trans rw + exact in-chart trans`),
    matching the corrected-layer proof exactly. The last via-chart
    sorry is gone. Build green (8172 jobs).

## Earlier (now stale; kept for context only)
## Stale Live Status (2026-04-26 22:23 EDT)

- Active jobs (ours): 1/5; canary `09cd85dd` QUEUED ~4h.
- **Integrated this tick (local Claude-owned):**
  - NEW `Jacobian/Periods/PathIntegralViaCoverPickNegSmul.lean`:
    Pick (unparameterised multi-chart) layer of `_neg_smul`
    (`pathIntegralViaCover_neg_smul` —
    `∫(-(k•ω),γ) = (-k)•∫(ω,γ)`). This identity now at 6/6 layers
    all the way to the user-facing wrapper. Build green (8172 jobs).

## Earlier (now stale; kept for context only)
## Stale Live Status (2026-04-26 22:15 EDT)

- Active jobs (ours): 1/5; canary `09cd85dd` QUEUED ~4h.
- **Integrated this tick (local Claude-owned):**
  - NEW `Jacobian/Periods/PathIntegralViaCoverPickSmulSmul.lean`:
    Pick (unparameterised multi-chart) layer of `_smul_smul`
    (`pathIntegralViaCover_smul_smul`). This identity now at 6/6
    layers all the way to the user-facing wrapper. Build green
    (8171 jobs).

## Earlier (now stale; kept for context only)
## Stale Live Status (2026-04-26 22:09 EDT)

- Active jobs (ours): 1/5; canary `09cd85dd` QUEUED ~4h.
- **Integrated this tick (local Claude-owned):**
  - NEW `Jacobian/Periods/PathIntegralViaCoverPickNegEqNegOneSmul.lean`:
    Pick (unparameterised multi-chart) layer of `_neg_eq_neg_one_smul`
    (`pathIntegralViaCover_neg_eq_neg_one_smul`). This identity now
    at 6/6 layers all the way to the user-facing wrapper. Build
    green (8170 jobs).

## Earlier (now stale; kept for context only)
## Stale Live Status (2026-04-26 22:02 EDT)

- Active jobs (ours): 1/5; canary `09cd85dd` QUEUED ~3.5h.
- **Integrated this tick (local Claude-owned):**
  - NEW `Jacobian/Periods/PathIntegralViaCoverPickOneSmul.lean`:
    Pick (unparameterised multi-chart) layer of `_one_smul`
    (`pathIntegralViaCover_one_smul`). Identity now at 6/6 layers
    all the way to the user-facing `pathIntegralViaCover`
    wrapper. Build green (8169 jobs).

## Earlier (now stale; kept for context only)
## Stale Live Status (2026-04-26 21:51 EDT)

- Active jobs (ours): 1/5; canary `09cd85dd` QUEUED ~3.5h.
- **Integrated this tick (local Claude-owned):**
  - NEW `Jacobian/Periods/PathIntegralViaChartOneSmul.lean`:
    provisional via-chart layer of `_one_smul`
    (`pathIntegralViaChart_one_smul`). Identity now at 5/5 layers
    (in-chart provisional/corrected, via-chart provisional/corrected,
    cover). Build green (8168 jobs).

## Earlier (now stale; kept for context only)
## Stale Live Status (2026-04-26 21:43 EDT)

- Active jobs (ours): 1/5; canary `09cd85dd` QUEUED ~3.5h.
- **Integrated this tick (local Claude-owned):**
  - NEW `Jacobian/Periods/PathIntegralChartOneSmul.lean`:
    provisional in-chart layer of `_one_smul`
    (`pathIntegralInChart_one_smul`). Identity now at 4 layers.
    Build green (8167 jobs).

## Earlier (now stale; kept for context only)
## Stale Live Status (2026-04-26 21:36 EDT)

- Active jobs (ours): 1/5; canary `09cd85dd` QUEUED ~3.5h.
- **Integrated this tick (local Claude-owned):**
  - NEW `Jacobian/Periods/PathIntegralChartCorrectOneSmul.lean`:
    in-chart corrected layer of `_one_smul`. Identity now at 3
    layers. Build green (8166 jobs).

## Earlier (now stale; kept for context only)
## Stale Live Status (2026-04-26 21:31 EDT)

- Active jobs (ours): 1/5; canary `09cd85dd` QUEUED ~3h.
- **Integrated this tick (local Claude-owned):**
  - NEW `Jacobian/Periods/PathIntegralViaChartCorrectOneSmul.lean`:
    via-chart corrected layer of `_one_smul`. Build green
    (8165 jobs).

## Earlier (now stale; kept for context only)
## Stale Live Status (2026-04-26 21:26 EDT)

- Active jobs (ours): 1/5; canary `09cd85dd` QUEUED ~3h.
- **Integrated this tick (local Claude-owned):**
  - NEW `Jacobian/Periods/PathIntegralViaCoverOneSmul.lean`:
    `pathIntegralViaCoverWith_one_smul` — identity-scalar
    normalization. Build green (8164 jobs).

## Earlier (now stale; kept for context only)
## Stale Live Status (2026-04-26 21:21 EDT)

- Active jobs (ours): 1/5; canary `09cd85dd` QUEUED ~3h.
- **Integrated this tick (local Claude-owned):**
  - NEW `Jacobian/TraceDegree/PullbackFormsLinearMapApplyApplyLinear.lean`:
    five bundled-LinearMap-level vector-apply forms.
    Build green (2440 jobs).

## Earlier (now stale; kept for context only)
## Stale Live Status (2026-04-26 21:19 EDT)

- Active jobs (ours): 1/5; canary `09cd85dd` QUEUED ~3h.
- **Integrated this tick (local Claude-owned):**
  - NEW `Jacobian/TraceDegree/PullbackFunSimpApplyVec.lean`:
    five vector-apply (x v) forms of `pullbackFormsFun` linearity
    (zero, neg, add, sub, smul). Build green (2439 jobs).

## Earlier (now stale; kept for context only)
## Stale Live Status (2026-04-26 21:13 EDT)

- Active jobs (ours): 1/5; canary `09cd85dd` QUEUED ~3h.
- **Integrated this tick (local Claude-owned):**
  - NEW `Jacobian/Periods/ChartedFormLinearMapApplyApplyLinear.lean`:
    five bundled provisional vector-apply linearity forms.
    Build green (8163 jobs).

## Earlier (now stale; kept for context only)
## Stale Live Status (2026-04-26 21:10 EDT)

- Active jobs (ours): 1/5; canary `09cd85dd` QUEUED ~3h.
- **Integrated this tick (local Claude-owned):**
  - NEW `Jacobian/Periods/ChartedFormApplyApplyLinear.lean`: five
    vector-apply forms of provisional `chartedForm` linearity.
    Build green (8162 jobs).

## Earlier (now stale; kept for context only)
## Stale Live Status (2026-04-26 21:03 EDT)

- Active jobs (ours): 1/5; canary `09cd85dd` QUEUED ~3h.
- **Integrated this tick (local Claude-owned):**
  - NEW `Jacobian/Periods/ChartedFormPullbackLinearMapApplyApplyLinear.lean`:
    five bundled-LinearMap-level vector-apply (e v) forms.
    Build green (8161 jobs).

## Earlier (now stale; kept for context only)
## Stale Live Status (2026-04-26 20:59 EDT)

- Active jobs (ours): 1/5; canary `09cd85dd` QUEUED ~3h.
  Backend still asleep.
- **Integrated this tick (local Claude-owned):**
  - NEW `Jacobian/Periods/ChartedFormPullbackApplyApplyLinear.lean`:
    five vector-apply (e v) forms of `chartedFormPullback`
    linearity (zero, neg, add, sub, smul). Each is `rw` to the
    point-apply form + `rfl`. Build green (8160 jobs).

## Earlier (now stale; kept for context only)
## Stale Live Status (2026-04-26 20:51 EDT)

- **Integrated this tick (local Claude-owned):**
  - NEW `Jacobian/Periods/PathIntegralViaChartNegEqNegOneSmul.lean`:
    `pathIntegralViaChart_neg_eq_neg_one_smul` — provisional
    via-chart layer, completing the bridge identity across all
    five layers. Wired into Periods umbrella; build green
    (8159 jobs).
- The bridge identity now exists at four layers: in-chart
  provisional (this tick), in-chart corrected, via-chart
  corrected, cover-with.

## Earlier (now stale; kept for context only)
## Stale Live Status (2026-04-26 20:43 EDT)

- Active jobs (ours): 1/5; canary `09cd85dd` QUEUED ~2.5h+.
- **Integrated this tick (local Claude-owned):**
  - NEW `Jacobian/Periods/PathIntegralViaCoverNegEqNegOneSmul.lean`:
    cover-layer `_neg_eq_neg_one_smul`.
- **Submitted this tick:** none.

## Earlier (now stale; kept for context only)
## Stale Live Status (2026-04-26 20:37 EDT)

- Active jobs (ours): 0/5 (queue empty); backend still frozen.
- **Integrated this tick (local Claude-owned):**
  - NEW `Jacobian/Periods/PathIntegralChartCorrectSmulSymm.lean`:
    `pathIntegralInChartCorrect_smul_symm`. 1-line `rw` proof.
- **Submitted this tick:** none.

## Earlier (now stale; kept for context only)
## Stale Live Status (2026-04-26 15:43 EDT)

- Active jobs (ours): 0/5 (queue empty); backend still frozen.
- **Integrated this tick (local Claude-owned):**
  - NEW `Jacobian/Periods/PathIntegralViaChartCorrectSmulSymm.lean`:
    `pathIntegralViaChartCorrect_smul_symm`. 1-line `rw` proof.
- **Submitted this tick:** none.

## Earlier (now stale; kept for context only)
## Stale Live Status (2026-04-26 15:27 EDT)

- Active jobs (ours): 0/5 (queue empty).
- **Integrated this tick:** none. Brief refresh.
- **Submitted this tick:** none.

## Earlier (now stale; kept for context only)
## Stale Live Status (2026-04-26 15:24 EDT)

- Active jobs (ours): 0/5 (queue empty).
- **Integrated this tick:** none. Brief refresh.
- **Submitted this tick:** none.

## Earlier (now stale; kept for context only)
## Stale Live Status (2026-04-26 15:21 EDT)

- Active jobs (ours): 0/5 (queue empty).
- **Integrated this tick:** none. Brief refresh.
- **Submitted this tick:** none.

## Earlier (now stale; kept for context only)
## Stale Live Status (2026-04-26 15:18 EDT)

- Active jobs (ours): 0/5 (queue empty).
- **Integrated this tick:** none. Brief refresh — backend frozen ~11h.
- **Submitted this tick:** none.

## Earlier (now stale; kept for context only)
## Stale Live Status (2026-04-26 15:15 EDT)

- Active jobs (ours): 0/5 (queue empty).
- **Integrated this tick:** none. Brief refresh — backend frozen ~11h.
- **Submitted this tick:** none.

## Earlier (now stale; kept for context only)
## Stale Live Status (2026-04-26 15:13 EDT)

- Active jobs (ours): 0/5 (queue empty).
- **Integrated this tick:** none. Brief refresh — bounded-target
  hunt is well past diminishing returns. Today's session has
  added 30+ new files/lemmas; the substantive cover-symm milestone
  + 5+ corollaries are all merged. The bigger remaining items
  (well-definedness of pathIntegralViaCover, Pick-layer _symm,
  pullbackFormsFun_smooth, periodPairing Stokes step, decomposed
  TorusExample retry) all need careful multi-tick planning rather
  than single-tick attempts.
- **Submitted this tick:** none.

## Earlier (now stale; kept for context only)
## Stale Live Status (2026-04-26 15:06 EDT)

- Active jobs (ours): 0/5 (queue empty).
- **Integrated this tick (local Claude-owned, while Aristotle blocked):**
  - NEW `Jacobian/Periods/PathIntegralViaCoverSmulSymm.lean`:
    `pathIntegralViaCoverWith_smul_symm` — integrating `k • ω` along
    γ.symm equals `-(k • cover-with-integral)`. 1-line proof:
    `rw [_smul, _symm, smul_neg]`.
  - Wired into `Jacobian/Periods.lean` umbrella; build green
    (8051 jobs, 40s).
- **Submitted this tick:** none.

## Earlier (now stale; kept for context only)
## Stale Live Status (2026-04-26 15:03 EDT)

- Active jobs (ours): 0/5 (queue empty).
- **Integrated this tick:** none. Brief refresh.
- **Submitted this tick:** none.

## Earlier (now stale; kept for context only)
## Stale Live Status (2026-04-26 15:00 EDT)

- Active jobs (ours): 0/5 (queue empty).
- **Integrated this tick:** none. Brief consolidation refresh —
  wakeup fired 2 min after previous refresh.
- **Submitted this tick:** none.

## Earlier (now stale; kept for context only)
## Stale Live Status (2026-04-26 14:58 EDT)

- Active jobs (ours): 0/5 (queue empty).
- **Integrated this tick:** none. Brief consolidation refresh —
  wakeup fired 2 min after previous refresh.
- **Submitted this tick:** none.

## Earlier (now stale; kept for context only)
## Stale Live Status (2026-04-26 14:56 EDT)

- Active jobs (ours): 0/5 (queue empty).
- **Integrated this tick:** none. Refresh tick — diminishing returns
  on bounded-target hunt. The post-cover-symm session has added
  many useful but trivial corollaries:
  - `pathIntegralViaCoverWith_symm` (the substantive milestone)
  - `pathIntegralViaCoverWith_neg_form_eq_symm_path` (cover layer
    corollary)
  - `pathIntegralViaChartCorrect_neg_form_eq_symm_path`
    (corrected via-chart layer)
  - `pathIntegralInChartCorrect_neg_form_eq_symm_path`
    (corrected in-chart layer)
  - `pathIntegralInChart_neg_form_eq_symm_path` (provisional in-chart)
  - `pathIntegralViaChart_neg_form_eq_symm_path` (provisional via-chart)
- Bigger remaining items (well-definedness of `pathIntegralViaCover`,
  Pick-layer `_symm` lift, `pullbackFormsFun_smooth`, periodPairing
  Stokes step, decomposed TorusExample retry) all need careful
  multi-tick planning.
- **Submitted this tick:** none.

## Earlier (now stale; kept for context only)
## Stale Live Status (2026-04-26 14:52 EDT)

- Active jobs (ours): 0/5 (queue empty).
- **Integrated this tick (local Claude-owned, while Aristotle blocked):**
  - NEW `Jacobian/Periods/PathIntegralChartNegSymm.lean`:
    `pathIntegralInChart_neg_form_eq_symm_path` (provisional in-chart).
  - NEW `Jacobian/Periods/PathIntegralViaChartNegSymm.lean`:
    `pathIntegralViaChart_neg_form_eq_symm_path` (provisional from-X).
  - Both 1-line `rw [_neg, _symm]` proofs.
  - Both wired into `Jacobian/Periods.lean` umbrella; builds green.
- The `_neg_form_eq_symm_path` family is now complete at the
  provisional layer too (in-chart, via-chart). Together with the
  corrected versions (in-chart, via-chart, cover) from earlier
  ticks, the full set is in place.
- **Submitted this tick:** none.

## Earlier (now stale; kept for context only)
## Stale Live Status (2026-04-26 14:50 EDT)

- Active jobs (ours): 0/5 (queue empty).
- **Integrated this tick (local Claude-owned, while Aristotle blocked):**
  - NEW `Jacobian/Periods/PathIntegralChartCorrectNegSymm.lean`:
    `pathIntegralInChartCorrect_neg_form_eq_symm_path` —
    foundational in-chart `_neg`/`_symm` corollary. 1-line proof:
    `rw [pathIntegralInChartCorrect_neg, pathIntegralInChartCorrect_symm]`.
  - Wired into `Jacobian/Periods.lean` umbrella; build green
    (2673 jobs, 60s).
- The `_neg_form_eq_symm_path` family is now complete across three
  layers: in-chart (this tick), via-chart (yesterday), and cover (yesterday).
- **Submitted this tick:** none.

## Earlier (now stale; kept for context only)
## Stale Live Status (2026-04-26 14:47 EDT)

- Active jobs (ours): 0/5 (queue empty).
- **Integrated this tick (local Claude-owned, while Aristotle blocked):**
  - NEW `Jacobian/Periods/PathIntegralViaChartCorrectNegSymm.lean`:
    `pathIntegralViaChartCorrect_neg_form_eq_symm_path` — single-chart
    analogue of last tick's `pathIntegralViaCoverWith_neg_form_eq_symm_path`.
    1-line proof via `rw [_neg, _symm]`.
  - Wired into `Jacobian/Periods.lean` umbrella; build green
    (2679 jobs, 64s).
- **Submitted this tick:** none.

## Earlier (now stale; kept for context only)
## Stale Live Status (2026-04-26 14:36 EDT)

- Active jobs (ours): 0/5 (queue empty).
- **Integrated this tick (local Claude-owned, while Aristotle blocked):**
  - NEW `Jacobian/Periods/PathIntegralViaCoverNegSymm.lean`:
    `pathIntegralViaCoverWith_neg_form_eq_symm_path` — corollary
    combining `_neg` (form negation) with `_symm` (path reversal):
    integrating `-ω` along `γ` equals integrating `ω` along `γ.symm`
    (with re-indexed cover). Both equal `-cover-with-integral`.
  - Proof: 1 line `rw [pathIntegralViaCoverWith_neg,
    pathIntegralViaCoverWith_symm]`.
  - Wired into `Jacobian/Periods.lean` umbrella; build green
    (8051 jobs, 178s).
- This is the discrete analogue of the classical
  `∫ -ω on γ = ∫ ω on -γ` from complex analysis.
- **Submitted this tick:** none.

## Earlier (now stale; kept for context only)
## Stale Live Status (2026-04-26 14:33 EDT)

- Active jobs (ours): 0/5 (queue empty).
- **Integrated this tick:** none. Wakeup fired 3 min after the
  previous refresh tick. Backend still frozen.
- **Submitted this tick:** none.

## Earlier (now stale; kept for context only)
## Stale Live Status (2026-04-26 14:30 EDT)

- Active jobs (ours): 0/5 (queue empty).
- **Integrated this tick:** none. Just timestamp refresh —
  wakeup fired 2 min after the previous refresh tick.
- **Submitted this tick:** none.

## Earlier (now stale; kept for context only)
## Stale Live Status (2026-04-26 14:28 EDT)

- Active jobs (ours): 0/5 (queue empty).
- **Integrated this tick:** none. Refresh-only after the cover-symm
  milestone landed at 14:05.
- **Substantive work remaining (long-tail), in rough order of fit:**
  1. Lift `pathIntegralViaCoverWith_symm` to the unparameterised
     `pathIntegralViaCover` (Pick) layer. Needs well-definedness of
     `pathIntegralViaCover` first (different `Classical.choose`
     partitions for γ vs γ.symm).
  2. Well-definedness of `pathIntegralViaCover` itself —
     independence from the picked partition. Substantive.
  3. `pullbackFormsFun_smooth` (Queue G) — the ContMDiff step
     for upgrading `pullbackFormsFun` to `HolomorphicOneForm E X`.
  4. Decomposed TorusExample retry around the
     `Bundle.continuousLinearMap` constant-section roadblock.
- These are all multi-tick jobs that benefit from careful planning.
  Next ticks will pick one and outline a strategy.
- **Submitted this tick:** none.

## Earlier (now stale; kept for context only)
## Stale Live Status (2026-04-26 14:05 EDT)

- Active jobs (ours): 0/5 (queue empty).
- **Integrated this tick (local Claude-owned, while Aristotle blocked):**
  **🎉 The full `pathIntegralViaCoverWith_symm` theorem is proved
  and compiles cleanly!**
  - NEW `Jacobian/Periods/PathIntegralViaCoverSymm.lean`:
    ```
    theorem pathIntegralViaCoverWith_symm
        (ω) (γ) (n) (hn) (pickChart) (hcov) :
      pathIntegralViaCoverWith ω γ.symm n hn (pickChart ∘ Fin.rev)
          (cover_symm_of_cover γ n hn pickChart hcov) =
        - pathIntegralViaCoverWith ω γ n hn pickChart hcov
    ```
  - Proof structure:
    1. `unfold pathIntegralViaCoverWith` to expose the Finset.sum
    2. `← Finset.sum_neg_distrib` to pull negation out
    3. `Fintype.sum_equiv Fin.revPerm` to set up the bijection
    4. `simp only [Fin.revPerm_apply]` to rewrite to Fin.rev
    5. Per-segment `pathIntegralViaChartCorrect_symm_subpath_divFinIcc`
       with `range_subpath_sigma_subset_source` filling in the
       σ-form range hypothesis
    6. `congr 1` to drop the negation
    7. `pathIntegralViaChartCorrect_eq_of_heq` (HEq path congruence)
       with σ-to-arith endpoint equalities (e1, e2 via Subtype.ext +
       coe_symm_eq + divFinIcc_val + Fin.val_rev + Nat.cast_sub +
       field_simp + omega for the Nat sub identity)
    8. `rw [e1, e2]` closes the HEq.
  - Build green (8046 jobs, 133s).
- This is the substantive cover-symm theorem that's been the
  focus of the last ~10 ticks. All 8 prerequisite helper lemmas
  combine cleanly.
- **Submitted this tick:** none.

## Earlier (now stale; kept for context only)
## Stale Live Status (2026-04-26 13:43 EDT)

- Active jobs (ours): 0/5 (queue empty).
- **Integrated this tick (local Claude-owned, while Aristotle blocked):**
  - NEW `Jacobian/Periods/PathPartitionCoverSigmaForm.lean`:
    `range_subpath_sigma_subset_source` — constructs the range
    hypothesis for the σ-form γ-segment from `hcov`. Mostly
    arithmetic: σ((i+1)/n) ≤ σ(i/n) iff (i+1)/n ≥ i/n (true);
    the σ-form parameter range coincides with γ's segment-(Fin.rev i)
    parameter range. Proof uses `symm_le_symm`, `divFinIcc_le_succ`,
    `Set.uIcc_of_le`, `coe_symm_eq`, `Fin.val_rev`, `Nat.cast_sub`,
    `div_le_iff₀`/`le_div_iff₀`, `mul_le_mul_of_nonneg_right`,
    `div_mul_cancel₀`, and `linarith` to close after multiplying
    through. Hit several iterative debug rounds (Real-vs-unitInterval
    coercion, Nat.cast_sub firing).
  - Build green (`lake build Jacobian.Periods.PathPartitionCoverSigmaForm`
    → 8029 jobs, 128s).
- This unblocks the cover-symm proof: with both `cover_symm_of_cover`
  (handles γ.symm side) and `range_subpath_sigma_subset_source`
  (handles σ-form γ side), all range hypotheses for the
  per-segment sign-flip rewrite are now derivable from `hcov`.
- **Submitted this tick:** none.

## Earlier (now stale; kept for context only)
## Stale Live Status (2026-04-26 13:27 EDT)

- Active jobs (ours): 0/5 (queue empty).
- **Integrated this tick (local Claude-owned, while Aristotle blocked):**
  - Extended `Jacobian/Periods/PathIntegralCongr.lean` with
    `pathIntegralViaChartCorrect_eq_of_heq` — HEq version of the
    path-congruence lemma, taking `ha : a = a'`, `hb : b = b'`,
    `hγ : HEq γ γ'`. Proof: `subst ha; subst hb; cases hγ; rfl`.
    Useful when path endpoint terms are propositionally equal but
    not definitionally.
  - Build green (2676 jobs, 44s).
- **Cover-symm progress:**
  - Found the right re-indexing API: `Fintype.sum_equiv` with
    `Fin.revPerm : Equiv.Perm (Fin n)` works as the bijection.
  - Proof advances past `Fintype.sum_equiv` and `per-segment _symm`,
    leaving two remaining hurdles:
    1. Need `Fin.revPerm_apply` simp to identify `Fin.revPerm i`
       with `Fin.rev i` after rewrites.
    2. Need an explicit cover proof for the σ-form path (i.e.,
       construct the range hypothesis from `hcov` at index `Fin.rev i`,
       since the σ-form path equals γ's (Fin.rev i)-th segment).
  - Will tackle these in the next tick.
- **Submitted this tick:** none.

## Earlier (now stale; kept for context only)
## Stale Live Status (2026-04-26 13:20 EDT)

- Active jobs (ours): 0/5 (queue empty).
- **Integrated this tick:** none. Attempted the full
  `pathIntegralViaCoverWith_symm` using `Finset.sum_nbij'` with
  Fin.rev as the bijection, but hit a universe-constraint failure
  on the bijection signature. The proof structure is sound (all
  helper lemmas land cleanly when applied per-segment), but the
  Finset re-indexing API needs more careful selection — likely
  `Fintype.sum_equiv` with `Fin.revPerm` or similar — beyond
  what fits in one tick. Failed attempt deleted.
- **Submitted this tick:** none.

## Earlier (now stale; kept for context only)
## Stale Live Status (2026-04-26 13:17 EDT)

- Active jobs (ours): 0/5 (queue empty).
- **Integrated this tick:** none. Spent the tick planning the
  full `pathIntegralViaCoverWith_symm` Finset.sum_bij' re-indexing
  proof. The remaining piece needs:
  1. Unfold both sides; pull `-∑ = ∑ -` via `Finset.sum_neg_distrib`
  2. `Finset.sum_bij'` with `Fin.rev` (involution; rev_rev = id)
  3. Per-term: apply `pathIntegralViaChartCorrect_symm_subpath_divFinIcc`
     (the σ-form helper landed last tick)
  4. Bridge σ-form-path to arith-form-path via `divFinIcc_symm`
     (twice) + `pathIntegralViaChartCorrect_eq_of_path_eq` (the
     congruence helper) to handle the Path-type mismatch
  5. Use `Fin.val_rev` to convert `n - 1 - i.val` to `(Fin.rev i).val`
  This is a substantive multi-step proof; deferred to a future
  tick when more time is available. All 5 helper lemmas are
  in place.
- **Submitted this tick:** none.

## Earlier (now stale; kept for context only)
## Stale Live Status (2026-04-26 13:11 EDT)

- Active jobs (ours): 0/5 (queue empty).
- **Integrated this tick (local Claude-owned, while Aristotle blocked):**
  - NEW `Jacobian/Periods/PathIntegralCongr.lean`: path-congruence
    helpers `pathIntegralViaChartCorrect_eq_of_path_eq` and the
    provisional analogue `pathIntegralViaChart_eq_of_path_eq`.
    Both proved by `subst hγ; rfl` — relies on proof irrelevance
    in `Prop` to handle the range-hypothesis arguments under path
    equality. Resolves last tick's dependent-type rewrite blocker.
  - NEW `Jacobian/Periods/PathIntegralSegmentSymm.lean`: now
    completes the per-segment sign-flip lemma
    `pathIntegralViaChartCorrect_symm_subpath_divFinIcc`. Proof
    pattern: `set σpath`, derive `eq : γ.symm.subpath ... = σpath.symm`
    from `path_symm_subpath_divFinIcc`, transport `h_symm` along
    `eq` to get `h_symm'`, use `pathIntegralViaChartCorrect_eq_of_path_eq`
    to rewrite the LHS, and finish with `pathIntegralViaChartCorrect_symm`.
  - Both wired into `Jacobian/Periods.lean` umbrella; build green
    (2762 jobs, 51s).
- All path-side helpers for `pathIntegralViaCoverWith_symm` are
  now in place. Remaining: the Finset.sum_bij Fin.rev re-indexing
  + putting the full theorem together. (Will need `cover_symm_of_cover`
  + `pathIntegralViaChartCorrect_symm_subpath_divFinIcc` per
  segment + Finset re-index by Fin.rev + `divFinIcc_symm` for
  the σ-to-arithmetic conversion.)
- **Submitted this tick:** none.

## Earlier (now stale; kept for context only)
## Stale Live Status (2026-04-26 13:02 EDT)

- Active jobs (ours): 0/5 (queue empty).
- **Integrated this tick (local Claude-owned, while Aristotle blocked):**
  - NEW `Jacobian/Periods/PathIntegralChartApply.lean`:
    `pathIntegralInChart_apply` — definitional unfolding to
    `curveIntegral (chartedForm c ω) γ` (rfl). Mirrors corrected
    layer's `PathIntegralChartCorrectApply`.
  - NEW `Jacobian/Periods/PathIntegralViaChartApply.lean`:
    `pathIntegralViaChart_apply` — definitional unfolding to
    `pathIntegralInChart c ω (chartLift c γ h)` (rfl). Mirrors
    corrected layer's `PathIntegralViaChartCorrectApply`.
  - Both wired into `Jacobian/Periods.lean` umbrella; build green
    (2672 jobs, 57s).
- **Abandoned attempt:** the more substantive
  `pathIntegralViaChartCorrect_symm_subpath_divFinIcc` per-segment
  symm lemma. Hit a dependent-type rewrite issue: the range
  hypothesis `h_symm : range (γ.symm.subpath ...) ⊆ c.source` has
  type that depends on the path argument, so rewriting the path
  via `path_symm_subpath_divFinIcc` requires also transporting
  the hypothesis. Lean's `rw` doesn't motive-compute through this
  cleanly; needs explicit `Eq.mpr`/`cast`/`convert` handling,
  beyond what fits in one tick. Marked for later.
- **Submitted this tick:** none.

## Earlier (now stale; kept for context only)
## Stale Live Status (2026-04-26 12:40 EDT)

- Active jobs (ours): 0/5 (queue empty).
- **Integrated this tick (local Claude-owned, while Aristotle blocked):**
  - NEW `Jacobian/Periods/PathPartitionCoverSymm.lean`: substantive
    helper `cover_symm_of_cover` — given an n-segment cover of γ
    by `pickChart`, produces a cover of γ.symm by
    `pickChart ∘ Fin.rev`. The intuition: segment i of γ.symm
    (running through γ(σ t)) lies in chart `pickChart (n-1-i) =
    pickChart (Fin.rev i)`.
  - Proof: refine apply hcov at index `Fin.rev i` and time `σ t`;
    discharge the two boundary inequalities via `Fin.val_rev`,
    `coe_symm_eq`, `Nat.cast_sub i.isLt`, `div_le_iff₀`/`le_div_iff₀`,
    `push_cast`, and linarith. Hit and fixed two initial linarith
    failures by stripping divisions out of `hlo`/`hhi` before the
    refine.
  - Wired into `Jacobian/Periods.lean` umbrella; build green
    (8028 jobs, 123s).
- This is the fifth (and most substantive) helper toward
  `pathIntegralViaCoverWith_symm`. With this in hand, the full
  cover-symm proof reduces to a Finset.sum re-indexing under
  Fin.rev plus the per-segment sign flip from
  `pathIntegralInChartCorrect_symm` and the segment reflection
  from `path_symm_subpath_divFinIcc`.
- **Submitted this tick:** none.

## Earlier (now stale; kept for context only)
## Stale Live Status (2026-04-26 12:36 EDT)

- Active jobs (ours): 0/5 (queue empty).
- **Integrated this tick (local Claude-owned, while Aristotle blocked):**
  - NEW `Jacobian/Periods/ChartedFormLinearMapApplyLinear.lean`:
    five pointwise apply-form simp lemmas at the bundled provisional
    LinearMap layer:
    `chartedFormLinearMap_{zero,neg,add,sub,smul}_apply`. Each
    delegates through `chartedFormLinearMap_apply_at` (the rfl-
    bridge to the unbundled provisional form) to the apply-form
    bundle in `ChartedFormApplyLinear.lean`.
  - Mirror of corrected layer's
    `ChartedFormPullbackLinearMapApplyLinear`.
  - Wired into `Jacobian/Periods.lean` umbrella; build green
    (2417 jobs, 46s).
- The provisional `chartedForm` API (function-level + bundled
  LinearMap + apply forms + curve-integrability propagation +
  conditional add/sub/refl/symm) is now fully complete and
  parallel to the corrected layer.
- **Submitted this tick:** none.

## Earlier (now stale; kept for context only)
## Stale Live Status (2026-04-26 12:33 EDT)

- Active jobs (ours): 0/5 (queue empty).
- **Integrated this tick (local Claude-owned, while Aristotle blocked):**
  - NEW `Jacobian/Periods/ChartedFormLinearMapApply.lean`:
    - `chartedFormLinearMap_apply_at : LinearMap c ω e = chartedForm c ω e` (rfl)
    - `chartedFormLinearMap_apply_vec : LinearMap c ω e v = ω.toFun (c.symm e) v` (rfl)
    Note that unlike the corrected layer, the provisional version
    drops the chart derivative — fine for translation-transition
    charts only.
  - Mirror of corrected layer's `ChartedFormPullbackLinearMapApply`.
  - Wired into `Jacobian/Periods.lean` umbrella; build green
    (2412 jobs, 20s).
- **Submitted this tick:** none.

## Earlier (now stale; kept for context only)
## Stale Live Status (2026-04-26 12:30 EDT)

- Active jobs (ours): 0/5 (queue empty).
- **Integrated this tick (local Claude-owned, while Aristotle blocked):**
  - NEW `Jacobian/Periods/ChartedFormLinearMapSimp.lean`:
    `chartedFormLinearMap_zero`, `_neg`, `_add`, `_sub` (all
    1-line term proofs via `LinearMap.map_*`).
  - NEW `Jacobian/Periods/ChartedFormLinearMapSmul.lean`:
    `chartedFormLinearMap_smul` (1-line `(chartedFormLinearMap c).map_smul k ω`).
  - Mirror of corrected layer's `ChartedFormPullbackLinearMapSimp`
    and `ChartedFormPullbackLinearMapSmul`.
  - Both wired into `Jacobian/Periods.lean` umbrella; build green
    (2413 jobs, 27s each).
- **Submitted this tick:** none.

## Earlier (now stale; kept for context only)
## Stale Live Status (2026-04-26 12:27 EDT)

- Active jobs (ours): 0/5 (queue empty).
- **Integrated this tick (local Claude-owned, while Aristotle blocked):**
  - NEW `Jacobian/Periods/ChartedFormLinearMap.lean`: bundles the
    provisional `chartedForm c` as a `HolomorphicOneForm E X →ₗ[ℂ]
    (E → E →L[ℂ] ℂ)`. Uses the existing `chartedForm_add` and
    `chartedForm_smul` for `map_add'` and `map_smul'`. The sanity
    `_apply` simp is `rfl`. Mirror of corrected layer's
    `ChartedFormPullbackLinearMap`.
  - Wired into `Jacobian/Periods.lean` umbrella; build green
    (2411 jobs, 22s).
- **Submitted this tick:** none.

## Earlier (now stale; kept for context only)
## Stale Live Status (2026-04-26 12:24 EDT)

- Active jobs (ours): 0/5 (queue empty).
- **Integrated this tick (local Claude-owned, while Aristotle blocked):**
  - NEW `Jacobian/Periods/ChartedFormCurveIntegrable.lean`:
    five conditional curve-integrability propagation lemmas at
    the provisional layer:
    - `chartedForm_zero_curveIntegrable` (unconditional)
    - `chartedForm_neg_curveIntegrable` (conditional on h)
    - `chartedForm_smul_curveIntegrable` (conditional on h)
    - `chartedForm_add_curveIntegrable` (conditional on hω, hη)
    - `chartedForm_sub_curveIntegrable` (conditional on hω, hη)
    Each is 2 lines: rewrite the function-level simp + apply
    `CurveIntegrable.{zero,neg,smul,add,sub}`. Mirrors
    `ChartedFormPullbackCurveIntegrable` at the corrected layer.
  - Wired into `Jacobian/Periods.lean` umbrella; build green
    (2672 jobs, 25s).
- **Submitted this tick:** none.

## Earlier (now stale; kept for context only)
## Stale Live Status (2026-04-26 12:21 EDT)

- Active jobs (ours): 0/5 (queue empty).
- **Integrated this tick (local Claude-owned, while Aristotle blocked):**
  - NEW `Jacobian/Periods/ChartedFormApplyLinear.lean`: five
    pointwise apply-form simp lemmas at the provisional layer:
    `chartedForm_{zero,neg,add,sub,smul}_apply`. Each rewrites the
    function-level simp lemma and closes by `rfl` (2 lines).
    Mirrors `ChartedFormPullbackApplyLinear` at the corrected layer.
  - Wired into `Jacobian/Periods.lean` umbrella; build green
    (2412 jobs, 22s).
- **Submitted this tick:** none.

## Earlier (now stale; kept for context only)
## Stale Live Status (2026-04-26 12:19 EDT)

- Active jobs (ours): 0/5 (queue empty).
- **Integrated this tick (local Claude-owned, while Aristotle blocked):**
  - NEW `Jacobian/Periods/PathIntegralViaChartAdd.lean`:
    `pathIntegralViaChart_add_of_curveIntegrable` — 2-line `unfold;
    exact` delegating through the in-chart version landed last tick.
  - NEW `Jacobian/Periods/PathIntegralViaChartSub.lean`:
    `pathIntegralViaChart_sub_of_curveIntegrable` — same shape.
  - Both wired into `Jacobian/Periods.lean` umbrella; builds green
    (2676 jobs, 24s each).
- Provisional from-X linearity ladder is now complete and parallel
  to the corrected from-X layer.
- **Submitted this tick:** none.

## Earlier (now stale; kept for context only)
## Stale Live Status (2026-04-26 12:15 EDT)

- Active jobs (ours): 0/5 (queue empty).
- **Integrated this tick (local Claude-owned, while Aristotle blocked):**
  - NEW `Jacobian/Periods/ChartedFormSub.lean`: `chartedForm_sub`
    (provisional layer) — 1-line `rw [sub_eq_add_neg, sub_eq_add_neg,
    chartedForm_add, chartedForm_neg]`.
  - NEW `Jacobian/Periods/PathIntegralChartAdd.lean`:
    `pathIntegralInChart_add_of_curveIntegrable` — conditional
    addition linearity at the provisional in-chart layer
    (`curveIntegral_add` needs CurveIntegrable). Mirrors corrected.
  - NEW `Jacobian/Periods/PathIntegralChartSub.lean`:
    `pathIntegralInChart_sub_of_curveIntegrable` — same shape.
  - All three wired into `Jacobian/Periods.lean` umbrella; builds
    green (2672 jobs, 21-22s each).
- Provisional in-chart linearity ladder is now complete to match
  the corrected layer:
  zero ✓, neg ✓, smul ✓, refl ✓, symm ✓, add (cond) ✓, sub (cond) ✓.
- **Submitted this tick:** none.

## Earlier (now stale; kept for context only)
## Stale Live Status (2026-04-26 12:10 EDT)

- Active jobs (ours): 0/5 (queue empty).
- **Integrated this tick (local Claude-owned, while Aristotle blocked):**
  - NEW `Jacobian/Periods/PathIntegralChartLinear.lean`:
    `pathIntegralInChart_neg` and `pathIntegralInChart_smul` at
    the provisional in-chart layer (the `_zero` already lives in
    `PathIntegralChart.lean`). Three-line proofs each: `show ...
    rw [chartedForm_neg, curveIntegral_neg]` and the smul analogue.
    Mirror of `PathIntegralChartCorrect{Linear,Smul}` at the
    corrected layer.
  - Refactored `Jacobian/Periods/PathIntegralViaChartLinear.lean`
    (the from-X version landed at 11:38) to delegate through the
    new in-chart lemmas: `unfold pathIntegralViaChart; exact
    pathIntegralInChart_{neg,smul} c ω _` (2 lines per lemma,
    down from 3). Cleaner because the chartLift application is now
    just an underscore.
  - Build green: `lake build Jacobian.Periods.PathIntegralChartLinear`
    → 2672/2672 (58s); refactored ViaChart version → 2674/2674 (51s).
- **Submitted this tick:** none.

## Earlier (now stale; kept for context only)
## Stale Live Status (2026-04-26 12:05 EDT)

- Active jobs (ours): 0/5 (queue empty).
- **Integrated this tick (local Claude-owned, while Aristotle blocked):**
  - Refactored `pathIntegralViaChartCorrect_symm` (in
    `PathIntegralViaChartCorrect.lean`) and `pathIntegralViaChart_symm`
    (in `PathLiftSimp.lean`) to use the new `chartLift_symm` lemma
    landed last tick. Each proof shrinks from a 5-line inline
    `Path.ext rfl` setup to a 3-line `unfold; rw; exact` chain.
  - Build green: `lake build Jacobian.Periods.PathIntegralViaChartCorrect`
    → 2675/2675 (47s); `Jacobian.Periods.PathLiftSimp` →
    2672/2672 (54s).
- Cumulative session: 7 new local helpers/refactors today
  (4 toolkit lemmas + 3 proof-cleanup refactors), total
  net negative line count vs the original inline proofs.
- **Submitted this tick:** none.

## Earlier (now stale; kept for context only)
## Stale Live Status (2026-04-26 12:02 EDT)

- Active jobs (ours): 0/5 (queue empty).
- **Integrated this tick (local Claude-owned, while Aristotle blocked):**
  - `Jacobian/Periods/ChartLiftSymm.lean` — new file with
    `chartLift_symm : chartLift c γ.symm h' = (chartLift c γ h).symm`.
    Proof is `unfold chartLift; exact Path.ext rfl` — both sides
    expand to `c ∘ γ ∘ σ`, the σ just gets factored out at
    different points in the bracketing. Promotes the inline
    `Path.ext rfl` from `pathIntegralViaChartCorrect_symm`
    (PathLiftSimp.lean) to a reusable named lemma.
  - Wired into `Jacobian/Periods.lean` umbrella; build green
    (2671 jobs, 51s).
- This is the fourth helper toward `pathIntegralViaCoverWith_symm`.
  Status of toolkit:
  1. `divFinIcc_symm` ✓ (boundary point reflection)
  2. `path_symm_subpath_eq` ✓ (subpath through symm)
  3. `path_symm_subpath_divFinIcc` ✓ (segment-level reflection)
  4. `chartLift_symm` ✓ (chartLift commutes with symm) — NEW
  Still needed: Fin.rev re-indexing of the Finset sum (the easy
  combinatorial step).
- **Submitted this tick:** none.

## Earlier (now stale; kept for context only)
## Stale Live Status (2026-04-26 11:58 EDT)

- Active jobs (ours): 0/5 (queue empty).
- **Integrated this tick (local Claude-owned, while Aristotle blocked):**
  - `Jacobian/Periods/PathPartitionSymm.lean` — new file with
    `path_symm_subpath_divFinIcc`:
    ```
    γ.symm.subpath (i/n) ((i+1)/n)
      = (γ.subpath (σ ((i+1)/n)) (σ (i/n))).symm
    ```
    First attempt expanded σ via `divFinIcc_symm` inside the type
    and hit a type mismatch (Path endpoints involve `γ.symm s` vs
    `γ ((n-i)/n)`, which are equal propositionally via
    `divFinIcc_symm` but not definitionally). Fixed by keeping σ
    in the statement so endpoints unify via `γ.symm s = γ (σ s)`
    (which IS rfl). Proof reduces to a 2-line rw chain.
  - Wired into `Jacobian/Periods.lean` umbrella; build green
    (`lake build Jacobian.Periods.PathPartitionSymm` →
    1582 jobs, 31s).
- This is the third helper toward `pathIntegralViaCoverWith_symm`,
  combining the previous `divFinIcc_symm` and `path_symm_subpath_eq`
  into one usable segment-level identity.
- **Submitted this tick:** none.

## Earlier (now stale; kept for context only)
## Stale Live Status (2026-04-26 11:53 EDT)

- Active jobs (ours): 0/5 (queue empty).
- **Integrated this tick (local Claude-owned, while Aristotle blocked):**
  - `Jacobian/Periods/PathSymmSubpath.lean` — new file with
    `path_symm_subpath_eq : γ.symm.subpath s t = γ.subpath (σ s) (σ t)`.
    Proof: `Path.ext + funext + show + congr + Subtype.ext + ring`,
    discharging the underlying real identity
    `1 - ((1-r)s + rt) = (1-r)(1-s) + r(1-t)`.
  - Wired into `Jacobian/Periods.lean` umbrella; build green
    (`lake build Jacobian.Periods.PathSymmSubpath` → 1580 jobs, 45s).
- This is the second prerequisite helper for the eventual
  `pathIntegralViaCoverWith_symm` proof, after `divFinIcc_symm`
  (last tick): with both lemmas in hand, the partition-by-partition
  re-indexing for γ.symm reduces to `Fin.rev` re-indexing of the
  Finset sum.
- **Submitted this tick:** none.

## Earlier (now stale; kept for context only)
## Stale Live Status (2026-04-26 11:49 EDT)

- Active jobs (ours): 0/5 (queue empty; 3 cancelled today during
  the ~7.5h backend freeze).
- **Integrated this tick (local Claude-owned, while Aristotle blocked):**
  - `Jacobian/Periods/DivFinIcc.lean`: added `divFinIcc_symm`
    (`σ (divFinIcc n hn i hi) = divFinIcc n hn (n - i) ...`),
    the partition-point reflection identity. Proof in 4 lines:
    `apply Subtype.ext; show 1 - (i:ℝ)/n = ((n-i:ℕ):ℝ)/n;
    rw [Nat.cast_sub hi, sub_div, div_self _]`. This is a
    prerequisite helper for `pathIntegralViaCoverWith_symm`
    (the partition reflects under `γ.symm`, so segment `i` of
    `γ.symm` lives at `[σ((i+1)/n), σ(i/n)] = [(n-i-1)/n, (n-i)/n]`).
  - Build green (`lake build Jacobian.Periods.DivFinIcc` →
    1361 jobs, 32s).
- **Submitted this tick:** none.
- Continuing to set up substantive Claude-owned proof work
  toward `pathIntegralViaCoverWith_symm` while backend frozen.

## Earlier (now stale; kept for context only)
## Stale Live Status (2026-04-26 11:45 EDT)

- Active jobs (ours): 0/5 (queue empty; 3 cancelled today during
  the ~7.5h backend freeze).
- **Integrated this tick (local Claude-owned, while Aristotle blocked):**
  - Refactored `pathIntegralInChartCorrect_neg` (in
    `PathIntegralChartCorrectLinear.lean`) from a 22-line proof
    to a 7-line proof: replaced inline `funext +
    ContinuousLinearMap.neg_comp` chain with `rw
    [chartedFormPullback_neg, curveIntegral_neg]` using the modern
    simp lemma I added at 10:39.
  - Same refactor for `pathIntegralInChartCorrect_smul` in
    `PathIntegralChartCorrectSmul.lean` (from 20 lines to 7).
  - Net change: -29 lines of dead boilerplate; same theorem
    signatures and statements. Build green
    (`lake build Periods.PathIntegralChartCorrectLinear
    Periods.PathIntegralChartCorrectSmul` → 2673 jobs, 61s).
- **Submitted this tick:** none.
- Queue is empty. Next: pick up substantive Claude-owned work
  (e.g. `pathIntegralViaCoverWith_symm`, well-definedness of
  `pathIntegralViaCover`, or decomposed TorusExample retry).

## Earlier (now stale; kept for context only)
## Stale Live Status (2026-04-26 11:42 EDT)

- Active jobs (ours): 0/5. **In-flight queue fully drained
  locally** during the ~7.5h backend freeze (3 cancelled jobs
  today: f8faacda, bf7d62c4, 82687eb7 — all proved in-house).
- **Integrated this tick (local Claude-owned, while Aristotle blocked):**
  - `Jacobian/TraceDegree/PullbackFunSimpApply.lean` — three
    pointwise apply-form simp lemmas
    `pullbackFormsFun_{zero,neg,smul}_apply`. Proved by
    `rw [pullbackFormsFun_{zero,neg,smul}]; rfl` (2 lines each).
  - **In-flight job `82687eb7` cancelled** after local landing.
  - Wired into `Jacobian/TraceDegree.lean` umbrella; module builds
    green (2410 jobs, 50s).
- **Submitted this tick:** none.
- Queue is now empty. Next ticks need to either (a) wait for backend
  recovery, (b) prepare and submit a new substantive packet, or
  (c) continue local Claude-owned proof work on bigger items
  (e.g. pathIntegralViaCoverWith_symm, well-definedness of
  pathIntegralViaCover, decomposed TorusExample retry).

## Earlier (now stale; kept for context only)
## Stale Live Status (2026-04-26 11:38 EDT)

- Active jobs (ours): 1/5. One QUEUED ~7.5h
  (`82687eb7` PullbackFunSimpApply) — backend stalled since
  ~04:09 EDT, no jobs moving on any project.
- **Integrated this tick (local Claude-owned, while Aristotle blocked):**
  - `Jacobian/Periods/PathIntegralViaChartLinear.lean` —
    `pathIntegralViaChart_neg` and `pathIntegralViaChart_smul` for
    the provisional from-X integral. Proof per lemma:
    `show curveIntegral (chartedForm c _) (chartLift c γ h) = ...; rw [chartedForm_neg/smul, curveIntegral_neg/smul]`
    (3 lines).
  - **In-flight job `bf7d62c4` cancelled** after local landing
    (was QUEUED ~7.5h with no progress).
  - Wired into `Jacobian/Periods.lean` umbrella; module builds
    green (2673 jobs, 55s).
- **Submitted this tick:** none.
- Continuing to drain in-flight queue locally while backend frozen.

## Earlier (now stale; kept for context only)
## Stale Live Status (2026-04-26 11:34 EDT)

- Active jobs (ours): 2/5. Two QUEUED ~7.5h — backend stalled
  since ~04:09 EDT, no jobs moving on any project.
- **Integrated this tick (local Claude-owned, while Aristotle blocked):**
  - `Jacobian/Periods/ChartLiftBoundary.lean` — `chartLift_zero`
    and `chartLift_one` boundary-value simp lemmas. Proved by
    `rw [chartLift_apply, γ.source]` and `rw [chartLift_apply, γ.target]`
    respectively (2 lines each).
  - **In-flight job `f8faacda` cancelled** after local landing
    (was QUEUED ~7.5h with no progress).
  - Wired into `Jacobian/Periods.lean` umbrella; module builds
    green (2672 jobs, 38s).
- **Submitted this tick:** none.
- Per user feedback: when backend is frozen, do substantive local
  proof work each tick instead of refresh-only commits.

## Earlier (now stale; kept for context only)
## Stale Live Status (2026-04-26 11:33 EDT)

- Active jobs (ours): 3/5. All three QUEUED ~7h — backend stalled
  since ~04:09 EDT, no jobs moving on any project.
- **Integrated this tick:** none. Last lemma-add was 10:54
  (PullbackFormsLinearMapApplyLinear).
- **Submitted this tick:** none (backlog still blocking).
- Session has added 17 small apply-form simp lemmas over ~25 min
  across 4 new files. Trivial-apply category exhausted; further
  work needs substantive lemmas best delegated to Aristotle once
  backend recovers.

## Earlier (now stale; kept for context only)
## Stale Live Status (2026-04-26 11:06 EDT)

- Active jobs (ours): 3/5. All three QUEUED ~7h — backend stalled
  since ~04:09 EDT, no jobs moving on any project.
- **Integrated this tick:** none. Last lemma-add was 10:54
  (PullbackFormsLinearMapApplyLinear).
- **Submitted this tick:** none (backlog still blocking).
- Session has added 17 small apply-form simp lemmas over ~25 min
  across 4 new files. Trivial-apply category exhausted; further
  work needs substantive lemmas best delegated to Aristotle once
  backend recovers.

## Earlier (now stale; kept for context only)
## Stale Live Status (2026-04-26 11:03 EDT)

- Active jobs (ours): 3/5. All three QUEUED ~6.9h — backend stalled
  since ~04:09 EDT, no jobs moving on any project.
- **Integrated this tick:** none. Last lemma-add was 10:54
  (PullbackFormsLinearMapApplyLinear).
- **Submitted this tick:** none (backlog still blocking).
- Session has added 17 small apply-form simp lemmas over the last
  ~25 minutes across 4 new files. Trivial-apply category
  exhausted; further work needs substantive lemmas best delegated
  to Aristotle once backend recovers.

## Earlier (now stale; kept for context only)
## Stale Live Status (2026-04-26 11:00 EDT)

- Active jobs (ours): 3/5. All three QUEUED ~6.8h — backend stalled
  since ~04:09 EDT, no jobs moving on any project.
- **Integrated this tick:** none. Last lemma-add was 10:54
  (PullbackFormsLinearMapApplyLinear); this is a 1-minute-after
  refresh tick.
- **Submitted this tick:** none (backlog still blocking).
- Session has added 17 small apply-form simp lemmas over the last
  ~25 minutes (ChartedFormPullbackApplyLinear,
  ChartedFormPullbackLinearMapApplyLinear, PullbackFunAddSubApply,
  PullbackFormsLinearMapApplyLinear). Trivial-apply category
  exhausted; further work would need substantive lemmas best
  delegated to Aristotle once backend recovers.

## Earlier (now stale; kept for context only)
## Stale Live Status (2026-04-26 10:59 EDT)

- Active jobs (ours): 3/5. All three QUEUED ~6.8h — backend stalled
  since ~04:09 EDT, no jobs moving on any project.
- **Integrated this tick:** none (refresh-only; previous tick at
  10:54 just landed five LinearMap-layer apply-form lemmas in
  `PullbackFormsLinearMapApplyLinear`).
- **Submitted this tick:** none (backlog still blocking).
- Quick bookkeeping refresh tick. No new code; tree clean.

## Earlier (now stale; kept for context only)
## Stale Live Status (2026-04-26 10:54 EDT)

- Active jobs (ours): 3/5. All three QUEUED ~6.7h — backend stalled
  since ~04:09 EDT, no jobs moving on any project.
- **Integrated this tick (local Claude-owned, while Aristotle blocked):**
  - `Jacobian/TraceDegree/PullbackFormsLinearMapApplyLinear.lean` —
    five pointwise apply-form simp lemmas at the bundled-LinearMap
    layer: `pullbackFormsLinearMap_{zero,neg,add,sub,smul}_apply`.
    Each rewrites the function-level simp and closes by `rfl`.
    Mirrors the Periods-side
    `ChartedFormPullbackLinearMapApplyLinear` landed at 10:43.
    Out of scope of any in-flight Aristotle job.
  - Wired into `Jacobian/TraceDegree.lean` umbrella; module builds
    green (2416 jobs, 99s).
- **Submitted this tick:** none (backlog still blocking).
- Continuing local Claude-owned progress while Aristotle queue
  remains frozen.

## Earlier (now stale; kept for context only)
## Stale Live Status (2026-04-26 10:51 EDT)

- Active jobs (ours): 3/5. All three QUEUED ~6.7h — backend stalled
  since ~04:09 EDT, no jobs moving on any project.
- **Integrated this tick:** none (refresh-only; previous tick at
  10:48 just landed `pullbackFormsFun_{add,sub}_apply` in
  `PullbackFunAddSubApply`).
- **Submitted this tick:** none (backlog still blocking).
- Quick bookkeeping refresh tick. No new code; tree clean.

## Earlier (now stale; kept for context only)
## Stale Live Status (2026-04-26 10:48 EDT)

- Active jobs (ours): 3/5. All three QUEUED ~6.5h — backend stalled
  since ~04:09 EDT, no jobs moving on any project.
- **Integrated this tick (local Claude-owned, while Aristotle blocked):**
  - `Jacobian/TraceDegree/PullbackFunAddSubApply.lean` — two
    pointwise apply-form simp lemmas:
    `pullbackFormsFun_add_apply` and `pullbackFormsFun_sub_apply`.
    Each rewrites the function-level simp and closes by `rfl`.
    Out of scope of the in-flight Aristotle job 82687eb7
    (`PullbackFunSimpApply.lean`, which targets only
    `_zero/_neg/_smul_apply`).
  - Wired into `Jacobian/TraceDegree.lean` umbrella; module builds
    green (2410 jobs, 25s).
- **Submitted this tick:** none (backlog still blocking).
- Continuing local Claude-owned progress while Aristotle queue
  remains frozen.

## Earlier (now stale; kept for context only)
## Stale Live Status (2026-04-26 10:46 EDT)

- Active jobs (ours): 3/5. All three QUEUED ~6.5h — backend stalled
  since ~04:09 EDT, no jobs moving on any project.
- **Integrated this tick:** none (refresh-only; previous tick at
  10:43 just landed 5 LinearMap-layer apply-form lemmas in
  `ChartedFormPullbackLinearMapApplyLinear`).
- **Submitted this tick:** none (backlog still blocking).
- Quick bookkeeping refresh tick — wakeup fired sooner than the
  scheduled 30 min window. No new code; tree clean.

## Earlier (now stale; kept for context only)
## Stale Live Status (2026-04-26 10:43 EDT)

- Active jobs (ours): 3/5. All three QUEUED ~6.5h — backend stalled
  since ~04:09 EDT, no jobs moving on any project.
- **Integrated this tick (local Claude-owned, while Aristotle blocked):**
  - `Jacobian/Periods/ChartedFormPullbackLinearMapApplyLinear.lean` —
    five pointwise apply-form simp lemmas at the bundled-LinearMap
    layer: `chartedFormPullbackLinearMap_{zero,neg,add,sub,smul}_apply`.
    Each delegates through `chartedFormPullbackLinearMap_apply_at`
    (the rfl-bridge to the unbundled form) to the apply-form bundle
    landed in the previous tick.
  - Wired into `Jacobian/Periods.lean` umbrella; module builds green
    (2418 jobs, 35s).
- **Submitted this tick:** none (backlog still blocking).
- Continuing local Claude-owned progress while Aristotle queue
  remains frozen.

## Earlier (now stale; kept for context only)
## Stale Live Status (2026-04-26 10:41 EDT)

- Active jobs (ours): 3/5. All three QUEUED ~6.5h — backend stalled
  since ~04:09 EDT, no jobs moving on any project.
- **Integrated this tick:** none (refresh-only; previous tick at
  10:39 just landed 5 pointwise apply-form simp lemmas in
  `ChartedFormPullbackApplyLinear`).
- **Submitted this tick:** none (backlog still blocking).
- Quick bookkeeping refresh tick — wakeup fired sooner than
  expected. No new code; tree clean.

## Earlier (now stale; kept for context only)
## Stale Live Status (2026-04-26 10:39 EDT)

- Active jobs (ours): 3/5. All three QUEUED ~6.5h — backend stalled
  since ~04:09 EDT, no jobs moving on any project.
- **Integrated this tick (local Claude-owned, while Aristotle blocked):**
  - `Jacobian/Periods/ChartedFormPullbackApplyLinear.lean` — five
    pointwise apply-form simp lemmas:
    `chartedFormPullback_{zero,neg,add,sub,smul}_apply`. Each
    rewrites the function-level simp lemma and closes by `rfl`.
    Useful for direct-tactic proofs (Aristotle prompt style)
    without invoking the full simp set.
  - Wired into `Jacobian/Periods.lean` umbrella; Periods builds
    green (8083/8083, 162s).
- **Submitted this tick:** none (backlog still blocking).
- Continuing local Claude-owned progress while Aristotle queue
  remains frozen.

## Earlier (now stale; kept for context only)
## Stale Live Status (2026-04-26 10:27 EDT)

- Active jobs (ours): 3/5. All three QUEUED 2h+ — backend stalled
  since ~04:09 EDT, no jobs moving on any project.
- **Integrated this tick:** none.
- **Submitted this tick:** none (backlog still blocking).
- Bookkeeping tick. Waiting on backend recovery.

## Earlier (now stale; kept for context only)
## Stale Live Status (2026-04-26 05:17 EDT)

- Active jobs (ours): 3/5. All three QUEUED ~1 hr — backend
  stalled since ~04:09 EDT, no jobs moving on any project.
- **Integrated this tick (local Claude-owned, while Aristotle blocked):**
  - `Jacobian/TraceDegree/PullbackFormsLinearMapSimp.lean`:
    +`pullbackFormsLinearMap_sub` (LinearMap-derived subtraction
    linearity, named simp lemma matching the existing
    `_zero`/`_neg`/`_add` pattern).
- **Submitted this tick:** none (backlog still blocking).
- Continuing local Claude-owned progress while Aristotle queue
  remains frozen.

## Earlier (now stale; kept for context only)
## Stale Live Status (2026-04-26 05:16 EDT)

- Active jobs (ours): 3/5. All three QUEUED ~57 min — backend
  stalled since ~04:09 EDT, no jobs moving on any project.
- **Integrated this tick (local Claude-owned, while Aristotle blocked):**
  - `Jacobian/TraceDegree/PullbackFunApplyVec.lean` — tangent-vector
    apply: `(pullbackFormsFun f η x) v = η.toFun (f x) (mfderiv f x v)`,
    a `rfl` chain-rule unfolding.
  - `Jacobian/TraceDegree/PullbackFunSub.lean` — subtraction
    linearity: `pullbackFormsFun_sub` derived from `_add`/`_neg`.
  - Both wired into `Jacobian/TraceDegree.lean` umbrella.
- **Submitted this tick:** none (backlog still blocking).
- No-op-on-Aristotle, locally productive: keep waiting on the 3
  in-flight packets while pushing small Claude-owned lemmas.

## Earlier (now stale; kept for context only)
## Stale Live Status (2026-04-26 04:14 EDT)

- Active jobs (ours): 3/5. All three QUEUED; backlog resurfaced
  (5 non-ours jobs ahead of us).
- **Integrated this tick:** none.
- **Submitted this tick:** none.
- Brief tick — letting the queue drain.

## Earlier (now stale; kept for context only)
## Stale Live Status (2026-04-26 04:07 EDT)

- Active jobs (ours): 3/5.
- 🎉 **Integrated this tick:** `f9550953` —
  `Periods/ChartLiftApply.lean`. `rfl` one-liner.
- **Submitted this tick (3 refills):**
  - `f8faacda` — `Periods/ChartLiftBoundary.lean`. Boundary-value
    simps (`chartLift_zero`, `chartLift_one`).
  - `bf7d62c4` — `Periods/PathIntegralViaChartLinear.lean`.
    Provisional from-`X` `_neg` and `_smul` (completes provisional
    linearity except `_add`, same Packet F blocker).
  - `82687eb7` — `TraceDegree/PullbackFunSimpApply.lean`. Pointwise
    `_zero/_neg/_smul` apply lemmas for `pullbackFormsFun`.

## Layer status

- **Complex torus layer: complete (sorry-free).**
- **Queue C foundation in place.**
- **Queue D scaffolding (1 opaque, no sorries):** 11 files +
  umbrella; growing.
- **Queue E foundation:** `AnalyticJacobianGroup E X` + umbrella.
- **Queue F:** Recon document.
- **Queue G:** Recon document (`Jacobian/TraceDegree/Recon.lean`)
  inventories `mfderiv`/`ContMDiff` (PRESENT) vs `pullbackForms`/
  `traceForms`/`analyticDegree` (ABSENT); lays out chain-rule for
  pullback, fiber-sum for trace, 6 packets, flags
  `pushforward_pullback` as the strongest multiplicative anti-hack
  theorem.
- All challenge queues (A through G) have at least a recon document
  or production scaffold; Queue H's theorems live in
  `Jacobian/Challenge.lean` directly.

### Queued for next submission round (gated on current batch)

- `pullbackFormsFun_smooth` — Queue G follow-up to `0b8b1163`:
  prove the chain-rule pullback function is `ContMDiff` when `f` is.
  The substantive piece for upgrading to `HolomorphicOneForm E X`.
- `pathIntegralViaChartCorrect` linearity (zero/neg/add) — gated on
  `ee3ce016` + `fe592ee1`.
- Multi-chart `pathIntegralViaCover` definition combining
  `exists_uniform_chart_partition` (from `PathPartition`) with
  chart-local integrals. Needs Claude-owned design step first
  (subpath / affine reparam), then a clean Aristotle packet for
  the well-definedness lemmas.
- Decomposed TorusExample replacement (split into "constant
  function `_ ↦ id` is `ContMDiff`" as a standalone helper, then
  build the section on top), retrying `259b18a1`'s scope.

## Top open correctness item

`chartedForm c ω e v` should equal
`ω.toFun (c.symm e) (D(c.symm)_e v)`, but the current definition
drops the chart-derivative `D(c.symm)_e` and only evaluates the
section at `c.symm e`. Lean accepts the type only because
`TangentSpace I _ = E` trivially. Consequence: `pathIntegralInChart`
is the right integral only when chart transitions are translations
(torus case); it is wrong on a general Riemann surface. Flagged in
the `ChartedForm.lean` docstring and tracked here as the highest-
priority correctness fix. The proper version uses
`mfderiv 𝓘(ℂ, E) (chartedSpaceSelf ...) c.symm e` (or the
inverse-chart partial derivative API).
- Deferred (per the user's explicit guidance and the
  reviewer-acknowledged staging-phase tradeoff): file granularity
  consolidation, naming-convention alignment, and the
  `FullComplexLattice → Submodule + IsZLattice` design change. These
  belong to the eventual Mathlib-prep cleanup, not this phase.

## Planned packets (queued for Aristotle when queue unblocks)

The chart layer is complete; the next layer is `LieAddGroup` smoothness
of `+` and `-` on `quotient V Λ`. Decomposition into Aristotle-sized
packets below. Each packet targets one new file; allowed writes are
that file only; forbidden files always include `Jacobian/Challenge.lean`.

1. **`Jacobian/ComplexTorus/AddSmoothLocal.lean`** — `ContMDiffAt`
   of `(q1, q2) ↦ q1 + q2` at a single point. Strategy: at point
   `(q1, q2)` lift to representatives `v1, v2` via `Function.surjInv`,
   use the chart machinery (the same δ from
   `exists_pos_le_norm_of_discreteTopology` works for both factors),
   and observe that on a small ball the chart-coordinate addition is
   exactly the linear sum on `V × V → V`, then mk back. Re-uses
   `localSection_mk_locally_translate`-style reasoning; no new heavy
   API.

2. **`Jacobian/ComplexTorus/AddSmooth.lean`** — promote (1) to
   `ContMDiff (modelWithCornersSelf ℂ V).prod (modelWithCornersSelf ℂ V)
   (modelWithCornersSelf ℂ V) ⊤ (fun p => p.1 + p.2)` and from there
   to a `ContMDiffAdd` instance.

3. **`Jacobian/ComplexTorus/NegSmoothLocal.lean`** — `ContMDiffAt` of
   `q ↦ -q`. Same lift+chart pattern; in chart coordinates negation
   is `x ↦ -x` on `V`, which is `ContDiff ℂ ω`.

4. **`Jacobian/ComplexTorus/NegSmooth.lean`** — promote (3) to
   `ContMDiff` everywhere.

5. **`Jacobian/ComplexTorus/LieAddGroup.lean`** — combine the
   `ContMDiffAdd` instance from (2) and the `contMDiff_neg` from (4)
   into a `LieAddGroup (modelWithCornersSelf ℂ V) (⊤ : WithTop ℕ∞)
   (quotient V Λ)` instance. One- or two-line `where`-clause once the
   pieces are in place.

When the queue unblocks, submit (1) and (3) in parallel (disjoint
write scopes), then (2) and (4), then (5). All five fit the
"prefer simple tactics" guideline.

## General Job Template

```text
Working directory: C:\ver\JacobianChallenge
Target file: <one Lean file>
Allowed writes: only <target file>
Do not edit: Jacobian/Challenge.lean
Task: prove or implement the named declarations below.
Expected verification: lake build <module name>
If blocked: leave the theorem statement unchanged and add a short comment naming
the missing prerequisite.
```

## Queue A: Inventory

Source namespace:

```lean
JacobianChallenge.Inventory
```

Useful declarations:

- `MathlibInventory`
- `inventoryComplete`

Expected output:

- a factual inventory of existing Mathlib declarations at the pinned commit;
- exact file paths and declaration names;
- a list of missing infrastructure.

## Queue B: Complex Tori

Source namespace:

```lean
JacobianChallenge.ComplexTorus
```

Useful declarations:

- `FullComplexLattice`
- `quotient`
- `mk`
- `mk_surjective`
- `map`
- `map_mk`
- `map_id`
- `map_comp`
- `quotientChartedSpaceStatement`
- `quotientIsManifoldStatement`
- `quotientLieAddGroupStatement`

Good first Aristotle packets:

- prove quotient-map universal property lemmas;
- prove `map_mk`, `map_id`, and `map_comp`;
- replace placeholder lattice fields with existing Mathlib predicates if found;
- isolate the exact quotient-manifold theorem needed.

## Queue C: Holomorphic Forms and Genus

Source namespace:

```lean
JacobianChallenge.HolomorphicForms
```

Useful declarations:

- `HolomorphicOneForm`
- `FiniteDimensionalHolomorphicOneForms`
- `analyticGenus`
- `genus_eq_analyticGenus`
- `analyticGenus_eq_zero_iff_homeomorphic_sphere`

Expected packets:

- define holomorphic 1-forms using existing differential-form API;
- prove vector-space structure;
- state finite-dimensionality as a named theorem;
- connect analytic genus to the challenge `genus`.

## Queue D: Periods

Source namespace:

```lean
JacobianChallenge.Periods
```

Useful declarations:

- `IntegralOneCycle`
- `HolomorphicOneFormDual`
- `periodFunctional`
- `periodSubgroup`
- `periodSubgroup_isClosed`
- `periodFullComplexLattice`
- `period_homology_invariance_statement`
- `period_pairing_full_rank_statement`

Expected packets:

- define path/cycle integration;
- prove homology invariance of periods;
- prove period subgroup is closed;
- prove the full-lattice theorem.

## Queue E: Analytic Jacobian

Source namespace:

```lean
JacobianChallenge.AnalyticJacobian
```

Useful declarations:

- `AnalyticJacobian`
- `analyticJacobianEquivChallenge`
- `analyticJacobian_homeomorph_challenge`

Expected packets:

- define Jacobian from the period lattice;
- bridge to the public challenge type;
- handle universe issues deliberately.

## Queue F: Abel-Jacobi

Source namespace:

```lean
JacobianChallenge.AbelJacobi
```

Useful declarations:

- `pathIntegralFunctional`
- `analyticOfCurve`
- `analyticOfCurve_path_independent`
- `analyticOfCurve_self`
- `analyticOfCurve_contMDiff`
- `analyticOfCurve_injective`
- `challenge_ofCurve_eq_analytic`

Expected packets:

- prove path independence modulo periods;
- prove basepoint maps to zero;
- prove holomorphicity;
- prove injectivity for positive genus.

## Queue G: Trace, Degree, Pushforward, Pullback

Source namespace:

```lean
JacobianChallenge.TraceDegree
```

Useful declarations:

- `pullbackForms`
- `traceForms`
- `analyticDegree`
- `trace_pullback_forms`
- `degree_eq_analyticDegree`
- `pullbackForms_preserves_periods`
- `traceForms_preserves_periods`
- `analyticDegree_comp`
- `pushforward_pullback_from_trace`

Expected packets:

- define pullback of forms;
- define trace of forms;
- prove the trace-pullback identity;
- define degree compatibly;
- descend maps to Jacobians.

## Queue H: Anti-Hack Theorems

Source namespace:

```lean
JacobianChallenge.AntiHack
```

Useful declarations:

- `genus_zero_topological_sphere`
- `positive_genus_nontrivial_jacobian`

Expected packets:

- prove or trace dependencies for the anti-hack theorems;
- keep these theorems separate from convenience API;
- do not weaken their statements.
