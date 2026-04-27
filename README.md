# Jacobian Challenge

A Lean 4 / Mathlib formalization of the Jacobian variety of a compact Riemann surface (see _About_ below for scope).

## Progress Report

Last tick: 2026-04-27 15:13 EDT

```text
Headline progress markers (every value below is a fresh count from this tick)
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
Public spec discharged          0 / 24    sorries in Jacobian/Challenge.lean (frozen target)
StatementBank declarations     22         named decls in Jacobian/WorkPackets/StatementBank.lean
                                          (excluding 2 Inventory metadata items)
Aristotle integrations to date 82         `"status":"integrated"` lines in aristotle_jobs.jsonl
Production sorry-free files   367 / 383   denominator excludes 11 intentional design files
                                          (Challenge, Solution, StatementBank, 8 *Recon*.lean)

Reproduction:
  total       find Jacobian -name "*.lean" | wc -l                        → 394
  intentional Challenge + Solution + StatementBank + 8 *Recon* files      → 11
  prod        394 − 11                                                    → 383
  with-sorry  grep -rl "\bsorry\b" prod-files                             → 18
              (2 are doc-comment-only matches in ComplexTorus.lean
               and Periods.lean umbrellas)                                → 16 real
  sorry-free  383 − 16                                                    → 367
```

```text
StatementBank promotion (curated ratio: how many named declarations have a
real production-module implementation? Denominator is the StatementBank
itself, not a count of the tree.)
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
                          promoted / total   notes
Inventory                    2 / 2           metadata only — counted separately
ComplexTorus                 3 / 3           Prop placeholders backed by IsManifold + LieAddGroup instances
HolomorphicForms             3 / 3           abbrev/def used directly as the working types
Periods                      1 / 6           IntegralOneCycle abbrev concrete; periodFunctional still
                                             `opaque`; period_homology/period_pairing_full_rank still
                                             `Prop := True`; periodFullComplexLattice not yet
AnalyticJacobian             1 / 3           AnalyticJacobianType ✓ (= AnalyticJacobianGroup);
                                             equivChallenge + homeomorph_challenge still placeholders
AbelJacobi                   0 / 2           pathIntegralFunctional opaque; analyticOfCurve still a stub
TraceDegree                  0 / 3           pullbackForms / traceForms / analyticDegree all opaque
                          ────────
Substantive total            8 / 20  (40%)   excludes 2 Inventory metadata items
```

```text
Aristotle status
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
Active jobs (ours):     5 / 5  ALL COMPLETE at backend this tick — but `result` retrieval
                        is failing with httpx.ConnectError (TLS / connectivity). `list`
                        works; only the tarball download fails. Will retry next tick.
                        `37b183aa` evalLinearMap_ne_zero_of_toFun_ne_zero (HolomorphicForms)
                        `6c252557` periodSubgroup_eq_range (Periods)
                        `2f5d999b` mk_eq_zero_iff_mem_range (AnalyticJacobian)
                        `b3a3b251` witnessAbelJacobi_self_both (AbelJacobi)
                        `2d65778f` evalJacobianClass_self_sub_self (AnalyticJacobian; now
                                   redundant — discharged locally last tick by `sub_self _`)
Integrated this tick:   0 from Aristotle (retrieval blocked). 4 lemmas via 1 new local file
                        (see "Local cadence" below).
Tree note:              Jacobian/Solution.lean (M), Jacobian/ComplexTorus/ULiftTransport.lean (M)
                        and Jacobian/{AbelJacobi/AnalyticOfCurveBasis,TraceDegree/PullbackBasis}.lean
                        (untracked) are pre-existing user work — left untouched per PROMPT.md.
                        TraceDegree/PullbackBasis.lean (3 sorrys) is included in the production
                        denominator and counts against sorry-free total.
```

```text
Local cadence this tick (Claude-owned, no Aristotle dependency)
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
NEW Jacobian/AnalyticJacobian/EvalJacobianClassEqSubMem.lean:
  `evalJacobianClass_eq_iff_sub_mem`
  `evalJacobianClass_sub_eq_zero_iff_eq`
  `evalJacobianClass_sub_eq_zero_iff_sub_mem`
  `evalJacobianClass_eq_of_sub_mem`
  → 4 sub-mem variants of the equality / vanish-iff characterizations,
    mirroring `mk_eq_mk_iff_sub_mem` upstream. All proofs are
    term-mode unfold + existing-lemma application or single-rewrite.
```

```text
Build status — recomputed each tick from the tree
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
Challenge target          pass         lake build Jacobian.Challenge
Statement bank            pass         lake build Jacobian.WorkPackets.StatementBank
Current target            pass         lake build Jacobian.AnalyticJacobian.EvalJacobianClassEqSubMem

Sorry-free coverage by directory (production files only — Recon files excluded
from both numerator and denominator)
                                       bar              ratio       %
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
Jacobian/AnalyticJacobian        ███████████████████░  22 / 23     95.7%
Jacobian/AbelJacobi              ██████████████████░░  18 / 20     90.0%
Jacobian/HolomorphicForms        █████████████████░░░  25 / 28     89.3%
Jacobian/ComplexTorus            █████████████████░░░  47 / 53     88.7%
Jacobian/Periods                 ████████████████████  168 / 171   98.2%
Jacobian/TraceDegree             ████████████████████  81 / 82     98.8%
Top-level Jacobian/*.lean        ████████████████████  6 / 6      100.0%

Reproduction:
  per dir: total = `find <dir> -maxdepth 1 -name "*.lean" | wc -l`
           recon = `find <dir> -maxdepth 1 -name "*Recon*.lean" | wc -l`
           with-sorry-word = (grep -l "\bsorry\b") minus Recon files
           clean = (total − recon) − with-sorry-word
           ratio = clean / (total − recon)
```

```text
Next tick priorities
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
1. Retry Aristotle `result` retrieval for the 5 COMPLETE packets;
   integrate any that come down clean. Network was up for `list`
   but failing for tarball download — likely transient.
2. If still blocked, replace `2d65778f` with a fresh packet anyway
   (target already discharged locally); submit a new task to refill
   the queue. Aim for 5/5 active.
3. Continue local 4-lemma cadence. Candidate: a Sub-Mem-style
   companion for the `evalLinearMap` (form-level) equality lemmas,
   or further `mk` arithmetic decomposition.
```

## About

A Lean 4 / Mathlib formalization project targeting the Jacobian variety of a
compact Riemann surface.

The public specification lives in `Jacobian/Challenge.lean` and asks for:

- `genus X` for a compact Riemann surface `X`;
- `Jacobian X` as a compact complex Lie additive group of dimension `genus X`;
- the Abel-Jacobi map `Jacobian.ofCurve`;
- pushforward and pullback maps along holomorphic maps;
- the degree of a holomorphic map of compact Riemann surfaces;
- the identity `pushforward f (pullback f P) = degree f • P`.

Approach: the analytic period-lattice construction
`Jacobian X = H0(X, Ω¹)* / H1(X, Z)`, built up through reusable layers
(complex tori, holomorphic forms, period integration, Abel-Jacobi, degree).

See `plan.md` for the full roadmap, phase breakdown, anti-hack audit, and
delegation strategy for Aristotle.
