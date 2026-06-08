# Worker jc1 — Plan: Issue #227 Type-0 Riemann Classical Period-Coordinate Frontier

Discharge the current reachable Type-0 #227 root in
`Jacobian/Periods/PeriodFunctional.lean`:

```lean
h1_basis_periodCoordinate_linearIndependent
```

This is the narrowed replacement for the original broad
`riemann_classical_real_LI_input` sorry. The public theorem now consumes a
`RiemannClassicalPeriodBasis` hypothesis and is sorry-free; the remaining work
is to prove, or maximally narrow, the basis-specific classical
period-coordinate nondegeneracy provider.

## 0. Allowed Write Scope

- **Write:** `Jacobian/Periods/PeriodFunctional.lean`.
- **Write if needed:** small helper files under `Jacobian/Periods/` for reusable
  Riemann-bilinear/period-basis linear algebra.
- **Read:** `Jacobian/Periods/PeriodVectorsLIU.lean`,
  `Jacobian/Periods/H1BasisU.lean`, `Jacobian/Periods/SurfaceClassification.lean`,
  `Jacobian/Periods/Hurewicz.lean`, and Chapter-06 blueprint files.
- **Forbidden:** `Jacobian/Challenge.lean`.
- **Avoid:** jc2 turf (`TietzeReduction.lean`, `HandleSwapHomeo.lean`), jc3
  StableChartAt reroute files, jc4 de Rham/Hodge files, and jc5 universe-`u`
  H1/period-vector files unless redirected.

## 1. Current Frontier

- [x] Prior jc1 work strengthened `riemann_classical_real_LI_input` with a
      `RiemannClassicalPeriodBasis X σ` hypothesis and proved the theorem
      sorry-free from that predicate.
- [x] Prior jc1 work introduced `h1_basis_periodCoordinate_linearIndependent`
      as the narrower remaining provider for a concrete integral H1 basis.
- [ ] Issue #227 is still open until the current provider is either discharged
      or narrowed to the precise classical symplectic-basis/Stokes/Hodge input.

## 2. Commit Sequence

### Milestone P0 — Audit the Current Provider Boundary
- [x] **P0.** Inspect `h1_basis_periodCoordinate_linearIndependent`,
      `h1_basis_riemannClassicalPeriodBasis`,
      `riemann_classical_real_LI_input`, and downstream consumers. Decide and
      record whether the current provider can be proved directly from existing
      substrate, or which exact missing classical statement must become the next
      provider. This should be one commit at most: no broad proof attempt, no
      public API churn unless a tiny signature/comment clarification is required.

### Milestone P1 — Build the Local Linear-Algebra Assembly
- [x] **P1.** If direct assembly is feasible, prove the finite-dimensional
      linear-algebra bridge from period-coordinate nondegeneracy to the current
      target using `holomorphicOneFormDualEquiv` and
      `RiemannBilinearRefinement.real_linearIndependent_of_quadratic_pos_def`.
      If not feasible, add a strictly narrower named provider for the missing
      basis-aligned period-coordinate nondegeneracy statement, then prove
      `h1_basis_periodCoordinate_linearIndependent` from it sorry-free.

### Milestone P2 — Thread the Provider Through the Existing API
- [x] **P2.** Keep `h1_basis_riemannClassicalPeriodBasis` and
      `riemann_classical_real_LI_input` as sorry-free assemblies. Verify
      downstream Type-0 period-vector and lattice declarations still consume
      the provider without weakening statements.

### Milestone P3 — Blueprint and Sorry Graph Refresh
- [x] **P3.** If the reachable root name or dependency boundary changes,
      refresh `sorries.jsonl` and update the Chapter-06 blueprint wording so
      #227 points at the current precise frontier. Do not mark any open provider
      green.

### Milestone P4 — Acceptance
- [ ] **P4.** `lake build Jacobian.Periods.PeriodFunctional`,
      `lake build Jacobian.Periods.PeriodVectorsLIU`, and
      `lake build Jacobian.Solution` all pass. `scripts/list-sorries.py --text`
      shows #227 discharged or narrowed to a strictly smaller provider with no
      net new reachable sorries.

## 3. Hazards

- The original arbitrary-injective #227 statement is mathematically too strong.
  Do not revert to it or prove it by stub.
- Keep the current public theorem shape honest: if a classical/symplectic-basis
  hypothesis is required, preserve it rather than pretending injection is enough.
- Do not create a second broad provider parallel to the current one. If a new
  provider is needed, it must be strictly narrower and the old root must be
  proved sorry-free from it.
- Do not introduce `axiom`, `unsafe`, or a new broad `sorry`.
