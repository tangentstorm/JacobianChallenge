# CLAUDE.md

This file provides guidance to Claude Code (claude.ai/code) when working with code in this repository.

## What this project is

A Lean 4 / Mathlib formalization of Kevin Buzzard's Jacobian challenge (v0.3). The public specification is `Jacobian/Challenge.lean` — a small API of `sorry`-stubbed definitions and theorems about the Jacobian variety of a compact Riemann surface. The challenge is structured to defeat hack answers (e.g. `genus X := 0`, `Jacobian X := PUnit`), so the implementation must build real underlying infrastructure, not axiom layers that merely make the file compile.

This is a multi-month infrastructure project, not a single-file proof exercise. Claude manages the project; Aristotle (a remote Lean worker) does bounded proof tasks.

## Build commands

At the start of a fresh session — or any time `.lake/packages/mathlib/.lake/build/` is missing — run `lake exe cache get` first to pull the prebuilt Mathlib oleans. Without the cache, the first `lake build` will rebuild Mathlib from source (hours) instead of downloading the pinned binaries (minutes).

```bash
lake exe cache get                               # pull prebuilt Mathlib oleans (run once per fresh checkout)
lake build Jacobian.Challenge                    # the public target — must keep compiling
lake build Jacobian.Solution                     # the assembled solution skeleton
lake build Jacobian                              # everything (slow)
```

Always prefer the narrowest module build after a code change. Single-file builds use the dotted module path (e.g. `lake build Jacobian.ComplexTorus.QuotientMap`).

Pinned to `leanprover/lean4:v4.28.0` and `mathlib v4.28.0` (commit `8f9d9cff6bd728b17a24e163c9402775d9e6a365`). `Jacobian/Challenge.lean` references a slightly later Mathlib commit (`8e3c989...`) but the v4.28.0 tag is what builds; do not unpin without a deliberate decision.

## Architecture

Three load-bearing files define the project's structure:

- **`Jacobian/Challenge.lean`** — the public API target. Treated as a frozen specification: do not edit, weaken, or rename declarations here unless explicitly instructed. Every theorem/definition is a `sorry` to be discharged eventually.
- **`Jacobian/Solution.lean`** — the assembled solution skeleton; `(X : Type u_1)` matches `Challenge.lean`'s universe shape; bodies delegate to production decls under `Jacobian/<Layer>/`.
- **`ref/Inventory.md`** — Phase 0.5 narrative inventory of the pinned Mathlib commit, marking each prerequisite **PRESENT** / **PARTIAL** / **ABSENT**. (Was `Jacobian/WorkPackets/Inventory.md` before W3 retirement; the machine-readable Lean pointer `JacobianChallenge.Inventory.pinnedMathlibInventory` was retired with `StatementBank.lean`.)

Construction strategy (per `ref/plan.md`): use the analytic period-lattice route, `Jacobian X = H⁰(X, Ω¹)* / H₁(X, ℤ)`, built bottom-up through reusable layers (complex tori → holomorphic forms → periods → Jacobian → Abel-Jacobi → trace/degree). The empty `Jacobian/ComplexTorus/` directory is a placeholder for the first concrete milestone: a standalone proof that a finite-dimensional complex vector space modulo a full lattice is a compact complex Lie additive group.

Phase ordering matters. Do not drift into a higher layer (e.g. periods, Abel-Jacobi) until the lower-layer dependency is explicitly stable or formally blocked. The quotient group/topology/lattice API must come before quotient charted-space/manifold/LieAddGroup work.

## Anti-hack theorems

Four declarations in `Challenge.lean` exist specifically to rule out trivial fake constructions:
- `genus_eq_zero_iff_homeo` — forces `genus` to be tied to topology (no `genus X := 0`).
- `ofCurve_inj` — forces nonconstant injective Abel-Jacobi for positive genus (no `Jacobian X := PUnit`).
- The compact complex Lie group instances on `Jacobian X` — force torus-like analytic structure.
- `pushforward_pullback` — forces pushforward/pullback/degree to interact through the classical trace identity, not arbitrary homomorphisms.

When designing or reviewing definitions, keep an explicit audit trail showing which construction theorem satisfies each anti-hack check.

## Aristotle delegation workflow

This project runs on a timer (`ref/PROMPT.md`, intended for `/loop 15m`). Each tick: read state, check Aristotle status once (no polling), retrieve completed jobs, integrate clean patches, refresh `README.md` progress report, keep ~5 active Aristotle tasks with disjoint write scopes, update `aristotle_tasks.md` (the human-readable ledger).

Every Aristotle job must specify: working directory `C:\ver\JacobianChallenge`, exact target file, allowed write scope, forbidden files (always including `Jacobian/Challenge.lean`), exact declaration names, expected `lake build` command, and fallback behavior if blocked. Prefer many small file-scoped jobs over one large job. `aristotle_tasks.md` has per-queue templates (Queues A–H) keyed to the namespaces in the statement bank.

**When the target sorry is gated on an upstream placeholder** (`True := trivial` leaves, `noncomputable opaque` defs with no axioms, `:= PUnit` / `:= 0` data-trivial stubs, etc.), default single-file scope produces a clean BLOCKER triage but no progress. Instead, widen the allowed-writes scope to include the upstream stub file and explicitly task Aristotle with making the upstream definition real (existing sorry-free call sites must still type-check; no existing sorry-free decl may become sorry). Or, prefer creating a fresh infrastructure file when the missing prerequisite can be built from existing primitives (`Jacobian/Periods/HurewiczMap.lean` is the 2026-05-07 prototype). See `ref/PROMPT.md` § "When the target is blocked by a placeholder upstream" for the framing.

Tell Aristotle to prefer direct tactics (`simp`, `rw`, `exact`, `refine`, `constructor`, `ext`, `intro`, `apply`) and small helper lemmas. Avoid large `aesop`, `grind`, broad `simp_all`, and fragile automation unless the task explicitly justifies it.

Bad delegation ("solve the Jacobian challenge", "fix all sorries") is explicitly listed in `ref/plan.md` as forbidden — Claude owns global definition choices and statement design; Aristotle owns bounded local proofs.

## Conventions

- `autoImplicit = false` is set in `lakefile.toml` — declare every variable explicitly.
- Public theorem names and statements stay stable once another file or Aristotle job depends on them.
- If a statement is too hard, split it into helper lemmas. Do not paper over it with axioms in production files (placeholders in the statement bank are acceptable but should be tracked as missing infrastructure).
- After integrating Aristotle work, update `README.md`'s progress report (UTF-8 shaded bars `█`/`░`, separator `━` — exact format in `ref/PROMPT.md`) and include both `README.md` and `aristotle_tasks.md` in the integration commit.
- **Git Commit Crediting**: All commits must be authored and committed under `Michal Wallace <michal.wallace@gmail.com>`. Contributing agents must be credited using normalized `Co-authored-by:` trailers as specified in [scialect/rules/commit-guide.md](file:///Users/michal/ver/scialect/rules/commit-guide.md).
- **Agent Status & Unblocking**: All workers must manage their active checklists in `task.md` using the standardized status lines of the format `[STATUS]: [detail]` (e.g. `WORKING: [Active step description]`, `STEP-DONE: [Active step description]`, or `BLOCKED: [reason]`) and follow the strict local-infrastructure unblocking protocol defined in [scialect/rules/status-guide.md](file:///Users/michal/ver/scialect/rules/status-guide.md). Never declare yourself blocked by Mathlib gaps—build the missing helper lemmas locally!
