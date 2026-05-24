# Agent Status and Unblocking Protocol

To ensure highly effective, autonomous progress in this multi-agent setup, all workers must adhere strictly to the following status lifecycle and unblocking rules.

---

## 1. Status-Line Specification

The very first line of each worker's `task.md` must be a standardized status and detail indicator of the format `[STATUS]: [detail]`:

*   `WORKING: [Active step description]` — The worker is actively developing the specified commit-sized step.
    *   *Example*: `WORKING: Prove discreteness of closed subgroup`
*   `STEP-DONE: [Active step description]` — The worker has completed the specified step (it compiles sorry-free) and is waiting for peer-review.
    *   *Example*: `STEP-DONE: Prove discreteness of closed subgroup`
*   `BLOCKED: [Detailed reason or Group dependency gate]` — The worker is genuinely stuck and cannot proceed.
    *   *Example*: `BLOCKED: Gated on Group 2 Banach metric space`

---

## 2. Commit-Sized Steps (`task.md`)

Each task assigned in `task.md` must be scoped strictly to **exactly one git commit's worth of work** (e.g. proving a single lemma, defining a single coordinate chart, or completing a single step of a topology constructor).
*   **Do not** try to solve the entire group's goals in a single step.
*   Keep the scope tight, reviewable, and verifiable.

---

## 3. The `STEP-DONE` Review Loop

Once a worker changes their status line to `STATUS: STEP-DONE`:
1.  **Review Dispatch**: A separate, independent **Reviewer Agent** is dispatched to the workspace.
2.  **Verification**: The Reviewer Agent checks that:
    *   The newly written Lean code compiles perfectly under `lake build`.
    *   No `sorry`s or stubs were introduced.
    *   The code is mathematically honest (no fake axiomatic assumptions or trivializing defs).
3.  **Integration**: If verified, the Reviewer Agent commits the step under the developer's git identity and merges the work. If it fails, the status is reverted to `STATUS: WORKING` with specific feedback.

---

## 4. The Unblocking Protocol (Preventing Constant Blockage)

Because this is a month-long formalization project where much of the underlying infrastructure is missing from Mathlib, **hitting a Mathlib gap is NOT a valid reason to declare `STATUS: BLOCKED`.** 

Agents must follow this protocol:

### Rule 1: Build the Local Infrastructure Yourself
If a prerequisite lemma, topological instance, or algebraic structure is missing from Mathlib, you are **not** blocked. You must **define and prove that missing infrastructure yourself** as a local, sorry-free helper lemma in your assigned directory. 
*   *Example*: If quotient manifold transition machinery is missing, Worker 0's task is explicitly to *write* the local translation chart transition proofs, not to get blocked by its absence in Mathlib.

### Rule 2: Exhaust Local Primitives
Before declaring a block, you must exhaust all local primitives. If the missing piece can be proved by composing simpler Mathlib facts or basic metric topology properties, you must write that proof locally.

### Rule 3: Valid `BLOCKED` Criteria
You may **only** set `STATUS: BLOCKED` if one of the following conditions is met:

1.  **Cross-Group Gating (Dependency Block)**:
    *   You are waiting on a prerequisite statement owned by a lower-layer Group (e.g. Group 4 Abel-Jacobi waiting for Group 1 to stabilize the quotient Lie group manifold instances).
    *   *Required Status*: `STATUS: BLOCKED: Gated on Group X (thm:name)`
2.  **Lean Compiler or Universe Limit**:
    *   You hit an unresolvable typeclass elaboration conflict, a universe level mismatch (e.g. `Type u` vs `Type*`), or a compiler panic that literally prevents the file from typechecking despite trying local helper wrappers.
    *   *Required Status*: `STATUS: BLOCKED: Lean Compiler Error (details)`
    *   *Required Action*: You must append a **Detailed Blocker Triage Report** to the bottom of `task.md` explaining the exact error and why local helper wrappers could not bypass it.
