# AI Formalization Prompting Guide

This guide contains strategies to ensure that AI agents (Claude, Codex, Gemini) produce mathematically meaningful proofs and do not "game" the scaffolding or trivialize definitions.

## 1. Ensuring Definition Integrity
Agents may attempt to simplify a `def` to make a subsequent `theorem` easier to prove.
- **Guideline:** Explicitly state: "Do not modify existing `def` or `structure` declarations in the target file."
- **Failure Case:** Redefining a complex affine map as a constant function to make the continuity proof trivial (`continuous_const`).

## 2. Preventing Placeholder Exploitation
The project uses "typed scaffolding" where complex types are often aliased to simpler ones (e.g., `def relativeSkeletalH := cellularChain`) during initial assembly.
- **Guideline:** Forbid proofs that rely on these aliases. State: "The proof must not rely on the fact that [Type A] is currently defined as [Type B]. The proof should treat [Type A] as an abstract object satisfying the properties in the Blueprint."
- **Failure Case:** Using `simp` to discharge a dimension identity because the target type was aliased to a free module.

## 3. Mandatory Blueprint Alignment
- **Guideline:** Include the relevant section of the LaTeX Blueprint in the prompt.
- **Guideline:** State: "The proof must be semantically equivalent to the argument provided in the Blueprint. Shortcuts that bypass the core mathematical difficulty (e.g., skipping a Mayer–Vietoris argument) are unacceptable."

## 4. Verification & Auditing
- **Scripted Check:** Use `lake build` to check compilation, but also visually audit the `git diff` for changes to `def`s.
- **Axiom Check:** Use `#print axioms [theorem_name]` to ensure the proof hasn't introduced unwanted shortcuts or hidden dependencies.

## 9. Build & Cache Management
Project builds can be extremely slow if Mathlib is recompiled from scratch.
- **Guideline:** Explicitly state: "If you need to build the project to verify your work, you MUST run `lake exe cache get` first to retrieve the pre-built Mathlib binaries."
- **Path Portability:** Do **NOT** include absolute paths or "Working directory" lines in prompts. Agents should discover the project root automatically or use relative paths.

## 5. Explicit Anti-Cheat Instructions
Add this block to all high-effort formalization prompts:
> **ANTI-CHEAT CLAUSE:**
> - You must **NOT** change the definitions of the mathematical objects provided in the scaffolding.
> - You must **NOT** rely on placeholder type aliases to discharge the goal.
> - If you need to build, run `lake exe cache get` first.
> - If you find a definition is insufficient for a real proof, STOP and report the issue rather than providing a degenerate solution.

## 6. Upgrading Scaffolding (Type Separation)
If an agent discovers that a proof is trivialized by an alias (e.g., `abbrev Foo := Bar`), the human/orchestrator should upgrade the scaffolding before the next attempt.
- **Method:** Replace the `abbrev` with a `noncomputable def` and a distinct wrapper (e.g., `ULift`).
- **Goal:** This forces the agent to use the provided equivalence (`≃ₗ`) or bridge lemmas to transport properties, rather than relying on definitional equality.

## 7. Deep Context Missions
Skeletal prompts lead to skeletal thinking.
- **Guideline:** Provide the FULL mathematical reasoning from the Blueprint, including dependencies and proof sketches.
- **Format:** Copy-paste the exact LaTeX environment (lemma + proof) into the prompt or a linked `.md` plan.

## 8. Top-Down Refinement Strategy
Finish the project by working "Leafward" from the goal.
1. **Scaffold:** Define the high-level theorem and `sorry` the proof.
2. **Breakdown:** Decompose the `sorry` into 3-5 named lemmas (stubs).
3. **Assemble:** Prove the top-level theorem `sorry-free` using the stubs.
4. **Recurse:** Assign the new stubs as missions to specialized agents.
5. **Promote:** Once a stub is proven, move its implementation from the "Infrastructure/Generated" files into the production modules.
