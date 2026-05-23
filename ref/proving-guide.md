# Proving Guide for Agents

This document defines the standards and rules you **must** follow when working as an agent in the JacobianChallenge project. These rules exist to prevent wasted effort, duplicated work, and weak progress that looks like activity but does not meaningfully advance the project.

You must read and follow this guide in every session. Violations of these rules will be treated as failures of execution.

## 1. Core Philosophy

You are not here to "make progress" in a vague sense. You are here to produce **exact, named, reusable mathematical progress**.

- You must break large problems into **exact provider theorems** rather than broad wrappers or minor reorganizations.
- You must **name** the new theorems you introduce. Vague or temporary names are not acceptable.
- You must keep frontiers accurate. Do not hide real mathematical difficulty behind large "infrastructure" theorems that still contain the original hard sorries.
- You must prefer smaller, precisely scoped providers over large, multi-purpose ones.
- You must not perform large refactors or renamings unless they are necessary to create clean, named providers. Cosmetic changes that do not reduce the frontier are forbidden.

If your work does not result in at least one new, clearly named, smaller provider (or a direct proof of an existing frontier), you have not made acceptable progress.

## 2. Verification Discipline (Mandatory)

Before you may write or update `result.md`, you **must** complete the following verification steps:

1. Run `lake exe cache get` if you have not done so recently.
2. Run `lake build Jacobian.Solution`.
3. Check the build output for any warnings that are **not** of the form "declaration uses `sorry`". You must not introduce new linter warnings. The presence of non-sorry warnings is a failure.

You must only claim a task is complete when:
- `lake build Jacobian.Solution` succeeds with no disallowed warnings,
- the relevant sorries have been substantively reduced (either proved or replaced by strictly narrower, named providers).

Running only a partial build is not enough to mark the assignment ready unless your current `goal.md` explicitly says otherwise. If you only ran partial builds, report that clearly in `result.md`.

## 3. Working with sorries.jsonl

You must treat `sorries.jsonl` with extreme care.

- You may **not** modify `sorries.jsonl` during normal work.
- You must not run `fix-sorries.py` or `audit-sorries.py` during the proving stage unless your current `goal.md` explicitly instructs you to.
- You must not manually edit `sorries.jsonl` to adjust upstream/downstream relationships, effort estimates, or status unless explicitly instructed to do so in your current `goal.md`.
- Updating and auditing `sorries.jsonl` is part of the post-ACCEPT pushing workflow, not part of proof development. See `ref/pushing-guide.md`.

Violations of these rules will be considered a failure to follow instructions.

## 4. Writing result.md

Your `result.md` is the primary way the manager evaluates your work. It must be clear, accurate, and structured.

Every `result.md` you write must contain at minimum:

- A clear statement of what you actually achieved.
- The exact new provider theorems you introduced (with names and file locations).
- Which previous frontier sorries are now direct-sorry-free as a result of your work.
- Which sorries remain and why (be precise).
- The output of `lake build Jacobian.Solution` (or confirmation that it passed cleanly).
- A brief assessment of the quality of the progress (e.g., "This is a clean provider decomposition" or "This is only a partial reduction and the core difficulty remains").

You must not exaggerate progress or present reorganization as new mathematical content.

## 5. Committing Your Work

Before marking the assignment `READY:`, commit the intentional project changes you made. Use a clear commit message and include a `Co-authored-by` trailer for the agent that actually did the work.

Use the correct identity for your agent. For example, Codex workers should use:

```text
Co-authored-by: Codex <codex@openai.com>
```

Do not use the Codex trailer unless you are Codex.

Do not include unrelated scratch files. Do not commit `result.md` or `.swarm-status` unless the current `goal.md` explicitly asks you to.

## 6. Status Reporting

When you receive a new assignment, the manager will usually set `.swarm-status` to `ASSIGNED: <branch-or-task>`. Before doing any implementation work, immediately update `.swarm-status` to acknowledge that you have received and understood the instructions:

```
WORKING: started
```

Keep the `WORKING:` line under 50 characters. Put details in notes or `result.md`, not in `.swarm-status`.

After you have written or updated `result.md`, you **must** create or update the file `.swarm-status` in the root of your working directory with an **extremely short one-line summary** of your current status.

The line **must** start with one of the following prefixes:

- `READY:`   — Use this when `result.md` explains what was done and the work is ready for review.
- `BLOCKED:` — Use this when you are stuck. The status should briefly identify the blocker.

The full line must be fewer than 50 characters. Put details in `result.md`, not in `.swarm-status`.

**Examples:**

```
READY: endpoint matching closed
BLOCKED: needs prism lemma
```

Do not write multi-line content or long explanations in `.swarm-status`. Keep it to a single line under 50 characters. This file is used by the manager (via `swarm -c status`) to get a quick overview of all workers.

## 7. Handling Difficulty and Getting Stuck

You are expected to make forward progress. If you find yourself unable to do so:

- You must stop after a reasonable amount of time (typically no more than 30–60 minutes of unproductive thrashing).
- You must clearly describe the precise mathematical blocker in your `result.md`.
- You must not continue making superficial changes to the code in an attempt to appear productive.
- You should propose what you believe the next concrete step should be (e.g., "A new provider theorem X is needed that states...").

Repeated failure to recognize when you are stuck will be treated as poor execution.

## 8. Collaboration with the Manager

The manager (jc0) is responsible for maintaining global coherence. You must support this:

- Communicate clearly and concisely in `result.md`.
- When proposing new structure or new providers, explain why the decomposition is mathematically natural.
- If you believe the current goal is poorly scoped or missing a necessary intermediate theorem, say so directly instead of working around it.
- Do not assume the manager will notice problems in your work. It is your responsibility to surface them.

## 9. Forbidden Anti-Patterns

You must not engage in the following behaviors:

- Shuffling sorries between files or theorems without creating meaningfully narrower providers.
- Proving the same mathematical content in multiple places under different names.
- Modifying `sorries.jsonl` during proof development.
- Claiming "progress" when the core difficulty has simply been moved or renamed.
- Ignoring linter warnings or build failures.
- Continuing to work for long periods after becoming stuck without clearly signaling it.
- Editing definitions or core structures unless explicitly authorized in your current goal.

## 10. Tooling Expectations

You are expected to be competent with the following commands and use them appropriately:

- `lake build Jacobian.Solution`
- `git status`, `git diff`, and `git commit`

You should run these tools proactively rather than waiting to be told.

---

**You are expected to internalize this guide.** Future goals will assume you have read and are following it. Repeated failure to adhere to these standards will result in reduced or terminated work assignments.
