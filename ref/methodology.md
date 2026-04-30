# Methodology — fleshing out the proof, then formalizing it

This is the *strategy doc* for how we move from a partially-formalized
project to a fully-closed Lean proof. The mechanics of any given round
of refinement live in `ref/TOPDOWN.md`; the overall roadmap lives in
`ref/plan.md`; this file connects them and adds the new cross-tool
workflow we're using to plan ahead of formalization.

## The problem with where we are now

The blueprint (in `tex/`, rendered at `blueprint/`) covers the *outer
scaffold* of the proof — about 22 named theorems and definitions, with a
dependency graph that shows how they relate. But:

* Many proof steps that are *not yet in Mathlib* are buried inside the
  proofs of those 22 nodes. Examples: Abel's theorem (existence
  direction), Riemann–Hurwitz, Hodge decomposition, Riemann bilinear
  relations, divisor theory — none of these have their own node.
* So the dep graph is **not** a true Mathlib-gap inventory. It's a
  Mathlib-gap *outline*.
* That means we cannot yet pick a leaf and ask "is this in Mathlib?"
  because most leaves are still abstractions over multi-thousand-line
  classical results.

The job is to drive the blueprint's granularity down until every leaf
is either (a) directly in Mathlib or (b) a precise stand-alone
"missing-from-Mathlib" statement.

## The three phases

### Phase A — Refine the *informal* proofs in `tex/`

Apply the same TOPDOWN workflow we use on Lean files (`ref/TOPDOWN.md`)
but to the LaTeX proofs. For each `\begin{proof}` block in `tex/main.tex`:

1. Identify each non-trivial step that's not yet a named lemma/theorem.
2. Promote each step to its own `\begin{theorem}` (or `\begin{lemma}`,
   `\begin{proposition}`, `\begin{definition}`) with `\label{...}`,
   `\uses{...}` linking back to its prerequisites, and (if a Lean target
   is identified) `\lean{...}`.
3. The original proof shrinks to: "by [step1], [step2], …".
4. Recurse on each new node. Stop when each leaf is either Mathlib (mark
   with `\notready` or similar — no node needed) or a clean
   missing-from-Mathlib statement (this *does* get a node).

Goal: when the resulting blueprint is rebuilt, the dep graph shows the
*entire* proof skeleton, with every Mathlib gap as its own labelled
node.

The gating signal for Phase A done: walking the dep graph, every node
either has an existing Lean declaration (green border/background) or is
a clean stand-alone statement of a single missing piece. No node hides
a multi-thousand-line classical theorem inside a single sentence.

### Phase B — Strategy elicitation per leaf

For each leaf "Mathlib gap" identified in Phase A, we don't formalize
yet — we *plan* the formalization first, using the human-paid LLMs as
a math sounding board:

1. Open ChatGPT. There's a "Jacobian Challenge" project there. Start a
   fresh chat.
2. Paste the leaf's statement (and relevant context from the
   blueprint). Work through the proof strategy: outline → required
   lemmas → expected difficulty → which Mathlib pieces plug in.
3. Open Grok. There's also a "Jacobian Challenge" project. Paste the
   strategy. Get critique.
4. Iterate between the two as needed until the strategy is concrete.
5. Save the final strategy paragraph back into the blueprint's
   `\begin{proof}` block for that leaf node, plus any new `\uses{...}`
   links the strategy revealed (they often surface intermediate lemmas
   that become their own sub-nodes — i.e. Phase A continues
   incrementally).

Multiple chats can run in parallel across browser tabs. Each one is
*per-leaf*, not per-session, so they don't interfere.

The point of using *both* ChatGPT and Grok: they have different blind
spots and different math priors. Cross-checking catches silent errors
that a single-model planning loop would miss.

### Phase C — Bottom-up formalization in cloud sessions

After A and B are done for a sub-tree, we start formalizing — bottom up,
one leaf at a time:

1. Pick the smallest, most-leaf statement in the sub-tree.
2. Launch a Claude Code cloud session targeting that statement. The
   session prompt cites the blueprint node (label + URL), pastes the
   strategy paragraph from Phase B, and instructs the agent to:
   * Apply `ref/TOPDOWN.md`-style refinement *internally* — break the
     formal target into Lean-ready pieces.
   * Formalize each piece, looping bottom-up.
   * Open a PR when the leaf is fully closed.
3. Integrate the PR into `main`.
4. Move up the tree. The next layer's "leaves" are the
   already-formalized lemmas the strategy depended on plus any new ones
   surfaced by the formalization.

This is the same recursive shrinking move described in `ref/TOPDOWN.md`,
but driven by a blueprint that already has every gap surfaced as a
node.

## Tooling

### Browser tabs (Playwright)

We keep the following tabs open during a working session:

| Tab | Purpose |
| --- | --- |
| Dependency graph | live view of the blueprint's structure; the canonical "where's the next gap" surface |
| Claude Code (claude.ai/code) | env config, session launch, session monitoring |
| ChatGPT (Jacobian Challenge project) | Phase B strategy elicitation |
| Grok (Jacobian Challenge project) | Phase B strategy critique |
| GitHub (current run / PR / issue) | as needed |

Never call `browser_close` on these tabs — the user manages window
lifecycle.

### Cloud env

The "lean" cloud environment is configured with:

* Network access: **Full** (so `release.lean-lang.org` and the Mathlib
  cache are reachable).
* Setup script (env-level, snapshotted): installs elan + the pinned
  Lean toolchain (`leanprover/lean4:v4.28.0`), symlinks elan/lean/lake
  into `/usr/local/bin` so non-login shells see them.
* SessionStart hook (in repo `.claude/settings.json`,
  `scripts/cloud-cache-prime.sh`): runs `lake exe cache get` per
  session to prime Mathlib oleans (≈30s, vs. multi-hour from-scratch
  build).

### Local agents

* Aristotle (remote Lean prover, MCP) — for bounded local proof goals.
* `codex exec` — local sub-agent for top-down rounds on Solution.lean.
* This file (Claude main) — orchestrates everything.

## What this methodology replaces

Previously the project ran in `/loop 15m` ticks driven by `ref/PROMPT.md`,
with each tick consuming Aristotle results, refreshing the README
progress bar, and pushing. That loop is paused while we do Phases A–C
above. Once the blueprint is fully gap-surfaced (end of Phase A) and
strategies are written (Phase B), tick-style execution can resume in
Phase C, but driven by the blueprint's leaves rather than ad-hoc sorry
selection.

## Status checklist

* [ ] Phase A — every leaf in the dep graph is either Mathlib-backed
      (green) or a clean stand-alone gap statement (orange).
* [ ] Phase B — every gap leaf has a written strategy paragraph in the
      blueprint, vetted via ChatGPT + Grok.
* [ ] Phase C — bottom-up cloud formalization is closing leaves at a
      steady cadence; PR cadence becomes the project's heartbeat.
