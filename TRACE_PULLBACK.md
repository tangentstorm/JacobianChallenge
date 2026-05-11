# TOP-DOWN Refinement Task: The Trace-Pullback Identity

**Your Mission:**
You are assigned to work **Top-Down** on one of the project's most mathematically involved "Anti-Hack" theorems: the Trace-Pullback Identity.

**Target:**
The core obligation is `trace_pullback_identity` (ID 124) in `Jacobian/HolomorphicForms/TraceBundled.lean`.
The theorem asserts that for a holomorphic map $f: X \to Y$ and a holomorphic 1-form $\omega$ on $X$, the integral of the trace $\sum \omega \circ (f|^{-1})_i$ over a cycle in $Y$ is equal to the integral of $\omega$ over the pullback of that cycle.

**The Gap:**
Mathlib v4.28.0 has no built-in theory for branched coverings of complex manifolds, no formal definition of "trace" for differential forms, and no pre-packaged identity principle for global holomorphic 1-forms. You must build the conceptual bridge.

**Your Strategy (Top-Down):**
1. Start at `trace_pullback_identity`. Break it down into sub-obligations:
   - Defining the trace of a form along a branched cover.
   - Proving that the trace of a holomorphic form is holomorphic on the target (away from branch points).
   - Extending the identity from the regular locus to the entire surface (Identity Principle).
   - Verifying the cycle-level identity for local inverse branches.
2. Create a **sorry-free assembly** by wiring these new lemmas together.
3. Stub out the missing analytic infrastructure in new files like `Jacobian/TraceDegree/TraceDefinition.lean`.
4. Recursively refine your new `sorry`s toward the Mathlib leaves.

**Rules:**
- Maintain a clean `lake build`.
- Update the corresponding Blueprint section in `tex/sections/09-degree-trace-push-pull.tex`.
- This is a high-level architectural task. Focus on defining the right intermediate structures to make the proof manageable.
