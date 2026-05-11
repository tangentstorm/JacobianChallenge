# TOP-DOWN Refinement Task: Arzelà–Ascoli for Holomorphic 1-Forms

**Your Mission:**
You are assigned to work **Top-Down** on the compactness of the unit ball of holomorphic 1-forms on a compact Riemann surface.

**Target:**
The core obligation is `holomorphicOneForm_arzela_ascoli` (ID 31) in `Jacobian/HolomorphicForms/CompactRiemannSurface.lean`.
This theorem is the analytic backbone for proving that the space of holomorphic 1-forms is finite-dimensional.

**The Gap:**
Mathlib v4.28.0 has `Topology.UnitBall` and `Topology.Algebra.InfiniteSum`, but it lacks a pre-packaged Arzelà–Ascoli theorem for sections of complex cotangent bundles. You need to bridge the gap between abstract functional analysis and the geometry of Riemann surfaces.

**Your Strategy (Top-Down):**
1. Start at `holomorphicOneForm_arzela_ascoli`. Break it down into sub-obligations:
   - Equicontinuity of holomorphic sections (via local Cauchy estimates).
   - Pointwise boundedness (via the maximum principle or sup-norm properties).
   - Diagonal extraction argument (Arzelà–Ascoli).
2. Create a **sorry-free assembly** by wiring these new lemmas together.
3. Stub out the missing analytic infrastructure in new files like `Jacobian/HolomorphicForms/Equicontinuity.lean`.
4. Recursively refine your new `sorry`s.

**Rules:**
- Use `lake build` to verify your assemblies.
- Update the corresponding `.tex` sections in `tex/sections/02-holomorphic-forms-finite-dim.tex`.
- Keep pushing the `sorry`s toward the Mathlib leaves.
