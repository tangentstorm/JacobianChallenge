# TOP-DOWN Refinement Task: The Riemann–Roch Theorem (Umbrella)

**Your Mission:**
You are assigned to work **Top-Down** on the highest-level "Umbrella" theorem for the Riemann–Roch formula.

**Target:**
The core obligation is `riemann_roch_umbrella_exists` (ID 1) in `Jacobian/Blueprint/Sec02/InputRiemannRoch.lean`.
This theorem asserts the existence of the Riemann–Roch formula $\ell(D) - \ell(K-D) = \deg(D) + 1 - g$ for any divisor $D$.

**Context:**
A temporary "toy" instance using `PUnit` has been provided to unblock the top-level build (see `InputRiemannRoch.lean`). **Your job is to REPLACE this stub with the real mathematical construction.**

**The Gap:**
Mathlib v4.28.0 has no Riemann–Roch theorem for Riemann surfaces. It lacks the sheaf-cohomology definition of $\ell(D)$ and the topological definition of genus $g$. You must build the bridge between the high-level formula and the implementation-level sheaf cohomology.

**Your Strategy (Top-Down):**
1. Replace the `PUnit` stub in `riemann_roch_umbrella_exists` with the production definitions:
   - $h^0(D)$ and $h^1(D)$ via `RSSheafCohomology`.
   - $g$ via `RSGenus`.
   - $\deg(D)$ via the Divisor API.
2. Break down the resulting identity into:
   - Riemann's Inequality ($\ell(D) \ge \deg(D) + 1 - g$).
   - Serre Duality ($h^1(L) = h^0(K \otimes L^{-1})$).
   - Euler Characteristic calculation for line bundles.
3. Replace the top-level `sorry` with a **sorry-free assembly**.
4. Use the infrastructure in `Jacobian/HolomorphicForms/RiemannRoch.lean` as your integration point.
5. Continue recursively by breaking down the new analytic/sheaf-theoretic sorries.

**Rules:**
- Maintain a clean `lake build`.
- Update the Blueprint in `tex/sections/03-riemann-roch.tex`.
- Focus on the mathematical architecture: ensure the definitions of degree, genus, and $\ell(D)$ are consistent across the bridge.
