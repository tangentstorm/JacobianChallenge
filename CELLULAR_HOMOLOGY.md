# TOP-DOWN Refinement Task: Cellular vs. Singular Homology

**Your Mission:**
You are assigned to work **Top-Down** on a massive algebraic topology gap in the Jacobian Challenge: the isomorphism between Cellular and Singular Homology, specifically applied to the fundamental polygon (`Polygon4g`).

**Target:**
The core obligation is `polygon4g_cellular_singular_iso` (ID 84) in `Jacobian/Periods/Polygon4gCellular.lean`. 
The mathematical goal is to prove that the algebraic boundary complex of the 4g-gon exactly computes the first singular homology group of the quotient surface.

**The Gap:**
Mathlib v4.28.0 has `Topology.CWComplex` and it has `AlgebraicTopology.SingularHomology`, but it has **NO** `CellularChainComplex`, no cellular boundary formula, and no Hurewicz homomorphism bridging fundamental groups to singular homology for general spaces.

**Your Strategy (Top-Down):**
1. Do **NOT** stop or exit just because this is a huge Mathlib gap. We know it is. Your job is to build the bridge.
2. Start at the target theorem in `Polygon4gCellular.lean`. Break the isomorphism down into strictly smaller, named algebraic topology sub-obligations (using `sorry`).
3. Replace the top-level `sorry` with a **sorry-free assembly** that combines your new lemmas.
4. Create new files in `Jacobian/Periods/` (e.g., `CellularChainComplex.lean`, `Hurewicz.lean`) to stub out the missing algebraic topology infrastructure.
5. Recursively break down your new `sorry`s. If you need the Hurewicz map, define it (with a `sorry` for functoriality/well-definedness if needed), and prove the isomorphism assuming it.
6. Push the `sorry`s as deep into the Mathlib leaves as possible. 

**Rules:**
- Work in the designated workspace directory.
- Ensure your intermediate assemblies compile (`lake build`). 
- A successful iteration leaves the top-level theorem `sorry`-free, supported by 3-5 smaller, clearly documented `sorry`'d lemmas.
- Update the Blueprint in `tex/sections/05-polygonal-model.tex` to document the new homology API you are designing.
