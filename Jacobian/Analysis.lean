import Jacobian.Analysis.Rado
import Jacobian.Analysis.Tietze
import Jacobian.Analysis.PolygonalModel
import Jacobian.Analysis.DeRham
import Jacobian.Analysis.HodgeDecomposition
import Jacobian.Analysis.HodgeDeRham
import Jacobian.Analysis.Dolbeault
import Jacobian.Analysis.SerreDuality
import Jacobian.Analysis.BundledForms
import Jacobian.Analysis.SobolevElliptic

/-!
# `Jacobian.Analysis` — the major classical-analysis gaps

This module is the umbrella for the red-border umbrellas in the
project's blueprint dependency graph: classical results outside
current Mathlib v4.28.0 that block the analytic-period-lattice route
to the Jacobian.  Most gaps live under `Jacobian/Analysis/<Node>/`
containing an `Overview.lean` (headline statement + named sub-leaves,
all real-typed `sorry` declarations) and a `README.md` (master plan).
Once a gap has been refined to a single sorry-free Lean file, the
content is folded into `Jacobian/Analysis/<Node>.lean` directly with
the master-plan content moved into the file's top-of-module docstring
(see `Jacobian.Analysis.Tietze` for the worked example).

| Gap | Headline | Build target | Status |
|---|---|---|---|
| R1 | Radó's triangulation | `Jacobian.Analysis.Rado` | sub-leaves |
| R2 | Tietze normal form | `Jacobian.Analysis.Tietze` | local sorry-free |
| R3 | Polygonal-model theorem | `Jacobian.Analysis.PolygonalModel` | sub-leaves |
| R4 | De Rham theorem | `Jacobian.Analysis.DeRham` | sub-leaves |
| R5 | Hodge decomposition | `Jacobian.Analysis.HodgeDecomposition` | sub-leaves |
| R6 | Hodge / de Rham rank | `Jacobian.Analysis.HodgeDeRham` | sub-leaves |
| R7 | Dolbeault isomorphism | `Jacobian.Analysis.Dolbeault` | sub-leaves |
| R8 | Serre duality on a Riemann surface | `Jacobian.Analysis.SerreDuality` | sub-leaves |
| R9 | Bundled differential forms `Ω^k(M)` | `Jacobian.Analysis.BundledForms` | sub-leaves |
| R10 | Sobolev / elliptic regularity | `Jacobian.Analysis.SobolevElliptic` | sub-leaves |

"Local sorry-free" means every sub-leaf in the corresponding file is
type-checked without `sorry`; the headline may still transit through
a `sorry` in another module (for R2: StageA's
`orientable_edgeWord_tietzeEq_standardWord`).

R9 (bundled `Ω^k`) and R10 (Sobolev/elliptic) are *recursive sub-gaps*
that surface inside R4/R5/R7 and have been promoted to their own
top-level dep-graph nodes because they are shared infrastructure and
substantial in their own right (R10 alone is the single largest
sub-gap in the entire tree, ~2500–4000 LOC).

Each sub-module states real-typed propositions; the blueprint
counterpart is `tex/sections/12-classical-analysis-gaps.tex`.
-/
