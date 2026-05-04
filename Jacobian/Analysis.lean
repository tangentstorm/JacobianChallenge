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
to the Jacobian.  Each gap has its own sub-directory under
`Jacobian/Analysis/<Node>/` containing an `Overview.lean` (headline
statement + named sub-leaves, all real-typed `sorry` declarations)
and a `README.md` (master plan: classical proof, Lean realisation
route, plain-English description).

| Gap | Headline | Build target |
|---|---|---|
| R1 | Radó's triangulation | `Jacobian.Analysis.Rado` |
| R2 | Tietze normal form | `Jacobian.Analysis.Tietze` |
| R3 | Polygonal-model theorem | `Jacobian.Analysis.PolygonalModel` |
| R4 | De Rham theorem | `Jacobian.Analysis.DeRham` |
| R5 | Hodge decomposition | `Jacobian.Analysis.HodgeDecomposition` |
| R6 | Hodge / de Rham rank | `Jacobian.Analysis.HodgeDeRham` |
| R7 | Dolbeault isomorphism | `Jacobian.Analysis.Dolbeault` |
| R8 | Serre duality on a Riemann surface | `Jacobian.Analysis.SerreDuality` |
| R9 | Bundled differential forms `Ω^k(M)` | `Jacobian.Analysis.BundledForms` |
| R10 | Sobolev / elliptic regularity | `Jacobian.Analysis.SobolevElliptic` |

R9 (bundled `Ω^k`) and R10 (Sobolev/elliptic) are *recursive sub-gaps*
that surface inside R4/R5/R7 and have been promoted to their own
top-level dep-graph nodes because they are shared infrastructure and
substantial in their own right (R10 alone is the single largest
sub-gap in the entire tree, ~2500–4000 LOC).

Each sub-`Overview.lean` states real-typed propositions backed by
`sorry` proofs, importable as if they were Mathlib lemmas.  The
blueprint counterpart is `tex/sections/12-classical-analysis-gaps.tex`.
-/
