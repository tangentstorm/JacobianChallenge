import Jacobian.ComplexTorus.Basic
import Jacobian.ComplexTorus.Mk
import Jacobian.ComplexTorus.MapMk
import Jacobian.ComplexTorus.Surjective
import Jacobian.ComplexTorus.NhdsZero
import Jacobian.ComplexTorus.IsClosedSubgroup
import Jacobian.ComplexTorus.MapInjective
import Jacobian.ComplexTorus.Neg
import Jacobian.ComplexTorus.Add
import Jacobian.ComplexTorus.Smul
import Jacobian.ComplexTorus.OfClm
import Jacobian.ComplexTorus.Connected
import Jacobian.ComplexTorus.Nhds
import Jacobian.ComplexTorus.Dense
import Jacobian.ComplexTorus.FirstCountable
import Jacobian.ComplexTorus.PathConnected
import Jacobian.ComplexTorus.Compact
import Jacobian.ComplexTorus.ContIff
import Jacobian.ComplexTorus.MkImage
import Jacobian.ComplexTorus.MkPreimage
import Jacobian.ComplexTorus.MkBundled
import Jacobian.ComplexTorus.MkRange
import Jacobian.ComplexTorus.MapNegSub
import Jacobian.ComplexTorus.MkInjective
import Jacobian.ComplexTorus.MapClmInjective
import Jacobian.ComplexTorus.MapClmSurjective
import Jacobian.ComplexTorus.MkHomKer
import Jacobian.ComplexTorus.MapZero
import Jacobian.ComplexTorus.GenericQuotient
import Jacobian.ComplexTorus.ZLatticeFundDom
import Jacobian.ComplexTorus.IsolationAtZero
import Jacobian.ComplexTorus.MkInjOnSmallBall
import Jacobian.ComplexTorus.ChartBall
import Jacobian.ComplexTorus.LocalSection
import Jacobian.ComplexTorus.LocalSectionRightInv
import Jacobian.ComplexTorus.LocalSectionContinuous
import Jacobian.ComplexTorus.Chart
import Jacobian.ComplexTorus.ChartedSpace
import Jacobian.ComplexTorus.TransitionSubMem
import Jacobian.ComplexTorus.TransitionSubContinuous
import Jacobian.ComplexTorus.TransitionLocallyTranslate
import Jacobian.ComplexTorus.TransitionContDiffOn
import Jacobian.ComplexTorus.IsManifold

/-!
# Complex torus infrastructure

Top-level module that re-exports the production Queue B target files.
Other modules can import `Jacobian.ComplexTorus` instead of pulling each
sibling in by hand.

**Excluded on purpose:**
- `ZLatticeRecon` — name-discovery scratch with the `fullComplexLatticeOfZLattice`
  bridge; will be promoted into a clean module once the chart layer is in.
- `ManifoldRecon` — narrative reconnaissance with `sorry` placeholders; not
  intended as public API.
- `DiscretenessRecon` — comment-only Q&A document for the `FullComplexLattice`
  refactor; not API.

These three files still build (they are valid Lean modules) and remain on
disk for now, but they are not re-exported. They will be removed or migrated
out of `Jacobian/ComplexTorus/` when the manifold layer is complete.
-/
