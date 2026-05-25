import Jacobian.Periods.Polygon4g
import Jacobian.Periods.Orientable
import Jacobian.Periods.EdgeWord
import Mathlib.Geometry.Manifold.IsManifold.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2

/-!
# Stage A surface-classification opaque data

This module collects the opaque type-level placeholders needed by the
Stage A surface-classification decomposition. They are extracted into
their own module so that:

* the production refinement modules (`RadoTriangulation`, `EdgeWord`-side
  Tietze pipeline, etc.) can name the data without importing the
  high-level `SurfaceClassification` umbrella, avoiding cycles;
* the umbrella file in turn imports them as a single small module.

## Contents

* `Triangulation M` — opaque finite-triangulation datum.
* `EdgeWordPresentation M` — opaque edge-word-presentation datum.
* `PolygonalQuotientPresentation M` — *bundled* (not opaque) datum
  carrying the quotient map from the disk.
-/

namespace JacobianChallenge.Periods

open scoped Manifold

/--
Bundled polygonal-quotient datum: a continuous surjection
`q : DiskC → M` whose fibres coincide with the side-pairing
equivalence `Polygon4g.SideRel genus`.
-/
structure PolygonalQuotientPresentation
    (M : Type) [TopologicalSpace M] where
  /--
The genus parameter — the topological genus of the surface
  presented by this datum.
-/
  genus : ℕ
  /--
The continuous surjection from the closed disk witnessing the
  presentation.
-/
  proj : DiskC → M
  /-- Continuity of `proj`. -/
  cts : Continuous proj
  /--
Surjectivity of `proj` (every point of `M` is presented by some
  disk point).
-/
  surj : Function.Surjective proj
  /--
Kernel: `proj z = proj w` exactly when the standard `4*genus`-gon
  side identification relates `z` and `w`.
-/
  kernel : ∀ z w : DiskC, proj z = proj w ↔ Polygon4g.SideRel genus z w


def Triangulation (_M : Type) [TopologicalSpace _M] : Type :=
  PUnit

/--
**Edge-word presentation of `M`.** Bundles the data of "M presented
as a `2k`-gon with side identifications given by some edge-pairing
word `w` of length `2k`".

This is the non-standardized generalization of
`PolygonalQuotientPresentation`.
-/
structure EdgeWordPresentation (M : Type) [TopologicalSpace M] where
  /-- The genus parameter of the alphabet used by the word. -/
  g : ℕ
  /-- The boundary word labelling the 2k-gon. -/
  word : EdgeWord g
  /--
The continuous surjection from the closed disk witnessing the
  presentation.
-/
  proj : DiskC → M
  /-- Continuity of `proj`. -/
  cts : Continuous proj
  /-- Surjectivity of `proj`. -/
  surj : Function.Surjective proj
  /--
Kernel: `proj z = proj w` exactly when the word's side
  pairing relates `z` and `w`.
-/
  kernel : ∀ z w : DiskC, proj z = proj w ↔ EdgeWord.sidePairingRel g word z w

end JacobianChallenge.Periods
