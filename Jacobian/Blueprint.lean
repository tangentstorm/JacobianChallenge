-- sec01
import Jacobian.Blueprint.Sec01.VanishingOrder
import Jacobian.Blueprint.Sec01.Divisor
import Jacobian.Blueprint.Sec01.DivisorDegree
import Jacobian.Blueprint.Sec01.DivisorDiscrete
import Jacobian.Blueprint.Sec01.DivisorFiniteSupport
import Jacobian.Blueprint.Sec01.MeromorphicFunction
import Jacobian.Blueprint.Sec01.PrincipalDivisor
import Jacobian.Blueprint.Sec01.PrincipalDivisors
import Jacobian.Blueprint.Sec01.PrincipalDegreeZero
import Jacobian.Blueprint.Sec01.MeromorphicToCp1
import Jacobian.Blueprint.Sec01.MeromorphicAsCp1Map
import Jacobian.Blueprint.Sec01.RiemannRochSpace
import Jacobian.Blueprint.Sec01.RiemannRochSpaceVector
import Jacobian.Blueprint.Sec01.InputDivisors

-- sec02
import Jacobian.Blueprint.Sec02.CotangentFiberNorm
import Jacobian.Blueprint.Sec02.HolomorphicSupNorm
import Jacobian.Blueprint.Sec02.ChartCoefficientBound
import Jacobian.Blueprint.Sec02.MontelCompactness
import Jacobian.Blueprint.Sec02.HoneUnitBallCompact
import Jacobian.Blueprint.Sec02.FdFromRiesz
import Jacobian.Blueprint.Sec02.InputFiniteDimensionality
import Jacobian.Blueprint.Sec02.FdHolomorphicOneForms
import Jacobian.Blueprint.Sec02.AnalyticGenusDef
import Jacobian.Blueprint.Sec02.FdHolomorphicOneFormsThm
import Jacobian.Blueprint.Sec02.GenusZeroClassification

-- sec03
import Jacobian.Blueprint.Sec03.HolomorphicFormIsClosed
import Jacobian.Blueprint.Sec03.StokesOnRsWithBoundary
import Jacobian.Blueprint.Sec03.SymplecticBasis
import Jacobian.Blueprint.Sec03.PolygonalModel
import Jacobian.Blueprint.Sec03.PrimitiveOnPolygon
import Jacobian.Blueprint.Sec03.BilinearFromStokes
import Jacobian.Blueprint.Sec03.HermitianPositivity
import Jacobian.Blueprint.Sec03.PeriodVectorsFullRealRank
import Jacobian.Blueprint.Sec03.PeriodPairing
import Jacobian.Blueprint.Sec03.PeriodLattice

-- sec04
import Jacobian.Blueprint.Sec04.AnalyticJacobian

-- sec05
import Jacobian.Blueprint.Sec05.AbelJacobiDef
import Jacobian.Blueprint.Sec05.AbelJacobiInjective
import Jacobian.Blueprint.Sec05.AjDivisorHom
import Jacobian.Blueprint.Sec05.AbelExistence
import Jacobian.Blueprint.Sec05.PrincipalDeg0SimpleSupportDeg1
import Jacobian.Blueprint.Sec05.RiemannHurwitzDeg1
import Jacobian.Blueprint.Sec05.AbelPointSeparation

-- sec06
import Jacobian.Blueprint.Sec06.TracePullback
import Jacobian.Blueprint.Sec06.PushPullFunctoriality
import Jacobian.Blueprint.Sec06.PushforwardPullback

-- sec07
import Jacobian.Blueprint.Sec07.ChallengeApi

/-!
# Blueprint stubs index

Imports every per-label stub file under `Jacobian/Blueprint/SecXX/`.
These files exist to make every blueprint dep-graph node "pick-up-able":
each blueprint label has a corresponding Lean declaration (real or
`sorry`-stubbed), so a contributor can pick any node, see its statement,
and discharge the proof.

Phase A+D audit doc: `ref/blueprint-audit.md`.

This module is intentionally separate from the production `Jacobian.*`
modules: the stubs here are scaffolds, not production decls. When a
blueprint label has a real production decl elsewhere, the blueprint TeX
should `\lean{...}` the production name; the matching `Blueprint/`
file becomes obsolete and can be removed.
-/
