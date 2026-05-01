-- sec01
import Jacobian.Blueprint.Sec01.VanishingOrder
import Jacobian.Blueprint.Sec01.Divisor
import Jacobian.Blueprint.Sec01.DivisorDegree
import Jacobian.Blueprint.Sec01.DivisorDiscrete
import Jacobian.Blueprint.Sec01.DivisorFiniteSupport
import Jacobian.Blueprint.Sec01.MeromorphicFunction
import Jacobian.Blueprint.Sec01.MeromorphicFunctionConcrete
import Jacobian.Blueprint.Sec01.MeromorphicFunctionStructure
import Jacobian.Blueprint.Sec01.MeromorphicEqHolomorphicToCp1
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
import Jacobian.Blueprint.Sec02.DegreeOneNoRamification
import Jacobian.Blueprint.Sec02.DegreeOneBijective
import Jacobian.Blueprint.Sec02.DegreeOneIsomorphism
import Jacobian.Blueprint.Sec02.BranchedDegree
import Jacobian.Blueprint.Sec02.BranchLocusFinite
import Jacobian.Blueprint.Sec02.LocalBiholoUnramified
import Jacobian.Blueprint.Sec02.InputDegreeOneIsomorphism
import Jacobian.Blueprint.Sec02.InputRiemannRoch

-- sec03
import Jacobian.Blueprint.Sec03.HolomorphicFormIsClosed

-- sec03
import Jacobian.Blueprint.Sec03.StokesOnRSWithBoundary

-- sec03
import Jacobian.Blueprint.Sec03.SymplecticBasis

-- sec05
import Jacobian.Blueprint.Sec05.AbelExistence
import Jacobian.Blueprint.Sec05.AjDivisorHom
import Jacobian.Blueprint.Sec05.PrincipalDeg0SimpleSupportDeg1
import Jacobian.Blueprint.Sec05.InputAbelTheorem
import Jacobian.Blueprint.Sec05.RiemannHurwitzDeg1

/-!
# Blueprint stubs index

Imports every per-label stub file under `Jacobian/Blueprint/SecXX/`.
These files exist to make every blueprint dep-graph node "pick-up-able":
each blueprint label has a corresponding Lean declaration (real or
`sorry`-stubbed), so a contributor can pick any node, see its statement,
and discharge the proof.

Phase A audit doc: `ref/blueprint-audit.md`. As of this commit, sec01 is
fully covered; sec02 is partial (5 of 11 stubs); sec03–sec07 still need
stubs (see Tables 2–4 of the audit doc for the full plan).

This module is intentionally separate from the production `Jacobian.*`
modules: the stubs here are scaffolds, not production decls. When a
blueprint label has a real production decl elsewhere, the blueprint TeX
should `\lean{...}` the production name; the matching `Blueprint/`
file becomes obsolete and can be removed.
-/
