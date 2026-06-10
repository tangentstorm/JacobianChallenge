import Mathlib.Topology.UniformSpace.LocallyUniformConvergence
import Mathlib.Analysis.Complex.Basic

namespace JacobianChallenge.HolomorphicForms

theorem eqOn_of_tendstoLocallyUniformlyOn_same
    {U : Set ℂ} (_hU : IsOpen U)
    {F : ℕ → ℂ → ℂ} {f g : ℂ → ℂ}
    (hf : TendstoLocallyUniformlyOn F f Filter.atTop U)
    (hg : TendstoLocallyUniformlyOn F g Filter.atTop U) :
    Set.EqOn f g U :=
  hf.unique hg

end JacobianChallenge.HolomorphicForms
