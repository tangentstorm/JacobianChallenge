import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Analysis.Complex.Basic

/-! # Blueprint stub: `thm:fd-from-riesz`

Section 2 of `tex/sections/02-holomorphic-forms-and-genus.tex`.

Riesz's theorem: a normed `ℂ`-vector space whose closed unit ball is
compact is finite-dimensional.

This is a thin re-export of Mathlib's
`FiniteDimensional.of_isCompact_closedBall` (file
`Mathlib/Analysis/Normed/Module/FiniteDimension.lean`, line 492). We
introduce a blueprint-side decl name so the dep-graph node has a
matching `\lean{}` annotation and the chain reads cleanly to a
contributor without going outside `JacobianChallenge.Blueprint`. -/

namespace JacobianChallenge.Blueprint

/-- Riesz's theorem (blueprint re-export): if a closed ball of positive
radius in a normed `ℂ`-vector space is compact, the space is
finite-dimensional. -/
theorem fd_from_riesz
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] {r : ℝ} (_hr : 0 < r)
    (_h : IsCompact (Metric.closedBall (0 : E) r)) :
    FiniteDimensional ℂ E := by
  -- TODO: exact FiniteDimensional.of_isCompact_closedBall₀ ℂ _hr _h
  -- (field argument first; `[CompleteSpace ℂ]` is supplied by Mathlib.)
  sorry

end JacobianChallenge.Blueprint
