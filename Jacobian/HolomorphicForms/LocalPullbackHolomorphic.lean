import Jacobian.HolomorphicForms.BranchedCover
import Jacobian.HolomorphicForms.HolomorphicMap

/-!
# Local-pullback holomorphic-variation infrastructure (M4 prep)

This file establishes a key prerequisite for discharging the project's
single custom axiom

```
axiom localPullbackAt_holomorphic
    {f : X → Y} (h : BranchedCoverData X Y f)
    (hcompat : h.RamificationIndexCompatible)
    (hf : IsHolomorphic f)
    (ω : HolomorphicOneForm ℂ X)
    (x : X) (hx : h.ramificationIndex x = 1) :
    IsHolomorphicAt (localPullbackAt h hf ω x hx) (f x)
```

(declared at `Jacobian/TraceDegree/TraceDefinition.lean:220`; see
`ref/axiom-audit.md` §1 for the 13 transitive dependents).

The axiom's proof requires that, locally near `f x`, the chart-pulled
back function `y' ↦ cotangentPushforward f (localInverseAt y')
(η.toFun (localInverseAt y'))` is analytic. The existing chart-local
helper `cotangentPushforward_eq_toSpanSingleton_scalar` (TraceSpec.lean
~L1047) gives an explicit `toSpanSingleton ℂ`-form for the cotangent
pushforward — but it requires the preimage point to be unramified
(`h.ramificationIndex x' = 1`). To apply this formula pointwise in a
neighborhood of `f x`, we need to know that **the local inverse stays
in the unramified locus eventually**.

This file provides that single missing fact as `BranchedCoverData.
localInverseAt_eventually_unramified`. The downstream M4 commits will
chain it with the existing TraceSpec chart-local helpers to discharge
the axiom.
-/

namespace JacobianChallenge.HolomorphicForms

open scoped Manifold Topology
open Filter Set

variable {X Y : Type*}
  [TopologicalSpace X] [ChartedSpace ℂ X]
  [TopologicalSpace Y] [ChartedSpace ℂ Y]

omit [ChartedSpace ℂ X] [ChartedSpace ℂ Y] in
/--
**Eventually-unramified at the local inverse.**

For an unramified preimage `x` of `f x` (i.e.
`h.ramificationIndex x = 1`), the local inverse `h.localInverseAt x hx`
maps a neighborhood of `f x` into the unramified locus of `f`. Hence,
for all `y'` in a neighborhood of `f x`, the preimage `h.localInverseAt
x hx y'` has ramification index `1`.

This is the bridge that lets pointwise unramified-only formulas like
`cotangentPushforward_eq_toSpanSingleton_scalar` (TraceSpec.lean
~L1047) apply uniformly in a neighborhood of `f x`, enabling the
holomorphic-variation arguments needed for
`localPullbackAt_holomorphic`.

**Proof idea.** The local-bijection property of `BranchedCoverData`
at the unramified point `x` gives an open set `U ⊆ X` with
`x ∈ U` and `f` bijective from `U` onto an open `V ⊆ Y` with `f x ∈ V`.
The ramification set is finite (`h.ramified_finite`); a finite subset
of `X` minus the singleton `{x}` is disjoint from `U` after
intersection with a smaller open neighborhood `U'` of `x` (or simply
`U \ ({y | h.ramificationIndex y ≠ 1} \ {x})`, which is still open if
the ramification set is closed — for Riemann surfaces, finite sets are
closed since `T2Space` is in scope).

Since `localInverseAt y' ∈ U` eventually (by
`localInverseAt_preimage_mem_nhds`-style arguments), and `U'` is also
open with `localInverseAt (f x) = x ∈ U'`, we get
`localInverseAt y' ∈ U'` eventually, hence
`h.ramificationIndex (localInverseAt y') = 1`.
-/
theorem BranchedCoverData.localInverseAt_eventually_unramified
    [T2Space X] [T2Space Y] [Nonempty X]
    {f : X → Y} (h : BranchedCoverData X Y f)
    (x : X) (hx : h.ramificationIndex x = 1) :
    ∀ᶠ y' in 𝓝 (f x), h.ramificationIndex (h.localInverseAt x hx y') = 1 := by
  classical
  -- Step 1: extract the local bijection witness from BranchedCoverData
  obtain ⟨U, V, hUopen, hVopen, hxU, hfxV, hbij, hright_branch, hleft_branch⟩ :=
    h.localInverse_is_inverse hx
  -- Step 2: ramified set without x is closed (finite ⊂ T2 ⇒ closed; finite minus a point is still finite).
  set ramSet : Set X := {y | h.ramificationIndex y ≠ 1} \ {x} with hramSet_def
  have hramSet_finite : ramSet.Finite := by
    apply Set.Finite.subset h.ramified_finite
    intro y hy; exact hy.1
  have hramSet_closed : IsClosed ramSet := hramSet_finite.isClosed
  -- Step 3: U' := U \ ramSet is open, contains x, and is bijective with V' under f.
  set U' : Set X := U \ ramSet with hU'_def
  have hU'_open : IsOpen U' := hUopen.sdiff hramSet_closed
  have hxU' : x ∈ U' := by
    refine ⟨hxU, ?_⟩
    -- x ∉ ramSet because x ∉ {y | h.ramificationIndex y ≠ 1} \ {x}
    -- (either h.ramificationIndex x = 1, which is hx, OR x ∈ {x})
    intro hramX
    -- hramX : x ∈ ramSet = {y | h.ramificationIndex y ≠ 1} \ {x}
    exact hramX.2 rfl
  -- Step 4: For y' near f x, localInverseAt y' ∈ U' (eventually).
  -- Since the local inverse maps V to U bijectively, and stays at x at y' = f x,
  -- and U' is an open nhd of x within U, the preimage of U' under localInverseAt is open.
  have h_localInv_at_fx : h.localInverseAt x hx (f x) = x := by
    have := hleft_branch x hxU
    -- hleft_branch x hxU : localInverseAt (f x) = x
    exact this
  -- Now: localInverseAt is continuous on V (because it's the inverse of a continuous
  -- bijection on a compact-ish setting). But we don't actually need full continuity —
  -- we need it eventually maps into U'. We'll show this directly via the
  -- right-branch property + the closedness of ramSet.
  -- The eventually-in-V part:
  have h_evt_in_V : ∀ᶠ y' in 𝓝 (f x), y' ∈ V :=
    hVopen.mem_nhds hfxV
  -- For y' ∈ V, f (localInverseAt y') = y' (by hright_branch), so localInverseAt y' ∈ U
  -- (because hbij : Set.BijOn f U V, so the unique preimage in U exists).
  -- Specifically the value-of-localInverseAt-on-V is in U:
  have h_localInv_in_U : ∀ y' ∈ V, h.localInverseAt x hx y' ∈ U := by
    intro y' hy'V
    -- Use BijOn surjOn to get preimage x' ∈ U with f x' = y'.
    obtain ⟨x', hx'U, hfx'⟩ := hbij.surjOn hy'V
    -- localInverseAt y' = invFunOn f U y' should equal x' by uniqueness.
    -- We can use the leftInvOn property: localInverseAt (f x') = x' for x' ∈ U.
    have h_local_at_y : h.localInverseAt x hx y' = x' := by
      rw [← hfx']
      exact hleft_branch x' hx'U
    rw [h_local_at_y]; exact hx'U
  -- Combine: for y' near f x and y' ∈ V, localInverseAt y' ∈ U \ ramSet,
  -- provided we can also exclude localInverseAt y' ∈ ramSet eventually.
  -- The key: localInverseAt is continuous at f x (with value x ∉ ramSet),
  -- so eventually localInverseAt y' ∉ ramSet (since ramSet is closed).
  -- But we don't yet have continuity of localInverseAt directly. However:
  -- Approach: since ramSet ∩ U is finite (subset of finite set h.ramified_finite minus x),
  -- and U is open, U ∩ ramSet = {x₁, …, xₙ} where each xᵢ ≠ x and ramificationIndex xᵢ ≠ 1.
  -- For each such xᵢ, f xᵢ ≠ f x (because bij on U: if f xᵢ = f x then xᵢ = x by injectivity,
  -- contradicting xᵢ ≠ x). So we can separate y' from {f x₁, …, f xₙ} by an open nhd of f x
  -- (T2-ish on Y, but we have ChartedSpace ℂ Y which is T2).
  -- Inside that smaller nhd, y' ∉ {f x₁, …, f xₙ}, so localInverseAt y' ∉ {x₁, …, xₙ},
  -- so localInverseAt y' ∉ ramSet.
  -- Build the bad point set in Y and its complement nhd.
  set bad_X : Set X := U ∩ ramSet with hbad_X_def
  have hbad_X_finite : bad_X.Finite := hramSet_finite.subset (fun _ h' => h'.2)
  set bad_Y : Set Y := f '' bad_X with hbad_Y_def
  have hbad_Y_finite : bad_Y.Finite := hbad_X_finite.image f
  -- f x ∉ bad_Y because x ∉ ramSet (hxU' shows x ∈ U \ ramSet, so x ∉ ramSet).
  have hfx_not_bad : f x ∉ bad_Y := by
    intro hfxbad
    obtain ⟨x', hx'bad, hfx'eq⟩ := hfxbad
    -- x' ∈ U ∩ ramSet, f x' = f x.
    have hx'U : x' ∈ U := hx'bad.1
    -- Use injectivity (hbij : BijOn f U V) to conclude x' = x.
    have hx'x : x' = x := hbij.injOn hx'U hxU hfx'eq
    -- But x' ∈ ramSet and x ∉ ramSet (per hxU').
    have : x ∈ ramSet := hx'x ▸ hx'bad.2
    exact hxU'.2 this
  -- Since bad_Y is finite and Y is T2 (ChartedSpace ℂ Y gives T2 via ℂ),
  -- we get an open nhd W of f x disjoint from bad_Y.
  -- Use Y being T2 (charted on ℂ, which is T2; need [T2Space Y] though — let's see if
  -- ChartedSpace ℂ Y gives T2 automatically — it does NOT in Lean, only if we have a
  -- T2 instance separately. We need an explicit assumption).
  -- Actually: in Lean, ChartedSpace doesn't carry T2. But every finite set in ANY
  -- topological space is closed iff the space is T1. We need at least T1 on Y.
  -- For a Hausdorff (T2) space, finite sets are closed.
  -- The TraceSpec context has [T2Space Y] in scope. We need to add it as a hypothesis.
  -- See the theorem signature — let's add [T2Space Y].
  have hbad_Y_closed : IsClosed bad_Y := hbad_Y_finite.isClosed
  have h_compl_nhd : bad_Yᶜ ∈ 𝓝 (f x) :=
    hbad_Y_closed.isOpen_compl.mem_nhds hfx_not_bad
  -- Combine: y' ∈ V ∩ bad_Yᶜ eventually.
  filter_upwards [h_evt_in_V, h_compl_nhd] with y' hy'V hy'bad
  -- Now: localInverseAt y' ∈ U (by h_localInv_in_U).
  -- Need: localInverseAt y' ∉ ramSet, i.e. ramificationIndex (localInverseAt y') = 1 or
  -- localInverseAt y' = x.
  -- Suppose for contradiction localInverseAt y' ∈ ramSet ∩ U = bad_X.
  -- Then y' = f (localInverseAt y') ∈ f '' bad_X = bad_Y, contradicting hy'bad.
  by_contra h_neg
  have h_loc_in_U : h.localInverseAt x hx y' ∈ U := h_localInv_in_U y' hy'V
  have h_loc_in_ram : h.localInverseAt x hx y' ∈ ramSet := by
    refine ⟨h_neg, ?_⟩
    -- localInverseAt y' ≠ x because otherwise y' = f x, but then y' = f x and
    -- f x ∈ V → x = localInverseAt (f x) ∈ U, doesn't immediately give a contradiction.
    -- Wait — if localInverseAt y' = x, then h.ramificationIndex (localInverseAt y') =
    -- h.ramificationIndex x = 1 by hx, contradicting h_neg. So localInverseAt y' ≠ x.
    intro h_eq
    rw [h_eq] at h_neg
    exact h_neg hx
  have h_loc_in_bad : h.localInverseAt x hx y' ∈ bad_X := ⟨h_loc_in_U, h_loc_in_ram⟩
  have h_y'_in_bad : y' ∈ bad_Y := by
    refine ⟨h.localInverseAt x hx y', h_loc_in_bad, ?_⟩
    exact hright_branch y' hy'V
  exact hy'bad h_y'_in_bad

end JacobianChallenge.HolomorphicForms
