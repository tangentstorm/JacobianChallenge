import Jacobian.Periods.SurfaceClassificationData
import Jacobian.Periods.Orientable
import Jacobian.Periods.EdgeWord
import Mathlib.Geometry.Manifold.IsManifold.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2

/-!
# Round 49 — Tietze reduction `EdgeWordPresentation → PolygonalQuotientPresentation`

Decomposes the Stage A2.b frontier leaf into:

* `EdgeWordPresentation.extractRawWord` — extract the underlying
  `EdgeWord g` of length `2k` from an edge-word presentation.
* `rawWord_tietze_eq_to_standard_orientable` — for an *orientable*
  surface, the raw word is `TietzeEq` to the standard relator
  `standardWord (k/2)`.
* `tietzeEq_preserves_quotient` — Tietze-equivalent edge words yield
  homeomorphic quotient spaces.
* `standardWord_quotient_homeomorph_polygon4g` — the quotient by the
  standard relator is `Polygon4g g`.
* sorry-free assembly: `EdgeWordPresentation.toPolygonalQuotient_via_tietze`.

Each leaf is itself a `sorry`. Bottom-up routes are documented in the
docstrings.
-/

namespace JacobianChallenge.Periods

/-- Topological-space instance on the word quotient. Not provided by
`EdgeWord.wordQuotient` directly because it is a `def` rather than an
`abbrev`; this instance unblocks the homeomorphism statements below
without modifying `EdgeWord.lean`. -/
instance edgeWord_wordQuotient_topologicalSpace
    (g : ℕ) (w : EdgeWord g) : TopologicalSpace (EdgeWord.wordQuotient g w) :=
  inferInstanceAs (TopologicalSpace (Quotient _))

/-- **Round 49 / Stage A leaf.** Opaque "raw edge word" data of an
edge-word presentation. Bundles the genus parameter together with the
unstandardised list of letters. -/
opaque RawEdgeWord (M : Type) [TopologicalSpace M]
    (_E : EdgeWordPresentation M) : Type

/-- **Round 49 / Stage A leaf.** Opaque "genus parameter extracted
from an edge-word presentation": the half-length of the raw word
divided by 2 (the would-be genus if Tietze reduction succeeds). -/
opaque EdgeWordPresentation.extractedGenus
    {M : Type} [TopologicalSpace M] (_E : EdgeWordPresentation M) : ℕ

/-- **Round 49 / Stage A leaf (raw-word extraction).** Every
edge-word presentation produces a raw `EdgeWord` of the appropriate
genus. -/
theorem EdgeWordPresentation.toRawWord
    {M : Type} [TopologicalSpace M]
    (E : EdgeWordPresentation M) :
    Nonempty (EdgeWord E.extractedGenus) := by
  sorry

/-- **Round 54 / Stage A leaf (Brahana step 1: cyclic reduction).**
Any edge word reduces by `InverseCancel`s to one with no immediate
inverse pairs. Bottom-up content: termination by length induction
(each `InverseCancel` strictly decreases length, available via
`InverseCancel.length_lt`). -/
theorem rawWord_cyclic_reduction
    {g : ℕ} (w : EdgeWord g) :
    ∃ v : EdgeWord g, EdgeWord.WordEq w v ∧
      ∀ x : EdgeWord g, ¬ EdgeWord.InverseCancel v x := by
  sorry

/-- **Round 54 / Stage A leaf (Brahana step 2: handle separation,
orientable case).** A cyclically-reduced edge word of an orientable
2-manifold can be `HandleSwap`-rearranged so that letters of the same
handle index are adjacent. -/
theorem rawWord_handle_separation_orientable
    {M : Type} [TopologicalSpace M] [CompactSpace M] [T2Space M]
    [ConnectedSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 2)) M]
    [IsManifold (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 2)))
      (⊤ : WithTop ℕ∞) M]
    [Orientable M]
    (E : EdgeWordPresentation M) (w : EdgeWord E.extractedGenus)
    (_hReduced : ∀ x : EdgeWord E.extractedGenus, ¬ EdgeWord.InverseCancel w x) :
    ∃ v : EdgeWord E.extractedGenus, EdgeWord.TietzeEq w v ∧
      v = EdgeWord.standardWord E.extractedGenus := by
  sorry

/-- **Round 49 / Stage A leaf (Tietze reduction, orientable case,
reassembly).** For an orientable 2-manifold, the raw edge word is
Tietze-equivalent to the standard relator. Combines the cyclic
reduction (`rawWord_cyclic_reduction`) and the handle-separation
step (`rawWord_handle_separation_orientable`).

Bottom-up content: the classical Brahana / Seifert–Threlfall
reduction. -/
theorem rawWord_tietzeEq_standardWord_orientable
    {M : Type} [TopologicalSpace M] [CompactSpace M] [T2Space M]
    [ConnectedSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 2)) M]
    [IsManifold (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 2)))
      (⊤ : WithTop ℕ∞) M]
    [Orientable M]
    (E : EdgeWordPresentation M) (w : EdgeWord E.extractedGenus) :
    EdgeWord.TietzeEq w (EdgeWord.standardWord E.extractedGenus) := by
  obtain ⟨v, hwv, hRed⟩ := rawWord_cyclic_reduction w
  obtain ⟨u, hvu, hue⟩ := rawWord_handle_separation_orientable E v hRed
  have step1 : EdgeWord.TietzeEq w v := hwv.toTietzeEq
  exact step1.trans (hue ▸ hvu)

/-- **Round 49 / Stage A leaf (quotient invariance under Tietze
moves).** Tietze-equivalent edge words yield homeomorphic disk
quotients.

Bottom-up content: each Tietze move corresponds to a topological
move on the quotient — `InverseCancel` is a contraction that does
not change the homeomorphism type, and `HandleSwap` is the classical
"slide" of a handle along the surface. -/
theorem wordQuotient_homeomorph_of_tietzeEq
    {g : ℕ} {w v : EdgeWord g} (_h : EdgeWord.TietzeEq w v) :
    Nonempty (EdgeWord.wordQuotient g w ≃ₜ EdgeWord.wordQuotient g v) := by
  sorry

/-- **Round 49 / Stage A leaf (standard quotient = Polygon4g).** The
quotient by the standard word equals `Polygon4g g` definitionally;
the homeomorphism is the identity transport. -/
theorem standardWord_wordQuotient_homeomorph_polygon4g (g : ℕ) :
    Nonempty (EdgeWord.wordQuotient g (EdgeWord.standardWord g) ≃ₜ Polygon4g g) := by
  sorry

/-- **Round 49 / Stage A leaf (raw-word quotient ≃ₜ M).** The quotient
of `DiskC` by the side-pairing relation of an edge-word presentation
is homeomorphic to `M` itself.

Bottom-up content: a presentation is by definition the data of a
continuous surjection `DiskC → M` whose fibres are exactly the
side-pairing equivalence — so by the universal property of the
quotient, the lifted bijection is a continuous bijection from a
compact space to a T2 space, hence a homeomorphism. -/
theorem edgeWord_wordQuotient_homeomorph_M
    {M : Type} [TopologicalSpace M] [CompactSpace M] [T2Space M]
    (E : EdgeWordPresentation M) (w : EdgeWord E.extractedGenus) :
    Nonempty (EdgeWord.wordQuotient E.extractedGenus w ≃ₜ M) := by
  sorry

/-- **Round 49 / Stage A leaf (sorry-free assembly).** Combine the
five leaves above into a `PolygonalQuotientPresentation M`.

Strategy: extract the raw word `w`; produce three homeomorphisms
(M ≃ wordQuotient w via `edgeWord_wordQuotient_homeomorph_M`,
wordQuotient w ≃ wordQuotient (standardWord g) via the Tietze step,
wordQuotient (standardWord g) ≃ Polygon4g g via the standard-quotient
identification). Compose into `polyToM : Polygon4g g ≃ₜ M`, then take
`proj := polyToM ∘ Polygon4g.mk g` and verify `cts/surj/kernel` from
the homeomorphism + quotient API. -/
noncomputable def EdgeWordPresentation.toPolygonalQuotient_via_tietze
    {M : Type} [TopologicalSpace M] [CompactSpace M] [T2Space M]
    [ConnectedSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 2)) M]
    [IsManifold (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 2)))
      (⊤ : WithTop ℕ∞) M]
    [Orientable M]
    (E : EdgeWordPresentation M) : PolygonalQuotientPresentation M := by
  let w := Classical.choice E.toRawWord
  have htietze := rawWord_tietzeEq_standardWord_orientable E w
  let homeoWord := Classical.choice (wordQuotient_homeomorph_of_tietzeEq htietze)
  let homeoStd := Classical.choice
    (standardWord_wordQuotient_homeomorph_polygon4g E.extractedGenus)
  let homeoM := Classical.choice (edgeWord_wordQuotient_homeomorph_M E w)
  -- Compose: Polygon4g g ≃ₜ wordQuotient (standardWord g) ≃ₜ wordQuotient w ≃ₜ M.
  let polyToM : Polygon4g E.extractedGenus ≃ₜ M :=
    homeoStd.symm.trans (homeoWord.symm.trans homeoM)
  refine
    { genus := E.extractedGenus
      proj := fun z => polyToM (Polygon4g.mk E.extractedGenus z)
      cts := polyToM.continuous.comp continuous_quot_mk
      surj := polyToM.surjective.comp Quotient.mk_surjective
      kernel := ?_ }
  intro z w'
  refine ⟨fun h => ?_, fun h => ?_⟩
  · exact Quotient.exact (polyToM.injective h)
  · exact congrArg polyToM (Quotient.sound h)

end JacobianChallenge.Periods
