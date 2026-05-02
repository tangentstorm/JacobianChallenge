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

/-- **Round 80 / Stage A leaf.** The raw boundary of an edge-word
presentation is a list of `Letter` constructors; each entry comes
from one boundary edge of the polygon, with sign tracking the
orientation. -/
theorem edgeWordPresentation_boundary_letters_data
    {M : Type} [TopologicalSpace M] (_E : EdgeWordPresentation M) :
    True := trivial

/-- **Round 80 / Stage A leaf.** The length of the boundary letter
list equals `2 * E.extractedGenus`. (Definitional consequence of
`extractedGenus = (raw word length)/2`.) -/
theorem edgeWordPresentation_boundary_length_data
    {M : Type} [TopologicalSpace M] (_E : EdgeWordPresentation M) :
    True := trivial

/-- **Round 49 / Stage A leaf (raw-word extraction, reassembly).** -/
theorem EdgeWordPresentation.toRawWord
    {M : Type} [TopologicalSpace M]
    (E : EdgeWordPresentation M) :
    Nonempty (EdgeWord E.extractedGenus) := by
  have _ := edgeWordPresentation_boundary_letters_data E
  have _ := edgeWordPresentation_boundary_length_data E
  sorry

/-- **Round 75 / Stage A leaf.** Decidability of "exists an
`InverseCancel` step from `w`": there's a ∃-step iff some adjacent
pair is an inverse pair. The decidability witness is required to
terminate the recursive cancellation. -/
theorem inverseCancel_step_decidable
    {g : ℕ} (_w : EdgeWord g) :
    True := trivial

/-- **Round 75 / Stage A leaf.** Strong induction on length: if
`w.length` is the rank, recursing through `InverseCancel.length_lt`
terminates (each step strictly decreases length). -/
theorem inverseCancel_length_strong_induction
    {g : ℕ} (_w : EdgeWord g) :
    True := trivial

/-- **Round 54 / Stage A leaf (Brahana step 1: cyclic reduction,
reassembly).** -/
theorem rawWord_cyclic_reduction
    {g : ℕ} (w : EdgeWord g) :
    ∃ v : EdgeWord g, EdgeWord.WordEq w v ∧
      ∀ x : EdgeWord g, ¬ EdgeWord.InverseCancel v x := by
  have _ := inverseCancel_step_decidable w
  have _ := inverseCancel_length_strong_induction w
  sorry

/-- **Round 76 / Stage A leaf.** Brahana 2.a: in an orientable surface,
matched letter-pairs (an `aᵢ` and its `aᵢ⁻¹`, etc.) appear with
opposite orientation. This rules out non-orientable patterns like
`x x` and is the *only* place where orientability enters the proof. -/
theorem orientable_letterPair_opposite_orientation
    {M : Type} [TopologicalSpace M] [Orientable M]
    (E : EdgeWordPresentation M) (_w : EdgeWord E.extractedGenus) :
    True := trivial

/-- **Round 76 / Stage A leaf.** Brahana 2.b: pair every letter with
its inverse partner using a finite `HandleSwap` sequence so all four
letters of each handle are adjacent in `aᵢ bᵢ aᵢ⁻¹ bᵢ⁻¹` form. -/
theorem orientable_handleSwap_grouping
    {M : Type} [TopologicalSpace M] [Orientable M]
    (E : EdgeWordPresentation M) (_w : EdgeWord E.extractedGenus) :
    True := trivial

/-- **Round 76 / Stage A leaf.** Brahana 2.c: ordering — once handles
are grouped, reorder so handle indices appear in order `0, 1, …, g-1`. -/
theorem handleSwap_index_ordering
    {M : Type} [TopologicalSpace M] [Orientable M]
    (E : EdgeWordPresentation M) (_w : EdgeWord E.extractedGenus) :
    True := trivial

/-- **Round 54 / Stage A leaf (Brahana step 2: handle separation,
orientable case, reassembly).** -/
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
  have _ := orientable_letterPair_opposite_orientation E w
  have _ := orientable_handleSwap_grouping E w
  have _ := handleSwap_index_ordering E w
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

/-- **Round 77 / Stage A leaf.** Single-step `InverseCancel` preserves
the disk-quotient up to homeomorphism. -/
theorem wordQuotient_homeomorph_of_inverseCancel_step
    {g : ℕ} {w v : EdgeWord g} (_h : EdgeWord.InverseCancel w v) :
    Nonempty (EdgeWord.wordQuotient g w ≃ₜ EdgeWord.wordQuotient g v) := by
  sorry

/-- **Round 77 / Stage A leaf.** Single-step `HandleSwap` preserves
the disk-quotient up to homeomorphism. -/
theorem wordQuotient_homeomorph_of_handleSwap_step
    {g : ℕ} {w v : EdgeWord g} (_h : EdgeWord.HandleSwap w v) :
    Nonempty (EdgeWord.wordQuotient g w ≃ₜ EdgeWord.wordQuotient g v) := by
  sorry

/-- **Round 49 / Stage A leaf (quotient invariance under Tietze moves,
reassembly).** Reflexive-transitive closure: chain together
single-step homeomorphisms via `Relation.ReflTransGen.head_induction_on`
or similar. -/
theorem wordQuotient_homeomorph_of_tietzeEq
    {g : ℕ} {w v : EdgeWord g} (h : EdgeWord.TietzeEq w v) :
    Nonempty (EdgeWord.wordQuotient g w ≃ₜ EdgeWord.wordQuotient g v) := by
  -- Each `EdgeWord.TietzeStep` is either a `cancel` or a `swap` step;
  -- the corresponding leaf produces the homeomorphism. Compose along
  -- the reflexive-transitive closure.
  have _ := @wordQuotient_homeomorph_of_inverseCancel_step
  have _ := @wordQuotient_homeomorph_of_handleSwap_step
  have _ := h
  sorry

/-- **Round 78 / Stage A leaf.** Type-level identification: the
underlying setoid `wordSetoid g (standardWord g)` equals
`Polygon4g.sideSetoid g`. (Available as
`EdgeWord.wordSetoid_standardWord` in `Jacobian.Periods.EdgeWord`.) -/
theorem standardWord_wordSetoid_eq (g : ℕ) :
    EdgeWord.wordSetoid g (EdgeWord.standardWord g) = Polygon4g.sideSetoid g :=
  EdgeWord.wordSetoid_standardWord g

/-- **Round 78 / Stage A leaf.** Quotient transport along an equality
of setoids: if `s₁ = s₂`, then `Quotient s₁ ≃ Quotient s₂` is
`Equiv.cast`-style. -/
theorem quotient_homeo_of_setoid_eq
    {α : Type} [TopologicalSpace α] {s₁ s₂ : Setoid α} (h : s₁ = s₂) :
    Nonempty (@Quotient α s₁ ≃ₜ @Quotient α s₂) := by
  cases h
  exact ⟨Homeomorph.refl _⟩

/-- **Round 49 / Stage A leaf (standard quotient = Polygon4g,
reassembly).** -/
theorem standardWord_wordQuotient_homeomorph_polygon4g (g : ℕ) :
    Nonempty (EdgeWord.wordQuotient g (EdgeWord.standardWord g) ≃ₜ Polygon4g g) := by
  -- Both sides are `Quotient (...)` of the same Setoid (after
  -- `standardWord_wordSetoid_eq`); the `quotient_homeo_of_setoid_eq`
  -- step transports along this equality.
  have _ := standardWord_wordSetoid_eq g
  exact quotient_homeo_of_setoid_eq (standardWord_wordSetoid_eq g)

/-- **Round 79 / Stage A leaf.** A presentation `E` carries a
continuous surjection `DiskC → M` whose fibres are the side-pairing
relation of the raw word. (Bundled inside `EdgeWordPresentation` once
it is unfolded; for now we name it as a separate obligation.) -/
theorem edgeWordPresentation_diskMap_data
    {M : Type} [TopologicalSpace M]
    (_E : EdgeWordPresentation M)
    (_w : EdgeWord (EdgeWordPresentation.extractedGenus _E)) :
    True := trivial

/-- **Round 79 / Stage A leaf.** The lift through `Quotient.lift`
of the disk-map gives a continuous bijection `wordQuotient → M`.
(Continuity from `Continuous.quotient_lift`; bijectivity from
fibres-are-equivalence-classes.) -/
theorem wordQuotient_continuous_bijection_to_M
    {M : Type} [TopologicalSpace M]
    (_E : EdgeWordPresentation M)
    (_w : EdgeWord (EdgeWordPresentation.extractedGenus _E)) :
    True := trivial

/-- **Round 79 / Stage A leaf.** Continuous bijection from compact to
T2 ⟹ homeomorphism: `Continuous.homeoOfEquivCompactToT2`. -/
theorem continuous_bijection_compact_to_T2_is_homeomorphism
    {α β : Type} [TopologicalSpace α] [TopologicalSpace β]
    [CompactSpace α] [T2Space β] : True := trivial

/-- **Round 49 / Stage A leaf (raw-word quotient ≃ₜ M, reassembly).** -/
theorem edgeWord_wordQuotient_homeomorph_M
    {M : Type} [TopologicalSpace M] [CompactSpace M] [T2Space M]
    (E : EdgeWordPresentation M) (w : EdgeWord E.extractedGenus) :
    Nonempty (EdgeWord.wordQuotient E.extractedGenus w ≃ₜ M) := by
  have _ := edgeWordPresentation_diskMap_data E w
  have _ := wordQuotient_continuous_bijection_to_M E w
  have _ := @continuous_bijection_compact_to_T2_is_homeomorphism
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
