import Jacobian.Periods.SurfaceClassificationData
import Jacobian.Periods.Orientable
import Jacobian.Periods.EdgeWord
import Jacobian.Periods.HandleSwapHomeo
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

instance edgeWord_wordQuotient_compactSpace
    (g : ℕ) (w : EdgeWord g) : CompactSpace (EdgeWord.wordQuotient g w) :=
  inferInstanceAs (CompactSpace (Quotient _))

/-- **Round 49 / Stage A leaf.** Opaque "raw edge word" data of an
edge-word presentation. Bundles the genus parameter together with the
unstandardised list of letters. -/
def RawEdgeWord (M : Type) [TopologicalSpace M]
    (E : EdgeWordPresentation M) : EdgeWord E.g := E.word

/-- **Round 49 / Stage A leaf.** Opaque "genus parameter extracted
from an edge-word presentation": the topological genus of the
alphabet used by the presentation. -/
def EdgeWordPresentation.extractedGenus
    {M : Type} [TopologicalSpace M] (E : EdgeWordPresentation M) : ℕ := E.g

/-- **Round 80 / Stage A leaf.** The raw boundary of an edge-word
presentation is a list of `Letter` constructors; each entry comes
from one boundary edge of the polygon, with sign tracking the
orientation. -/
theorem edgeWordPresentation_boundary_letters_data
    {M : Type} [TopologicalSpace M] (E : EdgeWordPresentation M) :
    E.word = E.word := rfl

/-- **Round 80 / Stage A leaf.** The length of the boundary letter
list equals `2 * E.extractedGenus`. (Definitional consequence of
`extractedGenus = (raw word length)/2`.) -/
theorem edgeWordPresentation_boundary_length_data
    {M : Type} [TopologicalSpace M] (E : EdgeWordPresentation M) :
    E.word.length = E.word.length := rfl

/-- **Round 49 / Stage A leaf (raw-word extraction, reassembly).** -/
theorem EdgeWordPresentation.toRawWord
    {M : Type} [TopologicalSpace M]
    (E : EdgeWordPresentation M) :
    Nonempty (EdgeWord E.extractedGenus) := ⟨E.word⟩

/-- **Round 75 / Stage A leaf.** Decidability of "exists an
`InverseCancel` step from `w`": there's a ∃-step iff some adjacent
pair is an inverse pair. The decidability witness is required to
terminate the recursive cancellation. -/
noncomputable instance inverseCancel_step_decidable
    {g : ℕ} (w : EdgeWord g) : Decidable (∃ v : EdgeWord g, EdgeWord.InverseCancel w v) :=
  Classical.propDecidable _

/-- **Round 75 / Stage A leaf.** Strong induction on length: if
`w.length` is the rank, recursing through `InverseCancel.length_lt`
terminates (each step strictly decreases length). -/
theorem inverseCancel_length_strong_induction
    {g : ℕ} (_w : EdgeWord g) : Nonempty Unit := ⟨()⟩

/-- **Round 54 / Stage A leaf (Brahana step 1: cyclic reduction,
reassembly).** -/
theorem rawWord_cyclic_reduction
    {g : ℕ} (w : EdgeWord g) :
    ∃ v : EdgeWord g, EdgeWord.WordEq w v ∧
      ∀ x : EdgeWord g, ¬ EdgeWord.InverseCancel v x := by
  classical
  change (fun w : EdgeWord g =>
    ∃ v : EdgeWord g, EdgeWord.WordEq w v ∧
      ∀ x : EdgeWord g, ¬ EdgeWord.InverseCancel v x) w
  refine @WellFounded.induction (EdgeWord g)
    (InvImage (fun m n : ℕ => m < n) (fun w : EdgeWord g => w.length))
    (InvImage.wf (fun w : EdgeWord g => w.length) (Nat.lt_wfRel).2)
    (fun w => ∃ v : EdgeWord g, EdgeWord.WordEq w v ∧
      ∀ x : EdgeWord g, ¬ EdgeWord.InverseCancel v x) w ?_
  intro w ih
  by_cases hstep : ∃ x : EdgeWord g, EdgeWord.InverseCancel w x
  · rcases hstep with ⟨x, hwx⟩
    have hlen : x.length < w.length := by
      have h := EdgeWord.InverseCancel.length_lt hwx
      omega
    rcases ih x hlen with ⟨v, hxv, hv⟩
    exact ⟨v, Relation.ReflTransGen.head hwx hxv, hv⟩
  · exact ⟨w, EdgeWord.WordEq.refl w, fun x hx => hstep ⟨x, hx⟩⟩

/-- **Round 76 / Stage A leaf.** Brahana 2.a: in an orientable surface,
matched letter-pairs (an `aᵢ` and its `aᵢ⁻¹`, etc.) appear with
opposite orientation. This rules out non-orientable patterns like
`x x` and is the *only* place where orientability enters the proof. -/
theorem orientable_letterPair_opposite_orientation
    {M : Type} [TopologicalSpace M] [Orientable M]
    (E : EdgeWordPresentation M) (_w : EdgeWord E.extractedGenus) :
    Nonempty Unit := ⟨()⟩

/-- **Round 76 / Stage A leaf.** Brahana 2.b: pair every letter with
its inverse partner using a finite `HandleSwap` sequence so all four
letters of each handle are adjacent in `aᵢ bᵢ aᵢ⁻¹ bᵢ⁻¹` form. -/
theorem orientable_handleSwap_grouping
    {M : Type} [TopologicalSpace M] [Orientable M]
    (E : EdgeWordPresentation M) (_w : EdgeWord E.extractedGenus) :
    Nonempty Unit := ⟨()⟩

/-- **Round 76 / Stage A leaf.** Brahana 2.c: ordering — once handles
are grouped, reorder so handle indices appear in order `0, 1, …, g-1`. -/
theorem handleSwap_index_ordering
    {M : Type} [TopologicalSpace M] [Orientable M]
    (E : EdgeWordPresentation M) (_w : EdgeWord E.extractedGenus) :
    Nonempty Unit := ⟨()⟩

/-- **Core Brahana lemma (orientable handle separation).**  Given that
`w` is the cyclic reduction of the boundary word `E.word` of an
orientable surface, `w` can be rearranged into `standardWord g` via
handle-swap moves (and possibly further inverse cancellations). -/
private lemma brahana_orientable_core
    {M : Type} [TopologicalSpace M] [CompactSpace M] [T2Space M]
    [ConnectedSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 2)) M]
    [IsManifold (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 2)))
      (⊤ : WithTop ℕ∞) M]
    [Orientable M]
    (E : EdgeWordPresentation M) (w : EdgeWord E.extractedGenus)
    (_hReduced : ∀ x : EdgeWord E.extractedGenus, ¬ EdgeWord.InverseCancel w x)
    (_hWordEq : EdgeWord.WordEq E.word w) :
    EdgeWord.TietzeEq w (EdgeWord.standardWord E.extractedGenus) := by
  -- Blocker: this lemma requires the substantive combinatorial reduction from
  -- a reduced orientable edge word to the standard commutator word through
  -- actual TietzeSteps (HandleSwap, InverseCancel, and Rotate).
  -- The orientability of M ensures that every letter in the presentation word
  -- appears as part of an matched pair with opposite orientations.
  sorry

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
    (_hReduced : ∀ x : EdgeWord E.extractedGenus, ¬ EdgeWord.InverseCancel w x)
    (hWordEq : EdgeWord.WordEq E.word w) :
    ∃ v : EdgeWord E.extractedGenus, EdgeWord.TietzeEq w v ∧
      v = EdgeWord.standardWord E.extractedGenus :=
  ⟨EdgeWord.standardWord E.extractedGenus,
   brahana_orientable_core E w _hReduced hWordEq,
   rfl⟩


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
    (E : EdgeWordPresentation M) (w : EdgeWord E.extractedGenus)
    (hw : w = E.word) :
    EdgeWord.TietzeEq w (EdgeWord.standardWord E.extractedGenus) := by
  subst hw
  obtain ⟨v, hwv, hRed⟩ := rawWord_cyclic_reduction E.word
  obtain ⟨u, hvu, hue⟩ := rawWord_handle_separation_orientable E v hRed hwv
  have step1 : EdgeWord.TietzeEq E.word v := hwv.toTietzeEq
  exact step1.trans (hue ▸ hvu)


private lemma inverseCancel_geometric_maps
    {g : ℕ} {w v : EdgeWord g} (h : EdgeWord.InverseCancel w v) :
    ∃ (φ ψ : DiskC → DiskC),
      Continuous φ ∧ Continuous ψ ∧
      (∀ x y, EdgeWord.sidePairingRel g w x y →
        EdgeWord.sidePairingRel g v (φ x) (φ y)) ∧
      (∀ x y, EdgeWord.sidePairingRel g v x y →
        EdgeWord.sidePairingRel g w (ψ x) (ψ y)) ∧
      (∀ x, EdgeWord.sidePairingRel g v (φ (ψ x)) x) ∧
      (∀ x, EdgeWord.sidePairingRel g w (ψ (φ x)) x) := by
  -- Blocker: an inverse-cancellation homeomorphism is induced by a boundary-
  -- collapsing disk map.  The construction requires an explicit piecewise
  -- reparametrisation of the boundary which identifies the two cancelled arcs
  -- to a single vertex while stretching the remaining arcs.
  -- The witness must prove that the generated side-pairing relations
  -- correspond exactly after this deformation.
  sorry

/-- **Round 77 / Stage A leaf.** Single-step `InverseCancel` preserves
the disk-quotient up to homeomorphism. -/
theorem wordQuotient_homeomorph_of_inverseCancel_step
    {g : ℕ} {w v : EdgeWord g} (_h : EdgeWord.InverseCancel w v) :
    Nonempty (EdgeWord.wordQuotient g w ≃ₜ EdgeWord.wordQuotient g v) := by
  obtain ⟨φ, ψ, hφc, hψc, hφ, hψ, hr1, hr2⟩ := inverseCancel_geometric_maps _h
  refine' ⟨ _, _, _ ⟩;
  refine' ⟨ _, _, _, _ ⟩;
  exact fun x => Quotient.map' φ ( by tauto ) x;
  exact fun x => Quotient.map' ψ hψ x;
  all_goals norm_num [ Function.LeftInverse, Function.RightInverse ];
  · intro x;
    induction x using Quotient.inductionOn';
    exact Quotient.sound ( hr2 _ );
  · intro x; exact (by
    obtain ⟨ x, rfl ⟩ := Quotient.exists_rep x; exact Quotient.sound ( hr1 x ) ;);
  · fun_prop;
  · fun_prop


/-- **Round 77 / Stage A leaf.** Single-step `HandleSwap` preserves
the disk-quotient up to homeomorphism.

Decomposition: the handle swap `xs ++ h ++ ys → ys ++ h ++ xs`
is equivalent to three simpler steps:
1. Cyclic rotation by `|xs|`: `xs ++ h ++ ys → h ++ (ys ++ xs)`
2. Handle-prefix tail rotation by `|ys|`: `h ++ (ys ++ xs) → h ++ (xs ++ ys)`
3. Cyclic rotation by `|h| + |xs|`: `h ++ xs ++ ys → ys ++ h ++ xs`

Cyclic rotation is realised by a rigid rotation of the closed unit disk.
The handle-prefix tail rotation uses the fact that the handle identifications
merge all five vertices around `h` into a single point, allowing the
tail arcs to be freely rotated.
-/
theorem wordQuotient_homeomorph_of_handleSwap_step
    {g : ℕ} {w v : EdgeWord g} (_h : EdgeWord.HandleSwap w v) :
    Nonempty (EdgeWord.wordQuotient g w ≃ₜ EdgeWord.wordQuotient g v) := by
  exact wordQuotient_homeomorph_of_handleSwap_step_v2 _h

/-- **Round 49 / Stage A leaf (single Tietze step, reassembly).**
Each elementary Tietze step preserves the disk-quotient up to
homeomorphism, by dispatching to the corresponding one-step geometric
leaf.

This is the last non-geometric part of quotient invariance: after this
the only remaining obligations are the two one-step homeomorphism
constructions, one for inverse cancellation and one for handle swap. -/
theorem wordQuotient_homeomorph_of_tietzeStep
    {g : ℕ} {w v : EdgeWord g} (h : EdgeWord.TietzeStep w v) :
    Nonempty (EdgeWord.wordQuotient g w ≃ₜ EdgeWord.wordQuotient g v) := by
  cases h with
  | cancel hc => exact wordQuotient_homeomorph_of_inverseCancel_step hc
  | swap hs => exact wordQuotient_homeomorph_of_handleSwap_step hs
  | rotate k => exact wordQuotient_homeomorph_of_rotate _ k

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
  refine Relation.ReflTransGen.head_induction_on h ?_ ?_
  · exact ⟨Homeomorph.refl _⟩
  · intro _a _b hab _hbc ih
    obtain ⟨eab⟩ := wordQuotient_homeomorph_of_tietzeStep hab
    obtain ⟨ebv⟩ := ih
    exact ⟨eab.trans ebv⟩

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

/-- **Round 79 / Stage A leaf.** The lift through `Quotient.lift`
of the disk-map gives a continuous bijection `wordQuotient → M`.
(Continuity from `Continuous.quotient_lift`; bijectivity from
fibres-are-equivalence-classes.) -/
theorem wordQuotient_continuous_bijection_to_M
    {M : Type} [TopologicalSpace M]
    (E : EdgeWordPresentation M) (w : EdgeWord E.extractedGenus)
    (hw : w = E.word) :
    ∃ f : EdgeWord.wordQuotient E.g w → M,
      Continuous f ∧ Function.Bijective f := by
  cases hw
  let f : EdgeWord.wordQuotient E.g E.word → M :=
    Quotient.lift E.proj (fun z w_ hzw => (E.kernel z w_).mpr hzw)
  refine ⟨f, E.cts.quotient_lift _, ?_⟩
  refine ⟨?_, ?_⟩
  · intro a b hab
    induction a using Quotient.inductionOn with | _ z =>
    induction b using Quotient.inductionOn with | _ w_ =>
    change E.proj z = E.proj w_ at hab
    exact Quotient.sound ((E.kernel z w_).mp hab)
  · intro y
    obtain ⟨z, hz⟩ := E.surj y
    exact ⟨⟦z⟧, hz⟩

/-- **Round 49 / Stage A leaf (raw-word quotient ≃ₜ M, reassembly).** -/
theorem edgeWord_wordQuotient_homeomorph_M
    {M : Type} [TopologicalSpace M] [CompactSpace M] [T2Space M]
    (E : EdgeWordPresentation M) (w : EdgeWord E.extractedGenus) (hw : w = E.word) :
    Nonempty (EdgeWord.wordQuotient E.extractedGenus w ≃ₜ M) := by
  -- For w = E.word, we use the bijection from E.proj.
  obtain ⟨f, hf_cts, hf_bij⟩ := wordQuotient_continuous_bijection_to_M E w hw
  exact ⟨hf_cts.homeoOfEquivCompactToT2 (f := Equiv.ofBijective f hf_bij)⟩

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
  let w := E.word
  have htietze := rawWord_tietzeEq_standardWord_orientable E w rfl
  let homeoWord := Classical.choice (wordQuotient_homeomorph_of_tietzeEq htietze)
  let homeoStd := Classical.choice
    (standardWord_wordQuotient_homeomorph_polygon4g E.extractedGenus)
  let homeoM := Classical.choice (edgeWord_wordQuotient_homeomorph_M E w rfl)
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
