import Mathlib.Data.Fin.Basic
import Mathlib.Data.List.Basic
import Jacobian.Periods.Polygon4g

/-!
# Edge words for fundamental polygon side-pairing

For each genus `g`, this file defines the combinatorial data type
`EdgeWord g` representing a word in the generators
`a₀, b₀, a₀⁻¹, b₀⁻¹, …, a_{g-1}, b_{g-1}, a_{g-1}⁻¹, b_{g-1}⁻¹`
that labels the boundary of a fundamental `4g`-gon.

## Main definitions

* `Letter g` — the alphabet: four constructors `a i`, `b i`, `aInv i`, `bInv i`
  for `i : Fin g`.
* `EdgeWord g` — a word over `Letter g`, defined as `List (Letter g)`.
* `EdgeWord.IsStandardForm` — predicate characterising the standard relator
  `a₀ b₀ a₀⁻¹ b₀⁻¹ ⋯ a_{g-1} b_{g-1} a_{g-1}⁻¹ b_{g-1}⁻¹`.
* `standardWord g` — the standard-form word.
* `sidePairingRel g w` — the side-pairing equivalence relation on the closed
  unit disk `DiskC` determined by `w`. For `w = standardWord g`, it agrees
  with `Polygon4g.SideRel g`.
* `wordQuotient g w` — `DiskC / sidePairingRel g w`.

## References

This is leaf A2.1 of the surface-classification plan.
-/

namespace JacobianChallenge.Periods

/-- The four-letter alphabet for a genus-`g` polygon boundary word. -/
inductive Letter (g : ℕ) : Type where
  | a    (i : Fin g) : Letter g
  | b    (i : Fin g) : Letter g
  | aInv (i : Fin g) : Letter g
  | bInv (i : Fin g) : Letter g
  deriving DecidableEq

/-- An edge word is a list of letters over the genus-`g` alphabet. -/
def EdgeWord (g : ℕ) : Type := List (Letter g)

instance (g : ℕ) : Inhabited (EdgeWord g) := ⟨[]⟩

instance (g : ℕ) : DecidableEq (EdgeWord g) :=
  inferInstanceAs (DecidableEq (List (Letter g)))

namespace EdgeWord

/-- The block of four letters `aᵢ bᵢ aᵢ⁻¹ bᵢ⁻¹` for a single handle `i`. -/
def handleBlock {g : ℕ} (i : Fin g) : List (Letter g) :=
  [Letter.a i, Letter.b i, Letter.aInv i, Letter.bInv i]

/-- The standard relator word
`a₀ b₀ a₀⁻¹ b₀⁻¹ a₁ b₁ a₁⁻¹ b₁⁻¹ ⋯ a_{g-1} b_{g-1} a_{g-1}⁻¹ b_{g-1}⁻¹`
as an explicit list. -/
def standardWord (g : ℕ) : EdgeWord g :=
  (List.finRange g).flatMap handleBlock

/-- A predicate asserting that an edge word is in standard form, i.e. it equals
`standardWord g`. -/
def IsStandardForm {g : ℕ} (w : EdgeWord g) : Prop :=
  w = standardWord g

theorem standardWord_isStandardForm {g : ℕ} : (standardWord g).IsStandardForm :=
  rfl

instance {g : ℕ} (w : EdgeWord g) : Decidable w.IsStandardForm :=
  inferInstanceAs (Decidable (w = standardWord g))

/-! ### Quotient by side-pairing -/

/-- The side-pairing equivalence relation on the closed unit disk
determined by an edge word `w`.

For the standard word, this is `Polygon4g.SideRel g` — the four-arc
identification pattern `a-cycle: 4i ↔ 4i+2`, `b-cycle: 4i+1 ↔ 4i+3`,
each with parameter reversal. For non-standard words, this is the
trivial relation `Eq` (no identifications), so the quotient gives
back the disk; the full general construction (extracting the side-
pairing pattern from an arbitrary word) is leaf A2.2 of
`ref/plans/surface-classification.md` and is not yet needed
downstream — the proof of `thm:polygonal-model` only depends on the
standard word's quotient. -/
def sidePairingRel (g : ℕ) (w : EdgeWord g) : DiskC → DiskC → Prop :=
  if w.IsStandardForm then Polygon4g.SideRel g else Eq

/-- For the standard word, `sidePairingRel` agrees with `Polygon4g.SideRel`. -/
theorem sidePairingRel_standardWord (g : ℕ) :
    sidePairingRel g (standardWord g) = Polygon4g.SideRel g := by
  simp [sidePairingRel, IsStandardForm]

/-- `sidePairingRel` is an equivalence relation. -/
theorem sidePairingRel_equivalence (g : ℕ) (w : EdgeWord g) :
    Equivalence (sidePairingRel g w) := by
  unfold sidePairingRel
  by_cases h : w.IsStandardForm
  · simp [h]; exact Polygon4g.SideRel.equivalence g
  · simp [h]; exact eq_equivalence

/-- The quotient of the closed unit disk by the side-pairing relation
determined by `w`. -/
def wordQuotient (g : ℕ) (w : EdgeWord g) : Type :=
  Quotient ⟨sidePairingRel g w, sidePairingRel_equivalence g w⟩

/-- The Setoid used to construct `wordQuotient g w`. -/
def wordSetoid (g : ℕ) (w : EdgeWord g) : Setoid DiskC :=
  ⟨sidePairingRel g w, sidePairingRel_equivalence g w⟩

/-- For the standard word, the wordSetoid equals `Polygon4g.sideSetoid g`. -/
theorem wordSetoid_standardWord (g : ℕ) :
    wordSetoid g (standardWord g) = Polygon4g.sideSetoid g := by
  unfold wordSetoid Polygon4g.sideSetoid
  congr 1
  exact sidePairingRel_standardWord g

/-- **A3.1.** For the standard word, `wordQuotient` is the same type as
`Polygon4g g`. The two are constructed as quotients of `DiskC` by the
same equivalence relation (`SideRel g`); their setoids coincide via
`wordSetoid_standardWord`. -/
theorem polygon4g_eq_standard_word_quotient (g : ℕ) :
    wordQuotient g (standardWord g) = Polygon4g g := by
  unfold wordQuotient Polygon4g
  rw [show (⟨sidePairingRel g (standardWord g), sidePairingRel_equivalence g (standardWord g)⟩
        : Setoid DiskC) = Polygon4g.sideSetoid g from wordSetoid_standardWord g]

/-! ### List-level Tietze cancellation -/

/-- The single-step Tietze swap relation: cancel an adjacent
inverse pair `[ℓ, ℓ⁻¹]` (or `[ℓ⁻¹, ℓ]`) anywhere in a word. -/
inductive InverseCancel : {g : ℕ} → EdgeWord g → EdgeWord g → Prop where
  | ax_aInv {g : ℕ} (i : Fin g) (xs ys : List (Letter g)) :
      InverseCancel (xs ++ [Letter.a i, Letter.aInv i] ++ ys) (xs ++ ys)
  | aInv_a {g : ℕ} (i : Fin g) (xs ys : List (Letter g)) :
      InverseCancel (xs ++ [Letter.aInv i, Letter.a i] ++ ys) (xs ++ ys)
  | bx_bInv {g : ℕ} (i : Fin g) (xs ys : List (Letter g)) :
      InverseCancel (xs ++ [Letter.b i, Letter.bInv i] ++ ys) (xs ++ ys)
  | bInv_b {g : ℕ} (i : Fin g) (xs ys : List (Letter g)) :
      InverseCancel (xs ++ [Letter.bInv i, Letter.b i] ++ ys) (xs ++ ys)

/-- Length strictly decreases by 2 under `InverseCancel`. -/
theorem InverseCancel.length_lt {g : ℕ} {w v : EdgeWord g}
    (h : InverseCancel w v) :
    v.length + 2 = w.length := by
  cases h <;> simp [List.length_append] <;> omega

/-- The reflexive-transitive closure (word equivalence under
finitely many cancellations). -/
def WordEq {g : ℕ} : EdgeWord g → EdgeWord g → Prop :=
  Relation.ReflTransGen InverseCancel

/-- `WordEq` is reflexive. -/
theorem WordEq.refl {g : ℕ} (w : EdgeWord g) : WordEq w w :=
  Relation.ReflTransGen.refl

/-- `WordEq` is transitive. -/
theorem WordEq.trans {g : ℕ} {a b c : EdgeWord g}
    (hab : WordEq a b) (hbc : WordEq b c) : WordEq a c :=
  Relation.ReflTransGen.trans hab hbc

/-- Handle swap: a full handle block `[a i, b i, aInv i, bInv i]` may
be exchanged with any two adjacent letters that are independent of `i`.
This is one of the two essential moves (the other being InverseCancel)
in the classical proof that any orientable edge word reduces to the
standard form. -/
inductive HandleSwap : {g : ℕ} → EdgeWord g → EdgeWord g → Prop where
  | move {g : ℕ} (i : Fin g) (xs ys : List (Letter g))
      (h : List (Letter g)) (_hh : h = [Letter.a i, Letter.b i, Letter.aInv i, Letter.bInv i]) :
      HandleSwap (xs ++ h ++ ys) (ys ++ h ++ xs)

/-- The combined word equivalence: closed under both `InverseCancel`
and `HandleSwap`. -/
inductive TietzeStep : {g : ℕ} → EdgeWord g → EdgeWord g → Prop where
  | cancel {g : ℕ} {w v : EdgeWord g} (h : InverseCancel w v) : TietzeStep w v
  | swap   {g : ℕ} {w v : EdgeWord g} (h : HandleSwap w v) : TietzeStep w v

/-- Word equivalence under the full Tietze move set. -/
def TietzeEq {g : ℕ} : EdgeWord g → EdgeWord g → Prop :=
  Relation.ReflTransGen TietzeStep

theorem TietzeEq.refl {g : ℕ} (w : EdgeWord g) : TietzeEq w w :=
  Relation.ReflTransGen.refl

theorem TietzeEq.trans {g : ℕ} {a b c : EdgeWord g}
    (hab : TietzeEq a b) (hbc : TietzeEq b c) : TietzeEq a c :=
  Relation.ReflTransGen.trans hab hbc

/-- Single-step embedding of `WordEq` (cancellations only) into `TietzeEq`. -/
theorem WordEq.toTietzeEq {g : ℕ} {w v : EdgeWord g} (h : WordEq w v) :
    TietzeEq w v :=
  h.mono (fun _ _ hc => TietzeStep.cancel hc)

end EdgeWord

end JacobianChallenge.Periods
