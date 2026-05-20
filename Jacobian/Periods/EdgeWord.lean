import Mathlib.Data.Fin.Basic
import Mathlib.Data.List.Basic
import Mathlib.Data.List.FinRange
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Common
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
abbrev EdgeWord (g : ℕ) : Type := List (Letter g)

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

end EdgeWord

/-- Inverse of a letter: `a i ↔ aInv i`, `b i ↔ bInv i`. -/
def Letter.inv {g : ℕ} : Letter g → Letter g
  | Letter.a i => Letter.aInv i
  | Letter.b i => Letter.bInv i
  | Letter.aInv i => Letter.a i
  | Letter.bInv i => Letter.b i

@[simp] lemma Letter.inv_inv {g : ℕ} (ℓ : Letter g) : ℓ.inv.inv = ℓ := by
  cases ℓ <;> rfl

namespace EdgeWord

/-! ### Quotient by side-pairing -/

/-- Generating relation for the side-pairing on the boundary of the
closed unit disk determined by a general edge word `w`. For any two
indices `i, j` such that the letters `w[i]` and `w[j]` are inverses,
the corresponding boundary arcs are identified with parameter reversal. -/
inductive SideGen (g : ℕ) (w : EdgeWord g) : DiskC → DiskC → Prop
  | pair (i j : Fin w.length) (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) 1)
      (h : (w.get i).inv = w.get j) :
      SideGen g w
        (boundaryParam' w.length i t)
        (boundaryParam' w.length j (1 - t))

/-- The reflexive-symmetric-transitive closure of `SideGen g w`. -/
def sidePairingRel (g : ℕ) (w : EdgeWord g) : DiskC → DiskC → Prop :=
  Relation.EqvGen (SideGen g w)

/-- Length of the standard word for genus `g`. -/
lemma standardWord_length (g : ℕ) : (standardWord g).length = 4 * g := by
  unfold standardWord
  simp [handleBlock, List.length_flatMap, List.length_finRange]
  linarith

/-
The letters in `standardWord g` at indices `4i`, `4i+1`, `4i+2`, `4i+3`.
-/
lemma standardWord_get_handle {g : ℕ} (i : Fin g) :
    (standardWord g).get ⟨4 * i.val, by rw [standardWord_length]; linarith [i.is_lt]⟩ = Letter.a i ∧
    (standardWord g).get ⟨4 * i.val + 1, by rw [standardWord_length]; linarith [i.is_lt]⟩ = Letter.b i ∧
    (standardWord g).get ⟨4 * i.val + 2, by rw [standardWord_length]; linarith [i.is_lt]⟩ = Letter.aInv i ∧
    (standardWord g).get ⟨4 * i.val + 3, by rw [standardWord_length]; linarith [i.is_lt]⟩ = Letter.bInv i := by
  unfold standardWord; simp +decide ;
  -- By definition of `List.flatMap`, we can split the list into the first `i` elements, the `i`-th element, and the remaining elements.
  have h_split : List.flatMap handleBlock (List.finRange g) = List.flatMap handleBlock (List.take i (List.finRange g)) ++ handleBlock i ++ List.flatMap handleBlock (List.drop (i + 1) (List.finRange g)) := by
    have h_split : List.flatMap handleBlock (List.finRange g) = List.flatMap handleBlock (List.take (i.val + 1) (List.finRange g)) ++ List.flatMap handleBlock (List.drop (i.val + 1) (List.finRange g)) := by
      rw [ ← List.flatMap_append, List.take_append_drop ];
    simp_all +decide [ List.take_add_one ];
  have h_split : List.length (List.flatMap handleBlock (List.take i (List.finRange g))) = 4 * i := by
    simp +arith +decide [ handleBlock ];
  simp_all +decide [ handleBlock ]

/-
Each letter appears exactly once in `standardWord g`.
-/
lemma standardWord_get_unique {g : ℕ} (ℓ : Letter g) :
    ∃! i : Fin (standardWord g).length, (standardWord g).get i = ℓ := by
  -- By definition of `standardWord`, each letter appears exactly once.
  have h_unique : List.Nodup (standardWord g) := by
    unfold standardWord;
    rw [ List.nodup_flatMap ];
    unfold handleBlock; simp +decide [ List.pairwise_iff_get ] ;
    exact fun i j hij => ne_of_gt hij;
  obtain ⟨i, hi⟩ : ∃ i : Fin (standardWord g).length, (standardWord g).get i = ℓ := by
    have h_exists : ℓ ∈ standardWord g := by
      cases ℓ <;> simp +decide [ standardWord ];
      · exact ⟨ _, List.mem_cons_self ⟩;
      · exact ⟨ _, List.mem_cons_of_mem _ ( List.mem_cons_self ) ⟩;
      · exact ⟨ _, List.mem_cons_of_mem _ ( List.mem_cons_of_mem _ ( List.mem_cons_self ) ) ⟩;
      · exact ⟨ _, List.mem_cons_of_mem _ ( List.mem_cons_of_mem _ ( List.mem_cons_of_mem _ ( List.mem_singleton_self _ ) ) ) ⟩;
    exact List.mem_iff_get.mp h_exists;
  exact ⟨ i, hi, fun j hj => by have := List.nodup_iff_injective_get.mp h_unique; have := @this j i; aesop ⟩

/-- Helper: `boundaryParam'` respects changing the first argument along equality. -/
lemma boundaryParam'_congr_length {L₁ L₂ : ℕ} (hL : L₁ = L₂) (i : ℕ) (t : ℝ) :
    boundaryParam' L₁ i t = boundaryParam' L₂ i t := by
  subst hL; rfl

/-
The polygon side-pairing generator implies the edge-word side-pairing generator
for the standard word (up to EqvGen).
-/
private lemma polygon_sideGen_imp (g : ℕ) (x y : DiskC)
    (h : Polygon4g.SideGen g x y) :
    Relation.EqvGen (SideGen g (standardWord g)) x y := by
  obtain ⟨ i, t, ht ⟩ := h;
  · convert Relation.EqvGen.rel _ _ ( SideGen.pair ⟨ 4 * i.val, by linarith [ i.2, standardWord_length g ] ⟩ ⟨ 4 * i.val + 2, by linarith [ i.2, standardWord_length g ] ⟩ t ht _ ) using 1;
    · exact boundaryParam'_congr_length ( by rw [ standardWord_length ] ) _ _;
    · exact boundaryParam'_congr_length ( by rw [ standardWord_length ] ) _ _;
    · rw [ standardWord_get_handle i |>.1, standardWord_get_handle i |>.2.2.1 ];
      rfl;
  · simp +decide [ boundaryParam ];
    apply Relation.EqvGen.rel;
    convert SideGen.pair _ _ _ _ _;
    · exact (standardWord_length g).symm;
    rotate_left;
    · exact (standardWord_length g).symm;
    rotate_left;
    exact ⟨ 4 * ‹Fin g›.val + 1, by rw [ standardWord_length ] ; linarith [ Fin.is_lt ‹_› ] ⟩;
    exact ⟨ 4 * ‹Fin g›.val + 3, by rw [ standardWord_length ] ; linarith [ Fin.is_lt ‹_› ] ⟩;
    · assumption;
    · have := standardWord_get_handle ‹_›; aesop;
    · rfl;
    · rfl

/-
The edge-word side-pairing generator for the standard word implies the polygon
side-pairing generator (up to EqvGen).
-/
private lemma edgeWord_sideGen_imp (g : ℕ) (x y : DiskC)
    (h : SideGen g (standardWord g) x y) :
    Relation.EqvGen (Polygon4g.SideGen g) x y := by
  obtain ⟨ i, j, t, ht, h ⟩ := h;
  -- By definition of `standardWord`, we know that `i.val = 4 * k + r` for some `k : Fin g` and `r ∈ {0,1,2,3}`.
  obtain ⟨k, r, hr⟩ : ∃ k : Fin g, ∃ r : Fin 4, i.val = 4 * k.val + r.val := by
    exact ⟨ ⟨ i / 4, Nat.div_lt_of_lt_mul <| by linarith [ Fin.is_lt i, show List.length ( standardWord g ) = 4 * g from standardWord_length g ] ⟩, ⟨ i % 4, Nat.mod_lt _ <| by decide ⟩, by norm_num; linarith [ Nat.mod_add_div i 4 ] ⟩;
  -- By definition of `standardWord`, we know that `j.val = 4 * k' + r'` for some `k' : Fin g` and `r' ∈ {0,1,2,3}`.
  obtain ⟨k', r', hr'⟩ : ∃ k' : Fin g, ∃ r' : Fin 4, j.val = 4 * k'.val + r'.val := by
    have h_div : j.val < 4 * g := by
      exact j.2.trans_le ( by simp +decide [ standardWord_length ] );
    exact ⟨ ⟨ j / 4, Nat.div_lt_of_lt_mul <| by linarith ⟩, ⟨ j % 4, Nat.mod_lt _ <| by decide ⟩, by simp +decide [ Nat.div_add_mod ] ⟩;
  fin_cases r <;> fin_cases r' <;> simp_all +decide only [List.get_eq_getElem];
  all_goals have := standardWord_get_handle k; have := standardWord_get_handle k'; simp_all +decide [ Letter.inv ] ;
  · convert Relation.EqvGen.rel _ _ ( Polygon4g.SideGen.a_pair k' t ht ) using 1;
    · exact boundaryParam'_congr_length ( by rw [ standardWord_length ] ) _ _;
    · exact boundaryParam'_congr_length ( by simp +decide [ standardWord_length ] ) _ _;
  · convert Relation.EqvGen.rel _ _ ( Polygon4g.SideGen.b_pair k' t ht ) using 1;
    · exact boundaryParam'_congr_length ( standardWord_length g ) _ _;
    · exact boundaryParam'_congr_length ( standardWord_length g ) _ _;
  · have := Polygon4g.mk_a_pair g k' ( 1 - t ) ⟨ by linarith, by linarith ⟩ ; simp_all +decide [ boundaryParam ] ;
    convert this.symm using 1;
    · rw [ standardWord_length ];
    · rw [ standardWord_length ];
  · apply Relation.EqvGen.symm;
    convert Polygon4g.mk_b_pair g k' ( 1 - t ) ⟨ by linarith, by linarith ⟩ using 1;
    simp +decide [ Polygon4g.mk_eq_mk_iff, boundaryParam'_congr_length ( standardWord_length g ) ];
    rfl

/-
For the standard word, `sidePairingRel` agrees with `Polygon4g.SideRel`.
-/
theorem sidePairingRel_standardWord (g : ℕ) :
    sidePairingRel g (standardWord g) = Polygon4g.SideRel g := by
  unfold sidePairingRel;
  -- Unfold the definitions of `sidePairingRel` and `Polygon4g.SideRel`.
  unfold Polygon4g.SideRel;
  apply le_antisymm;
  · intro x y h;
    induction h;
    · exact edgeWord_sideGen_imp g _ _ ‹_›;
    · exact Relation.EqvGen.refl _;
    · exact Relation.EqvGen.symm _ _ ‹_›;
    · exact Relation.EqvGen.trans _ _ _ ‹_› ‹_›;
  · intro x y h;
    induction h;
    · exact polygon_sideGen_imp g _ _ ‹_›;
    · exact Relation.EqvGen.refl _;
    · exact Relation.EqvGen.symm _ _ ‹_›;
    · exact Relation.EqvGen.trans _ _ _ ‹_› ‹_›

/-- `sidePairingRel` is an equivalence relation. -/
theorem sidePairingRel_equivalence (g : ℕ) (w : EdgeWord g) :
    Equivalence (sidePairingRel g w) := by
  exact Relation.EqvGen.is_equivalence _

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
  cases h <;> simp [List.length_append] <;> linarith

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
  | rotate {g : ℕ} {w : EdgeWord g} (k : ℕ) : TietzeStep w (w.rotate k)

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