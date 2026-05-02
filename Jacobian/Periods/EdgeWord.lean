import Mathlib.Data.Fin.Basic
import Mathlib.Data.List.Basic

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
* `wordQuotient g w` — (placeholder) the quotient of the closed `4g`-gon disk
  by the side-pairing relation determined by `w`.

## References

This is leaf A2.1 of the surface-classification plan.
-/

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

namespace EdgeWord

/-- The block of four letters `aᵢ bᵢ aᵢ⁻¹ bᵢ⁻¹` for a single handle `i`. -/
def handleBlock {g : ℕ} (i : Fin g) : List (Letter g) :=
  [Letter.a i, Letter.b i, Letter.aInv i, Letter.bInv i]

/-- The standard relator word
`a₀ b₀ a₀⁻¹ b₀⁻¹ a₁ b₁ a₁⁻¹ b₁⁻¹ ⋯ a_{g-1} b_{g-1} a_{g-1}⁻¹ b_{g-1}⁻¹`
as an explicit list. -/
noncomputable def standardWord (g : ℕ) : EdgeWord g :=
  (List.finRange g).flatMap handleBlock

/-- A predicate asserting that an edge word is in standard form, i.e. it equals
`standardWord g`. -/
def IsStandardForm {g : ℕ} (w : EdgeWord g) : Prop :=
  w = standardWord g

theorem standardWord_isStandardForm {g : ℕ} : (standardWord g).IsStandardForm :=
  rfl

/-! ### Quotient by side-pairing (placeholder) -/

/-- The side-pairing equivalence relation on the boundary of a `4g`-gon
determined by an edge word `w`. Two boundary points are related when they
sit on paired sides at matching parameters.

This is a placeholder; the full definition will be supplied by leaf A2.2. -/
noncomputable def sidePairingRel (_g : ℕ) (_w : EdgeWord _g) :
    Unit → Unit → Prop :=
  sorry

/-- The quotient of the closed `4g`-gon disk by the side-pairing relation
determined by `w`. Placeholder — returns `Quot` of a `sorry`-ed relation. -/
noncomputable def wordQuotient (g : ℕ) (w : EdgeWord g) : Type :=
  Quot (sidePairingRel g w)

end EdgeWord
