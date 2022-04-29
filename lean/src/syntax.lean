import data.finset

set_option pp.beta true

namespace modal_syntax

section syntax

  inductive formula : Type
  | var (n : ℕ) : formula
  | neg (f : formula) : formula
  | box (f : formula) : formula
  | dia (f : formula) : formula
  | conj (f₁ f₂ : formula) : formula 
  | disj (f₁ f₂ : formula) : formula
  | impl (f₁ f₂ : formula) : formula

  open formula

  /-definition of formula size-/

  def size : formula → ℕ
  | (var _) := 1
  | (neg f) := 1 + size f
  | (box f) := 1 + size f
  | (dia f) := 1 + size f
  | (conj f₁ f₂)
    := 1 + size f₁ + size f₂
  | (disj f₁ f₂)
    := 1 + size f₁ + size f₂
  | (impl f₁ f₂)
    := 1 + size f₁ + size f₂

  /- building the set of variables -/

  def vars : formula → finset ℕ
  | (var v) := insert v ∅ 
  | (neg f) := vars f
  | (box f) := vars f
  | (dia f) := vars f
  | (conj f₁ f₂)
    := vars f₁ ∪ vars f₂
  | (disj f₁ f₂)
    := vars f₁ ∪ vars f₂
  | (impl f₁ f₂)
    := vars f₁ ∪ vars f₂
end syntax

/- notations for formulas -/

open formula

notation f₁ `.⟶.` f₂  := impl f₁ f₂
notation f₁ `.∨.` f₂  := disj f₁ f₂
notation f₁ `.∧.` f₂  := conj f₁ f₂
notation `.¬` f  := neg f
notation `.□` f  := box f
notation `.◇` f  := dia f

end modal_syntax
