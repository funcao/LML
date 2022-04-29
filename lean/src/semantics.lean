import data.finset
import syntax

set_option pp.beta true


section model

  structure frame := mk_frame :: (W : Type)(R : W → W → Prop)
  open frame 

  structure model := mk_model :: (F : frame)(V : ℕ → W F → Prop)
  open model

  open modal_syntax
  open modal_syntax.formula

  def fun_validation (M : model)(w : W (F M)) : formula → Prop
  | (var v) := V M v w
  | (.□ f) := ∀ w' : W (F M), R (F M) w w' → fun_validation f
  | (.◇ f) := ∃ w' : W (F M), R (F M) w w' ∧ fun_validation f
  | (.¬ f) := ¬ fun_validation f
  | (f₁ .∧. f₂) := fun_validation f₁ ∧ fun_validation f₂ 
  | (f₁ .∨. f₂) := fun_validation f₁ ∨ fun_validation f₂
  | (f₁ .⟶. f₂) := fun_validation f₁ → fun_validation f₂

  def validate_model (M : model)(f : formula) : Prop
    := ∀ w : W (F M), fun_validation M w f
end model

open model

notation M `;` w `⊧` f := fun_validation M w f
notation M `⊧` f := validate_model M f
