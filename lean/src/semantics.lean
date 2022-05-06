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

  @[simp]
  def fun_validation (M : model) : W (F M) → formula → Prop
  | w (var v)
    := V M v w
  | w (.□ f)
    := ∀ w' : W (F M), R (F M) w w' → fun_validation w' f
  | w (.◇ f)
    := ∃ w' : W (F M), R (F M) w w' ∧ fun_validation w' f
  | w (.¬ f)
    := ¬ fun_validation w f
  | w (f₁ .∧. f₂)
    := fun_validation w f₁ ∧ fun_validation w f₂
  | w (f₁ .∨. f₂)
    := fun_validation w f₁ ∨ fun_validation w f₂
  | w (f₁ .⟶. f₂)
    := fun_validation w f₁ → fun_validation w f₂

  @[simp]
  def validate_model (M : model)(f : formula) : Prop
    := ∀ w : W (F M), fun_validation M w f
end model

open model

notation M `;` w `⊧` f := fun_validation M w f
notation M `⊧` f := validate_model M f
