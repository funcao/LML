import syntax
       semantics
       frame_properties


section completeness
  open modal_syntax
  open model
  open frame
  open modal_syntax.formula

  theorem reflexive_frame_completeness
    : ∀ M φ, (M ⊧ ((.□ φ) .⟶. φ)) →
             reflexivity_frame (F M) :=
  begin
    intros M φ H w,
    simp [validate_model] at H,
    simp [fun_validation] at H,
    sorry
  end
end completeness
