import syntax semantics tactic.induction

section theory

  namespace list
  open modal_syntax
  open model
  open modal_syntax.formula

  def theory := list formula

  inductive modal_theory (M : model) : list formula → Prop
  | nil_theory : modal_theory nil
  | cons_theory : ∀ Γ φ, validate_model M φ → modal_theory Γ → modal_theory (cons φ Γ)

  def entails (M : model)(Γ : list formula)(φ : formula) : Prop
    := modal_theory M Γ → validate_model M φ

  notation M `;;` Γ `⊢` φ := entails M Γ φ

  section structural_properties

    theorem exact_deduction
      : ∀ (Γ : list formula)(φ : formula), φ ∈ Γ → ∀ (M : model), M ;; Γ ⊢ φ :=
    begin
      intros Γ,
      induction' Γ,
      { intros φ H, cases H },
      { intros φ Hin M MT,
        simp * at *,
        cases MT,
        cases Hin,
        { rw Hin at * ; assumption },
        apply ih ; assumption }
     end

     theorem refl_deduction 
       : ∀ M Γ φ, modal_theory M (φ :: Γ) → (M ;; (φ :: Γ) ⊢ φ)
     := by simp [exact_deduction]


     theorem modal_theory_union
       : ∀ M Γ Δ, modal_theory M (Γ ++ Δ) →
                  modal_theory M Γ ∧ modal_theory M Δ :=
     begin
       intros M Γ Δ HGD,
       induction' Γ,
       { split ; simp * at *,
         constructor },
       { cases HGD,
         have Hn : modal_theory M Γ ∧ modal_theory M Δ,
           from by {apply ih ; assumption},
         have HL : modal_theory M Γ, from and.elim_left Hn,
         have HR : modal_theory M Δ, from and.elim_right Hn,
         split ; try { constructor } ; assumption }
     end

  end structural_properties
  end list
end theory
