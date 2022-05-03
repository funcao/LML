import syntax
       semantics
       tactic.induction
       data.list.perm

section theory

  namespace list
  open modal_syntax
  open model
  open modal_syntax.formula

  def theory := list formula

  inductive modal_theory (M : model) : list formula → Prop
  | nil_theory : modal_theory nil
  | cons_theory : ∀ Γ φ, validate_model M φ →
                         modal_theory Γ →
                         modal_theory (φ :: Γ)

  def entails (M : model)
              (Γ : list formula)
              (φ : formula) : Prop
    := modal_theory M Γ → validate_model M φ

  notation M `;;` Γ `⊢` φ := entails M Γ φ

  section structural_properties

    theorem exact_deduction
      : ∀ (Γ : list formula)(φ : formula),
          φ ∈ Γ → ∀ (M : model), M ;; Γ ⊢ φ :=
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
       : ∀ M Γ φ, modal_theory M (φ :: Γ) →
                  (M ;; (φ :: Γ) ⊢ φ)
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


     theorem transitive_deduction_bu
       : ∀ M Γ Δ φ₁ φ₂ φ₃,
         (M ;; (φ₁ :: Γ) ⊢ φ₂) →
         (M ;; (φ₂ :: Δ) ⊢ φ₃) →
         (M ;; (φ₁ :: Γ ++ Δ) ⊢ φ₃) :=
     begin
       intros M Γ Δ φ₁ φ₂ φ₃ H1 H2 HM,
       simp * at *,
       have HMA : modal_theory M (φ₁ :: Γ) ∧ modal_theory M Δ,
         from by { apply modal_theory_union, simp * at * },
       cases HMA with HM1 HM2,
       apply H2,
       constructor ; try { assumption },
       apply H1, try { assumption }
     end

     theorem exchange
       : ∀ M Γ φ₁ φ₂ φ₃,
         (M ;; (φ₁ :: φ₂ :: Γ) ⊢ φ₃) →
         (M ;; (φ₂ :: φ₁ :: Γ) ⊢ φ₃) :=
     begin
       intros M Γ φ₁ φ₂ φ₃ H H1,
       cases H1 with M Γ H2 H3,
       cases H3 with M Γ H4 H5,
       apply H,
       repeat { constructor <|> assumption }
     end

     lemma modal_theory_permutation
       : ∀ M Γ Δ, Γ ~ Δ → modal_theory M Γ → modal_theory M Δ :=
       begin
         intros M Γ Δ H1 H2,
         induction' H1,
         case list.perm.nil
           { assumption },
         case list.perm.cons
           { cases H2,
             constructor,
             { assumption },
             { apply ih, assumption }},
         case list.perm.swap
           { cases H2 with M Γ H21 H22,
             cases H22 with M Γ H23 H24,
             repeat { constructor <|> assumption }}, 
         case list.perm.trans
           { apply ih_H1_1,
             apply ih_H1,
             assumption}
       end

     theorem permutation_deduction
       : ∀ M Γ Δ φ,
       Γ ~ Δ →
       (M ;; Γ ⊢ φ) →
       (M ;; Δ ⊢ φ)
     := begin
          intros M Γ Δ φ H,
          induction' H,
          case list.perm.nil 
             { intros H1 , assumption },
          case list.perm.cons
             { intros H1 HM1,
               cases HM1 with M Δ HM11 HM12,
               have HD1 : modal_theory M (x :: Γ),
               from begin
                      constructor,
                      assumption,
                      apply modal_theory_permutation ; try { assumption },
                      apply list.perm.symm,
                      assumption
                    end,
               apply H1, assumption},
          case list.perm.swap
            { intros H1 HM,
              cases HM with M Δ HM1 HM2,
              cases HM2 with M Δ HM3 HM4,
              apply H1,
              repeat { constructor <|> assumption }},
          case list.perm.trans
            { intros HM,
              apply ih_H_1,
              apply ih_H,
              assumption }
        end

    theorem contraction
      : ∀ M Γ φ₁ φ₂,
        (M ;; (φ₁ :: φ₁ :: Γ) ⊢ φ₂) →
        (M ;; (φ₁ :: Γ) ⊢ φ₂) :=
    begin
      intros M Γ φ₁ φ₂ H HM,
      cases HM with M Γ HM1 HM2,
      apply H,
      repeat { constructor <|> assumption }
    end

    theorem monotonicity
      : ∀ M Γ Δ φ,
        (M ;; Γ ⊢ φ) →
        (M ;; (Γ ++ Δ) ⊢ φ) :=
    begin
      intros M Γ Δ φ H HM,
      apply H,
      have HM1 : modal_theory M Γ ∧ modal_theory M Δ,
        from by { apply modal_theory_union, assumption },
      cases HM1, assumption
    end
  end structural_properties

  def entails_modal (Γ : list formula)(φ : formula) : Prop :=
    ∀ M, modal_theory M Γ → validate_model M φ

  def equivalence (φ₁ φ₂ : formula) : Prop :=
    (entails_modal (φ₁ :: nil) φ₂) ∧
    (entails_modal (φ₂ :: nil) φ₁)

  notation φ₁ `.=.` φ₂ := equivalence φ₁ φ₂
  notation Γ `⊩` φ := entails_modal Γ φ
  end list
end theory

