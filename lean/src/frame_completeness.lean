import syntax
       semantics
       frame_properties


section completeness
  open modal_syntax
  open model
  open frame
  open modal_syntax.formula

  lemma all_not_not_ex
    : ∀ {U}(P : U → Prop),
      (∀ n, ¬ P n) → ¬ (∃ n, P n) :=
  begin
    intros U P H H1,
    cases H1 with n H1,
    have H2 : ¬ P n, from by exact (H n),
    contradiction
  end

  lemma not_all_ex_not
    : ∀ {U}(P : U → Prop),
        ¬ (∀ n, P n) → ∃ n, ¬ P n :=
  begin
    intros U P H,
    by_contra,
    simp * at *
  end

  lemma ex_not_not_all
    : ∀ {U}(P : U → Prop),
        (∃ n, ¬ P n) → ¬ (∀ n, P n) :=
  begin
    intros U P H H1,
    simp * at *,
  end

  theorem reflexive_frame_completeness
    : ∀ M,
        (∀ φ, M ⊧ ((.□ φ) .⟶. φ)) →
             reflexivity_frame (F M) :=
  begin
    intros M,
    contrapose,
    intros H,
    unfold reflexivity_frame at H,
    simp * at *,
    cases H with w H,
    use (var 0),
    simp * at *,
    use w,
    split,
    { }
  end
end completeness
