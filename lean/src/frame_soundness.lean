import syntax
       semantics
       frame_properties


section soundness
  open modal_syntax
  open model
  open frame
  open modal_syntax.formula

  theorem reflexive_frame_soundness
    : ∀ M φ, reflexivity_frame (F M) →
             (M ⊧ ((.□ φ) .⟶. φ)) :=
  begin
    intros M φ HR w,
    rw reflexivity_frame at HR,
    simp [fun_validation],
    intros H,
    apply H ; try {assumption},
    apply HR
  end

  theorem transitive_frame_soundness
    : ∀ M φ, transitivity_frame (F M) →
             (M ⊧ ((.□ φ) .⟶. (.□ (.□ φ)))) :=
  begin
    intros M φ HT w,
    rw transitivity_frame at HT,
    simp [fun_validation],
    intros H1 w₁ Hww₁ w₂ Hww₂,
    apply H1,
    { assumption }
  end

  theorem symmetry_frame_soundness
    : ∀ M φ, simmetry_frame (F M) →
             (M ⊧ (φ .⟶. (.□ (.◇ φ)))) :=
  begin
    intros M φ HS w,
    rw simmetry_frame at HS,
    simp [fun_validation],
    intros H w' Hww',
    split ; try {assumption},
    constructor, {assumption}
  end

  theorem euclidean_frame_soundness
    : ∀ M φ, euclidean_frame (F M) →
             (M ⊧ (.◇ φ .⟶. (.□ (.◇ φ)))) :=
  begin
    intros M φ HE w,
    rw euclidean_frame at HE,
    simp [fun_validation],
    intros w1 Hww1 H1 w2 Hww2,
    split ; try { assumption },
    constructor, { assumption }
  end

  theorem serial_frame_soundness
    : ∀ M φ, serial_frame (F M) →
             (M ⊧ ((.□ φ) .⟶. (.◇ φ))) :=
  begin
    intros M φ HS w,
    rw serial_frame at HS,
    simp [fun_validation],
    intros H,
    have H1 : ∃ w', M.F.R w w', from
      by apply HS,
    cases H1,
    split,
    { constructor, assumption },
    { apply H, {assumption}}
  end

  theorem functional_frame_soundness
    : ∀ M φ, functional_frame (F M) →
             (M ⊧ ((.◇ φ) .⟶. (.□ φ))) :=
  begin
    intros M φ HF w,
    simp [fun_validation],
    intros w1 Hww1 H1 w2 Hww2,
    assumption
  end

  theorem dense_frame_soundness
    : ∀ M φ, dense_frame (F M) →
          (M ⊧ ((.◇ (.□ φ)) .⟶. (.◇ φ))) :=
  begin
    intros M φ HD w,
    simp [fun_validation],
    intros w1 Hww1 H2,
    split,
    { constructor ; try { assumption }},
    { apply H2 ; assumption }
  end

  theorem convergent_frame_soundness
    : ∀ M φ, convergent_frame (F M) →
     (M ⊧ ((.◇ (.□ φ)) .⟶. (.□ (.◇ φ)))) :=
  begin
    intros M φ HC w,
    simp [fun_validation],
    intros w1 Hww1 H1 w2 Hww2,
    split,
    {constructor ; try { assumption }},
    {apply H1 ; try {assumption}}
  end
end soundness
