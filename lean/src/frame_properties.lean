import syntax
       semantics

section properties

  open modal_syntax
  open model
  open frame
  open modal_syntax.formula

  def reflexivity_frame (F : frame) : Prop :=
    ∀ w, R F w w

  @[simp]
  def transitivity_frame (F : frame) : Prop :=
    ∀ w₁ w₂ w₃, R F w₁ w₂ → R F w₂ w₃ → R F w₁ w₃

  @[simp]
  def simmetry_frame (F : frame) : Prop :=
    ∀ w₁ w₂, R F w₁ w₂ → R F w₂ w₁

  @[simp]
  def euclidean_frame (F : frame) : Prop :=
    ∀ w₁ w₂ w₃, R F w₁ w₂ → R F w₁ w₃ → R F w₂ w₃

  @[simp]
  def serial_frame (F : frame) : Prop :=
    ∀ w, ∃ w', R F w w'


  @[simp]
  def functional_frame (F : frame) : Prop :=
    ∀ w₁ w₂ w₃, R F w₁ w₂ →
                R F w₁ w₃ →
                w₂ = w₃

  @[simp]
  def dense_frame (F : frame) : Prop :=
    ∀ w₁ w₂, ∃ w₃, R F w₁ w₂ → R F w₁ w₃ ∧ R F w₂ w₃


  @[simp]
  def convergent_frame (F : frame) : Prop :=
    ∀ w x y, ∃ z, (R F w x ∧ R F w y) → (R F x z ∧ R F y z)
end properties
