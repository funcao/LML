(*  
    Name: Ariel Agne da Silveira

    Advisor: Karina Girardi Roggia
    Co-Advisor: Paulo Torrens

    Minion: Miguel
*)

Require Import Arith List ListSet Notations Classical Relations.
Export ListNotations.

Inductive modalFormula: Set :=
  | Lit    : nat -> modalFormula
  | Neg    : modalFormula -> modalFormula
  | Box    : modalFormula -> modalFormula
  | Dia    : modalFormula -> modalFormula
  | And    : modalFormula -> modalFormula -> modalFormula
  | Or     : modalFormula -> modalFormula -> modalFormula
  | Implies: modalFormula -> modalFormula -> modalFormula.

(* Size modal formula *)
Fixpoint modalSize (f:modalFormula) : nat :=
  match f with 
  | Lit      x     => 1
  | Neg      p1    => 1 + (modalSize p1)
  | Box      p1    => 1 + (modalSize p1)
  | Dia      p1    => 1 + (modalSize p1)
  | And      p1 p2 => 1 + (modalSize p1) + (modalSize p2)
  | Or       p1 p2 => 1 + (modalSize p1) + (modalSize p2)
  | Implies  p1 p2 => 1 + (modalSize p1) + (modalSize p2)
end.

Fixpoint literals (f:modalFormula) : set nat :=
  match f with 
  | Lit      x     => set_add eq_nat_dec x (empty_set nat)
  | Dia      p1    => literals p1
  | Box      p1    => literals p1
  | Neg      p1    => literals p1
  | And      p1 p2 => set_union eq_nat_dec (literals p1) (literals p2)
  | Or       p1 p2 => set_union eq_nat_dec (literals p1) (literals p2)
  | Implies  p1 p2 => set_union eq_nat_dec (literals p1) (literals p2) 
end.

Record Frame: Type := {
  W: Set;
  R: W -> W -> Prop
}.

Record Model: Type := {
  F: Frame;
  v: nat -> (W F) -> Prop
}.

Fixpoint fun_validation (M: Model) (w: W (F M)) (φ: modalFormula): Prop :=
  match φ with
  | Lit     x   => v M x w 
  | Box     ψ   => forall w', R (F M) w w' -> fun_validation M w' ψ
  | Dia     ψ   => exists w', R (F M) w w' /\ fun_validation M w' ψ
  | Neg     ψ   => ~fun_validation M w ψ
  | And     ψ Ɣ => fun_validation M w ψ /\ fun_validation M w Ɣ
  | Or      ψ Ɣ => fun_validation M w ψ \/ fun_validation M w Ɣ
  | Implies ψ Ɣ => fun_validation M w ψ -> fun_validation M w Ɣ
  end.

(* Model satisfazibility *)
Definition validate_model (M: Model) (φ: modalFormula): Prop :=
  forall w, fun_validation M w φ.

(******  Finite theories and entailment ******)

Definition theory := list modalFormula.

Fixpoint theoryModal (M: Model) (Γ: theory): Prop :=
  match Γ with
  | nil => True
  | h :: t => (validate_model M h) /\ (theoryModal M t)
  end.

Definition entails (M: Model) (Γ: theory) (φ: modalFormula): Prop :=
  theoryModal M Γ -> validate_model M φ.

(***** structural properties of deduction ****)

(* If a formula belongs in a theory, it's valid. *)
Theorem exact_deduction:
  forall Γ φ,
  In φ Γ ->
  forall M,
  entails M Γ φ.
Proof.
  intros.
  induction Γ.
  - inversion H.
  - simpl in H.
    destruct H.
    + destruct H.
      unfold entails; intros.
      destruct H; auto.
    + unfold entails; intro.
      apply IHΓ; auto.
      destruct H0; auto.
Qed.

Theorem reflexive_deduction:
  forall M Γ φ,
  entails M (φ :: Γ) φ.
Proof.
  intros.
  apply exact_deduction.
  constructor; auto.
Qed.

Lemma theoryModal_union:
  forall M Γ ẟ,
  theoryModal M (Γ ++ ẟ) -> 
  theoryModal M Γ /\ theoryModal M ẟ.
Proof.
    intros.
    induction Γ.
    - simpl in *.
      split; tauto.
    - simpl in *.
      apply and_assoc.
      destruct H as [left right]; split.
      + assumption.
      + apply IHΓ.
        assumption.
Qed.

(* Bottom-up proof *)
Theorem transitive_deduction_bu:
  forall M Γ ẟ φ ψ Ɣ,
  entails M (φ :: Γ) ψ /\ entails M (ψ::ẟ) Ɣ -> 
  entails M (φ :: Γ ++ ẟ) Ɣ.
Proof.
  intros.
  unfold entails in *.
  destruct H as [H1 H2].
  intros; apply H2.
  simpl in *; destruct H as [left right].
  apply theoryModal_union in right.
  destruct right as [ModalG ModalD].
  tauto.
Qed.

Theorem exchange:
  forall M Γ φ ψ Ɣ,
  entails M (φ :: ψ :: Γ) Ɣ -> 
  entails M (ψ :: φ :: Γ) Ɣ.
Proof.
  intros.
  unfold entails in *; intros.
  apply H; simpl in *.
  split.
  - destruct H0 as [H0 [H1 H2]]; apply H1.
  - split.
    + destruct H0 as [H0 [H1 H2]].
      assumption.
    + destruct H0 as [H0 [H1 H2]].
      assumption.
Qed.

Inductive transpose {T}: list T -> list T -> Prop :=
  | tranpose_head:
    forall φ ψ tail,
    transpose (φ:: ψ :: tail) (ψ :: φ:: tail)
  | transpose_tail:
    forall φ tail1 tail2,
    transpose tail1 tail2 -> transpose (φ :: tail1) (φ :: tail2)
  | transpose_refl:
    forall ψ,
    transpose ψ ψ
  | transpose_trans:
    forall φ ψ Ɣ,
    transpose φ ψ -> transpose ψ Ɣ -> transpose φ Ɣ
  | transpose_sym:
    forall φ ψ,
    transpose φ ψ -> transpose ψ φ.

Lemma transpose_in:
  forall {T} xs ys,
  transpose xs ys ->
  forall φ: T,
  In φ xs <-> In φ ys.
Proof.
  induction 1; intros.
  - split; intros.
    + destruct H.
      * destruct H; intuition.
      * destruct H; try intuition.
        destruct H; intuition.
    + destruct H.
      * destruct H; intuition.
      * destruct H; try intuition.
        destruct H; intuition.
  - split; intros.
    + destruct H0.
      * destruct H0.
        left; auto.
      * right; apply IHtranspose.
        assumption.
    + destruct H0.
      * destruct H0.
        left; auto.
      * right; apply IHtranspose.
        assumption.
  - intuition.
  - split; intros.
    + apply IHtranspose2.
      apply IHtranspose1.
      assumption.
    + apply IHtranspose1.
      apply IHtranspose2.
      assumption.
  - split; intros.
    + apply IHtranspose; auto.
    + apply IHtranspose; auto.
Qed.

Theorem tranpose_deduction:
  forall M Γ ẟ φ,
  transpose Γ ẟ ->
  entails M Γ φ <-> entails M ẟ φ.
Proof.
  induction 1.
  - split; intros.
    + apply exchange.
      assumption.
    + apply exchange.
      assumption.
  - clear H.
    split; intros.
    + unfold entails in *; intros.
      destruct H0.
      edestruct IHtranspose as [H2 _].
      apply H2; intros.
      * apply H.
        split; auto.
      * auto.
    + unfold entails in *; intros.
      destruct H0.
      edestruct IHtranspose as [_ H2].
      apply H2; intros.
      * apply H.
        split; auto.
      * auto.
  - intuition.
  - split; intros.
    + apply IHtranspose2.
      apply IHtranspose1.
      assumption.
    + apply IHtranspose1.
      apply IHtranspose2.
      assumption.
  - split; intros.
    + apply IHtranspose; auto.
    + apply IHtranspose; auto.
Qed.

Theorem idempotence:
  forall M Γ φ ψ,
  entails M (φ :: φ :: Γ) ψ -> 
  entails M (φ :: Γ) ψ.
Proof.
  intros.
  unfold entails in *; intros.
  apply H; simpl in *.
  split; destruct H0.
  - apply H0.
  - split.
    + apply H0.
    + apply H1.
Qed.

Theorem monotonicity:
  forall M Γ ẟ φ,
  entails M Γ φ -> 
  entails M (Γ ++ ẟ) φ.
Proof.
  unfold entails in *; intros.
  apply H.
  apply theoryModal_union with (ẟ := ẟ).
  assumption.
Qed.

(* Reflexividade *)
Definition reflexivity_frame (F: Frame): Prop :=
  forall w, R F w w.

(* Transitividade *)
Definition transitivity_frame (F: Frame): Prop :=
  forall w w' w'': W F,
  (R F w w' /\ 
  R F w' w'') -> 
  R F w w''.

(* Simetria *)
Definition simmetry_frame (F: Frame): Prop :=
  forall w w',
  R F w w' -> 
  R F w' w.

(* Euclidiana *)
Definition euclidian_frame (F: Frame): Prop :=
  forall w w' w'',
  (R F w w' /\ 
  R F w w'') -> 
  R F w' w''.

(* Serial *)
Definition serial_frame (F: Frame): Prop :=
  forall w,
  exists w', R F w w'.

(* Funcional *)
Definition functional_frame (F: Frame): Prop :=
  forall w w' w'',
  (R F w w' /\ 
  R F w w'') -> 
  w' = w''.

(* Densa*)
Definition dense_frame (F: Frame): Prop :=
  forall w w',
  exists w'',
  R F w w' -> 
  (R F w w'' /\ 
  R F w'' w').

(* Convergente *)
Definition convergente_frame (F: Frame): Prop :=
  forall w x y,
  exists z,
  (R F w x /\ 
  R F w y) -> 
  (R F x z /\ R F y z).

Definition SubsetOfW (F: Frame): Type :=
  W F -> Prop.

Definition conversely_well_founded_frame (F: Frame): Prop :=
  (* Set-theoretic definition: *)
  forall X: SubsetOfW F, (exists x, X x) -> 
  exists w1, X w1 /\ forall w2, X w2 -> 
  ~ (R F w1 w2).

Definition noetherian_frame (F: Frame): Prop :=
  transitivity_frame F /\ conversely_well_founded_frame F.

(* Equivalencia lógica *)
Definition entails_modal (Γ: theory) (φ: modalFormula): Prop :=
  forall M,
  theoryModal M Γ -> 
  validate_model M φ.

Definition equivalence (φ ψ: modalFormula): Prop := 
  (entails_modal [φ] ψ) /\ (entails_modal [ψ] φ).