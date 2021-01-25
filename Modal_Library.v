(*  
    Name: Ariel Agne da Silveira

    Advisor: Karina Girardi Roggia
    Co-Advisor: Paulo Torrens

    Minion: Miguel
*)

Require Import Arith List ListSet Notations Classical.

Inductive modalFormula : Set :=
    | Lit          : nat -> modalFormula
    | Neg          : modalFormula -> modalFormula
    | Box          : modalFormula -> modalFormula
    | Dia          : modalFormula -> modalFormula
    | And          : modalFormula -> modalFormula -> modalFormula
    | Or           : modalFormula -> modalFormula -> modalFormula
    | Implies      : modalFormula -> modalFormula -> modalFormula 
.

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

Declare Custom Entry modal.
Declare Scope modal_scope.

(*
Algumas Convenções:
    Sempre encapsular formulas modais com [! !], mesmo se seja somente uma única formula
    Usar [ ] ao invés de nil
    Encapsular expressões do tipo #n com paranteses, isto é, sempre escrever (#n) no lugar de #n
*)

Record Frame : Type := {
  W : Set;
  R : W -> W -> Prop;
}.

Record Model : Type := {
  F : Frame; 
  v : nat -> (W F) -> Prop; 
}.

Notation "{ W -- R }" := (Build_Frame W R).
Notation "[ F -- V ]" := (Build_Model F V).

Notation "x"          := x (in custom modal at level 0, x ident).
Notation "( x )"      := x (in custom modal, x at level 99) : modal_scope.
Notation "[! m !]"    := m (at level 0, m custom modal at level 99) : modal_scope.
Notation " p -> q "   := (Implies p q) (in custom modal at level 13, right associativity).
Notation " p \/ q "   := (Or p q)      (in custom modal at level 12, left associativity).
Notation " p /\ q "   := (And p q)     (in custom modal at level 11, left associativity).
Notation " ~ p "      := (Neg p)       (in custom modal at level 9, right associativity).
Notation " [] p "     := (Box p)       (in custom modal at level 9, right associativity).
Notation " <> p "     := (Dia p)       (in custom modal at level 9, right associativity).
Notation " # p  "     := (Lit p)       (in custom modal at level 1, no associativity, p constr).
Notation "x :: l"     := (cons x l)    (in custom modal at level 60, right associativity).
Notation "[ ]"            := (nil)     (in custom modal).
Notation "[ x ; .. ; y ]" := (cons x .. (cons y nil) ..) (in custom modal).
Notation "x ++ y"     := (app x y)     (in custom modal at level 60, right associativity).

Notation "[ ]"            := nil.
Notation "x :: l"         := (cons x l) (at level 60, right associativity).
Notation "[ x ; .. ; y ]" := (cons x .. (cons y nil) ..).

Open Scope modal_scope.


Fixpoint formula_valuation (M: Model) (w: W (F M)) (phi: modalFormula): Prop :=
  match phi with
  | Lit     x            => v M x w 
  | Box     psi          => forall w': W (F M), R (F M) w w' -> formula_valuation M w' psi
  | Dia     psi          => exists w': W (F M), R (F M) w w' /\ formula_valuation M w' psi
  | Neg     psi          => ~formula_valuation M w psi
  | And     psi  gamma   => formula_valuation M w psi /\ formula_valuation M w gamma
  | Or      psi  gamma   => formula_valuation M w psi \/ formula_valuation M w gamma
  | Implies psi  gamma   => formula_valuation M w psi -> formula_valuation M w gamma
  end.

Definition valid_in_model (M: Model) (phi: modalFormula): Prop :=
  forall w: W (F M), formula_valuation M w phi.

Definition theory := list modalFormula.

Fixpoint theory_valid_in_model (M: Model) (Gamma: theory): Prop :=
  match Gamma with
  | nil => True
  | h :: t => (valid_in_model M h) /\ (theory_valid_in_model M t)
  end.

Definition entails (M: Model) (Gamma: theory) (phi: modalFormula): Prop :=
  theory_valid_in_model M Gamma -> valid_in_model M [! phi !].

Definition theory_valid_in_frame (Gamma: theory) (phi: modalFormula): Prop :=
  forall M, theory_valid_in_model M Gamma -> valid_in_model M [! phi !].

Definition equivalence (phi psi: modalFormula) : Prop := 
  (theory_valid_in_frame [! [phi] !] [! psi !] ) /\ (theory_valid_in_frame [! [psi] !] [! phi !]).

Definition valid_formula (phi: modalFormula): Prop :=
  forall F: Frame, theory_valid_in_frame [! [phi] !] [! phi !].

Notation "M ; w ||- p" := (formula_valuation M w p) 
  (at level 110, right associativity).

Notation "M ||= p" := (valid_in_model M p) 
  (at level 110, right associativity).

Notation "G |= p" := (theory_valid_in_frame G p) 
  (at level 110, no associativity).

Notation "M ; G |- p" := (entails M G p)
  (at level 110, no associativity).

Notation "p =|= q" := (equivalence p q) 
  (at level 110, no associativity).

Notation "|= p" := (valid_formula p)
  (at level 110, no associativity).

(*Print Custom Grammar modal.*)
(*
Definition teste (M: Model) (w: W (F M)) (p q: modalFormula) (G: theory): Prop :=
  G |= p.
*)

(* If a formula belongs in a theory that is valid in a model, then it's valid in that model. *)
Theorem entailment_valid_in_model:
  forall Gamma phi,
  In phi Gamma ->
  forall M,
  M; Gamma |- [! phi !].
Proof.
  intros.
  induction Gamma.
  - inversion H.
  - simpl in H.
    destruct H.
    + destruct H.
      unfold entails; intros.
      destruct H; auto.
    + unfold entails; intro.
      apply IHGamma; auto.
      destruct H0; auto.
Qed.

(* Semantic entailment is reflexive *)
Theorem reflexive_entailment:
  forall M Gamma phi,
  M; phi::Gamma |- [! phi !].
Proof.
  intros.
  apply entailment_valid_in_model.
  constructor; auto.
Qed.

Lemma theory_valid_in_model_union:
  forall M Gamma delta,
  theory_valid_in_model M (Gamma ++ delta) -> 
  (theory_valid_in_model M Gamma /\ 
  theory_valid_in_model M delta).
Proof.
    intros.
    induction Gamma.
    - simpl in *.
      split; tauto.
    - simpl in *.
      apply and_assoc.
      destruct H as [left right]; split.
      + assumption.
      + apply IHGamma.
        assumption.
Qed.

Theorem  transitive_entailment:
  forall M Gamma delta phi psi gamma,
  (M; phi::Gamma |- [! psi !]) /\ 
  (M; psi::delta |- [! gamma !]) -> 
  (M; phi::Gamma++delta |- [! gamma !]).
Proof.
  intros.
  unfold entails in *.
  destruct H as [H1 H2].
  intros; apply H2.
  simpl in *; destruct H as [left right].
  apply theory_valid_in_model_union in right; destruct right as [ModalG ModalD].
  tauto.
Qed.

Theorem exchange: 
  forall M Gamma phi psi gamma,
  (M; phi::psi::Gamma |- [! gamma !]) -> 
  (M; psi::phi::Gamma |- [! gamma !]).
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
    forall phi psi tail,
    transpose (phi:: psi :: tail) (psi :: phi:: tail)
  | transpose_tail:
    forall phi tail1 tail2,
    transpose tail1 tail2 -> transpose (phi :: tail1) (phi :: tail2)
  | transpose_refl:
    forall psi,
    transpose psi psi
  | transpose_trans:
    forall phi psi gamma,
    transpose phi psi -> transpose psi gamma -> transpose phi gamma
  | transpose_sym:
    forall phi psi,
    transpose phi psi -> transpose psi phi.

Lemma transpose_in:
  forall {T} xs ys,
  transpose xs ys ->
  forall phi: T,
  In phi xs <-> In phi ys.
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

Theorem transpose_entailment:
  forall M Gamma delta phi,
  transpose Gamma delta ->
  (M; Gamma |- [! phi !]) <-> 
  (M; delta |- [! phi !]).
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
  forall M Gamma phi psi,
  (M; phi::phi::Gamma |- [! psi !]) -> 
  (M; phi::Gamma |- [! psi !]).
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
  forall M Gamma delta phi,
  (M; Gamma |- [! phi !]) -> 
  (M; Gamma++delta |- [! phi !]).
Proof.
  unfold entails in *; intros.
  apply H.
  apply theory_valid_in_model_union with (delta := delta).
  assumption.
Qed.

(* Reflexividade *)
Definition reflexive_frame (F: Frame): Prop :=
  forall w, R F w w.

(* Transitividade *)
Definition transitive_frame (F: Frame): Prop :=
  forall w w' w'': W F,
  (R F w w' /\ 
  R F w' w'') -> 
  R F w w''.

(* Simetria *)
Definition symmetric_frame (F: Frame): Prop :=
  forall w w',
  R F w w' -> 
  R F w' w.

(* Euclidiana *)
Definition euclidean_frame (F: Frame): Prop :=
  forall w w' w'',
  (R F w w' /\ 
  R F w w'') -> 
  R F w' w''.

(* Serial *)
Definition serial_frame (F: Frame): Prop :=
  forall w,
  exists w', R F w w'.

(* Funcional *)
Definition functional_frame (F: Frame) : Prop :=
  forall w w' w'',
  (R F w w' /\ 
  R F w w'') -> 
  w' = w''.

(* Densa*)
Definition dense_frame (F: Frame) : Prop :=
  forall w w',
  exists w'',
  R F w w' -> 
  (R F w w'' /\ 
  R F w'' w').

(* Convergente *)
Definition convergent_frame (F: Frame): Prop :=
  forall w x y,
  exists z,
  (R F w x /\ 
  R F w y) -> 
  (R F x z /\ R F y z).
