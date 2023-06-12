Require Import Arith List ListSet Notations Classical Relations.
Export ListNotations.

(*** Core File of the Library ***)

(*Definition of formulas, literals (or atoms) are represented as natural numbers*)
Inductive formula: Set :=
  | Lit    : nat -> formula
  | Neg    : formula -> formula
  | Box    : formula -> formula
  | Dia    : formula -> formula
  | And    : formula -> formula -> formula
  | Or     : formula -> formula -> formula
  | Implies: formula -> formula -> formula.

(* Size of a formula of the modal language *)
Fixpoint modalSize (f:formula): nat :=
  match f with 
  | Lit     x     => 1
  | Neg     p1    => 1 + (modalSize p1)
  | Box     p1    => 1 + (modalSize p1)
  | Dia     p1    => 1 + (modalSize p1)
  | And     p1 p2 => 1 + (modalSize p1) + (modalSize p2)
  | Or      p1 p2 => 1 + (modalSize p1) + (modalSize p2)
  | Implies p1 p2 => 1 + (modalSize p1) + (modalSize p2)
end.

(* Set of literals of a modal formula *)
Fixpoint literals (f:formula): set nat :=
  match f with 
  | Lit     x     => set_add eq_nat_dec x (empty_set nat)
  | Dia     p1    => literals p1
  | Box     p1    => literals p1
  | Neg     p1    => literals p1
  | And     p1 p2 => set_union eq_nat_dec (literals p1) (literals p2)
  | Or      p1 p2 => set_union eq_nat_dec (literals p1) (literals p2)
  | Implies p1 p2 => set_union eq_nat_dec (literals p1) (literals p2) 
end.

(* Definition of frames: pairs of a possibly finite set W of worlds and an acessibility 
  relation R between any two of worlds*)
Record Frame: Type := {
  W: Set;
  R: W -> W -> Prop
}.

(* 
Definition of models: pairs of frames and valuation functions, functions which assign
truth values to literals -- or assign sets of worlds to given literals, these are meant to be
read as the worlds in which that literal is true, eg:
v(5) = {w0, w1, w2} means that literal 5 (in Latex we may write this as p_5) is true in
worlds w0, w1 and w2
*)
Record Model: Type := {
  F: Frame;
  v: nat -> (W F) -> Prop
}.

(* TODO: Reimplement as a pair? *)

(* Definition of the valuation of formulas, note the usage of the valuation function of models
  in the Lit case. This definitions follows usual definitions of modal valuation *)
Fixpoint fun_validation (M: Model) (w: W (F M)) (φ: formula): Prop :=
  match φ with
  | Lit     x   => v M x w 
  | Box     ψ   => forall w', R (F M) w w' -> fun_validation M w' ψ
  | Dia     ψ   => exists w', R (F M) w w' /\ fun_validation M w' ψ
  | Neg     ψ   => ~fun_validation M w ψ
  | And     ψ Ɣ => fun_validation M w ψ /\ fun_validation M w Ɣ
  | Or      ψ Ɣ => fun_validation M w ψ \/ fun_validation M w Ɣ
  | Implies ψ Ɣ => fun_validation M w ψ -> fun_validation M w Ɣ
  end.

(* TODO: Change order of rules to match what is in the paper *)

(* Definition of satisfiability in a model: a formula is valid in a model if it is true in
  all worlds of that model *)
Definition validate_model (M: Model) (φ: formula): Prop :=
  forall w, fun_validation M w φ.

(******  Finite theories and entailment ******)

(* Theories are finite sets (lists) of formulas *)
Definition theory := list formula.

(** 
  Definition of Semantic Entailment: 
  A theory T semantically entails a formula phi in a Model M
  iff for all formulas psi in T, psi being valid in M imples that phi is too 
**)

(* Helper function, tests if a given theory is valid in a model *)
Fixpoint theoryModal (M: Model) (Γ: theory): Prop :=
  match Γ with
  | nil => True
  | h :: t => (validate_model M h) /\ (theoryModal M t)
  end.

(* Entailment *)
Definition entails (M: Model) (Γ: theory) (φ: formula): Prop :=
  theoryModal M Γ -> validate_model M φ.

(***** Proof of some Structural Properties of Semantic Entailment ****)

(* If a formula phi is in a theory T, then T entails phi *)
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

(* I don't know *)
Theorem reflexive_deduction:
  forall M Γ φ,
  entails M (φ :: Γ) φ.
Proof.
  intros.
  apply exact_deduction.
  constructor; auto.
Qed.

(* Auxiliary lemma to following proof, if a theory T1 union a theory T2 is valid 
  then both T1 and T2 are valid *)
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

(* Semantic Entailment is Transitive, if T1 appended phi entails psi and T2 appended psi entails gamma
  then phi appended T1 ++ T2 entails gamma, where ++ is the operation of concatenating lists *)
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

(* Exchange of terms in a semantic entailment, i.e., the order of the formulas in a theory T does
  not matter for entailment *)
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

(* I don't know *)
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

(* I don't know *)
Lemma transpose_in:
  forall {T} xs ys,
  transpose xs ys ->
  forall φ: T,
  In φ xs <-> In φ ys.
Proof.
  induction 1; intros.
  - split; intros; try (repeat (destruct H; intuition)).
  - split; intros; destruct H0.
    + destruct H0.
      left; auto.
    + right; apply IHtranspose.
      assumption.
    + destruct H0.
      left; auto.
    + right; apply IHtranspose.
      assumption.
  - intuition.
  - split; intros.
    + apply IHtranspose2.
      apply IHtranspose1.
      assumption.
    + apply IHtranspose1.
      apply IHtranspose2.
      assumption.
  - split; intros; 
    apply IHtranspose; auto.
Qed.

Theorem tranpose_deduction:
  forall M Γ ẟ φ,
  transpose Γ ẟ ->
  entails M Γ φ <-> entails M ẟ φ.
Proof.
  induction 1.
  - split; intros; apply exchange; assumption.
  - clear H.
    split; intros; unfold entails in *; 
    intros; destruct H0.
    + edestruct IHtranspose as [H2 _].
      apply H2; intros; try (auto; apply H; split; auto).
    + edestruct IHtranspose as [_ H2].
      apply H2; intros; try (auto; apply H; split; auto).
  - intuition.
  - split; intros.
    + apply IHtranspose2.
      apply IHtranspose1.
      assumption.
    + apply IHtranspose1.
      apply IHtranspose2.
      assumption.
  - split; intros; apply IHtranspose; auto.
Qed.


(* Idempotence of entailment: if T entails phi, then adding formula psi to 
  T preserves the entailment *)
Theorem idempotence:
  forall M Γ φ ψ,
  entails M (φ :: φ :: Γ) ψ -> 
  entails M (φ :: Γ) ψ.
Proof.
  intros.
  unfold entails in *; intros.
  apply H; simpl in *.
  split; destruct H0; try apply H0.
  split; [apply H0 | apply H1].
Qed.

(* Monotonicity of entailment: if T1 entails phi, then extending T1 by 
  adding T2 preserves the entailment*)
Theorem monotonicity:
  forall M Γ ẟ φ,
  entails M Γ φ -> 
  entails M (Γ ++ ẟ) φ.
Proof.
  unfold entails in *; intros;
  apply H;
  apply theoryModal_union with (ẟ := ẟ);
  assumption.
Qed.

(** 
  Definition of Logical Equivalence: 
    Two formulas are logically equivalent iff, for every model M, 
    if T1 := {phi} entails psi and T2 := {psi} entails phi
**)

(* Generalized Entailment *)
Definition entails_modal (Γ: theory) (φ: formula): Prop :=
  forall M,
  theoryModal M Γ -> 
  validate_model M φ.

(* Modal Equivalence *)
Definition equivalence (φ ψ: formula): Prop := 
  (entails_modal [φ] ψ) /\ (entails_modal [ψ] φ).

(*** Frame Properties ***)
  (** i.e. what formulas correspond to frames that respect some property **)

(* TODO: Move to another file [?] *)

(* Reflexivity *)
Definition reflexivity_frame (F: Frame): Prop :=
  forall w, R F w w.

(* Transitivity *)
Definition transitivity_frame (F: Frame): Prop :=
  forall w w' w'': W F,
  (R F w w' /\ 
  R F w' w'') -> 
  R F w w''.

(* Simmetry *)
Definition simmetry_frame (F: Frame): Prop :=
  forall w w',
  R F w w' -> 
  R F w' w.

(* Euclideanity(?) *)
Definition euclidian_frame (F: Frame): Prop :=
  forall w w' w'',
  (R F w w' /\ 
  R F w w'') -> 
  R F w' w''.

(* Seriality *)
Definition serial_frame (F: Frame): Prop :=
  forall w,
  exists w', R F w w'.

(* Functionality *)
Definition functional_frame (F: Frame): Prop :=
  forall w w' w'',
  (R F w w' /\ 
  R F w w'') -> 
  w' = w''.

(* Density*)
Definition dense_frame (F: Frame): Prop :=
  forall w w',
  exists w'',
  R F w w' -> 
  (R F w w'' /\ 
  R F w'' w').

(* Convergence *)
Definition convergente_frame (F: Frame): Prop :=
  forall w x y,
  exists z,
  (R F w x /\ 
  R F w y) -> 
  (R F x z /\ R F y z).

(* Converse Well-Foundeness *)

(* 
  Definition of a subset of the set of worlds: A function (say, f) that assigns worlds to Props, 
  such that if  f w then w is in a subset of the set of worlds
*)
Definition SubsetOfW (F: Frame): Type :=
  W F -> Prop.

(* 
  Converse Well Fouded - Where the inverse relation is well founded
  The inverse of a relation R: A -> B is R': B -> A
  In this contexts, this simply means that terms are flipped in R, example:
  if we have R w0 w1, then it's converse will be R' w1 w0

  This is implicity stated bellow
*)
Definition conversely_well_founded_frame (F: Frame): Prop :=
  (* Set-theoretic definition: *)
  forall X: SubsetOfW F, (exists x, X x) -> 
  exists w1, X w1 /\ forall w2, X w2 -> 
  ~ (R F w1 w2).

(* Noetherianity(?) *)
Definition noetherian_frame (F: Frame): Prop :=
  transitivity_frame F /\ conversely_well_founded_frame F.