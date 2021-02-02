Require Import Modal_Library Deductive_System List Classical.

Definition Consistent (A: axiom -> Prop) (G : theory) : Prop := 
  forall p,
  ~ (A; G |-- [! p /\ ~p !]).

Definition Maximal_Consistent (A: axiom -> Prop) (G : theory) : Prop :=
  forall p,
  ~(In [! p !] G /\  In [! ~ p !] G) /\ Consistent A G.

Lemma lema_1 :
  forall A Delta Gamma,
  (Consistent A Delta /\ 
  subset Gamma Delta) -> 
  Consistent A Gamma.
Proof.
  intros.
  destruct H.
  unfold Consistent, not in *; intros.
  eapply H;
  eapply deduction_weak.
  exact H0.
  exact H1.
Qed.

Section Lindebaum.

Variable P: nat -> modalFormula.
Variable Gamma: theory.
Variable A: axiom -> Prop.

Inductive Lindenbaum_set : nat -> theory -> Prop :=
  | Lindenbaum_zero:
    Lindenbaum_set 0 Gamma
  | Lindenbaum_succ1:
    forall n Delta,
    Lindenbaum_set n Delta ->
    Consistent A (P n :: Delta) ->
    Lindenbaum_set (S n) (P n :: Delta)
  | Lindenbaum_succ2:
    forall n Delta,
    Lindenbaum_set n Delta ->
    ~Consistent A (P n :: Delta) ->
    Lindenbaum_set (S n) Delta.

Lemma construct_set: (*existe 1 conjunto de Lindenbaum*)
  forall n,
  exists Delta, 
  Lindenbaum_set n Delta.
Proof.
  intros; induction n.
  - exists Gamma.
    constructor.
  - destruct IHn as (Delta, ?H). 
    edestruct classic with (Consistent A (P n :: Delta)).
    + eexists.
      apply Lindenbaum_succ1; eauto.
    + eexists.
      apply Lindenbaum_succ2; eauto.
Qed.

(*
  P/ todo conjunto de Lindenbaum Delta, Gamma é subconjunto dele
*)

Lemma Lindenbaum_subset: 
  forall n Delta,
  Lindenbaum_set n Delta -> 
  subset Gamma Delta.
Proof.
  unfold subset; intros.
  induction H.
  - assumption.
  - intuition.
  - assumption.
Qed.

End Lindebaum.

(*
############################################
############################################
############################################
*)

Section Lindebaum'.

Variable P: nat -> modalFormula.
Variable A: axiom -> Prop.
Variable Gamma: theory.
Variable G: Consistent A Gamma.

Inductive Lindenbaum_set': nat -> theory -> Prop :=
  | Lindenbaum_zero':
    Lindenbaum_set' 0 Gamma
  | Lindenbaum_succ1':
    forall n Delta,
    Lindenbaum_set' n Delta ->
    Consistent A (P n :: Delta) ->
    Lindenbaum_set' (S n) (P n :: Delta)
  | Lindenbaum_succ2':
    forall n Delta,
    Lindenbaum_set' n Delta ->
    ~Consistent A (P n :: Delta) ->
    Lindenbaum_set' (S n) Delta.

Lemma construct_set': (*existe 1 conjunto de Lindenbaum*)
  forall n,
  exists Delta,
  Lindenbaum_set' n Delta.
Proof.
  intros; induction n.
  - exists Gamma.
    constructor.
  - destruct IHn as (Delta, ?H). 
    edestruct classic with (Consistent A (P n :: Delta)).
    + eexists.
      apply Lindenbaum_succ1'; eauto.
    + eexists.
      apply Lindenbaum_succ2'; eauto.
Qed.

(*
  P/ todo conjunto de Lindenbaum Delta, Gamma é subconjunto dele
*)

Lemma Lindenbaum_subset':  (*Exatamente o Lema 5 do texto*)
  forall n Delta,
  Lindenbaum_set' n Delta -> 
  subset Gamma Delta.
Proof.
  unfold subset; intros.
  induction H; try (assumption || intuition).
Qed.

(*
Provar os lemas 3-9 do texto
Pulei o Lema 4 pois acho que é impossível provar da maneira que
  foi representado o conjunto de Lindenbaum
*)

Lemma Lema3:
  forall n Delta,
  0 <= n -> 
  Lindenbaum_set' n Delta ->
  Consistent A Delta.
Proof.
  intros n Delta H1 H2.
  induction H2 as [ | | n' Delta' H2' IH2]; try assumption.
  - inversion H1.
    apply IH2 in H2.
    assumption.
Qed.

(* Lemma Lema6:
  forall k n Delta1 Delta2, *)

End Lindebaum'.

(*
############################################
############################################
############################################
*)

(*
  P/ todo conjunto Gamma, se ele é consistente então existe um conjunto
  maximal consistente Delta que contém Gamma
*)
Lemma Lindenbaum: 
  forall A Gamma, 
  Consistent A Gamma -> 
  exists Delta, 
  (Maximal_Consistent A Delta /\ 
  subset Gamma Delta).
Proof.
  admit. 
Admitted.