Require Import Modal_Library Deductive_System List Classical Bool.

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

Fixpoint union (Delta1 Delta2: theory): theory :=
  match Delta1, Delta2 with
    | nil, nil => nil
    | h::t, nil => h :: t
    | nil, h::t => h :: t
    | h1::t1, h2::t2 => if negb (modalequiv h1 h2) then h1 :: h2 :: union t1 t2
                        else h1 :: union t1 t2
  end
.

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

Inductive Lindenbaum_set'': nat -> theory -> Prop :=
  | Lindenbaum_zero'':
    Lindenbaum_set'' 0 Gamma
  | Lindenbaum_succ1'':
    forall n Delta,
    Lindenbaum_set'' n Delta ->
    Consistent A (P n :: Delta) ->
    Lindenbaum_set'' (S n) (P n :: Delta)
  | Lindenbaum_succ2'':
    forall n Delta,
    Lindenbaum_set'' n Delta ->
    ~Consistent A (P n :: Delta) ->
    Lindenbaum_set'' (S n) Delta
  | Lindenbaum_union1:
    forall n1 n2 Delta1 Delta2,
    Lindenbaum_set'' n1 Delta1 ->
    Lindenbaum_set'' n2 Delta2 ->
    n2 <= n1 ->
    Lindenbaum_set'' n1 (union Delta1 Delta2)
  | Lindenbaum_union2:
    forall n1 n2 Delta1 Delta2,
    Lindenbaum_set'' n1 Delta1 ->
    Lindenbaum_set'' n2 Delta2 ->
    n1 <= n2 ->
    Lindenbaum_set'' n2 (union Delta1 Delta2)
.

Definition BConsistent (A: axiom -> Prop) (G : theory) : bool := 
  match (forall p, ~ (A; G |-- [! p /\ ~p !])) with
    | True  => true
  end
.

Fixpoint Construct_Lindenbaum (n:nat) (Delta:theory): theory :=
  match n with
    | O    => Gamma
    | S n' => if BConsistent A (P n :: Delta) then
                union (P n :: Delta) (Construct_Lindenbaum n' Delta)
              else
                union Delta (Construct_Lindenbaum n' Delta)
  end
.

(*
  TODO: Confirmar que a segunda definição indutiva esta correta
        Verificar se a função é equivalente a alguma das 
          definições indutivas
        Fazer os Lemas 4, 6, 7, 8 e 9 do texto
*)

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