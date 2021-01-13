Require Import Modal_Library Deductive_System List Classical.

Definition Consistency (A: axiom -> Prop) (G : theory) : Prop := 
  forall p,
  ~ (A; G |-- [! p /\ ~p !]).

Definition Maximal_Consistency (A: axiom -> Prop) (G : theory) : Prop :=
  forall p,
  ~(In [! p !] G /\  In [! ~ p !] G) /\ Consistency A G.

Lemma lema_1 :
  forall A Delta Gamma,
  (Consistency A Delta /\ 
  subset Gamma Delta) -> 
  Consistency A Gamma.
Proof.
  intros.
  destruct H.
  unfold Consistency, not in *; intros.
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
    Consistency A (P n :: Delta) ->
    Lindenbaum_set (S n) (P n :: Delta)
  | Lindenbaum_succ2:
    forall n Delta,
    Lindenbaum_set n Delta ->
    ~Consistency A (P n :: Delta) ->
    Lindenbaum_set (S n) Delta.

Lemma construct_set:
  forall n,
  exists Delta, 
  Lindenbaum_set n Delta.
Proof.
  intros; induction n.
  - exists Gamma.
    constructor.
  - destruct IHn as (Delta, ?H). 
    edestruct classic with (Consistency A (P n :: Delta)).
    + eexists.
      apply Lindenbaum_succ1; eauto.
    + eexists.
      apply Lindenbaum_succ2; eauto.
Qed.

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

Lemma Lindenbaum:
  forall A Gamma,
  Consistency A Gamma -> 
  exists Delta, 
  (Maximal_Consistency A Delta /\ 
  subset Gamma Delta).
Proof.
  admit. 
Admitted.