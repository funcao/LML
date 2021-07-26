Require Import Modal_Library Deductive_System List Classical Bool.

Section Lindebaum.

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

(*
  Delta 0 := Gamma
  Delta (n + 1) := Delta n \union (phi n + 1)
                      se consistente
                   Delta n \union (~phi n + 1)
                      senao

  Delta = Union (n: N) Delta n

*)

Section Lindebaum'.

(*Inductive deduction (A: axiom -> Prop): theory -> modalFormula -> Prop*)
(*Isso é um problema*)
 Definition Consistent' (A: axiom -> Prop) (G : theory) : Prop := 
  forall p,
  ~ (A; G |-- [! p /\ ~p !]).

Definition Maximal_Consistent' (A: axiom -> Prop) (G : theory) : Prop :=
  forall p,
  ~(In [! p !] G /\  In [! ~ p !] G) /\ Consistent A G.

Variable P: nat -> modalFormula. 
Variable A: axiom -> Prop.
Variable Gamma: modalFormula -> Prop. (*X -> Prop == Conjunto de X*)
(*Variable G: Consistent A Gamma. Essa definição não funciona com a formulação
                                  atual de Gamma*)

Inductive Singleton {T} (t: T): T -> Prop := (*conjunto de um único*)
  | Singleton_mk: Singleton t t.             (*elemento*)

Definition Union {T} (A B: T -> Prop): T -> Prop :=
  fun t => A t \/ B t.

Fixpoint Delta (n: nat): modalFormula -> Prop := (*arrumar vc pra ver*)
  match n with                                   (*consistencia*)
  | 0   => Gamma
  | S n => Union (Delta n) (Singleton (P n))
  end.

Definition Subset {T} (A B: T -> Prop): Prop :=
  forall t: T,
  A t -> B t.

Goal
  forall n,
  Subset (Delta n) (Delta (S n)).
Proof.
  intros.
  unfold Subset; intros.
  simpl.
  unfold Union.
  left; assumption.
Qed.

Goal
  forall n,
  Delta (S n) (P n).
Proof.
  intros; simpl.
  unfold Union.
  right.
  constructor.
Qed.

(*I é um tipo de indices, S é um conjunto de T's indexados por I's*)
Inductive UnionOf {I} {T} (S: I -> T -> Prop): T -> Prop :=
  | UnionOf_mk:
    forall i: I,
    Subset (S i) (UnionOf S).

Definition MaxDelta: modalFormula -> Prop :=  UnionOf Delta.

Goal
  forall n,
  Subset (Delta n) MaxDelta.
Proof.
  intros.
  unfold Subset; intros.
  unfold MaxDelta.
  apply UnionOf_mk with n.
  assumption.
Qed.

Inductive FormulaSet: nat -> modalFormula -> Prop := (*deixando vc aqi*)
  | FLit: forall n m, m < n -> FormulaSet n (P m)    (*por enquanto*)
  | FNeg: forall n f, 
                     FormulaSet n f -> (*mudar o n ?*)
                     FormulaSet n (Neg f)
  | FBox: forall n f, 
                     FormulaSet n f -> 
                     FormulaSet n (Box f)
  | FDia: forall n f, 
                     FormulaSet n f -> 
                     FormulaSet n (Dia f)
  | FAnd: forall n1 f1 n2 f2, 
                     FormulaSet n1 f1 -> 
                     FormulaSet n2 f2 ->
                     FormulaSet (n1 * n2) (And f1 f2)
  | FOr: forall n1 f1 n2 f2, 
                     FormulaSet n1 f1 -> 
                     FormulaSet n2 f2 ->
                     FormulaSet (n1 + n2) (Or f1 f2)
  | FImplies: forall n1 f1 n2 f2, (*arrumar operador entre n1 e n2*)
                     FormulaSet n1 f1 -> 
                     FormulaSet n2 f2 ->
                     FormulaSet (n1 * n2) (Implies f1 f2).






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
