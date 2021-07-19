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
(*
Pn é um átomo, i.e., se insiro somente Pn's no conj. de lindenbaum,
nunca terei um conjunto de todas as formulas, apenas um conjunto de todos
os atomos
*)
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

Inductive FormulaSet (n: nat): modalFormula -> Prop := 
  | FLit: FormulaSet n (P n)
  | FNeg: FormulaSet n (Neg (P n))
  | FBox: FormulaSet n (Box (P n))
  | FDia: FormulaSet n (Dia (P n))
  | FAnd (f: modalFormula): FormulaSet n f ->
         FormulaSet n (And (P n) f)
  | FOr (f: modalFormula): FormulaSet n f ->
         FormulaSet n (Or (P n) f)
  | FImplies (f: modalFormula): FormulaSet n f ->
         FormulaSet n (Implies (P n) f)
.

Inductive FormulaSet': nat -> modalFormula -> Prop := 
  (*Não sei se isso \/ está certo*)
  | F'Lit: forall n m, m < n -> FormulaSet' n (P m) 
  | F'Neg: forall n f, 
                     FormulaSet' n f -> (*mudar o n ?*)
                     FormulaSet' n (Neg f)
  | F'Box: forall n f, 
                     FormulaSet' n f -> 
                     FormulaSet' n (Box f)
  | F'Dia: forall n f, 
                     FormulaSet' n f -> 
                     FormulaSet' n (Dia f)
  | F'And: forall n1 f1 n2 f2, 
                     FormulaSet' n1 f1 -> 
                     FormulaSet' n2 f2 ->
                     FormulaSet' (n1 * n2) (And f1 f2)
  | F'Or: forall n1 f1 n2 f2, 
                     FormulaSet' n1 f1 -> 
                     FormulaSet' n2 f2 ->
                     FormulaSet' (n1 + n2) (Or f1 f2)
  | F'Implies: forall n1 f1 n2 f2, (*arrumar operador entre n1 e n2*)
                     FormulaSet' n1 f1 -> 
                     FormulaSet' n2 f2 ->
                     FormulaSet' (n1 * n2) (Implies f1 f2)
.

Theorem FormulaSet'Increment:
  forall n m f,
  m < n -> FormulaSet' m f -> FormulaSet' n f.
Proof.
  clear A Gamma G.
  intros n m f H1 H2.
  
Admitted.

Theorem FormulaSet'Sound:
  forall n f,
  FormulaSet' n f.
Proof.
Admitted.

Inductive LindenbaumSet: theory -> Prop := 
  | LindenbaumZero: LindenbaumSet 0 Gamma
  | 
.
(*  
Inductive Lindenbaum_set' : nat -> theory -> Prop :=
  | Lindenbaum_zero':
    Lindenbaum_set' 0 Gamma
  | Lindenbaum_succ1:'
    forall n Delta,
    Lindenbaum_set' n Delta ->
    Consistent A (P n :: Delta) ->
    Lindenbaum_set' (S n) (P n :: Delta)
  | Lindenbaum_succ2':
    forall n Delta,
    Lindenbaum_set' n Delta ->
    ~Consistent A (P n :: Delta) ->
    Lindenbaum_set' (S n) Delta.

Lemma construct_lindenbaum':
  forall n,
  exists Delta Delta1,
  Delta1 = Construct_Lindenbaum n Delta. 

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