Require Import Modal_Library Modal_Notations Deductive_System Soundness List Classical Bool Sets.

(* Assume that formulas are constructively countable for now. *)
Axiom encode: formula -> nat.
Axiom decode: nat -> option formula.
Axiom countable: forall p, decode (encode p) = Some p.

Section Properties.

  Variable A: axiom -> Prop.
  Variable G: theory.

  Definition Consistent: Prop :=
    forall p,
    ~(A; G |-- [! p /\ ~p !]).

  Definition Maximal: Prop :=
    forall p,
    G p \/ G [! ~p !].

End Properties.

Section Lindebaum.

  (* For now, assume that the set of axioms is K. *)
  Definition A: axiom -> Prop := K.

  (* Base theory. *)
  Variable G: theory.

  (* Since Coq can't construct a type based on classical reasoning, turn this
     into an inductive type by assuming either a formula or its negation. *)
  Inductive Insert: option formula -> theory -> theory :=
    (* If we don't have a formula, keep D. *)
    | Insert_skip:
      forall D,
      Subset D (Insert None D)

    (* If our formula is sound, insert it. *)
    | Insert_valid:
      forall D p,
      Consistent A (Union (Singleton p) D) ->
      Subset (Union (Singleton p) D) (Insert (Some p) D)

    (* Finally, if our formula is not sound, insert it's opposite. *)
    | Insert_invalid:
      forall D p,
      ~Consistent A (Union (Singleton p) D) ->
      Subset (Union (Singleton [! ~p !]) D) (Insert (Some p) D).

  (* Lindebaum sets. *)
  Fixpoint Delta (n: nat): theory :=
    match n with
    | 0   => G
    | S n => Insert (decode n) (Delta n)
    end.

  (* Maximal set. *)
  Definition Max: theory :=
    UnionOf Delta.

  Lemma subset_of_insert:
    forall D p,
    Subset D (Insert p D).
  Proof.
    admit.
  Admitted.

  Lemma delta_subset_of_max:
    forall n,
    Subset (Delta n) Max.
  Proof.
    admit.
  Admitted.

  Lemma gamma_subset_of_max:
    Subset G Max.
  Proof.
    admit.
  Admitted.

  Lemma delta_is_monotonic:
    forall n m,
    n < m ->
    Subset (Delta n) (Delta m).
  Proof.
    admit.
  Admitted.

  Lemma insert_contains_formula:
    forall D p,
    Insert (Some p) D [! p !] \/ Insert (Some p) D [! ~p !].
  Proof.
    admit.
  Admitted.

  Lemma max_is_maximal:
    forall p,
    Max [! p !] \/ Max [! ~p !].
  Proof.
    admit.
  Admitted.

  Lemma insert_preserves_consistency:
    forall D p,
    Consistent A D -> Consistent A (Insert p D).
  Proof.
    admit.
  Admitted.

  Lemma delta_is_consistent:
    Consistent A G ->
    forall n,
    Consistent A (Delta n).
  Proof.
    admit.
  Admitted.

  Lemma max_is_consistent:
    Consistent A G ->
    Consistent A Max.
  Proof.
    admit.
  Admitted.

  Theorem lindebaum:
    Consistent A G ->
    exists D,
    Consistent A D /\ Maximal D /\ Subset G D.
  Proof.
    admit.
  Admitted.

End Lindebaum.
