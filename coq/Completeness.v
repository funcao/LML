Require Import Equality Relations.
Require Import Modal_Library Modal_Notations Modal_Tactics Deductive_System Soundness List Classical Bool Sets.

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

(* -------------------------------------------------------------------------- *)

Lemma deduction_subset:
  forall A G1 G2,
  Subset G1 G2 ->
  forall p,
  deduction A G1 p -> deduction A G2 p.
Proof.
  induction 2.
  - constructor 1.
    apply H.
    assumption.
  - econstructor 2.
    + eassumption.
    + assumption.
  - econstructor 3.
    + apply IHdeduction1.
      assumption.
    + apply IHdeduction2.
      assumption.
  - econstructor 4.
    assumption.
Qed.

(* -------------------------------------------------------------------------- *)

Section Lindebaum.

  Variable A: axiom -> Prop.

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
    intros.
    unfold Subset. intros. destruct p. 
    - edestruct classic.
      + apply Insert_valid.
        * eauto.
        * right; assumption.
      + apply Insert_invalid.
        * assumption.
        * right; assumption.
    - apply Insert_skip.
      assumption.
  Qed.

  Lemma delta_subset_of_max:
    forall n,
    Subset (Delta n) Max.
  Proof.
    unfold Subset; intros.
    unfold Max, UnionOf.
    eauto.
  Qed.

  Lemma gamma_subset_of_max:
    Subset G Max.
  Proof.
    unfold Subset; intros.
    unfold Max, UnionOf.
    exists O; simpl.
    assumption.
  Qed.

  Lemma delta_is_monotonic:
    forall n m,
    n <= m ->
    Subset (Delta n) (Delta m).
  Proof.
    induction 1; intros t ?.
    - assumption.
    - simpl.
      apply subset_of_insert.
      apply IHle.
      assumption.
  Qed.

  Lemma insert_contains_formula:
    forall D p,
    Insert (Some p) D [! p !] \/ Insert (Some p) D [! ~p !].
  Proof.
    intros.
    edestruct classic.
    - left. 
      apply Insert_valid.
      + eauto.
      + unfold Union.
        left.
        constructor.
    - right.
      apply Insert_invalid.
      + assumption.
      + unfold Union.
        left.
        constructor.
  Qed.

  Lemma max_is_maximal:
    forall p,
    Max [! p !] \/ Max [! ~p !].
  Proof.
    intros.
    edestruct insert_contains_formula with (Delta (encode p)) p.
    - left.
      exists (1 + encode p); simpl.
      rewrite countable.
      assumption.
    - right.
      exists (1 + encode p); simpl.
      rewrite countable.
      assumption.
  Qed.

  Hypothesis extending_K: Subset K A.

  Lemma consistency_negation:
    forall D f,
    Consistent A D ->
    ~Consistent A (Union (Singleton f) D) ->
    Consistent A (Union (Singleton [! ~f !]) D).
  Proof.
    intros.
    unfold Consistent in H0.
    assert (exists p, (A; Union (Singleton f) D |-- [! p /\ ~p !])).
    edestruct classic.
    exact H1.
    exfalso.
    apply H0; clear H0.
    intros p ?.
    apply H1; clear H1.
    exists p.
    assumption.
    clear H0.
    destruct H1 as (p, ?).
    assert (A; D |-- [! f \/ ~f !]).
    apply derive_excluded_middle.
    apply extending_K.
    apply modal_deduction in H0.
    assert (A; D |-- [! ~f !]).
    admit.
    intros q ?.
    apply H with [! ~f -> q !]; clear H H2.
    apply modal_deduction in H3.
    admit.
    apply extending_K.
    apply extending_K.
  Admitted.

  Lemma insert_preserves_consistency:
    forall D p,
    Consistent A D -> Consistent A (Insert p D).
  Proof.
    intros.
    destruct p.
    - destruct classic with (Consistent A (Union (Singleton f) D)).
      + intros p ?.
        eapply H0.
        apply deduction_subset with (Insert (Some f) D).
        * intros t ?.
          dependent destruction H2; firstorder.
        * exact H1.
      + intros p ?.
        eapply consistency_negation; eauto.
        apply deduction_subset with (Insert (Some f) D).
        * intros t ?.
          dependent destruction H2; firstorder.
        * exact H1.
    - intros p ?.
      apply H with p; clear H.
      apply deduction_subset with (Insert None D).
      + inversion 1.
        assumption.
      + assumption.
  Qed.

  Lemma delta_is_consistent:
    Consistent A G ->
    forall n,
    Consistent A (Delta n).
  Proof.
    induction n.
    - simpl.
      assumption.
    - simpl.
      apply insert_preserves_consistency.
      assumption.
  Qed.

  (* If we have a derivation using Max, then, as the proof tree is finite, there
     must be a n that is large enough for that. We don't require that it is
     minimal. *)
  Lemma find_largest_delta:
    forall p,
    (A; Max |-- p) ->
    exists n,
    (A; Delta n |-- p).
  Proof.
    intros.
    dependent induction H.
    (* This is a premise. We can find which n is needed! *)
    - destruct H as (n, ?).
      exists n.
      econstructor 1.
      assumption.
    (* This is an axiom; it works for any n! *)
    - exists 0.
      econstructor 2.
      + eassumption.
      + reflexivity.
    (* This is modus poenens. This means that we need the *largest* n between
       the two branches! *)
    - destruct IHdeduction1 as (n, ?); auto.
      destruct IHdeduction2 as (m, ?); auto.
      exists (max n m).
      econstructor 3.
      (* Left branch used n, can be rebuilt using (max n m)! *)
      + apply deduction_subset with (Delta n).
        * apply delta_is_monotonic.
          auto with arith.
        * eassumption.
      (* Right branch used m, can be rebuilt using (max n m)! *)
      + apply deduction_subset with (Delta m).
        * apply delta_is_monotonic.
          auto with arith.
        * assumption.
    (* For necessitation, it works even for Delta 0 as we drop the context. *)
    - exists 0; simpl.
      constructor 4.
      assumption.
  Qed.

  Lemma max_is_consistent:
    Consistent A G ->
    Consistent A Max.
  Proof.
    intros ? p ?.
    (* If Max |- p /\ ~p, then there is some n that is enough for that. *)
    edestruct find_largest_delta as (n, ?); eauto.
    (* Given that we know such n, Delta n is consistent as well. *)
    assert (Consistent A (Delta n)).
    - apply delta_is_consistent.
      assumption.
    - (* Since Delta n is consistent, it's a contradiction that we have both
         p and ~p in it. *)
      apply H2 with p.
      assumption.
  Qed.

  Theorem lindebaum:
    Consistent A G ->
    exists D,
    Consistent A D /\ Maximal D /\ Subset G D.
  Proof.
    intros.
    exists Max; split.
    - apply max_is_consistent.
      assumption.
    - split.
      + exact max_is_maximal.
      + exact gamma_subset_of_max.
  Qed.

End Lindebaum.

Section CanonicalModel.

  Definition canonical_accessibility: relation theory :=
    fun w v =>
      forall p, w [! []p !] -> v p.

  Definition canonical_frame :=
    Build_Frame theory canonical_accessibility.

  Definition canonical_valuation: nat -> theory -> Prop :=
    fun p w =>
      Maximal w /\ w [! #p !].

  Definition canonical_model :=
    Build_Model canonical_frame canonical_valuation.

End CanonicalModel.

Goal
  forall A G p,
  Subset K A ->
  ~(A; G |-- p) -> Consistent A (Union (Singleton [! ~p !]) G).
Proof.
  admit.
Admitted.

Theorem completeness:
  forall G p,
  (G ||= p) -> (S5; G |-- p).
Proof.
  intros.
  edestruct classic.
  - exact H0.
  - exfalso.
    admit.
Admitted.
