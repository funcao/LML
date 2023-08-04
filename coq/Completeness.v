Require Import Decidable Equality Relations.
Require Import Modal_Library Modal_Notations Modal_Tactics Deductive_System Soundness List Classical Bool Sets.
Set Implicit Arguments.

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

Section Completeness.

  Variable A: axiom -> Prop.

  Hypothesis extending_K: Subset K A.

  Section Lindebaum.

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
        Consistent A (Extend p D) ->
        Subset (Extend p D) (Insert (Some p) D)

      (* Finally, if our formula is not sound, insert it's opposite. *)
      | Insert_invalid:
        forall D p,
        ~Consistent A (Extend p D) ->
        Subset (Extend [! ~p !] D) (Insert (Some p) D).

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
      unfold Subset; intros.
      destruct p.
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

    Lemma consistency_negation:
      forall D f,
      Consistent A D ->
      ~Consistent A (Extend f D) ->
      Consistent A (Extend [! ~f !] D).
    Proof.
      intros.
      unfold Consistent in H0.
      assert (exists p, (A; Extend f D |-- [! p /\ ~p !])).
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
      apply modal_excluded_middle.
      apply extending_K.
      apply modal_deduction in H0.
      assert (A; D |-- [! ~f !]).
      admit.
      intros q ?.
      apply H with [! ~f -> q !]; clear H H2.
      apply modal_deduction in H3.
      apply modal_ax4.
      apply extending_K.
      apply K_ax1.
      apply extending_K.
      apply K_ax2.
      apply extending_K.
      apply K_ax4.
      admit.
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
      - destruct classic with (Consistent A (Extend f D)).
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

    (* TODO: is it necessary to consider that the world set only contains maximal
       theories, or is it enough to consider that the world is maximal during the
       valuation function? *)

    Local Notation W := { G: theory | Consistent A G & Maximal G }.

    Definition wit (w: W) (p: formula): Prop :=
      match w with
      | exist2 _ _ G _ _ => G p
      end.

    (* TODO: check why Coq is complaining in here. *)
    Coercion wit: sig2 >-> Funclass.

    Definition canonical_accessibility: relation W :=
      fun w v =>
        forall p, w [! []p !] -> v p.

    Local Notation R := canonical_accessibility.

    Definition canonical_frame :=
      Build_Frame W R.

    Local Notation F := canonical_frame.

    Definition canonical_valuation: nat -> W -> Prop :=
      fun p w =>
        w [! #p !].

    Local Notation V := canonical_valuation.

    Definition canonical_model :=
      Build_Model F V.

    Local Notation M := canonical_model.

    Lemma truth:
      forall p w,
      (M ' w ||- p) <-> (w p).
    Proof.
      induction p; split; intros.
      - simpl in H.
        assumption.
      - simpl.
        assumption.
      - simpl in H.
        assert (~w p) by firstorder.
        assert (Maximal w) by (destruct w; auto).
        destruct H1 with p.
        + contradiction.
        + assumption.
      - simpl; intro.
        apply IHp in H0.
        assert (Consistent A w) by (destruct w; auto).
        apply H1 with p.
        admit.
      - edestruct classic.
        + eassumption.
        + exfalso.
          assert (Maximal w) by (destruct w; auto).
          assert (w [! ~[] p !]) by firstorder.
          simpl in H.
          admit.
      - simpl; intros.
        apply IHp.
        apply H0.
        assumption.
      - simpl in H.
        (* TODO: change definition to exists2 please! *)
        destruct H as (w', (?, ?)).
        apply IHp in H0.
        admit.
      - simpl.
        admit.
      - simpl in H.
        destruct H.
        apply IHp1 in H.
        apply IHp2 in H0.
        admit.
      - simpl; split.
        + admit.
        + admit.
      - simpl in H.
        destruct H.
        + apply IHp1 in H.
          admit.
        + apply IHp2 in H.
          admit.
      - simpl.
        admit.
      - simpl in H.
        admit.
      - simpl; intros.
        apply IHp1 in H0.
        apply IHp2.
        admit.
    Admitted.

    Theorem canonical:
      forall G,
      Consistent A G ->
      forall p,
      G p ->
      exists w,
      M ' w ||- p.
    Proof.
      intros.
      destruct lindebaum with G as (w, (?, (?, ?))); simpl.
      - assumption.
      - exists (exist2 _ _ w H1 H2).
        apply truth; simpl.
        apply H3.
        assumption.
    Qed.

  End CanonicalModel.

  Lemma nonderivability_implies_consistency:
    forall G p,
    ~(A; G |-- p) -> Consistent A (Extend [! ~p !] G).
  Proof.
    intros G p ? f ?.
    apply H; clear H.
    apply modal_deduction in H0; auto.
    assert (A; G |-- [! p \/ ~p !]).
    apply modal_excluded_middle.
    assumption.
    admit.
  Admitted.

  Lemma theoryModal_superset:
    forall M D,
    theoryModal M D ->
    forall G,
    Subset G D ->
    theoryModal M G.
  Proof.
    intros M D ? G ? p ?.
    apply H.
    apply H0.
    assumption.
  Qed.

  Lemma entails_superset:
    forall G p,
    (G ||= p) ->
    forall D,
    Subset G D ->
    (D ||= p).
  Proof.
    intros G p ? D ? M ?.
    apply H.
    apply theoryModal_superset with D.
    - assumption.
    - assumption.
  Qed.

  Theorem completeness:
    forall G p,
    (G ||= p) -> (A; G |-- p).
  Proof.
    intros G p.
    apply contrapositive; intros.
    - apply classic.
    - assert (Consistent A (Extend [! ~p !] G)).
      + apply nonderivability_implies_consistency; assumption.
      + (* Lets call the maximum consistent set extending (G, ~p) as M. *)
        edestruct lindebaum as (M, (?, (?, ?))); eauto.
        (* Let's derive our contradiction! *)
        assert ((M ||= p) /\ (M ||= [! ~p !])) as (?, ?); try split.
        * apply entails_superset with G; auto.
          firstorder.
        * intros f ? w.
          apply H5.
          firstorder.
        * (* Huh... *)
          admit.
  Admitted.

End Completeness.
