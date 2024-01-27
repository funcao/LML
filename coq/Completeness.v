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

(* TODO: move this to tactics, please! *)

Lemma aux_deduction:
  forall A G p,
  (A; G |-- p) ->
  forall q,
  (A; Extend p G |-- q) -> (A; G |-- q).
Proof.
  intros.
  dependent induction H0.
  - destruct H0.
    + now dependent destruction H0.
    + now constructor 1.
  - now constructor 2 with a.
  - constructor 3 with f.
    + apply IHdeduction1.
      * assumption.
      * reflexivity.
    + apply IHdeduction2.
      * assumption.
      * reflexivity.
  - constructor 4.
    eapply IHdeduction.
    + assumption.
    + reflexivity.
Qed.

Lemma nonderivation_implies_consistency:
  forall A,
  Subset K A ->
  forall G p,
  ~(A; G |-- p) -> Consistent A G.
Proof.
  intros A ? G p ? q ?.
  apply H0; clear H0.
  (* Ok, p follows by explosion! *)
  admit.
Admitted.

Lemma consistency_deduction:
  forall A,
  Subset K A ->
  forall G p,
  (A; G |-- p) <-> ~Consistent A (Extend [! ~p !] G).
Proof.
  split.
  - intros ? ?.
    apply H1 with p.
    apply modal_ax4.
    + apply H.
      apply K_ax1.
    + apply H.
      apply K_ax2.
    + apply H.
      apply K_ax4.
    + apply deduction_subset with G.
      * intros t ?.
        now right.
      * assumption.
    + constructor 1.
      now left.
  - apply contrapositive; intros.
    + apply classic.
    + assert (Consistent A G).
      * now apply nonderivation_implies_consistency with p.
      * apply H1; clear H1; intros q ?.
        (* Left as an exercise to the reader. *)
        admit.
Admitted.

Lemma consistency_either:
  forall A,
  Subset K A ->
  forall G f,
  Consistent A G ->
  (Consistent A (Extend f G) \/ Consistent A (Extend [! ~f !] G)).
Proof.
  intros A ? G f.
  apply contrapositive; intros.
  - apply classic.
  - assert (~Consistent A (Extend f G) /\ ~Consistent A (Extend [! ~f !] G)).
    + split; intro.
      * apply H0.
        now left.
      * apply H0.
        now right.
    + clear H0; destruct H2.
      apply consistency_deduction in H2; auto.
      apply H0.
      (* If there's anything broken in here, then H1 is a contradiction! *)
      intros q ?.
      apply H1 with q.
      apply aux_deduction with f.
      * assumption.
      * assumption.
Qed.

Lemma consistency_negation:
  forall A,
  Subset K A ->
  forall G f,
  Consistent A G ->
  ~Consistent A (Extend f G) ->
  Consistent A (Extend [! ~f !] G).
Proof.
  intros.
  destruct consistency_either with A G f.
  - assumption.
  - assumption.
  - contradiction.
  - assumption.
Qed.

Section Completeness.

  Variable A: axiom -> Prop.

  Hypothesis extending_K: Subset K A.

  Section Lindenbaum.

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

    (* Lindenbaum sets. *)
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
      (* For necessitation, follows simply by the hypothesis. *)
      - destruct IHdeduction as (n, ?); auto.
        exists n.
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

    Theorem lindenbaum:
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

  End Lindenbaum.

  Section CanonicalModel.

    Variable G: theory.

    Inductive W: Type :=
      | W_mk D: Consistent A D -> Maximal D -> Subset G D -> W.

    Definition wit (w: W) (p: formula): Prop :=
      match w with
      | @W_mk D _ _ _ => D p
      end.

    Global Coercion wit: W >-> Funclass.

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
      [F -- V].

    Local Notation M := canonical_model.

    Lemma existential:
      forall (w: W) p,
      w [! ~[]p !] ->
      exists2 w',
      R w w' & w' [! ~p !].
    Proof.
      admit.
    Admitted.

    Lemma truth:
      forall p w,
      (M ' w ||- p) <-> (w p).
    Proof.
      induction p; split; intros.
      - simpl in *.
        assumption.
      - simpl in *.
        assumption.
      - simpl in *.
        assert (~w p) by firstorder.
        assert (Maximal w) by (destruct w; auto).
        destruct H1 with p.
        + contradiction.
        + assumption.
      - simpl in *; intro.
        apply IHp in H0.
        assert (Consistent A w) by (destruct w; auto).
        apply H1 with p.
        apply modal_ax4.
        + apply extending_K.
          apply K_ax1.
        + apply extending_K.
          apply K_ax2.
        + apply extending_K.
          apply K_ax4.
        + constructor 1.
          assumption.
        + constructor 1.
          assumption.
      - simpl in *.
        edestruct classic.
        + eassumption.
        + exfalso.
          assert (Maximal w) by now destruct w.
          assert (w [! ~[] p !]) by firstorder.
          destruct existential with w p as (w', ?, ?); auto.
          specialize (H w' H3).
          apply IHp in H.
          assert (Consistent A w') by now destruct w'.
          apply H5 with p.
          apply modal_ax4.
          * apply extending_K.
            apply K_ax1.
          * apply extending_K.
            apply K_ax2.
          * apply extending_K.
            apply K_ax4.
          * now constructor 1.
          * now constructor 1.
      - simpl in *; intros.
        apply IHp.
        apply H0.
        assumption.
      - simpl in *.
        destruct H as (w', ?, ?).
        apply IHp in H0.
        admit.
      - simpl in *.
        admit.
      - simpl in *.
        destruct H.
        apply IHp1 in H.
        apply IHp2 in H0.
        assert (Maximal w) by now destruct w.
        assert (Consistent A w) by now destruct w.
        destruct H1 with [! p1 /\ p2 !].
        + assumption.
        + exfalso.
          apply H2 with [! p1 /\ p2 !].
          apply modal_ax4.
          * apply extending_K.
            apply K_ax1.
          * apply extending_K.
            apply K_ax2.
          * apply extending_K.
            apply K_ax4.
          * apply modal_ax4.
            --- apply extending_K.
                apply K_ax1.
            --- apply extending_K.
                apply K_ax2.
            --- apply extending_K.
                apply K_ax4.
            --- now constructor 1.
            --- now constructor 1.
          * now constructor 1.
      - simpl in *.
        assert (Maximal w) by now destruct w.
        assert (Consistent A w) by now destruct w.
        split.
        + destruct H0 with p1.
          * apply IHp1.
            assumption.
          * exfalso.
            apply H1 with p1.
            apply modal_ax4.
            --- apply extending_K.
                apply K_ax1.
            --- apply extending_K.
                apply K_ax2.
            --- apply extending_K.
                apply K_ax4.
            --- apply modal_ax5 with p2.
                +++ apply extending_K.
                    apply K_ax5.
                +++ now constructor 1.
            --- now constructor 1.
        + destruct H0 with p2.
          * apply IHp2.
            assumption.
          * exfalso.
            apply H1 with p2.
            apply modal_ax4.
            --- apply extending_K.
                apply K_ax1.
            --- apply extending_K.
                apply K_ax2.
            --- apply extending_K.
                apply K_ax4.
            --- apply modal_ax6 with p1.
                +++ apply extending_K.
                    apply K_ax6.
                +++ now constructor 1.
            --- now constructor 1.
      - simpl in *.
        destruct H.
        + apply IHp1 in H.
          assert (Maximal w) by now destruct w.
          assert (Consistent A w) by now destruct w.
          destruct H0 with [! p1 \/ p2 !].
          * assumption.
          * exfalso.
            apply H1 with [! (p1 \/ p2) !].
            apply modal_ax4.
            --- apply extending_K.
                apply K_ax1.
            --- apply extending_K.
                apply K_ax2.
            --- apply extending_K.
                apply K_ax4.
            --- apply modal_ax7.
                +++ apply extending_K.
                    apply K_ax7.
                +++ now constructor 1.
            --- now constructor 1.
        + apply IHp2 in H.
          assert (Maximal w) by now destruct w.
          assert (Consistent A w) by now destruct w.
          destruct H0 with [! p1 \/ p2 !].
          * assumption.
          * exfalso.
            apply H1 with [! (p1 \/ p2) !].
            apply modal_ax4.
            --- apply extending_K.
                apply K_ax1.
            --- apply extending_K.
                apply K_ax2.
            --- apply extending_K.
                apply K_ax4.
            --- apply modal_ax8.
                +++ apply extending_K.
                    apply K_ax8.
                +++ now constructor 1.
            --- now constructor 1.
      - simpl in *.
        assert (Maximal w) by now destruct w.
        assert (Consistent A w) by now destruct w.
        destruct H0 with p1.
        + left.
          apply IHp1.
          assumption.
        + destruct H0 with p2.
          * right.
            apply IHp2.
            assumption.
          * exfalso.
            apply H1 with [! p1 \/ p2 !].
            apply modal_ax4.
            --- apply extending_K.
                apply K_ax1.
            --- apply extending_K.
                apply K_ax2.
            --- apply extending_K.
                apply K_ax4.
            --- now constructor 1.
            --- admit.
      - simpl in *.
        admit.
      - simpl in *; intros.
        apply IHp1 in H0.
        apply IHp2.
        admit.
    Admitted.

    Theorem canonical:
      Consistent A G ->
      forall p,
      G p ->
      exists w,
      M ' w ||- p.
    Proof.
      intros.
      destruct lindenbaum with G as (w, (?, (?, ?))); simpl.
      - assumption.
      - exists (@W_mk w H1 H2 H3).
        apply truth; simpl.
        apply H3.
        assumption.
    Qed.

    Lemma world_derivation:
      forall p,
      (A; G |-- p) <-> (forall w: W, w p).
    Proof.
      split; intros.
      - destruct w as (D, ?H, ?H, ?H); simpl.
        destruct H1 with p.
        + assumption.
        + exfalso.
          apply H0 with p.
          apply modal_ax4.
          * apply extending_K.
            apply K_ax1.
          * apply extending_K.
            apply K_ax2.
          * apply extending_K.
            apply K_ax4.
          * now apply deduction_subset with G.
          * now constructor.
      - apply consistency_deduction; auto; intro.
        destruct lindenbaum with (Extend [! ~p !] G) as (D, (?, (?, ?))).
        + assumption.
        + assert (Subset G D).
          * intros t ?.
            apply H3.
            now right.
          * specialize (H (W_mk H1 H2 H4)); simpl in H.
            apply H1 with p.
            apply modal_ax4.
            --- apply extending_K.
                apply K_ax1.
            --- apply extending_K.
                apply K_ax2.
            --- apply extending_K.
                apply K_ax4.
            --- now constructor 1.
            --- constructor 1.
                apply H3.
                now left.
    Qed.

    Lemma determination_if:
      forall p,
      (M |= p) -> (A; G |-- p).
    Proof.
      intros p.
      apply contrapositive; intros.
      - apply classic.
      - edestruct lindenbaum with (G := Extend [! ~p !] G)
          as (D, (?, (?, ?))).
        + intros q ?.
          apply H.
          apply world_derivation; intros.
          destruct w as (D, ?H, ?H, ?H); simpl.
          destruct H3 with p.
          * assumption.
          * exfalso.
            apply H2 with q.
            apply deduction_subset with (Extend [! ~p !] G); auto.
            destruct 1.
            --- now dependent destruction H6.
            --- now apply H4.
        + assert (Subset G D).
          * intros t ?.
            apply H3.
            now right.
          * specialize (H0 (@W_mk D H1 H2 H4)).
            apply truth in H0; simpl in H0.
            apply H1 with p.
            apply modal_ax4.
            --- apply extending_K.
                apply K_ax1.
            --- apply extending_K.
                apply K_ax2.
            --- apply extending_K.
                apply K_ax4.
            --- now constructor 1.
            --- constructor 1.
                firstorder.
    Qed.

    Lemma determination_only_if:
      forall p,
      (A; G |-- p) -> (M |= p).
    Proof.
      intros p ? (w, ?H, ?H, ?H).
      apply truth; simpl.
      destruct H1 with p; auto.
      destruct H0 with p.
      apply modal_ax4.
      - apply extending_K.
        apply K_ax1.
      - apply extending_K.
        apply K_ax2.
      - apply extending_K.
        apply K_ax4.
      - apply deduction_subset with G.
        + assumption.
        + assumption.
      - constructor 1.
        assumption.
    Qed.

    Lemma determination:
      forall p,
      (M |= p) <-> (A; G |-- p).
    Proof.
      split.
      - apply determination_if.
      - apply determination_only_if.
    Qed.

    Theorem completeness:
      forall p,
      (G ||= p) -> (A; G |-- p).
    Proof.
      intros p.
      (* We can't pretend we know how to derive this, but there must be a way. *)
      apply contrapositive; intros.
      - apply classic.
      - (* Since it's impossible to derive A; G |-- p, this means that G must
           be consistent. If it were inconsistent, anything could be derived! *)
        assert (Consistent A G).
        + now apply nonderivation_implies_consistency with p.
        + (* Now, by the determination lemma, since p isn't derivable, it can't
             be done in the canonical model as well. *)
          assert ((M |= p) -> False); intros.
          * apply determination with p in H2; auto.
          * apply H2, H0.
            (* Since our canonical model only contains worlds that extend G, by
               the truth lemma all of our possible worlds in here will contain
               the hypotheses of G. *)
            intros q ? w; apply truth.
            destruct w as (w, ?H, ?H, ?H); simpl.
            apply H6; assumption.
    Qed.

  End CanonicalModel.

End Completeness.
