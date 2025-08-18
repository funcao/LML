Require Import Decidable Equality Relations.
Require Import Modal_Library Modal_Notations Modal_Tactics Deductive_System Soundness List Classical Bool Sets.
Set Implicit Arguments.

Context `{X: modal_index_set}.

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

Lemma nonderivation_implies_consistency:
  forall A,
  Subset P A ->
  forall G p,
  ~(A; G |-- p) -> Consistent A G.
Proof.
  intros A ? G p ? q ?.
  apply H0; clear H0.
  apply modal_explosion with q.
  - apply H; constructor.
  - apply H; constructor.
  - apply H; constructor.
  - apply H; constructor.
  - apply modal_ax5 with [! ~q !].
    + apply H, P_ax5.
    + assumption.
  - apply modal_ax6 with q.
    + apply H, P_ax6.
    + assumption.
Qed.

Lemma consistency_deduction:
  forall A,
  Subset P A ->
  forall G p,
  (A; G |-- p) <-> ~Consistent A (Extend [! ~p !] G).
Proof.
  split.
  - intros ? ?.
    apply H1 with p.
    apply modal_ax4.
    + apply H.
      apply P_ax1.
    + apply H.
      apply P_ax2.
    + apply H.
      apply P_ax4.
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
        assert ((A; Extend [! ~p !] G |-- [! q !]) /\
                (A; Extend [! ~p !] G |-- [! ~q !])) as (?H, ?H);
        try split.
        --- apply modal_ax5 with [! ~q !]; auto.
            apply H.
            apply P_ax5.
        --- apply modal_ax6 with [! q !]; auto.
            apply H.
            apply P_ax6.
        --- apply modal_deduction in H3, H4; auto.
            apply H0.
            apply modal_ax9 with [! q !] [! ~q !].
            +++ apply H.
                apply P_ax9.
            +++ apply modal_ax3.
                *** apply H.
                    apply P_ax3.
                *** assumption.
            +++ apply modal_ax3.
                *** apply H.
                    apply P_ax3.
                *** apply modal_syllogism with q.
                    apply H.
                    apply P_ax1.
                    apply H.
                    apply P_ax2.
                    assumption.
                    apply modal_ax3.
                    apply H.
                    apply P_ax3.
                    apply Ax with (a := ax10 [! ~q !]).
                    apply H.
                    apply P_ax10.
                    reflexivity.
            +++ apply modal_excluded_middle.
                assumption.
Qed.

Lemma consistency_either:
  forall A,
  Subset P A ->
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
      now apply modal_cut with f.
Qed.

Lemma consistency_negation:
  forall A,
  Subset P A ->
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

  Hypothesis extending_P: Subset P A.

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
      (* For necessitation, zero is enough! *)
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

    Hypothesis extending_K: forall idx, Subset (K idx) A.

    Inductive W: Type :=
      | W_mk D: Consistent A D -> Maximal D -> W.

    Definition wit (w: W) (p: formula): Prop :=
      match w with
      | @W_mk D _ _ => D p
      end.

    Global Coercion wit: W >-> Funclass.

    Definition canonical_accessibility idx: relation W :=
      fun w v =>
        forall p, w [! [idx]p !] -> v p.

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

    Inductive existential_world (w: W) idx: formula -> Prop :=
      | existential_world_mk:
        forall x,
        w [! [idx]x !] ->
        existential_world w idx x.

    Local Ltac fill_axiom :=
      match goal with
      | |- A ?a =>
        apply extending_P;
        constructor
      end.

    Lemma finite_world:
      forall G p,
      (A; G |-- p) ->
      exists2 ps: list formula,
      (A; Fin ps |-- p) & Subset (Fin ps) G.
    Proof.
      induction 1.
      - exists [f].
        + apply Prem.
          left; reflexivity.
        + inversion_clear 1; subst.
          * assumption.
          * inversion H1.
      - exists nil.
        + now apply Ax with (a := a).
        + inversion 1.
      - destruct IHdeduction1 as (ps, ?, ?).
        destruct IHdeduction2 as (qs, ?, ?).
        (* The list doesn't have to be minimal, just finite. *)
        exists (ps ++ qs).
        + eapply Mp.
          * eapply deduction_subset with (Fin ps); eauto.
            intros p ?.
            apply in_or_app.
            left.
            assumption.
          * eapply deduction_subset with (Fin qs); eauto.
            intros p ?.
            apply in_or_app.
            right.
            assumption.
        + intros p ?.
          apply in_app_or in H5 as [ ? | ? ].
          * apply H2.
            assumption.
          * apply H4.
            assumption.
      - clear IHdeduction.
        exists nil.
        + now apply Nec.
        + inversion 1.
    Qed.

    Lemma finite_spread:
      forall ps p,
      (A; Fin ps |-- p) ->
      (A; Empty |-- fold_right Implies p ps).
    Proof.
      induction ps using rev_ind; simpl; intros.
      - assumption.
      - assert (A; Extend x (Fin ps) |-- p).
        + apply deduction_subset with (Fin (ps ++ [x])); auto.
          intros q ?.
          apply in_app_or in H0 as [ ? | ? ].
          * now right.
          * destruct H0; subst.
            --- now left.
            --- inversion H0.
        + apply modal_deduction in H0; auto.
          specialize (IHps [! x -> p !] H0).
          rewrite fold_right_app; simpl.
          assumption.
    Qed.

    Lemma existential_modus_ponens:
      forall (w: W) p ps idx,
      (forall q, In q ps -> w [! [idx]q !]) ->
      (A; w |-- Box idx (fold_right Implies p ps)) ->
      (A; w |-- [! [idx]p !]).
    Proof with try fill_axiom.
      induction ps; intros.
      - simpl in H0.
        assumption.
      - simpl in H, H0.
        apply IHps; intros.
        + apply H.
          now right.
        + apply modal_axK in H0...
          apply Mp with [! [idx]a !].
          * assumption.
          * constructor 1.
            apply H; now left.
          * apply extending_K with idx.
            apply K_axK.
    Qed.

    Lemma existential_world_consistent:
      forall p (w: W) idx,
      w [! ~[idx]p !] ->
      Consistent A (Extend [! ~p !] (existential_world w idx)).
    Proof with try fill_axiom.
      intros p w idx ?.
      set (E := existential_world w idx).
      intros q ?.
      (* We first move the ~p from the assumptions into the formula. *)
      apply modal_deduction in H0; auto.
      (* We have clearly a double negation, which we can remove. *)
      apply modal_implies_absurd_derives_negation in H0; auto.
      eapply Mp in H0; [| (* TODO: remake this bit? *)
        eapply Ax with (a := ax10 _);
        try reflexivity ]...
      (* We're left with formulas that are necessary in w inside of E. *)
      destruct finite_world with E p as (ps, ?, ?); auto.
      (* Using only ps we derive that ~p implies an absurd. We can spread this
         now with the deduction theorem. *)
      apply finite_spread in H1.
      (* Now we can apply the necessity axiom as we don't have assumptions. *)
      apply Nec with (t := w) (i := idx) in H1.
      (* We can derive everything in ps! *)
      apply existential_modus_ponens in H1; intros.
      - assert (Consistent A w) by now destruct w.
        apply H3 with [! [idx]p !].
        apply modal_ax4...
        + assumption.
        + now constructor 1.
      - rename q0 into t.
        specialize (H2 t H3).
        dependent destruction H2.
        assumption.
    Qed.

    Lemma existential:
      forall (w: W) p idx,
      w [! ~[idx]p !] ->
      exists2 w',
      R idx w w' & w' [! ~p !].
    Proof.
      intros.
      (* We have to pick a specific context and show it's consistent. *)
      set (E := Extend [! ~p !] (existential_world w idx)).
      destruct lindenbaum with E as (F, (?, (?, ?))).
      - apply existential_world_consistent.
        assumption.
      - exists (W_mk H0 H1).
        + unfold R; simpl.
          intros t ?.
          apply H2.
          now constructor.
        + simpl.
          apply H2.
          now constructor.
    Qed.

    Lemma truth:
      forall p w,
      (M ' w ||- p) <-> (w p).
    Proof with try fill_axiom.
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
        apply modal_ax4...
        + constructor 1.
          assumption.
        + constructor 1.
          assumption.
      - simpl in *.
        edestruct classic.
        + eassumption.
        + exfalso.
          assert (Maximal w) by now destruct w.
          assert (w [! ~[m] p !]) by firstorder.
          destruct existential with w p m as (w', ?, ?); auto.
          specialize (H w' H3).
          apply IHp in H.
          assert (Consistent A w') by now destruct w'.
          apply H5 with p.
          apply modal_ax4...
          * now constructor 1.
          * now constructor 1.
      - simpl in *; intros.
        apply IHp.
        apply H0.
        assumption.
      - simpl in *.
        destruct H as (w', ?, ?).
        apply IHp in H0.
        assert (Maximal w) by now destruct w.
        unfold R in H.
        destruct H1 with [! <m>p !].
        + assumption.
        + exfalso.
          destruct H1 with [! [m]~p !].
          * assert (Consistent A w') by now destruct w'.
            specialize (H [! ~p !] H3).
            apply H4 with [! p !].
            apply modal_ax4...
            --- now constructor 1.
            --- now constructor 1.
          * assert (Consistent A w) by now destruct w.
            apply H4 with [! <m>p !].
            apply modal_ax4...
            --- apply modal_axDual.
                +++ apply extending_K.
                +++ now constructor 1.
            --- now constructor 1.
      - simpl in *.
        destruct existential with w [! ~p !] m as (w', ?, ?); auto.
        + assert (Maximal w) by now destruct w.
          assert (Consistent A w) by now destruct w.
          destruct H0 with [! [m]~p !].
          * exfalso.
            apply H1 with [! [m]~p !].
            apply modal_ax4...
            --- now constructor 1.
            --- apply modal_axDual.
                +++ apply extending_K.
                +++ now constructor 1.
          * assumption.
        + assert (Maximal w') by now destruct w'.
          assert (Consistent A w') by now destruct w'.
          destruct H2 with p.
          * exists w'; auto.
            apply IHp.
            assumption.
          * exfalso.
            apply H3 with [! ~p !].
            apply modal_ax4...
            --- now constructor 1.
            --- now constructor 1.
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
          apply modal_ax4...
          * apply modal_ax4...
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
            apply modal_ax4...
            --- apply modal_ax5 with p2...
                now constructor 1.
            --- now constructor 1.
        + destruct H0 with p2.
          * apply IHp2.
            assumption.
          * exfalso.
            apply H1 with p2.
            apply modal_ax4...
            --- apply modal_ax6 with p1...
                now constructor 1.
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
            apply modal_ax4...
            --- apply modal_ax7...
                now constructor 1.
            --- now constructor 1.
        + apply IHp2 in H.
          assert (Maximal w) by now destruct w.
          assert (Consistent A w) by now destruct w.
          destruct H0 with [! p1 \/ p2 !].
          * assumption.
          * exfalso.
            apply H1 with [! (p1 \/ p2) !].
            apply modal_ax4...
            --- apply modal_ax8...
                now constructor 1.
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
            apply modal_ax4...
            --- now constructor 1.
            --- apply modal_ax9 with p1 p2...
                +++ apply modal_deduction; auto.
                    apply modal_explosion with p1...
                    *** constructor 1.
                        now left.
                    *** apply deduction_subset with w.
                        (* TODO: simplify? *)
                        now right.
                        now constructor 1.
                +++ apply modal_deduction; auto.
                    apply modal_explosion with p2...
                    *** constructor 1.
                        now left.
                    *** apply deduction_subset with w.
                        (* TODO: simplify? *)
                        now right.
                        now constructor 1.
                +++ now constructor 1.
      - simpl in *.
        assert (Maximal w) by now destruct w.
        assert (Consistent A w) by now destruct w.
        destruct H0 with p1.
        + apply IHp1 in H2.
          specialize (H H2).
          apply IHp2 in H.
          destruct H0 with [! p1 -> p2 !]; auto.
            exfalso; apply H1 with [! p1 -> p2 !].
            apply modal_ax4...
            --- apply modal_ax1...
                now constructor 1.
            --- now constructor 1.
        + destruct H0 with p2.
          * destruct H0 with [! p1 -> p2 !]; auto.
            exfalso; apply H1 with [! p1 -> p2 !].
            apply modal_ax4...
            --- apply modal_ax1...
                now constructor 1.
            --- now constructor 1.
          * destruct H0 with [! p1 -> p2 !]; auto.
            exfalso; apply H1 with [! p1 -> p2 !].
            apply modal_ax4...
            --- apply modal_ax3...
                apply modal_ax1...
                now constructor 1.
            --- now constructor 1.
      - simpl in *; intros.
        apply IHp1 in H0.
        apply IHp2.
        assert (Maximal w) by now destruct w.
        assert (Consistent A w) by now destruct w.
        destruct H1 with p2.
        + assumption.
        + exfalso.
          apply H2 with p2.
          apply modal_ax4...
          * apply Mp with p1.
            --- now constructor 1.
            --- now constructor 1.
          * now constructor 1.
    Qed.

    Variable G: theory.

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
      - exists (@W_mk w H1 H2).
        apply truth; simpl.
        apply H3.
        assumption.
    Qed.

    Lemma world_derivation:
      forall p,
      (A; Empty |-- p) <-> (forall w: W, w p).
    Proof.
      split; intros.
      - destruct w as (D, ?H, ?H); simpl.
        destruct H1 with p.
        + assumption.
        + exfalso.
          apply H0 with p.
          apply modal_ax4.
          * apply extending_P.
            apply P_ax1.
          * apply extending_P.
            apply P_ax2.
          * apply extending_P.
            apply P_ax4.
          * apply deduction_subset with Empty.
            --- inversion 1.
            --- assumption.
          * now constructor.
      - apply consistency_deduction; auto; intro.
        destruct lindenbaum with (Singleton [! ~p !]) as (D, (?, (?, ?))).
        + intros q ?.
          apply H0 with q.
          apply deduction_subset with (G1 := Singleton [! ~p !]).
          * inversion_clear 1.
            left; reflexivity.
          * assumption.
        + specialize (H (W_mk H1 H2)); simpl in H.
          apply H1 with p.
          apply modal_ax4.
          --- apply extending_P.
              apply P_ax1.
          --- apply extending_P.
              apply P_ax2.
          --- apply extending_P.
              apply P_ax4.
          --- now constructor 1.
          --- constructor 1.
              apply H3.
              reflexivity.
    Qed.

    Lemma determination_if:
      forall p,
      (M |= p) -> (A; Empty |-- p).
    Proof with try fill_axiom.
      intros p.
      apply contrapositive; intros.
      - apply classic.
      - edestruct lindenbaum with (G := Extend [! ~p !] Empty)
          as (D, (?, (?, ?))).
        + intros q ?.
          apply H.
          apply modal_deduction in H1; auto.
          apply world_derivation; intros.
          destruct w as (D, ?H, ?H); simpl.
          destruct H3 with p.
          * assumption.
          * exfalso.
            apply H2 with q.
            eapply Mp.
            --- apply deduction_subset with Empty.
                +++ inversion 1.
                +++ eassumption.
            --- apply Prem.
                assumption.
        + specialize (H0 (@W_mk D H1 H2)).
          apply truth in H0; simpl in H0.
          apply H1 with p.
          apply modal_ax4...
          * now constructor 1.
          * constructor 1.
            firstorder.
    Qed.

    Lemma determination_only_if:
      forall p,
      (A; Empty |-- p) -> (M |= p).
    Proof with try fill_axiom.
      intros p ? (w, ?H, ?H).
      apply truth; simpl.
      destruct H1 with p; auto.
      destruct H0 with p.
      apply modal_ax4...
      - apply deduction_subset with Empty.
        + inversion 1.
        + assumption.
      - constructor 1.
        assumption.
    Qed.

    Lemma determination:
      forall p,
      (M |= p) <-> (A; Empty |-- p).
    Proof.
      split.
      - apply determination_if.
      - apply determination_only_if.
    Qed.

    Theorem completeness:
      forall p,
      (Empty ||= p) -> (A; Empty |-- p).
    Proof.
      intros p.
      (* We can't pretend we know how to derive this, but there must be a
         way. *)
      apply contrapositive; intros.
      - apply classic.
      - (* Since it's impossible to derive A; Empty |-- p, this means that G
           must be consistent. If it were inconsistent, anything could be
           derived as we have explosion. *)
        assert (Consistent A Empty).
        + now apply nonderivation_implies_consistency with p.
        + (* Now, by the determination lemma, since p isn't derivable, it can't
             be done in the canonical model as well. *)
          assert ((M |= p) -> False); intros.
          * apply determination with p in H2.
            contradiction.
          * (* Since we have no assumptions, we don't have to show anything to
               be valid. *)
            apply H2, H0; easy.
    Qed.

  End CanonicalModel.

End Completeness.
