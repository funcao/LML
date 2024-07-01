Require Import Sets.
Require Import Equality.
Require Import List Modal_Library Modal_Notations Deductive_System.
Import ListNotations.

Section Tactics.

Context `{X: modal_index_set}.

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

Section Deduction.

  Variable A: axiom -> Prop.
  Variable G: theory.

  Lemma modal_cut:
    forall p,
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
      + apply IHdeduction1 with (p := p).
        * assumption.
        * reflexivity.
      + apply IHdeduction2 with (p := p).
        * assumption.
        * reflexivity.
    - constructor 4.
      assumption.
  Defined.

  Variable idx: modal_index.

  Lemma modal_ax1:
    forall p q,
    A (ax1 p q) ->
    (A; G |-- p) -> (A; G |-- [! q -> p !]).
  Proof.
    intros.
    apply Mp with p; auto.
    now apply Ax with (a := ax1 p q).
  Defined.

  Lemma modal_ax2:
    forall p q r,
    A (ax2 p q r) ->
    (A; G |-- [! p -> q -> r !]) ->
    (A; G |-- [! p -> q !]) ->
    (A; G |-- [! p -> r !]).
  Proof.
    intros.
    assert (A; G |-- [! (p -> q -> r) -> (p -> q) -> p -> r !]).
    - now apply Ax with (a := ax2 p q r).
    - assert (A; G |-- [! (p -> q) -> p -> r !]).
      + now apply Mp with [! p -> q -> r !].
      + now apply Mp with [! p -> q !].
  Defined.

  Lemma modal_ax3:
    forall p q,
    A (ax3 p q) ->
    (A; G |-- [! (~q -> ~p) !]) ->
    (A; G |-- [! p -> q !]).
  Proof.
    intros.
    assert (A; G |-- [! (~q -> ~p) -> p -> q !]).
    - now apply Ax with (a := ax3 p q).
    - now apply Mp with [! ~q -> ~p !].
  Defined.

  Lemma modal_ax4:
    forall p q,
    A (ax1 q p) ->
    A (ax2 p q [! p /\ q !]) ->
    A (ax4 p q) ->
    (A; G |-- p) ->
    (A; G |-- q) ->
    (A; G |-- [! p /\ q !]).
  Proof.
    intros.
    assert (A; G |-- [! (p -> q -> p /\ q) -> (p -> q) -> (p -> p /\ q) !]).
    - now apply Ax with (a := ax2 p q [! p /\ q !]).
    - assert (A; G |-- [! (p -> q) -> (p -> p /\ q) !]).
      + apply Mp with [! p -> q -> p /\ q !]; auto.
        now apply Ax with (ax4 p q).
      + apply Mp with p; auto.
        apply Mp with [! p -> q !]; auto.
        apply Mp with q; auto.
        now apply Ax with (ax1 q p).
  Defined.

  Lemma modal_ax5:
    forall p q,
    A (ax5 p q) ->
    (A; G |-- [! p /\ q !]) ->
    (A; G |-- p).
  Proof.
    intros.
    assert (A; G |-- [! p /\ q -> p !]).
    - now apply Ax with (a := ax5 p q).
    - now apply Mp with [! p /\ q !].
  Defined.

  Lemma modal_ax6:
    forall p q,
    A (ax6 p q) ->
    (A; G |-- [! p /\ q !]) -> (A; G |-- q).
  Proof.
    intros.
    assert (A; G |-- [! p /\ q -> q !]).
    - now apply Ax with (a := ax6 p q).
    - now apply Mp with [! p /\ q !].
  Defined.

  Lemma modal_ax7:
    forall p q,
    A (ax7 p q) ->
    (A; G |-- [! p !]) ->
    (A; G |-- [! p \/ q !]).
  Proof.
    intros.
    assert (A; G |-- [! p -> p \/ q !]).
    - now apply Ax with (a := ax7 p q).
    - now apply Mp with p.
  Defined.

  Lemma modal_ax8:
    forall p q,
    A (ax8 p q) ->
    (A; G |-- [! q !]) ->
    (A; G |-- [! p \/ q !]).
  Proof.
    intros.
    assert (A; G |-- [! q -> p \/ q !]).
    - now apply Ax with (a := ax8 p q).
    - now apply Mp with q.
  Defined.

  Lemma modal_ax9:
    forall p q r,
    A (ax9 p q r) ->
    (A; G |-- [! p -> r !]) ->
    (A; G |-- [! q -> r !]) ->
    (A; G |-- [! p \/ q !]) ->
    (A; G |-- [! r !]).
  Proof.
    intros.
    assert (A; G |-- [! p \/ q -> r !]).
    - apply Mp with [! q -> r !].
      + apply Mp with [! p -> r !].
        * now apply Ax with (a := ax9 p q r).
        * assumption.
      + assumption.
    - now apply Mp with [! p \/ q !].
  Qed.

  Lemma modal_ax10:
    forall p,
    A (ax10 p) ->
    (A; G |-- [! ~~p !]) ->
    (A; G |-- [! p !]).
  Proof.
    intros.
    apply Mp with [! ~~p !].
    - apply Ax with (a := ax10 p).
      + assumption.
      + reflexivity.
    - assumption.
  Qed.

  Lemma modal_syllogism:
    forall p q r,
    A (ax1 [! q -> r !] p) ->
    A (ax2 p q r) ->
    (A; G |-- [! p -> q !]) ->
    (A; G |-- [! q -> r !]) ->
    (A; G |-- [! p -> r !]).
  Proof.
    intros.
    assert (A; G |-- [! p -> q -> r !]).
    - now apply modal_ax1.
    - now apply modal_ax2 with q.
  Defined.

  Lemma modal_axK:
    forall p q,
    A (axK idx p q) ->
    (A; G |-- [! [idx](p -> q) !]) ->
    (A; G |-- [! [idx]p -> [idx]q !]).
  Proof.
    intros.
    assert (A; G |-- [! [idx](p -> q) -> [idx]p -> [idx]q !]).
    - now apply Ax with (a := axK idx p q).
    - now apply Mp with [! [idx](p -> q) !].
  Defined.

  Lemma modal_axK4:
    forall p,
    A (axK4 idx p) ->
    (A; G |-- [! [idx]p -> [idx][idx]p !]).
  Proof.
    intros.
    now apply Ax with (a := axK4 idx p).
  Defined.

  Lemma modal_explosion:
    forall p q,
    A (ax1 [! ~~p !] [! ~q !]) ->
    A (ax1 [! ~p !] [! ~~~p !]) ->
    A (ax3 [! ~p !] q) ->
    A (ax3 p [! ~~p !]) ->
    (A; G |-- p) ->
    (A; G |-- [! ~p !]) ->
    (A; G |-- q).
  Proof.
    intros.
    assert (A; G |-- [! ~p -> q !]).
    - apply modal_ax3; auto.
      apply modal_ax1; auto.
      apply Mp with p; auto.
      apply modal_ax3; auto.
      apply modal_ax1; auto.
    - (* I'm not sure how I did this one, but there we go! *)
      now apply Mp with [! ~p !].
  Defined.

End Deduction.

Lemma modal_deduction:
  forall A G p q,
  Subset P A ->
  (A; Extend p G |-- q) ->
  (A; G |-- [! p -> q !]).
Proof.
  intros.
  dependent induction H0.
  - destruct H0.
    + dependent destruction H0.
      apply derive_identity.
      assumption.
    + apply modal_ax1.
      * apply H.
        apply P_ax1.
      * constructor 1.
        assumption.
  - apply modal_ax1.
    + apply H.
      apply P_ax1.
    + econstructor 2.
      * eassumption.
      * reflexivity.
  - eapply modal_ax2.
    + apply H.
      apply P_ax2.
    + apply IHdeduction1.
      * assumption.
      * reflexivity.
    + apply IHdeduction2.
      * assumption.
      * reflexivity.
  - apply modal_ax1.
    + apply H.
      apply P_ax1.
    + constructor 4.
      assumption.
Qed.

Lemma modal_peirce_law:
  forall A G p,
  Subset P A ->
  (A; G |-- [! (~p -> p) -> p !]).
Proof.
  intros.
  (*
    This is too ugly! Could we rewrite this please?
    Okay!
  *)
  set (q := [! ~p -> p !]). (* This breaks notation in the VSCoq proof view, huh *)
  assert (A; G |-- [! ~p -> p -> ~q !]). 
  {
    do 2 (apply modal_deduction; auto).
    apply modal_explosion with p;
    try (apply H; constructor);
    apply Prem;
    firstorder.
  }
  assert (A; G |-- [! (~p -> p -> ~q) -> (~p -> p) -> ~p -> ~q !]) by
    (eapply Ax with (a := ax2 _ _ _); try reflexivity; 
      apply H; constructor).
  assert (A; G |-- [! (~p -> p) -> ~p -> ~q !]) by
    (eapply Mp; eassumption).
  assert (A; G |-- [! (~p -> p) -> q -> p !]).
  {
    apply modal_syllogism with [! ~p -> ~q !];
    do 2 (try(apply H; constructor)); try assumption.
    eapply Ax with (a := ax3 _ _); try reflexivity.
    apply H; constructor.
  }
  assert (A; G |-- [! (q -> q -> p) -> (q -> q) -> q -> p !]) by
    (eapply Ax with (a := ax2 _ _ _); try reflexivity;
      apply H; constructor).
  assert (A; G |-- [! (q -> q) -> q -> p !]) by
    (eapply Mp; eassumption).
  eapply Mp; try eassumption.
  apply derive_identity; auto.
Qed.

Lemma modal_double_negation_introduction:
  forall A G p,
  Subset P A ->
  (A; G |-- [! p -> ~~p !]).
Proof.
  intros.
  assert (A; G |-- [! ~~~p -> ~p !]).
  - apply Ax with (a := ax10 [! ~p !]); try reflexivity.
    apply H; constructor.
  - apply modal_ax3 in H0.
    + assumption.
    + apply H; constructor.
Qed.

Lemma modal_excluded_middle:
  forall A G p,
  Subset P A ->
  (A; G |-- [! p \/ ~p !]).
Proof.
  intros.
  set (q := [! p \/ ~p !]).
  assert ((A; G |-- [! ~q -> ~p !]) /\
          (A; G |-- [! ~p -> q !])) as (?, ?);
  repeat split.
  - apply modal_ax3.
    + apply H; constructor.
    + apply modal_syllogism with q.
      * apply H; constructor.
      * apply H; constructor.
      * apply modal_syllogism with p.
        apply H; constructor.
        apply H; constructor.
        apply Ax with (a := ax10 p).
        apply H; constructor.
        reflexivity.
        eapply Ax with (a := ax7 _ _); try reflexivity.
        apply H; constructor.
      * apply modal_double_negation_introduction.
        assumption.
  - eapply Ax with (a := ax8 _ _); try reflexivity.
    apply H; constructor.
  - apply Mp with [! (~q -> q) !].
    + apply modal_peirce_law.
      assumption.
    + apply modal_syllogism with [! ~p !].
      * apply H; constructor.
      * apply H; constructor.
      * assumption.
      * assumption.
Qed.

Lemma modal_axDual:
  forall A G p idx,
  Subset (K idx) A ->
  (A; G |-- [! <idx>p !]) <-> (A; G |-- [! ~[idx]~p !]).
Proof.
  intros.
  assert (A; G |-- [! <idx>p <-> ~[idx]~p !]).
  - apply Ax with (a := axDual idx p).
    + apply H.
      apply K_axDual.
    + reflexivity.
  - split; intros.
    + apply modal_ax5 in H0.
      * now apply Mp with [! <idx>p !].
      * apply H; do 2 constructor.
    + apply modal_ax6 in H0.
      * now apply Mp with [! ~[idx]~p !].
      * apply H; do 2 constructor.
Qed.

Lemma modal_implies_absurd_derives_negation:
  forall A G p q,
  Subset P A ->
  (A; G |-- [! p -> q /\ ~q !]) ->
  (A; G |-- [! ~p !]).
Proof.
  intros.
  assert (A; G |-- [! p \/ ~p !]).
  - apply modal_excluded_middle.
    assumption.
  - apply modal_ax9 with [! p !] [! ~p !].
    + apply H; constructor.
    + apply modal_syllogism with [! q /\ ~q !].
      * apply H; constructor.
      * apply H; constructor.
      * assumption.
      * apply modal_deduction; auto.
        apply modal_explosion with q...
        --- apply H; constructor.
        --- apply H; constructor.
        --- apply H; constructor.
        --- apply H; constructor.
        --- apply modal_ax5 with [! ~q !]...
            +++ apply H; constructor.
            +++ apply Prem.
                now left.
        --- apply modal_ax6 with [! q !]...
            +++ apply H; constructor.
            +++ apply Prem.
                now left.
    + apply derive_identity.
      assumption.
    + assumption.
Qed.

Lemma modal_negation_derives_implies_absurd:
  forall A G p q,
  Subset P A ->
  (A; G |-- [! ~p !]) ->
  (A; G |-- [! p -> q /\ ~q !]).
Proof.
  intros.
  apply modal_deduction; auto.
  - apply modal_explosion with p.
    + apply H; constructor.
    + apply H; constructor.
    + apply H; constructor.
    + apply H; constructor.
    + apply Prem.
      now left.
    + apply deduction_subset with G.
      * intros t ?.
        now right.
      * assumption.
Qed.

Lemma modal_impl_transitivity:
  forall M a b c,
  (M |= [! a -> b !]) /\ (M |= [! b -> c !]) ->
  (M |= [! a -> c !]).
Proof.
  intros M a b c [H1 H2] w H3.
  apply H2; apply H1; assumption.
Defined.

End Tactics.
