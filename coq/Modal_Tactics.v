Require Import Sets.
Require Import Equality.
Require Import List Modal_Library Modal_Notations Deductive_System.
Import ListNotations.

Section Deduction.

  Variable A: axiom -> Prop.
  Variable G: theory.

  Lemma modal_cut:
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
  Defined.

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

  Lemma modal_compose:
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
    A (axK p q) ->
    (A; G |-- [! [](p -> q) !]) ->
    (A; G |-- [! []p -> []q !]).
  Proof.
    intros.
    assert (A; G |-- [! [](p -> q) -> []p -> []q !]).
    - now apply Ax with (a := axK p q).
    - now apply Mp with [! [](p -> q) !].
  Defined.

  Lemma modal_axK4:
    forall p,
    A (axK4 p) ->
    (A; G |-- [! []p -> [][]p !]).
  Proof.
    intros.
    now apply Ax with (a := axK4 p).
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

  (* Lemma modal_excluded_middle:
    forall A Γ φ,
    Subset K A ->
    A; Γ |-- [! φ \/ ~φ !].
  Proof.
    intros.
    admit.
  Admitted. *)

End Deduction.

Lemma modal_impl_transitivity:
  forall M a b c,
  (M |= [! a -> b !]) /\ (M |= [! b -> c !]) ->
  (M |= [! a -> c !]).
Proof.
  intros M a b c [H1 H2] w H3.
  apply H2; apply H1; assumption.
Defined.

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
    apply IHdeduction.
    assumption.
Qed.
