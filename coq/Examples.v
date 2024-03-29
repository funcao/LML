Require Import List Modal_Library Modal_Notations Deductive_System Modal_Tactics Sets.
Import ListNotations.

Definition fixed_point A G :=
  forall f,
  exists p,
  (* TODO: we should improve the notation here! *)
  (A; G |-- And (Implies p (f (Box p))) (Implies (f (Box p)) p)).

Definition subset {T} (P: T -> Prop) (Q: T -> Prop): Prop :=
  forall x, P x -> Q x.

(* Some quick automation! *)
Local Hint Unfold subset: modal.
Local Hint Constructors K: modal.
Local Hint Constructors K4: modal.

Theorem Lob:
  (* Löb's theorem is provable in any superset of K4 with fixed points. *)
  forall A,
  subset K4 A /\ fixed_point A Empty ->
  forall p,
  (A; Empty |-- [! []p -> p !]) ->
  (A; Empty |-- [! p !]).
Proof.
  set (G := Empty).
  (* Step 1. *)
  intros A [I FP] p H1.
  (* Step 2. *)
  destruct FP with (fun X => [! X -> p !]) as (psi, H2).
  (* Step 3. *)
  assert (A; Empty |-- [! psi -> []psi -> p !]) as H3.
  apply modal_ax5 in H2; auto with modal.
  (* Step 4. *)
  assert (A; G |-- [! [](psi -> []psi -> p) !]) as H4.
  apply Nec; auto.
  (* Step 5. *)
  assert (A; G |-- [! []psi -> []([]psi -> p) !]) as H5.
  apply modal_axK in H4; auto with modal.
  (* Step 6. *)
  assert (A; G |-- [! []([]psi -> p) -> [][]psi -> []p !]) as H6.
  eapply Ax with (a := axK ?[X] ?[Y]); auto with modal.
  reflexivity.
  (* Step 7. *)
  assert (A; G |-- [! []psi -> [][]psi -> []p !]) as H7.
  eapply modal_syllogism; eauto with modal.
  (* Step 8. *)
  assert (A; G |-- [! []psi -> [][]psi !]) as H8.
  apply modal_axK4; auto with modal.
  (* Step 9. *)
  assert (A; G |-- [! []psi -> []p !]) as H9.
  eapply modal_ax2; eauto with modal.
  (* Step 10. *)
  assert (A; G |-- [! []psi -> p !]) as H10.
  eapply modal_syllogism; eauto with modal.
  (* Step 11. *)
  assert (A; G |-- [! ([]psi -> p) -> psi !]) as H11.
  apply modal_ax6 in H2; auto with modal.
  (* Step 12. *)
  assert (A; G |-- psi) as H12.
  eapply Mp; try eassumption.
  (* Step 13. *)
  assert (A; G |-- [! []psi !]) as H13.
  apply Nec; try assumption.
  (* Step 14. *)
  eapply Mp; eassumption.
Qed.

(* TODO: review later!

Definition fromList (ps: list formula): theory :=
  fun p =>
    In p ps.

Example Ex1:
  (* TODO: fix notation for deduction! *)
  T; (fromList ([! [](#0 -> #1) !] :: [! [](#1 -> #2) !] :: nil)) |--
    [! [](#0 -> #2) !].
Proof.
  (* Line: 16 *)
  apply Nec.
  (* Line: 15 *)
  apply Mp with (f := [! #0 -> #1 !]).
    (* Line: 14 *)
  - apply Mp with (f := [! #1 -> #2 !]).
      (* Line: 9 *)
    + apply Mp with (f := [! (#1 -> #2) -> (#0 -> (#1 -> #2)) !]).
        (* Line: 7 *)
      * apply Mp with (f := [! (#1 -> #2) -> ((#0 -> (#1 -> #2)) -> (#0 -> #1) -> (#0 -> #2)) !]).
          (* Line: 6 *)
        -- apply Ax with (a := ax2 [! #1 -> #2 !] [! #0 -> (#1 -> #2) !] [! (#0 -> #1) -> (#0 -> #2) !]).
          ++ constructor.
             constructor.
          ++ reflexivity.
        (* Line: 5 *)
        -- apply Mp with (f := [! (#0 -> (#1 -> #2)) -> ((#0 -> #1) -> (#0 -> #2)) !]).
          (* Line: 3 *)
          ++ apply Ax with (a := ax1 [! (#0 -> (#1 -> #2)) -> ((#0 -> #1) -> (#0 -> #2)) !] [! #1 -> #2 !]).
            ** constructor.
               constructor.
            ** reflexivity.
          (* Line: 4 *)
          ++ apply Ax with (a := ax2 [! #0 !] [! #1 !] [! #2 !]).
            ** constructor; constructor.
            ** reflexivity.
        (* Line: 8 *)
      * apply Ax with (a := ax1 [! #1 -> #2 !] [! #0 !]).
        -- constructor; constructor.
        -- reflexivity.
      (* Line: 11 *)
    + apply Mp with (f := [! [](#1 -> #2) !]).
      * apply Ax with (a := axT [! #1 -> #2 !]).
        -- constructor; constructor.
        -- reflexivity.
        (* Line: 2 *)
      * apply Prem; simpl.
        firstorder.
    (* Line: 13 *)
  - apply Mp with (f := [! [](#0 -> #1) !]).
      (* Line: 12 *)
    + apply Ax with (a := axT [! #0 -> #1 !]).
      * constructor; constructor.
      * reflexivity.
      (* Line: 1 *)
    + apply Prem; simpl.
      firstorder.
Qed.

*)
