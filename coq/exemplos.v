Require Import List Modal_Library Modal_Notations Deductive_System Modal_Tactics.
Import ListNotations.

Definition fixed_point S g :=
  forall f,
  exists p,
  (* TODO: we should improve the notation here! *)
  (S; g |-- And (Implies p (f (Box p))) (Implies (f (Box p)) p)).

Example Lob:
  (* Löb's theorem is provable in K4 (assuming fixed points). *)
  forall P,
  fixed_point K4 nil ->
  (K4; nil |-- [! []P -> P !]) ->
  (K4; nil |-- [! P !]).
Proof.
  (* Step 1. *)
  intros P FP H1.
  (* Step 2. *)
  destruct FP with (fun X => [! X -> P !]) as (psi, H2).
  (* Step 3. *)
  assert (K4; nil |-- [! psi -> []psi -> P !]) as H3.
  apply modal_ax5 in H2; try repeat constructor.
  exact H2.
  (* Step 4. *)
  assert (K4; nil |-- [! [](psi -> []psi -> P) !]) as H4.
  apply Nec; auto.
  (* Step 5. *)
  assert (K4; nil |-- [! []psi -> []([]psi -> P) !]) as H5.
  apply modal_axK; try repeat constructor.
  exact H3.
  (* Step 6. *)
  assert (K4; nil |-- [! []([]psi -> P) -> [][]psi -> []P !]) as H6.
  eapply Ax with (a := axK ?[X] ?[Y]); try repeat constructor.
  (* Step 7. *)
  assert (K4; nil |-- [! []psi -> [][]psi -> []P !]) as H7.
  eapply modal_compose; try repeat constructor.
  exact H5.
  exact H6.
  (* Step 8. *)
  assert (K4; nil |-- [! []psi -> [][]psi !]) as H8.
  apply modal_axK4; try constructor 2.
  (* Step 9. *)
  assert (K4; nil |-- [! []psi -> []P !]) as H9.
  eapply modal_ax2; try repeat constructor.
  exact H7.
  exact H8.
  (* Step 10. *)
  assert (K4; nil |-- [! []psi -> P !]) as H10.
  eapply modal_compose; try repeat constructor.
  exact H9.
  exact H1.
  (* Step 11. *)
  assert (K4; nil |-- [! ([]psi -> P) -> psi !]) as H11.
  apply modal_ax6 in H2; try repeat constructor.
  exact H2.
  (* Step 12. *)
  assert (K4; nil |-- psi) as H12.
  eapply Mp.
  exact H11.
  exact H10.
  (* Step 13. *)
  assert (K4; nil |-- [! []psi !]) as H13.
  apply Nec.
  exact H12.
  (* Step 14. *)
  eapply Mp.
  exact H10.
  exact H13.
Qed.

Example Ex1:
  (* TODO: fix notation for deduction! *)
  T; ([! [](#0 -> #1) !] :: [! [](#1 -> #2) !] :: nil) |-- [! [](#0 -> #2) !].
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
      * apply Prem with (i := 1).
        reflexivity.
    (* Line: 13 *)
  - apply Mp with (f := [! [](#0 -> #1) !]).
      (* Line: 12 *)
    + apply Ax with (a := axT [! #0 -> #1 !]).
      * constructor; constructor.
      * reflexivity.
      (* Line: 1 *)
    + apply Prem with (i := 0).
      reflexivity.
Qed.
