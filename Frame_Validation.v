Require Import Modal_Library Classical.

(*
https://coq.inria.fr/library/Coq.Logic.Classical_Pred_Type.html
*)

Theorem contra:
  forall P Q,
  (~ P -> ~ Q) -> (Q -> P).
Proof.
  intros. apply NNPP. intro. apply H in H1. contradiction.
Qed.

Definition neg_formula_valuation (M: Model) (m: W (F M)) (q: modalFormula): Prop :=
  ~ (formula_valuation M m [! q !]) <-> (formula_valuation M m [! ~ q!]).

(*Fazer contrapositiva e eliminação da dupla negação modais*)

Theorem reflexive_frame_implies_axiomT:
    forall f,
    reflexive_frame f ->
    (forall v p, Build_Model f v ||= [! [] p -> p !]).
Proof.
  intros f HR v p w H1. 
  simpl in H1. 
  unfold reflexive_frame in HR.
  apply H1 in HR. 
  assumption. 
Qed.

Theorem axiomT_implies_reflexive_frame:
  forall f,
  (forall v p, Build_Model f v ||= [! []p -> p !]) -> 
  reflexive_frame f.
Proof.
  intros f. 
  apply contra. 
  intros H; unfold reflexive_frame in H. 
  apply not_all_ex_not in H; destruct H as [w].
  apply ex_not_not_all. 
  exists (fun _ x => R f w x). 
  apply ex_not_not_all. 
  exists [!(#0)!]. 
  intros H1; unfold valid_in_model in H1. 
  simpl in H1. 
  destruct H.
  apply H1. 
  intros w'.
  intros H'. 
  assumption.
Qed.

Theorem transitive_frame_implies_axiom4: 
  forall f,
    transitive_frame f ->
    (forall v p, Build_Model f v ||= [! []p -> [][]p !]).
Proof.
  intros f H v p w H1.
  simpl.
  intros w' H2 w'' H3.
  simpl in H1.
  apply H1.
  unfold transitive_frame in H.
  apply H with (w:=w) (w':=w') (w'':=w'').
  split; assumption.
Qed.


Theorem axiom4_implies_transitive_frame:
  forall f,
  (forall v p, Build_Model f v ||= [! []p -> [][]p !]) -> 
  transitive_frame f.
Proof.
  intros f.
  apply contra.
  intros H; unfold transitive_frame in H.
  apply not_all_ex_not in H.
  destruct H as [w].
  apply not_all_ex_not in H.
  destruct H as [w'].
  apply not_all_ex_not in H.
  destruct H as [w''].
  apply imply_to_and with (P:= R f w w' /\ R f w' w'') in H.
  destruct H as [H1 H3]; destruct H1 as [H1 H2].
  apply ex_not_not_all.
  exists (fun _ x => R f w x).
  apply ex_not_not_all.
  exists [!(#0)!].
  intros H; unfold valid_in_model in H; simpl in H.
  destruct H3.
  eapply H.
    - intros w''' H3; exact H3.
    - exact H1.
    - exact H2.
Qed.

Theorem symmetric_frame_implies_axiomB:
  forall f,
  symmetric_frame f ->
  (forall v p, Build_Model f v ||= [! p -> []<> p !]).
Proof.
  intros f H v p w H1.
  simpl.
  intros w' H2.
  exists w.
  unfold symmetric_frame in H.
  split.
  - apply H.
    assumption.
  - assumption.
Qed.

Theorem axiomB_implies_symmetric_frame:
  forall f,
  (forall v p, Build_Model f v ||= [! p -> []<>p !]) -> 
  symmetric_frame f.
Proof.
  intros f.
  apply contra.
  intros H; unfold symmetric_frame in H.
  apply not_all_ex_not in H; destruct H as [w].
  apply not_all_ex_not in H; destruct H as [w'].
  apply imply_to_and in H; destruct H as [H1 H2].
  apply ex_not_not_all.
  exists (fun _ x => ~ R f w' x).
  apply ex_not_not_all.
  exists [!(#0)!].
  intros H; unfold valid_in_model in H; simpl in H.
  pose H1 as H3.
  apply H in H3.
  - destruct H3 as [w''].
    destruct H0 as [H3 H4].
    contradiction.
  - exact H2.
Qed.

Theorem euclidean_frame_implies_axiom5:
  forall f,
  euclidian_frame f ->
  (forall v p, Build_Model f v ||= [! <>p -> []<> p !]).
Proof.
Admitted.

Theorem axiom5_implies_euclidean_frame: 
  forall f,
  (forall v p, Build_Model f v ||= [! <>p -> []<>p !]) -> 
  euclidian_frame f.
Proof.
Admitted.

Theorem serial_frame_implies_axiomD:
  forall f,
  serial_frame f ->
  (forall v p, Build_Model f v ||= [! []p -> <> p !]).
Proof.
Admitted.

Theorem axiomD_implies_serial_frame: 
  forall f,
  (forall v p, Build_Model f v ||= [! []p -> <> p !]) ->
  serial_frame f.
Proof.   
Admitted.


Theorem functional_frame_implies_axiom:
  forall f,
  functional_frame f ->
  (forall v p, Build_Model f v ||= [! <>p -> [] p !]).
Proof.
Admitted.

Theorem axiom_implies_functional_frame:
  forall f,
  (forall v p, Build_Model f v ||= [! <>p -> [] p !]) ->
  functional_frame f.
Proof.
Admitted.


Theorem dense_frame_implies_axiom:
  forall f,
  dense_frame f ->
  (forall v p, Build_Model f v ||= [! [][]p -> [] p !]).
Proof.
Admitted.


Theorem axiom_implies_dense_frame:
  forall f,
  (forall v p, Build_Model f v ||= [! [][]p -> [] p !]) ->
  dense_frame f.
Proof.
Admitted.

Theorem convergent_frame_implies_axiom:
  forall f,
  convergent_frame f ->
  (forall v p, Build_Model f v ||= [! <>[]p -> []<> p !]).
Proof.
Admitted.

Theorem axiom_implies_convergent_frame:
  forall f,
  (forall v p, Build_Model f v ||= [! <>[]p -> []<> p !]) ->
  convergent_frame f.
Proof.
Admitted.
