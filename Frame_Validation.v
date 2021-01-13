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
	forall M p,
	reflexive_frame (F M) ->
	(M ||= [! [] p -> p !]).
Proof.
	intros;
	unfold valid_in_model in *;
	simpl in *; intuition.
Qed.

Theorem axiomT_implies_reflexive_frame:
  forall M p,
  (M ||= [! [] p -> p !]) -> 
  reflexive_frame (F M).
Proof.
  intros M p. apply contra. intros H. unfold reflexive_frame in H. 
  apply not_all_ex_not in H. destruct H; rename x into s. unfold valid_in_model.
  apply ex_not_not_all. exists s.
(*  apply (neg_formula_valuation M s [! [] p -> p !]).*)
Admitted.


Theorem transitive_frame_implies_axiom4: 
  forall M phi,
  transitive_frame (F M) -> 
  (M ||= [! []phi -> [][]phi !]).
Proof. 
  unfold valid_in_model, transitive_frame.
  simpl; intros.
  apply H0.
  eapply H; split. 
  - apply H1. 
  - assumption. 
Qed.


Theorem axiom4_implies_transitive_frame: 
  forall M phi,
  (M ||=  [! []phi -> [][]phi !]) -> 
  transitive_frame (F M).
Proof.
Admitted.

Theorem symmetric_frame_implies_axiomB: 
  forall M phi,
  symmetric_frame (F M) -> 
  (M ||= [! phi -> []<> phi !]).
Proof.
  unfold valid_in_model, symmetric_frame.
  simpl in *; intros; exists w.
  apply and_comm; split.
  - apply H0.
  - eauto.
Qed.

Theorem axiomB_implies_symmetric_frame: 
  forall M phi,
  (M ||= [! phi -> []<> phi !]) -> 
  symmetric_frame (F M).
Proof.    
Admitted.

Theorem euclidean_frame_implies_axiom5: 
  forall M phi,
  euclidian_frame (F M) -> 
  (M ||= [! <>phi -> []<> phi !]).
Proof.
  unfold euclidian_frame, valid_in_model.
  simpl in *; intros.
  edestruct H0.
  exists x; split.
  - eapply H; split. 
    * apply H1. 
    * intuition. 
  - intuition.
Qed.

Theorem axiom5_implies_euclidean_frame: 
  forall M phi,
  (M ||= [! <>phi -> []<> phi !]) -> 
  euclidian_frame (F M).
Proof.
Admitted.

Theorem serial_frame_implies_axiomD: 
  forall M phi,
  serial_frame (F M) -> 
  (M ||= [! []phi -> <> phi !]).
Proof.
  unfold valid_in_model, serial_frame.   
  simpl in *; intros.
  edestruct H.
  exists x; split. 
  - apply H1.
  - eauto.
Qed.

Theorem axiomD_implies_serial_frame: 
  forall M phi,
  (M ||= [! []phi -> <> phi !]) -> 
  serial_frame (F M).
Proof.   
Admitted.


Theorem functional_frame_implies_axiom:
  forall M phi,
  functional_frame (F M) -> 
  (M ||= [! <>phi -> [] phi !]).
Proof.
  intros; unfold valid_in_model; 
  unfold functional_frame in *.
  intros w H0 w1 H1.
  edestruct H0.
  edestruct H with (w:=w) (w':=w1) (w'':=x).
  - split. 
    + apply H1. 
    + intuition. 
  - intuition.
Qed.

Theorem axiom_implies_functional_frame:
  forall M phi,
  (M ||= [! <>phi -> []phi !]) -> 
  functional_frame (F M).
Proof.
Admitted.


Theorem dense_frame_implies_axiom:
  forall M phi,
  dense_frame (F M) -> 
  (M ||= [! [][] phi -> [] phi !]).
Proof.
Admitted.


Theorem axiom_implies_dense_frame:
  forall M phi,
  (M ||= [! [][] phi -> []phi !]) -> 
  dense_frame (F M).
Proof.
Admitted.

Theorem convergent_frame_implies_axiom:
  forall M phi,
  convergent_frame (F M) -> 
  (M ||= [! <>[] phi -> []<> phi !]).
Proof.
  unfold convergent_frame, valid_in_model.
  simpl in *; intros.
  edestruct H0.
  destruct H with (w:=w) (x:=x) (y:=w').
  destruct H0; auto.
  exists x0.
  split; intuition.
Qed.

Theorem axiom_implies_convergent_frame:
  forall (M: Model) (phi: modalFormula),
  (M ||= [! <>[] phi -> []<> phi !]) -> 
  convergent_frame (F M).
Proof.
Admitted.
