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
    forall f p,
    reflexive_frame f ->
    (forall v, Build_Model f v ||= [! [] p -> p !]).
Proof.
  intros f p HR v w1 H1. 
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
  apply not_all_ex_not in H; destruct H as [w1].
  apply ex_not_not_all. 
  exists (fun _ x => R f w1 x). 
  apply ex_not_not_all. 
  exists [!(#0)!]. 
  intros H1; unfold valid_in_model in H1; simpl in H1. 
  destruct H.
  apply H1. 
  intros w2 H'; assumption.
Qed.
(*
Theorem axiomT_implies_reflexive_frame':
  forall f p,
  (forall v, Build_Model f v ||= [! []p -> p !]) -> 
  reflexive_frame f.
Proof.
  intros f p. 
  apply contra. 
  intros H; unfold reflexive_frame in H. 
  apply not_all_ex_not in H; destruct H as [w1].
  apply ex_not_not_all. 
  exists (fun _ x => R f w1 x).
  unfold valid_in_model.
  intros H1; unfold valid_in_model in H1; simpl in H1.
  destruct H.
  apply H1.
   apply ex_not_not_all. 
  exists w1. 
  intros H1; unfold valid_in_model in H1; simpl in H1.
  destruct H.
  apply H1. 
  intros w2.
  intros H'. 
  assumption. 
Qed.
*)
Theorem transitive_frame_implies_axiom4: 
  forall f,
    transitive_frame f ->
    (forall v p, Build_Model f v ||= [! []p -> [][]p !]).
Proof.
  intros f H v p w1 H1.
  simpl.
  intros w2 H2 w3 H3.
  simpl in H1.
  apply H1.
  unfold transitive_frame in H.
  apply H with (w:=w1) (w':=w2) (w'':=w3).
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
  apply not_all_ex_not in H; destruct H as [w1].
  apply not_all_ex_not in H; destruct H as [w2].
  apply not_all_ex_not in H; destruct H as [w3].
  apply imply_to_and with (P:= R f w1 w2 /\ R f w2 w3) in H.
  destruct H as [H1 H3]; destruct H1 as [H1 H2].
  apply ex_not_not_all.
  exists (fun _ x => R f w1 x).
  apply ex_not_not_all.
  exists [!(#0)!].
  intros H; unfold valid_in_model in H; simpl in H.
  destruct H3.
  eapply H.
  - intros w4 H3; exact H3.
  - exact H1.
  - exact H2.
Qed.

Theorem symmetric_frame_implies_axiomB:
  forall f,
  symmetric_frame f ->
  (forall v p, Build_Model f v ||= [! p -> []<> p !]).
Proof.
  intros f H v p w1 H1.
  simpl.
  intros w2 H2.
  exists w1.
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
  apply not_all_ex_not in H; destruct H as [w1].
  apply not_all_ex_not in H; destruct H as [w2].
  apply imply_to_and in H; destruct H as [H1 H2].
  apply ex_not_not_all.
  exists (fun _ x => ~ R f w2 x).
  apply ex_not_not_all.
  exists [!(#0)!].
  intros H; unfold valid_in_model in H; simpl in H.
  pose H1 as H3.
  apply H in H3.
  - destruct H3 as [w3].
    destruct H0 as [H3 H4].
    contradiction.
  - exact H2.
Qed.

Theorem euclidean_frame_implies_axiom5:
  forall f,
  euclidean_frame f ->
  (forall v p, Build_Model f v ||= [! <>p -> []<> p !]).
Proof.
  intros f H v p w1 H1.
  simpl.
  intros w2 H2.
  unfold euclidean_frame in H.
  simpl in H1.
  destruct H1 as [w3].
  destruct H0 as [H1 H3].
  exists w3.
  split.
  - eapply H.
    split. 
    + exact H2.
    + assumption.
  - assumption.
Qed.

Theorem axiom5_implies_euclidean_frame: 
  forall f,
  (forall v p, Build_Model f v ||= [! <>p -> []<>p !]) -> 
  euclidean_frame f.
Proof.
  intros f.
  apply contra.
  intros H; unfold euclidean_frame in H.
  apply not_all_ex_not in H; destruct H as [w1].
  apply not_all_ex_not in H; destruct H as [w2].
  apply not_all_ex_not in H; destruct H as [w3].
  apply imply_to_and with (P := R f w1 w2 /\ R f w1 w3) in H.
  destruct H as [H1 H3]; destruct H1 as [H1 H2].
  apply ex_not_not_all.
  exists (fun _ x =>  ~ R f w2 x).
  apply ex_not_not_all.
  exists [!(#0)!].
  intros H; unfold valid_in_model in H; simpl in H.
  destruct H with (w:=w1) (w':=w2).
  - exists w3.
    split.
    + assumption.
    + assumption.
  - assumption.
  - destruct H0 as [H4 H5].
    contradiction.
Qed.

Theorem serial_frame_implies_axiomD:
  forall f,
  serial_frame f ->
  (forall v p, Build_Model f v ||= [! []p -> <> p !]).
Proof.
  intros f H v p w1 H1.
  unfold serial_frame in H.
  destruct H with (w:=w1) as [w2].
  rename H0 into H2.
  simpl in H1.
  simpl.
  exists w2.
  split.
  - assumption.
  - apply H1.
    assumption.
Qed.

Theorem axiomD_implies_serial_frame: 
  forall f,
  (forall v p, Build_Model f v ||= [! []p -> <> p !]) ->
  serial_frame f.
Proof.
  intros f.
  apply contra.
  intros H.
  unfold serial_frame in H.
  apply not_all_ex_not in H; destruct H as [w1].
  apply ex_not_not_all.
  exists (fun _ x => ~ R f w1 x).
  apply ex_not_not_all.
  exists [!(#0)!].
  intros H1; unfold valid_in_model in H1; simpl in H1.
  edestruct H1.
  - intros w2 H2.
    destruct H.
    exists w2.
    exact H2.
  - destruct H0 as [H2 H3].
    contradiction.
Qed.

Theorem functional_frame_implies_axiom:
  forall f,
  functional_frame f ->
  (forall v p, Build_Model f v ||= [! <>p -> [] p !]).
Proof.
  intros f H v p w1 H1 w2 H2.
  unfold functional_frame in H.
  simpl in H1.
  destruct H1 as [w3 H1]; destruct H1 as [H1 H3].
  assert (H4: R (F [f -- v]) w1 w2 /\ R f w1 w3) by (split; assumption).
  apply H in H4.
  subst.
  assumption.
Qed.

Theorem axiom_implies_functional_frame:
  forall f,
  (forall v p, Build_Model f v ||= [! <>p -> [] p !]) ->
  functional_frame f.
Proof.
  intros f.
  apply contra.
  intros H; unfold functional_frame in H.
  apply not_all_ex_not in H; destruct H as [w1].
  apply not_all_ex_not in H; destruct H as [w2].
  apply not_all_ex_not in H; destruct H as [w3].
  apply imply_to_and with (P := R f w1 w2 /\ R f w1 w3) in H.
  destruct H as [H1 H3]; destruct H1 as [H1 H2].
  apply ex_not_not_all.
  exists (fun _ x => R f w1 x /\ x <> w3).
  apply ex_not_not_all.
  exists [!(#0)!].
  intros H; unfold valid_in_model in H; simpl in H.
  apply H in H2.
  - destruct H2 as [H2 H4].
    contradiction.
  - exists w2; repeat split; assumption.
Qed.

Theorem dense_frame_implies_axiom:
  forall f,
  dense_frame f ->
  (forall v p, Build_Model f v ||= [! [][]p -> [] p !]).
Proof.
  intros f H v p w1 H1 w2 H2.
  unfold dense_frame in H.
  destruct H with (w:=w1) (w':=w2) as [w3].
  simpl in H1.
  pose H2 as H4.
  apply H0 in H4.
  destruct H4 as [H4 H5].
  eapply H1.
  - exact H4.
  - assumption.
Qed.

(*Definição de frame denso no código estava errada*)

Theorem axiom_implies_dense_frame:
  forall f,
  (forall v p, Build_Model f v ||= [! [][]p -> [] p !]) ->
  dense_frame f.
Proof.
  intros f.
  apply contra.
  intros H; unfold dense_frame in H.
  apply not_all_ex_not in H; destruct H as [w1].
  apply not_all_ex_not in H; destruct H as [w2].
  apply ex_not_not_all.
  exists (fun _ x => ~ R f w1 x).
  apply ex_not_not_all.
  exists [!(#0)!].
  intros H1; unfold valid_in_model in H1; simpl in H1. 
  eapply not_ex_all_not in H.
  apply imply_to_and in H.
  destruct H as [H H'].
  apply not_and_or in H'.
  destruct H' as [H' | H''].
  - apply H' in H; contradiction.
  - edestruct H1.
    + intros w3 H3 w4 H4.
      apply H1 in H4.
      * assumption.
      * intros w5 H5 w6 H6.
        apply H1 in H6.
        -- assumption.
        -- intros w7 H7 w8 H8. admit.
    + exact H.
    + apply H. 
Admitted.

Theorem convergent_frame_implies_axiom:
  forall f,
  convergent_frame f ->
  (forall v p, Build_Model f v ||= [! <>[]p -> []<> p !]).
Proof.
  intros f H v p w1 H1 w2 H2.
  unfold convergent_frame in H.
  simpl in H1.
  destruct H1 as [w3].
  destruct H0 as [H1 H3].
  destruct H with (w:=w1) (x:=w2) (y:=w3) as [w4].
  destruct H0.
  - split; assumption.
  - simpl.
    exists w4.
    split.
    + assumption.
    + apply H3 in H4.
      assumption.
Qed.

Theorem axiom_implies_convergent_frame:
  forall f,
  (forall v p, Build_Model f v ||= [! <>[]p -> []<> p !]) ->
  convergent_frame f.
Proof.
  intros f.
  apply contra.
  intros H; unfold convergent_frame in H.
  apply not_all_ex_not in H; destruct H as [w1].
  apply not_all_ex_not in H; destruct H as [w2].
  apply not_all_ex_not in H; destruct H as [w3].
  eapply not_ex_all_not in H.
  apply imply_to_and in H.
  destruct H as [H H'']; destruct H as [H H'].
  apply not_and_or in H''.
  destruct H'' as [H0 | H0].
  - apply ex_not_not_all.
    exists (fun _ x => (R f w3 x)).
    apply ex_not_not_all.
    exists ([!#0!]).
    intros H1; unfold valid_in_model in H1; simpl in H1.
    destruct H1 with (w1) (w2).
    + exists w2; split; try assumption.
      intros w4 H2.
(*      apply H2 in H0.
      contradiction.
      Admitted.*)
      admit.
    + assumption.
    + admit.
  - apply ex_not_not_all.
    exists (fun _ x => (R f w2 x)).
    apply ex_not_not_all.
    exists ([!#0!]).
    intros H1; unfold valid_in_model in H1; simpl in H1.
    destruct H1 with (w1) (w3).
    + exists w3; split; try assumption.
      intros w4 H2.
(*      apply H2 in H0.
      contradiction.
      Admitted.*)
      admit.
    + assumption.
    + admit.
Admitted.


Theorem axiom_implies_convergent_frame':
  forall f,
  (forall v p, Build_Model f v ||= [! <>[]p -> []<> p !]) ->
  convergent_frame f.
Proof.
  intros f.
  apply contra.
  intros H; unfold convergent_frame in H.
  apply not_all_ex_not in H; destruct H as [w1].
  apply not_all_ex_not in H; destruct H as [w2].
  apply not_all_ex_not in H; destruct H as [w3].
  assert ((R f w1 w2 /\ R f w1 w3) /\ (forall z, ~ R f w2 z \/ ~ R f w3 z)).
  - split.
    + eapply not_ex_all_not in H.
      apply imply_to_and in H.
      destruct H.
      exact H.
    + intros w4.
      eapply not_ex_all_not in H.
      apply imply_to_and in H.
      destruct H.
      apply not_and_or in H0.
      exact H0.
  - destruct H0.
    edestruct H1. (*Ver isso aqui*)
    apply ex_not_not_all.
    exists (fun _ x => (R f w3 x)).
    edestruct H.
    apply not_and_or in H1.
    destruct H1.
    + 
    apply ex_not_not_all.
    exists ([!#0!]).
    intros H1; unfold valid_in_model in H1; simpl in H1.
    destruct H1 with (w1) (w2).
    + exists w2; split.
      * edestruct H. apply H0.
      * intros w4 H2.
        edestruct H.
        apply not_and_or in H3.
        destruct H3.
        -- apply H3 in H2; contradiction.
        --