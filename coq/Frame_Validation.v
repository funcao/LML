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

Theorem reflexive_frame_implies_axiomT:
    forall f p,
    reflexivity_frame f ->
    (forall v, Build_Model f v |= .[] p .-> p).
Proof.
  intros f p HR v w1 H1. 
  simpl in H1. 
  unfold reflexivity_frame in HR.
  apply H1 in HR. 
  assumption. 
Qed.

Theorem axiomT_implies_reflexive_frame:
  forall f,
  (forall v p, Build_Model f v |= .[]p .-> p) -> 
  reflexivity_frame f.
Proof.
  intros f. 
  apply contra.
  intros H; unfold reflexivity_frame in H. 
  apply not_all_ex_not in H; destruct H as [w1].
  apply ex_not_not_all. 
  exists (fun _ x => R f w1 x). 
  apply ex_not_not_all. 
  exists (#0). 
  intros H1; unfold fun_validation in H1; simpl in H1. 
  destruct H.
  apply H1. 
  intros w2 H'; assumption.
Qed.

Theorem transitive_frame_implies_axiom4: 
  forall f,
    transitivity_frame f ->
    (forall v p, Build_Model f v |= .[]p .-> .[].[]p).
Proof.
  intros f H v p w1 H1.
  simpl.
  intros w2 H2 w3 H3.
  simpl in H1.
  apply H1.
  unfold transitivity_frame in H.
  apply H with (w:=w1) (w':=w2) (w'':=w3).
  split; assumption.
Qed.

Theorem axiom4_implies_transitive_frame:
  forall f,
  (forall v p, Build_Model f v |= .[]p .-> .[].[]p) -> 
  transitivity_frame f.
Proof.
  intros f.
  apply contra.
  intros H; unfold transitivity_frame in H.
  apply not_all_ex_not in H; destruct H as [w1];
  apply not_all_ex_not in H; destruct H as [w2];
  apply not_all_ex_not in H; destruct H as [w3].
  apply imply_to_and with (P:= R f w1 w2 /\ R f w2 w3) in H.
  destruct H as [H1 H3]; destruct H1 as [H1 H2].
  apply ex_not_not_all.
  exists (fun _ x => R f w1 x).
  apply ex_not_not_all.
  exists (#0).
  intros H; unfold fun_validation in H; simpl in H.
  destruct H3.
  eapply H.
  - intros H3 H4; apply H4.
  - apply H1.
  - apply H2.
Qed.

Theorem symmetric_frame_implies_axiomB:
  forall f,
  simmetry_frame f ->
  (forall v p, Build_Model f v |= p .-> .[].<> p).
Proof.
  intros f H v p w1 H1.
  simpl.
  intros w2 H2.
  exists w1.
  unfold simmetry_frame in H.
  split; try apply H; assumption.
Qed.

Theorem axiomB_implies_symmetric_frame:
  forall f,
  (forall v p, Build_Model f v |= p .-> .[].<>p) -> 
  simmetry_frame f.
Proof.
  intros f.
  apply contra.
  intros H; unfold simmetry_frame in H.
  apply not_all_ex_not in H; destruct H as [w1];
  apply not_all_ex_not in H; destruct H as [w2].
  apply imply_to_and in H; destruct H as [H1 H2].
  apply ex_not_not_all.
  exists (fun _ x => ~ R f w2 x).
  apply ex_not_not_all.
  exists (#0).
  intros H; unfold fun_validation in H; simpl in H.
  pose H1 as H3.
  apply H in H3; try assumption.
  destruct H3 as [w3];
  destruct H0 as [H3 H4];
  contradiction.
Qed.

Theorem euclidean_frame_implies_axiom5:
  forall f,
  euclidian_frame f ->
  (forall v p, Build_Model f v |= .<>p .-> .[].<> p).
Proof.
  intros f H v p w1 H1.
  simpl.
  intros w2 H2.
  unfold euclidian_frame in H.
  simpl in H1;
  destruct H1 as [w3];
  destruct H0 as [H1 H3].
  exists w3.
  split; try assumption.
  - eapply H; split; [exact H2 | assumption].
Qed.

Theorem axiom5_implies_euclidean_frame: 
  forall f,
  (forall v p, Build_Model f v |= .<>p .-> .[].<>p) -> 
  euclidian_frame f.
Proof.
  intros f.
  apply contra.
  intros H; unfold euclidian_frame in H.
  apply not_all_ex_not in H; destruct H as [w1];
  apply not_all_ex_not in H; destruct H as [w2];
  apply not_all_ex_not in H; destruct H as [w3].
  apply imply_to_and with (P := R f w1 w2 /\ R f w1 w3) in H.
  destruct H as [H1 H3]; destruct H1 as [H1 H2].
  apply ex_not_not_all.
  exists (fun _ x =>  ~ R f w2 x).
  apply ex_not_not_all.
  exists (#0).
  intros H; unfold fun_validation in H; simpl in H.
  destruct H with (w1) (w2); try assumption.
  - exists w3; split; assumption.
  - destruct H0 as [H4 H5]; contradiction.
Qed.

Theorem serial_frame_implies_axiomD:
  forall f,
  serial_frame f ->
  (forall v p, Build_Model f v |= .[]p .-> .<> p).
Proof.
  intros f H v p w1 H1.
  unfold serial_frame in H.
  destruct H with (w1) as [w2].
  simpl in *.
  exists w2.
  split; try assumption.
  apply H1; assumption.
Qed.

Theorem axiomD_implies_serial_frame: 
  forall f,
  (forall v p, Build_Model f v |= .[]p .-> .<> p) ->
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
  exists (#0).
  intros H1; unfold fun_validation in H1; simpl in H1.
  edestruct H1.
  - intros w2 H2.
    destruct H.
    exists w2; exact H2.
  - destruct H0 as [H2 H3]; contradiction.
Qed.

Theorem functional_frame_implies_axiom:
  forall f,
  functional_frame f ->
  (forall v p, Build_Model f v |= .<>p .-> .[]p).
Proof.
  intros f H v p w1 H1 w2 H2.
  unfold functional_frame in H.
  simpl in H1.
  destruct H1 as [w3 H1]; destruct H1 as [H1 H3].
  assert (H4: R (F (Build_Model f v)) w1 w2 /\ R f w1 w3) by (split; assumption).
  apply H in H4; subst; assumption.
Qed.

Theorem axiom_implies_functional_frame:
  forall f,
  (forall v p, Build_Model f v |= .<>p .-> .[] p) ->
  functional_frame f.
Proof.
  intros f.
  apply contra.
  intros H; unfold functional_frame in H.
  apply not_all_ex_not in H; destruct H as [w1];
  apply not_all_ex_not in H; destruct H as [w2];
  apply not_all_ex_not in H; destruct H as [w3].
  apply imply_to_and with (P := R f w1 w2 /\ R f w1 w3) in H.
  destruct H as [H1 H3]; destruct H1 as [H1 H2].
  apply ex_not_not_all.
  exists (fun _ x => R f w1 x /\ x <> w3).
  apply ex_not_not_all.
  exists (#0).
  intros H; unfold fun_validation in H; simpl in H.
  apply H in H2.
  - destruct H2 as [H2 H4]; contradiction.
  - exists w2; repeat split; assumption.
Qed.

Theorem dense_frame_implies_axiom:
  forall f,
  dense_frame f ->
  (forall v p, Build_Model f v |= .[].[]p .-> .[] p).
Proof.
  intros f H v p w1 H1 w2 H2.
  unfold dense_frame in H.
  destruct H with (w1) (w2) as [w3].
  simpl in H1.
  apply H0 in H2; destruct H2 as [H2 H3].
  apply H1 with (w3); assumption.
Qed.

Theorem axiom_implies_dense_frame:
  forall f,
  (forall v p, Build_Model f v |= .[].[]p .-> .[] p) ->
  dense_frame f.
Proof.
  intros f.
  apply contra.
  intros H; unfold dense_frame in H.
  apply not_all_ex_not in H; destruct H as [w1];
  apply not_all_ex_not in H; destruct H as [w2].
  apply ex_not_not_all.
  exists (fun _ x => exists y, R f w1 y /\ R f y x).
  apply ex_not_not_all.
  exists (#0).
  intros H1; unfold fun_validation in H1; simpl in H1. 
  edestruct H1.
  - intros w3 H3 w4 H4.
    exists w3; split; [apply H3 | assumption].
  - eapply not_ex_all_not in H.
    apply imply_to_and in H; destruct H as [H H']; exact H.
  - eapply not_ex_all_not in H.
    apply imply_to_and in H; destruct H as [H H']; apply not_and_or in H'.
    destruct H0 as [H2 H3].
    Unshelve.
    destruct H' as [H' | H''].
    + apply H' in H2; contradiction.
    + apply H'' in H3; contradiction.
    + assumption.
Qed.

Theorem convergent_frame_implies_axiom:
  forall f,
  convergente_frame f ->
  (forall v p, Build_Model f v |= .<>.[]p .-> .[].<> p).
Proof.
  intros f H v p w1 H1 w2 H2.
  unfold convergente_frame in H.
  simpl in H1.
  destruct H1 as [w3]; destruct H0 as [H1 H3];
  destruct H with (w1) (w2) (w3) as [w4];  destruct H0.
  - split; assumption.
  - simpl.
    exists w4.
    split; try assumption.
    apply H3 in H4; assumption.
Qed.

(*Isso está tudo errado*)
Theorem noetherian_frame_implies_axiomGL:
  forall f,
  noetherian_frame f ->
  (forall v p, Build_Model f v |= .[](.[]p .-> p) .-> .[]p).
Proof.
  intros f H v p w1 H1 w2 H2.
  unfold noetherian_frame in H; destruct H as [H H'].
  unfold transitivity_frame in H.
  simpl in H1; apply H1; try assumption.
  intros w3 H3.
  assert (H4: R f w1 w3) by (eapply H; split; [exact H2 | exact H3]).
Admitted.

Theorem axiomGL_implies_noetherian_frame:
  forall f,
  (forall v p, Build_Model f v |= .[](.[]p .-> p) .-> .[]p) ->
  noetherian_frame f.
Proof.
  intros f; apply contra.
  intros H; unfold noetherian_frame in H.
  apply not_and_or in H.

Admitted.

(*
Problema aqui: Não tenho informação suficiente pois cada 
lado da disjunção tem uma função de valoração diferente

Quebra a disjunção da hipótese e cada lado tem sua própria função de valoração,
estas que são as que eu defini na prova no papel
*)
Theorem axiom_implies_convergent_frame: 
  forall f,
  (forall v p, Build_Model f v |= .<>.[]p .-> .[].<> p) ->
  convergente_frame f.
Proof.
  intros f.
  apply contra.
  intros H; unfold convergente_frame in H.
  apply not_all_ex_not in H; destruct H as [w1];
  apply not_all_ex_not in H; destruct H as [w2];
  apply not_all_ex_not in H; destruct H as [w3].
  eapply not_ex_all_not in H.
  apply imply_to_and in H.
  destruct H as [H H1]; destruct H as [H H'].
  apply not_and_or in H1; destruct H1 as [H1 | H1].
  - apply ex_not_not_all.
    exists (fun _ x => (R f w3 x)).
    apply ex_not_not_all.
    exists (#0).
    intros H2; unfold fun_validation in H2; simpl in H2.
    destruct H2 with (w1) (w2).
    + exists w2; split; try assumption.
      intros w4 H3.
(*      apply H2 in H0.
      contradiction.
      Admitted.*)
      admit.
    + assumption.
    + admit.
  - apply ex_not_not_all.
    exists (fun _ x => (R f w2 x)).
    apply ex_not_not_all.
    exists (#0).
    intros H2; unfold fun_validation in H2; simpl in H2.
    destruct H2 with (w1) (w3).
    + exists w3; split; try assumption.
      intros w4 H3.
(*      apply H2 in H0.
      contradiction.
      Admitted.*)
      admit.
    + assumption.
    + admit.
Abort.

(*
Problema aqui: Chego num ponto onde não tenho informação suficiente 
para chegar numa contradição nas hipoteses

Uma só função de valoração que é uma disjunção entre as funções de valoração
de antes. Resolve o problema de variáveis existênciais que não 
podiam ser instanciadas
*)
Theorem axiom_implies_convergent_frame':
  forall f,
  (forall v p, Build_Model f v |= .<>.[]p .-> .[].<> p) ->
  convergente_frame f.
Proof.
  intros f.
  apply contra.
  intros H; unfold convergente_frame in H.
  apply not_all_ex_not in H; destruct H as [w1];
  apply not_all_ex_not in H; destruct H as [w2];
  apply not_all_ex_not in H; destruct H as [w3].
  apply ex_not_not_all.
  exists(fun _ x => R f w3 x \/ R f w2 x).
  apply ex_not_not_all.
  exists (#0).
  intros H2; unfold fun_validation in H2; simpl in H2.
  destruct H2 with (w1) (w2).
  - exists w2; split.
    + eapply not_ex_all_not in H;
      apply imply_to_and in H;
      destruct H as [H0 H1]; destruct H0; assumption.
    + intros w4 H4; right; assumption.
  - eapply not_ex_all_not in H; apply imply_to_and in H;
    destruct H as [H0 H1]; destruct H0; assumption.
  - rename x into w4.
    clear H2. (*Isso não vai ajudar em nada e ocupa espaço no Proof View*)
    apply not_ex_all_not with (n := w4) in H.
    apply imply_to_and in H.
    destruct H as [H H1]; destruct H as [H H']; destruct H0 as [H2 H3].
    pose H1 as H4.
    destruct H3.
    firstorder.
    (*super stuck*)
Abort.

(*
Problema aqui: Chego num ponto onde não tenho informação suficiente 
para fazer qualquer progresso na prova

Mudando a função de valoração de antes pra uma implicação que diz que se há
relacionamento de um lado, do outro não pode haver
*)
Theorem axiom_implies_convergent_frame'':
  forall f,
  (forall v p, Build_Model f v |= .<>.[]p .-> .[].<> p) ->
  convergente_frame f.
Proof.
  intros f.
  apply contra.
  intros H; unfold convergente_frame in H.
  apply not_all_ex_not in H; destruct H as [w1];
  apply not_all_ex_not in H; destruct H as [w2];
  apply not_all_ex_not in H; destruct H as [w3].
  apply ex_not_not_all.
  exists(fun _ w4 => (R f w3 w4 -> ~ R f w2 w4) \/ (R f w2 w4 -> ~ R f w3 w4)).
  apply ex_not_not_all.
  exists (#0).
  intros H2; unfold fun_validation in H2; simpl in H2.
  destruct H2 with (w1) (w2).
  - exists w2; split.
    + eapply not_ex_all_not in H;
      apply imply_to_and in H;
      destruct H as [H0 H1]; destruct H0; assumption.
    + intros w4 H4.
      eapply not_ex_all_not in H;
      apply imply_to_and in H;
      destruct H as [H0 H1]; 
      destruct H0.
      apply not_and_or in H1.
      destruct H1.
      * apply H1 in H4; contradiction.
      * left; intros; contradiction.
  - eapply not_ex_all_not in H;
    apply imply_to_and in H;
    destruct H as [H0 H1];
    destruct H0; 
    assumption.
  - rename x into w4.
    clear H2. (*Isso não vai ajudar em nada e ocupa espaço no Proof View*)
    apply not_ex_all_not with (n := w4) in H.
    apply imply_to_and in H.
    destruct H as [H H1]; destruct H as [H H'].
    destruct H0 as [H2 H3].
    destruct H3.
    + destruct H1; split.
      * assumption.
      * admit. (*não tem como provar isso*)
    + destruct H1; split.
      * assumption.
      * admit. (*não tem como provar isso*)
Abort.

Theorem axiom_implies_convergent_frame''':
  forall f,
  (forall v p, Build_Model f v |= .<>.[]p .-> .[].<> p) ->
  convergente_frame f.
Proof.
  intros f.
  apply contra.
  intros H; unfold convergente_frame in H.
  apply not_all_ex_not in H; destruct H as [w1].
  apply not_all_ex_not in H; destruct H as [w2].
  apply not_all_ex_not in H; destruct H as [w3].
  apply ex_not_not_all.
  exists(fun _ w4 => (R f w3 w4 /\ ~ R f w2 w4) \/ (R f w2 w4 /\ ~ R f w3 w4)).
  apply ex_not_not_all.
  exists (#0).
  intros H2; unfold fun_validation in H2; simpl in H2.
  destruct H2 with (w1) (w2).
  - exists w2; split.
    + eapply not_ex_all_not in H;
      apply imply_to_and in H;
      destruct H as [H0 H1]; 
      destruct H0; 
      assumption.
    + intros w4 H4.
      eapply not_ex_all_not in H;
      apply imply_to_and in H;
      destruct H as [H0 H1]; 
      destruct H0.
      apply not_and_or in H1.
      destruct H1.
      * apply H1 in H4; contradiction.
      * right; split; assumption.
  - eapply not_ex_all_not in H;
    apply imply_to_and in H;
    destruct H as [H0 H1];
    destruct H0; 
    assumption.
  - rename x into w4.
    clear H2. (*Isso não vai ajudar em nada e ocupa espaço no Proof View*)
    apply not_ex_all_not with (n := w4) in H.
    apply imply_to_and in H.
    destruct H as [H H1]; destruct H as [H H'].
    destruct H0 as [H2 H3].
    destruct H3 as [H3 | H3].
    (*stuck*)
    (*dar destruct em H1 não muda em nada*)
Abort.



