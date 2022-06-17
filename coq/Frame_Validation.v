Require Import Modal_Library Modal_Notations Classical.

Theorem contra:
  forall P Q,
  (~ P -> ~ Q) -> (Q -> P).
Proof.
  intros. apply NNPP. intro. apply H in H1. contradiction.
Qed.

Theorem reflexive_frame_implies_axiomT:
  forall f p,
  reflexivity_frame f ->
  forall v,
  [f -- v] |= [! []p -> p !].
Proof.
  intros f p HR v w1 H1.
  simpl in H1.
  unfold reflexivity_frame in HR.
  apply H1 in HR.
  assumption.
Qed.

Theorem axiomT_implies_reflexive_frame:
  forall f,
  (forall v p, [f -- v] |= [! []p -> p !]) ->
  reflexivity_frame f.
Proof.
  intros f.
  apply contra.
  intros H; unfold reflexivity_frame in H.
  apply not_all_ex_not in H; destruct H as [w1].
  apply ex_not_not_all.
  exists (fun _ x => R f w1 x).
  apply ex_not_not_all.
  exists [! #0 !].
  intros H1; unfold validate_model in H1; simpl in H1.
  destruct H.
  apply H1.
  intros w2 H'; assumption.
Qed.

Theorem transitive_frame_implies_axiom4:
  forall f,
  transitivity_frame f ->
  forall v p,
  [f -- v] |= [! []p -> [][]p !].
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
  (forall v p, [f -- v] |= [! []p -> [][]p !]) ->
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
  exists [! #0 !].
  intros H; unfold validate_model in H; simpl in H.
  destruct H3.
  eapply H.
  - intros H3 H4; apply H4.
  - apply H1.
  - apply H2.
Qed.

Theorem symmetric_frame_implies_axiomB:
  forall f,
  simmetry_frame f ->
  forall v p,
  [f -- v] |= [! p -> []<>p !].
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
  (forall v p, [f -- v] |= [! p -> []<>p !]) ->
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
  exists [! #0 !].
  intros H; unfold validate_model in H; simpl in H.
  pose H1 as H3.
  apply H in H3; try assumption.
  destruct H3 as [w3];
  destruct H0 as [H3 H4];
  contradiction.
Qed.

Theorem euclidean_frame_implies_axiom5:
  forall f,
  euclidian_frame f ->
  forall v p,
  [f -- v] |= [! <>p -> []<>p !].
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
  eapply H; split; [exact H2 | assumption].
Qed.

Theorem axiom5_implies_euclidean_frame:
  forall f,
  (forall v p, [f -- v] |= [! <>p -> []<>p !]) ->
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
  exists [! #0 !].
  intros H; unfold validate_model in H; simpl in H.
  destruct H with (w1) (w2); try assumption.
  - exists w3; split; assumption.
  - destruct H0 as [H4 H5]; contradiction.
Qed.

Theorem serial_frame_implies_axiomD:
  forall f,
  serial_frame f ->
  forall v p,
  [f -- v] |= [! []p -> <>p !].
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
  (forall v p, [f -- v] |= [! []p -> <>p !]) ->
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
  exists [! #0 !].
  intros H1; unfold validate_model in H1; simpl in H1.
  edestruct H1.
  - intros w2 H2.
    destruct H.
    exists w2; exact H2.
  - destruct H0 as [H2 H3]; contradiction.
Qed.

Theorem functional_frame_implies_axiom:
  forall f,
  functional_frame f ->
  forall v p,
  [f -- v] |= [! <>p -> []p !].
Proof.
  intros f H v p w1 H1 w2 H2.
  unfold functional_frame in H.
  simpl in H1.
  destruct H1 as [w3 H1]; destruct H1 as [H1 H3].
  assert (H4: R (f) w1 w2 /\ R f w1 w3) by (split; assumption).
  apply H in H4; subst; assumption.
Qed.

Theorem axiom_implies_functional_frame:
  forall f,
  (forall v p, [f -- v] |= [! <>p -> []p !]) ->
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
  exists [! #0 !].
  intros H; unfold validate_model in H; simpl in H.
  apply H in H2.
  - destruct H2 as [H2 H4]; contradiction.
  - exists w2; repeat split; assumption.
Qed.

Theorem dense_frame_implies_axiom:
  forall f,
  dense_frame f ->
  forall v p,
  [f -- v] |= [! [][]p -> []p !].
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
  (forall v p, [f -- v] |= [! [][]p -> []p !]) ->
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
  exists [! #0 !].
  intros H1; unfold validate_model in H1; simpl in H1. 
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
  forall v p,
  [f -- v] |= [! <>[]p -> []<> p !].
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

Theorem axiom_implies_convergent_frame:
  forall f,
  (forall v p, [f -- v] |= [! <>[]p -> []<> p !]) ->
  convergente_frame f.
Proof.
  intros f.
  apply contra.
  intros H; unfold convergente_frame in H.
  apply not_all_ex_not in H; destruct H as [w1];
  apply not_all_ex_not in H; destruct H as [w2];
  apply not_all_ex_not in H; destruct H as [w3].
  apply ex_not_not_all.
  exists (fun _ x => ~ R f w3 x).
  apply ex_not_not_all.
  exists [! #0 !].
  intros H5; unfold validate_model in H5; simpl in H5.
  destruct H5 with (w1) (w3).
  - simpl; exists w2; split.
    + eapply not_ex_all_not in H;
      apply imply_to_and in H;
      destruct H as [H1 H']; destruct H1 as [H1 H2]; assumption.
    + intros w4 H4;
      eapply not_ex_all_not in H;
      apply imply_to_and in H;
      destruct H as [H1 H']; destruct H1 as [H1 H2];
      apply not_and_or in H'; destruct H' as [H3 | H3].
      * destruct H3; apply H4.
      * assumption.
  - simpl; 
    eapply not_ex_all_not in H;
    apply imply_to_and in H;
    destruct H as [H1 H']; destruct H1 as [H1 H2]; assumption.
  - simpl in *; rename x into w4.
    destruct H0; contradiction.
    Unshelve. assumption. assumption. (*Coq não aceitou ; aqui*)
Qed.

Theorem modal_double_neg: 
  forall M w p, (M ' w ||- [! ~~ p !]) -> (M ' w ||- p).
Proof.
  intros M w p H; simpl in H; apply NNPP; apply H.
Qed.

Theorem modal_contra: 
  forall M p q,
  (M |= [! ~ p -> ~ q !]) -> (M |= [! q -> p !]).
Proof.
  intros M p q H w1 H1.
  unfold validate_model in H; simpl in *.
  apply modal_double_neg; intros H2.
  apply H in H2; apply H2 in H1; contradiction.
Qed.

Lemma and_to_imply: 
  forall P Q:Prop, P /\ ~ Q -> ~ (P -> Q).
Proof.
  intros P Q [H1 H2] H3; apply H3 in H1; contradiction.
Qed.

Theorem noetherian_frame_implies_axiomGL:
  forall f,
  noetherian_frame f ->
  forall v p,
  [f -- v] |= [! []([]p -> p) -> []p !].
Proof.
  intros f H v p.
  apply modal_contra.
  intros w H1; simpl in w, H1.
  apply not_all_ex_not in H1; destruct H1 as [w1 H1];
  apply imply_to_and in H1; destruct H1 as [H1 H2].
  set (S := fun w1 => R f w w1 /\ ([f -- v] ' w1 ||- [! ~ p !])).
  destruct H as [H H'];
  destruct H' with S as [w2 [[H3 H4] H5]]; try (exists w1; split; trivial).
  clear H'; unfold S in H5; clear S.
  simpl; apply ex_not_not_all.
  exists w2.
  intros H6; simpl in H6.
  apply H6 in H3; try eauto.
  intros w3 H7.
  assert (H8: [f-- v] ' w2 ||- [! [] p -> p !]) by (intros ?H; apply H6; assumption);
  assert (H9: [f-- v] ' w2 ||- [! ~ [] p !]) by (intros H9; apply H8 in H9; contradiction).
  simpl in H9; apply not_all_ex_not in H9;
  destruct H9 as [w4 H9];
  apply imply_to_and in H9.
  assert (H10: (R f w2 w4 /\ ~([f--v] ' w4 ||- p)) -> (R f w2 w4 /\ ([f--v] ' w4 ||- [! ~ p !]))) by (easy);
  apply H10 in H9; clear H10.
  assert (H10: R f w w4) by (apply H with (w:=w) (w':=w2) (w'':=w4); easy).
  destruct H9;
  assert (H11: R f w w4 /\ ([f--v] ' w4 ||- [! ~ p !])) by (easy).
  apply H5 in H11;
  contradiction.
Qed.

Lemma GL_implies_4:
  forall f v p,
  ([f -- v] |= [! []([]p -> p) -> []p !]) ->
  ([f -- v] |= [! []p -> [][]p !]).
Proof.
  intros f v p H.
  
  (*Step 0: |= X -> ((Y /\ Z) -> (Z /\ X)) -- Tautology*)
  assert(H0: forall x y z, [f -- v] |= [! x -> ((y /\ z) -> (z /\ x)) !]) 
    by (intros x y z w H0;split; destruct H1; trivial).

  (*Step 1: |= [][]X /\ []X -> []([]X /\ X) -- Theorem*)
  assert(H1: forall x, [f -- v] |= [! x -> ([]([]x /\ x) -> ([]x /\ x)) !])
    by (intros x w H1 H2; simpl; split; [apply H2 | assumption]).

  (*Step 2: (|= A -> B) -> (|= []A -> []B) -- Syntatic Property*)
  assert(H2: forall x y, ([f -- v] |= [! x -> y !]) -> ([f -- v] |= [! []x -> []y !]))
    by (intros x y H2 w H3 w1 H4; apply H2; apply H3; assumption).

  (*Step 3: (|= []X /\ X -> []X) -- Tautology*)
  assert(H3: forall x, ([f--v] |= [! []x /\ x -> []x !]))
    by (intros ?x ?w H3; apply H3).

  (*Step 4: Prove an instance of Step 0*)
  assert(H4: [f -- v] |= [! p -> (([][]p /\ []p) -> ([]p /\ p)) !])
    by (apply H0 with (x:=[!p!]) (y:=[![][]p!]) (z:=[![]p!])); 
  clear H0.
  
  (*Step 5: Apply Step 1 on Step 4*)
  assert(H5: [f -- v] |= [! p -> ([]([]p /\ p) -> ([]p /\ p)) !]) 
    by (apply H1); 
  clear H1; clear H4.

  (*Step 6: Apply Step 2 on Step 5*)
  assert(H6: [f -- v] |= [! []p -> []( ([]([]p /\ p) -> ([]p /\ p)) ) !]) 
    by (apply H2; assumption);
  clear H5.

  (*Step 7: Prove an instance of GL*)
  assert(H7: [f -- v] |= [! []([]([]p /\ p) -> ([]p /\ p)) -> []([]p /\ p) !])
    by (admit);
  clear H.

  (*Step 8: From Step 6 and Step 7, prove |= []p -> []([]p /\ p) 
  by transitivity of -> *)
  assert(H8: [f -- v] |= [! []p -> []([]p /\ p) !])
    by (admit);
  clear H6; clear H7.

  (*Step 9: Prove an instance of Step 3*)
  assert(H9: [f--v] |= [! []p /\ p -> []p !]) 
    by (apply H3 with (x:=p));
  clear H3.

  (*Step 10: Apply Step 2 on Step 9*)
  assert(H10: [f--v] |= [! []([]p /\ p) -> [][]p !])
    by (auto);
  clear H2; clear H9.

  (*Step 11: From Step 8 and 10, prove |= []p -> [][]p
  by transitivity of ->*)
  assert(H11: [f--v] |= [! []p -> [][]p !])
    by (admit);
  clear H8; clear H10.
  
  assumption.

Admitted.

Theorem axiomGL_implies_noetherian_frame:
  forall f,
  (forall v p, [f -- v] |= [! []([]p -> p) -> []p !]) ->
  noetherian_frame f.
Proof.
  intros f H.
  unfold noetherian_frame; split.
  - apply axiom4_implies_transitive_frame; intros; 
    apply GL_implies_4; apply H.
  - generalize dependent H; apply contra; intros H;
    unfold conversely_well_founded_frame in H;
    apply not_all_ex_not in H; destruct H as [S];
    apply imply_to_and in H; destruct H as [H'' H].
    assert(H0: forall w, S w -> exists w', ~ (S w' -> ~ R f w w')). (*S não tem elemento máximo*)
    + intros w2 H3.
      apply not_ex_all_not with(n:=w2) in H;
      apply not_and_or in H; destruct H; try contradiction.
      apply not_all_ex_not in H;
      destruct H as [w1 H].
      exists w1; apply H.
    + destruct H'' as [w H'']; apply not_ex_all_not with(n:=w) in H.
      apply not_and_or in H; destruct H; try contradiction.
      apply not_all_ex_not in H;
      destruct H as [w1 H];
      apply imply_to_and in H;
      destruct H as [H''' H]; apply NNPP in H.
      apply ex_not_not_all;
      exists (fun _ x => ~ S x);
      apply ex_not_not_all;
      exists [! #0 !].
      intros H1; unfold validate_model in H1; simpl in H1.
      assert (H2: ~ ([f--(fun _ x => ~ S x)] ' w ||- [! []#0 !])) by (intros H2; apply H2 in H; contradiction);
      simpl in H2.
      destruct H1 with (w) (w1); try assumption.
      intros w2 H3 H4 H5.
      apply H0 in H5.
      destruct H5 as [w3 H5].
      apply imply_to_and in H5.
      destruct H5 as [H5 H6]; apply NNPP in H6.
      apply H4 in H6;
      contradiction.
Qed.