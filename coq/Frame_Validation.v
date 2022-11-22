Require Import Modal_Library Modal_Notations Modal_Tactics Classical.

(** Proving Soundeness results in modal systems **)

(*
  To prove the soundness of any of the model systems defined in the paper / in the previous files,
  suffices to prove that, for any given frame that "belongs" to that systems, it's corresponding axiom
  will be a tautology in any model built with that frame.
  Example, to prove the soundness of T, suffices to prove that, in any reflexive frame F, any model 
  built with F will have T as a tautology.

  The reasoning behind these proofs is simple -- systems of modal logic are semantically defined
  by imposing restrictions on the accessibility relations of frames, restrictions are first order formulas
  that defined how the accessibility relation behaves. Those first order formulas _correspond_ to certain
  modal formulas, i.e. there's a equivalence in between the first order condition and the modal formula.
  This becomes easier to see once you remember that semmantic valuation of formulas is defined 
  by means of the accessibility relation.

  For example, in T, the restriction is that forall w, R w w, this corresponds to the formula []phi -> phi

  Here we prove both that the frame beloging to a system implies the tautology of it's corresponding 
  axiom and that the axiom being a tautology implies that the frame belongs to the corresponding system.
  It's interesting to note that the latter is far more complex than the former, and we could not find a way
  to prove it in a constructive manner, that is, the proofs are all by contraposition.

  Moreso, for the latter proofs, it is necessary to find a witness valuation function, that is, a valuation
  function that shows that if the frame does not belong to the system, then is corresponding axiom is not
  tautological
*)

(*
  Proving contraposition
*)

Theorem contra:
  forall P Q,
  (~P -> ~Q) -> (Q -> P).
Proof.
  intros. apply NNPP. tauto.
Qed.

(*
  If a frame F is reflexive, then T is valid in every model built with F
*)
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

(*
  If T is valid in every model built with frame F, then F is a reflexive frame
*)
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
  (*forall p, V(p) = {x | w1 R x}, atoms are true in all worlds that w1 can reach*)
  apply ex_not_not_all.
  exists [! #0 !]. (*It is necessary to specify an atom, so we specify p_0*)
  intros H1; unfold validate_model in H1; simpl in H1.
  destruct H.
  apply H1.
  intros w2 H'; assumption.
Qed.

(*
  If a frame F is transitive, then 4 is valid in every model built with F
*)
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
  apply H with (w := w1) (w' := w2) (w'' := w3).
  split; assumption.
Qed.

(*
  If 4 is valid in every model built with frame F, then F is a transitive frame
*)
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
  exists (fun _ x => R f w1 x). (*Same function as before *)
  apply ex_not_not_all.
  exists [! #0 !].
  intros H; unfold validate_model in H; simpl in H.
  destruct H3.
  eapply H.
  - intros H3 H4; apply H4.
  - apply H1.
  - apply H2.
Qed.

(*
  If a frame F is symmetric, then B is valid in every model built with F
*)
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

(*
  If B is valid in every model built with frame F, then F is a symmetric frame
*)
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
  (*forall p, V(p) = {x | ~ w2 R x}, atoms are true in all worlds that w2 cannot reach*)
  apply ex_not_not_all.
  exists [! #0 !].
  intros H; unfold validate_model in H; simpl in H.
  pose H1 as H3.
  apply H in H3; try assumption.
  destruct H3 as [w3];
  destruct H0 as [H3 H4];
  contradiction.
Qed.

(*
  If a frame F is euclidean, then 5 is valid in every model built with F
*)
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

(*
  If 5 is valid in every model built with frame F, then F is a euclidean frame
*)
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
  exists (fun _ x =>  ~ R f w2 x). (*Same function as before*)
  apply ex_not_not_all.
  exists [! #0 !].
  intros H; unfold validate_model in H; simpl in H.
  destruct H with (w1) (w2); try assumption.
  - exists w3; split; assumption.
  - destruct H0 as [H4 H5]; contradiction.
Qed.

(*
  If a frame F is serial, then D is valid in every model built with F
*)
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
  split; try apply H1; assumption.
Qed.

(*
  If D is valid in every model built with frame F, then F is a serial frame
*)
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
  (*forall p, V(p) = {x | ~ w1 R x}, atoms are true in all worlds that w1 cannot reach*)
  apply ex_not_not_all.
  exists [! #0 !].
  intros H1; unfold validate_model in H1; simpl in H1.
  edestruct H1.
  - intros w2 H2.
    destruct H.
    exists w2; exact H2.
  - destruct H0 as [H2 H3]; contradiction.
Qed.

(*
  If a frame F is serial, then it's axiom is valid in every model built with F
*)
Theorem functional_frame_implies_axiom:
  forall f,
  functional_frame f ->
  forall v p,
  [f -- v] |= [! <>p -> []p !].
Proof.
  intros f H v p w1 H1 w2 H2.
  unfold functional_frame in H.
  simpl in *.
  destruct H1 as [w3 H1]; destruct H1 as [H1 H3].
  assert (H4: R f w1 w2 /\ R f w1 w3) by (split; assumption).
  apply H in H4; subst; assumption.
Qed.

(*
  If the functional axiom is valid in every model built with frame F, then F is a functional frame
*)
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
  (*forall p, V(p) = {x | w1 R x and x != w3}, atoms are true in all worlds that are not w3 
    which w1 can reach*)
  apply ex_not_not_all.
  exists [! #0 !].
  intros H; unfold validate_model in H; simpl in H.
  apply H in H2.
  - destruct H2 as [H2 H4]; contradiction.
  - exists w2; repeat split; assumption.
Qed.

(*
  If a frame F is dense, then it's axiom is valid in every model built with F
*)
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

(*
  If the dense axiom is valid in every model built with frame F, then F is a dense frame
*)
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
  (*forall p, V(p) = {x | exists y such that w1 R y and y R x}, 
    atoms are true in all worlds such that there exists a world y that can reach x 
    and that can be reached by w1 *)
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
    (*Coq did some weird shelving with terms somewhere along this proof, this Unshelve is needed to
    removed them from the shelve so that the proof can be completed*)
    destruct H' as [H' | H''].
    + apply H' in H2; contradiction.
    + apply H'' in H3; contradiction.
    + assumption. (*Somehow the 2 terms of type W f that were Unshelved became only one term of type W f*)
Qed.

(*
  If a frame F is convergent, then it's axiom is valid in every model built with F
*)
Theorem convergent_frame_implies_axiom:
  forall f,
  convergente_frame f ->
  forall v p,
  [f -- v] |= [! <>[]p -> []<> p !].
Proof.
  intros f H v p w1 H1 w2 H2.
  unfold convergente_frame in H.
  simpl in *.
  destruct H1 as [w3]; destruct H0 as [H1 H3];
  destruct H with (w1) (w2) (w3) as [w4];  destruct H0.
  - split; assumption.
  - exists w4.
    split; try assumption.
    apply H3 in H4; assumption.
Qed.

(*
  If the convergent axiom is valid in every model built with frame F, then F is a convergent frame
*)
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
  (*forall p, V(p) = {x | ~ w3 R x}, atoms are true in all worlds that w3 cannot reach*)
  apply ex_not_not_all.
  exists [! #0 !].
  intros H5; unfold validate_model in H5; simpl in H5.
  destruct H5 with w1 w3.
  - simpl; exists w2; split.
    + eapply not_ex_all_not in H;
      apply imply_to_and in H;
      destruct H as [H1 H']; destruct H1 as [H1 H2]; assumption.
    + intros w4 H4;
      eapply not_ex_all_not in H;
      apply imply_to_and in H;
      destruct H as [H1 H']; destruct H1 as [H1 H2];
      apply not_and_or in H'; destruct H' as [H3 | H3];
      eauto.
  - simpl; 
    eapply not_ex_all_not in H;
    apply imply_to_and in H;
    destruct H as [H1 H']; destruct H1 as [H1 H2]; assumption.
  - simpl in *; rename x into w4.
    destruct H0; contradiction.
    (*Once again, some weird shelving from Coq here*)
    Unshelve. assumption. assumption.
Qed.

(*
  If a frame F is noetherian, then GL is valid in every model built with F
*)
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
  (*S is a function that describes a subset of w, that is, it is the characteristic function of 
  a subset of W, in this particular case, it describes the (sub)set of all worlds w1 such that
  w R w1 and p is not true at w1*)
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

(*
  If, in any model M, (any instance of) GL is a tautology, then (any instance of) 4 is a tautology in M
*)
Lemma GL_implies_4:
  forall M,
  (forall q, M |= [! []([]q -> q) -> []q !]) ->
  (forall p, M |= [! []p -> [][]p !]).
Proof.
  intros M H p.
  
  (*Step 0: |= X -> ((Y /\ Z) -> (Z /\ X)) -- Tautology*)
  assert(H0: forall x y z, M |= [! x -> ((y /\ z) -> (z /\ x)) !]) 
    by (intros x y z w H0;split; destruct H1; trivial).

  (*Step 1: |= [][]X /\ []X -> []([]X /\ X) -- Theorem*)
  assert(H1: forall x, M |= [! x -> ([]([]x /\ x) -> ([]x /\ x)) !])
    by (intros x w H1 H2; simpl; split; [apply H2 | assumption]).

  (*Step 2: (|= A -> B) -> (|= []A -> []B) -- Syntatic Property*)
  assert(H2: forall x y, (M |= [! x -> y !]) -> (M |= [! []x -> []y !]))
    by (intros x y H2 w H3 w1 H4; apply H2; apply H3; assumption).

  (*Step 3: (|= []X /\ X -> []X) -- Tautology*)
  assert(H3: forall x, (M |= [! []x /\ x -> []x !]))
    by (intros ?x ?w H3; apply H3).

  (*Step 4: Prove an instance of Step 0*)
  assert(H4: M |= [! p -> (([][]p /\ []p) -> ([]p /\ p)) !])
    by (apply H0 with (x:=[!p!]) (y:=[![][]p!]) (z:=[![]p!])); 
  clear H0.
  
  (*Step 5: Apply Step 1 on Step 4*)
  assert(H5: M |= [! p -> ([]([]p /\ p) -> ([]p /\ p)) !]) 
    by (apply H1); 
  clear H1; clear H4.

  (*Step 6: Apply Step 2 on Step 5*)
  assert(H6: M |= [! []p -> []( ([]([]p /\ p) -> ([]p /\ p)) ) !]) 
    by (apply H2; assumption);
  clear H5.

  (*Step 7: Prove an instance of GL*)
  assert(H7: M |= [! []([]([]p /\ p) -> ([]p /\ p)) -> []([]p /\ p) !])
    by (apply H with (q:=[! []p /\ p !]));
  clear H.

  (*Step 8: From Step 6 and Step 7, prove |= []p -> []([]p /\ p) 
            by transitivity of -> *)
  assert(H8: M |= [! []p -> []([]p /\ p) !])
    by (eapply modal_impl_transitivity; split; [exact H6 | exact H7]);
  clear H6; clear H7.

  (*Step 9: Prove an instance of Step 3*)
  assert(H9: M |= [! []p /\ p -> []p !]) 
    by (apply H3 with (x:=p));
  clear H3.

  (*Step 10: Apply Step 2 on Step 9*)
  assert(H10: M |= [! []([]p /\ p) -> [][]p !])
    by (auto);
  clear H2; clear H9.

  (*Step 11: From Step 8 and 10, prove |= []p -> [][]p
             by transitivity of ->*)
  assert(H11: M |= [! []p -> [][]p !])
    by (eapply modal_impl_transitivity; split; [exact H8 | exact H10]);
  clear H8; clear H10.
  
  assumption.

Qed.

(*
  If GL is valid in every model built with frame F, then F is a noetherian frame
*)
Theorem axiomGL_implies_noetherian_frame:
  forall f,
  (forall v p, [f -- v] |= [! []([]p -> p) -> []p !]) ->
  noetherian_frame f.
Proof.
  intros f H.
  unfold noetherian_frame; split.
  (*If F is noetherian, then it is both transitive and conversely well founded*)
  - apply axiom4_implies_transitive_frame; intros; 
    apply GL_implies_4; apply H. (*Proving transitivity*)
  - generalize dependent H; apply contra; intros H;
    unfold conversely_well_founded_frame in H;
    apply not_all_ex_not in H; destruct H as [S];
    apply imply_to_and in H; destruct H as [H'' H].
    (*Asserting that the subset S of the set of worlds has no maximal element*)
    assert(H0: forall w, S w -> exists w', ~ (S w' -> ~ R f w w')).
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
      (*forall p, V(p) = {x | ~ S x}, atoms are true in all worlds that are not in S*)
      apply ex_not_not_all;
      exists [! #0 !].
      intros H1; unfold validate_model in H1; simpl in H1.
      assert (H2: ~ ([f--(fun _ x => ~ S x)] ' w ||- [! []#0 !])) 
        by (intros H2; apply H2 in H; contradiction);
      simpl in H2. 
      (*It is not true that, in a model built with the function described above, []p_0 is true at w*)
      destruct H1 with (w) (w1); try assumption.
      intros w2 H3 H4 H5.
      apply H0 in H5.
      destruct H5 as [w3 H5].
      apply imply_to_and in H5.
      destruct H5 as [H5 H6]; apply NNPP in H6.
      apply H4 in H6;
      contradiction.
Qed.
