Require Import Equality.
Require Import Modal_Library Deductive_System Sets.

(* Typeclass that states that we "lift" indexes of either base set to fusion set *)
Class lift_conv (A B: Type): Type := {
  lift: A -> B
}.

Section Fusion.

  (*Index sets*)
  Context {I1: Set}.
  Context {I2: Set}.

  (*Fusion of indexes is simply disjoint set union*)
  Definition fusion: Set :=
    I1 + I2.

  (*Instances of the modal index set typeclass*)
  Context {X1: @modal_index_set I1}.
  Context {X2: @modal_index_set I2}.

  (*Indexes of the fusion*)
  Instance fusion_index_set: @modal_index_set fusion := {|
    C i :=
      match i with
      | inl a => @C I1 X1 a
      | inr b => @C I2 X2 b
      end
  |}.

  (*** Helper Notations ***)

  (* Modal Indexes of either logic and the logic resulting from their fusion *)
  Local Notation modal_index1 := (@modal_index I1 X1).
  Local Notation modal_index2 := (@modal_index I2 X2).
  Local Notation modal_indexF := (@modal_index fusion fusion_index_set).

  (* Formulas of either logic and the logic resulting from their fusion *)
  Local Notation formula1 := (@formula I1 X1).
  Local Notation formula2 := (@formula I2 X2).
  Local Notation formulaF := (@formula fusion fusion_index_set).

  (* Frames of either logic and the logic resulting from their fusion *)
  Local Notation Frame1 := (@Frame I1 X1).
  Local Notation Frame2 := (@Frame I2 X2).
  Local Notation FrameF := (@Frame fusion fusion_index_set).

  (* Models of either logic and the logic resulting from their fusion *)
  Local Notation Model1 := (@Model I1 X1).
  Local Notation Model2 := (@Model I2 X2).
  Local Notation ModelF := (@Model fusion fusion_index_set).

  (* Axiom Sets of either logic and the logic resulting from their fusion *)
  Local Notation axiom1 := (@axiom I1 X1).
  Local Notation axiom2 := (@axiom I2 X2).
  Local Notation axiomF := (@axiom fusion fusion_index_set).

  (* Definition of the fusion of frames *)
  Definition join_frames (f1: Frame1) (f2: Frame2) (H: W f2 = W f1): FrameF.
  Proof.
    constructor 1 with (W f1).
    intros ([ idx | idx ], idx_valid) w v.
    - exact (R f1 (Build_modal_index idx idx_valid) w v).
    - rewrite <- H in w, v.
      exact (R f2 (Build_modal_index idx idx_valid) w v).
  Defined.

  (* Proofs that we can "lift" indexes of either base system to the fusion system *)
  Instance index_lift1: lift_conv modal_index1 modal_indexF.
  Proof.
    constructor; intros.
    destruct H as (idx, idx_valid).
    constructor 1 with (index := inl idx).
    simpl; assumption.
  Defined.

  Instance index_lift2: lift_conv modal_index2 modal_indexF.
  Proof.
    constructor; intros.
    destruct H as (idx, idx_valid).
    constructor 1 with (index := inr idx).
    simpl; assumption.
  Defined.

  (* Proofs that we can "lift" formulas of either base system to the fusion system *)
  Instance formula_lift1: lift_conv formula1 formulaF.
  Proof.
    constructor; intros.
    induction H.
    - constructor 1.
      exact n.
    - constructor 2.
      exact IHformula.
    - constructor 3.
      + exact (lift m).
      + exact IHformula.
    - constructor 4.
      + exact (lift m).
      + exact IHformula.
    - constructor 5.
      + exact IHformula1.
      + exact IHformula2.
    - constructor 6.
      + exact IHformula1.
      + exact IHformula2.
    - constructor 7.
      + exact IHformula1.
      + exact IHformula2.
  Defined.

  Instance formula_lift2: lift_conv formula2 formulaF.
  Proof.
    constructor; intros.
    induction H.
    - constructor 1.
      exact n.
    - constructor 2.
      exact IHformula.
    - constructor 3.
      + exact (lift m).
      + exact IHformula.
    - constructor 4.
      + exact (lift m).
      + exact IHformula.
    - constructor 5.
      + exact IHformula1.
      + exact IHformula2.
    - constructor 6.
      + exact IHformula1.
      + exact IHformula2.
    - constructor 7.
      + exact IHformula1.
      + exact IHformula2.
  Defined.

  (* Some cheeky automation that may not work :-( *)
  (* TODO: Ver se é possível fazer essa automação funcionar *)
  Ltac lift_me_up type :=
    repeat match goal with
    | [H: type |- formulaF] => try (exact (lift H)) 
    | _                     => fail "expected fomulaF"
    end.

  (* Proofs that we can "lift" axioms of either base system to the fusion system *)
  Instance axiom_lift1: lift_conv axiom1 axiomF.
  Proof.
    constructor; intros.
    destruct H.
    - constructor 1.
      + exact (lift f).
      + exact (lift f0).
    - constructor 2.
      + exact (lift f).
      + exact (lift f0).
      + exact (lift f1).
    - constructor 3.
      + exact (lift f).
      + exact (lift f0).
    - constructor 4.
      + exact (lift f).
      + exact (lift f0).
    - constructor 5.
      + exact (lift f).
      + exact (lift f0).
    - constructor 6.
      + exact (lift f).
      + exact (lift f0).
    - constructor 7.
      + exact (lift f).
      + exact (lift f0).
    - constructor 8.
      + exact (lift f).
      + exact (lift f0).
    - constructor 9.
      + exact (lift f).
      + exact (lift f0).
      + exact (lift f1).
    - constructor 10.
      exact (lift f).
    - constructor 11.
      + exact (lift m).
      + exact (lift f).
      + exact (lift f0).
    - constructor 12.
      + exact (lift m).
      + exact (lift f).
    - constructor 13.
      + exact (lift m).
      + exact (lift f).
    - constructor 14.
      + exact (lift m).
      + exact (lift f).
    - constructor 15.
      + exact (lift m).
      + exact (lift f).
    - constructor 16.
      + exact (lift m).
      + exact (lift f).
    - constructor 17.
      + exact (lift m).
      + exact (lift f).
    - constructor 18.
      + exact (lift m).
      + exact (lift f).
  Defined.

  Instance formula_axiom2: lift_conv axiom2 axiomF.
  Proof.
    constructor; intros.
    destruct H.
    - constructor 1.
      + exact (lift f).
      + exact (lift f0).
    - constructor 2.
      + exact (lift f).
      + exact (lift f0).
      + exact (lift f1).
    - constructor 3.
      + exact (lift f).
      + exact (lift f0).
    - constructor 4.
      + exact (lift f).
      + exact (lift f0).
    - constructor 5.
      + exact (lift f).
      + exact (lift f0).
    - constructor 6.
      + exact (lift f).
      + exact (lift f0).
    - constructor 7.
      + exact (lift f).
      + exact (lift f0).
    - constructor 8.
      + exact (lift f).
      + exact (lift f0).
    - constructor 9.
      + exact (lift f).
      + exact (lift f0).
      + exact (lift f1).
    - constructor 10.
      exact (lift f).
    - constructor 11.
      + exact (lift m).
      + exact (lift f).
      + exact (lift f0).
    - constructor 12.
      + exact (lift m).
      + exact (lift f).
    - constructor 13.
      + exact (lift m).
      + exact (lift f).
    - constructor 14.
      + exact (lift m).
      + exact (lift f).
    - constructor 15.
      + exact (lift m).
      + exact (lift f).
    - constructor 16.
      + exact (lift m).
      + exact (lift f).
    - constructor 17.
      + exact (lift m).
      + exact (lift f).
    - constructor 18.
      + exact (lift m).
      + exact (lift f).
  Defined.

  (* Proving that lift and instantiate are commutative *)
    Lemma instantiate_lift_inversion1:
      forall (p: axiom1) (f: formulaF),
      instantiate (lift p) = f ->
      f = lift (instantiate p).
  Proof.
    intros.
    induction p; auto.
  Qed.

  Lemma instantiate_lift_inversion2:
    forall (p: axiom2) (f: formulaF),
    instantiate (lift p) = f ->
    f = lift (instantiate p).
  Proof.
    intros.
    induction p; auto.
  Qed.

  (* Proving that we can recover the frames/models of the base logics after fusion *)
  Lemma split_frame1:
    FrameF -> Frame1.
  Proof.
    intros F.
    destruct F as (W, R).
    constructor 1 with W.
    intros idx w v.
    apply R.
    - destruct idx.
      constructor 1 with (index := inl index).
      assumption.
    - exact w.
    - exact v.
  Defined.

  Lemma split_model1:
    ModelF -> Model1.
  Proof.
    intros M.
    destruct M as (F, v).
    constructor 1 with (F := split_frame1 F).
    destruct F; simpl in *.
    exact v.
  Defined.

  (* Proving that if we lift a model that was split we get a fusion model back*)
  Instance lift_split_model1 M: @lift_conv (W (F (split_model1 M))) (W (F M)).
  Proof.
    constructor; intros.
    destruct M as ((W, R), v);
    simpl in *.
    assumption.
  Defined.

  (* Proving that splitting model preserves evaluation of formulas *)
  (* That is, if a formula was true/false in the base model, it will be true/false 
      in the fusion model *)
  Lemma split_model1_coherence:
    forall M f w,
    fun_validation (split_model1 M) w f <->
      fun_validation M (lift w) (lift f).
  Proof.
    intros until f.
    destruct M as ((W, R), v). 
    set (F := Build_Frame W R).
    set (M := Build_Model F v).
    fold M in v; simpl in v.
    induction f; split; intros.
    - assumption.
    - assumption.
    - replace (lift (Neg f)) with (Neg (lift f)) by auto.
      intros ?H.
      eapply H.
      apply IHf.
      assumption.
    - replace (lift (Neg f)) with (Neg (lift f)) in H by auto.
      intros ?H.
      eapply H.
      apply IHf.
      assumption.
    - replace (lift (Box m f)) with (Box (lift m) (lift f)) by auto.
      intros w' ?.
      apply IHf.
      apply H.
      assumption.
    - replace (lift (Box m f)) with (Box (lift m) (lift f)) in H by auto.
      intros w' ?.
      apply IHf.
      apply H.
      assumption.
    - replace (lift (Dia m f)) with (Dia (lift m) (lift f)) by auto.
      destruct H as (w', ?, ?).
      exists w'; 
      [ | apply IHf]; assumption.
    - replace (lift (Dia m f)) with (Dia (lift m) (lift f)) in H by auto.
      destruct H as (w', ?, ?).
      exists w'; 
      [ | apply IHf]; assumption.
    - replace (lift (And f1 f2)) with (And (lift f1) (lift f2)) by auto.
      destruct H; constructor;
      [ apply IHf1 | apply IHf2 ];
      assumption.
    - replace (lift (And f1 f2)) with (And (lift f1) (lift f2)) in H by auto.
      destruct H; constructor;
      [ apply IHf1 | apply IHf2 ];
      assumption.
    - replace (lift (Or f1 f2)) with (Or (lift f1) (lift f2)) by auto.
      destruct H;
      [left; apply IHf1 | right; apply IHf2];
      assumption.
    - replace (lift (Or f1 f2)) with (Or (lift f1) (lift f2)) in H by auto.
      destruct H;
      [left; apply IHf1 | right; apply IHf2];
      assumption.
    - replace (lift (Implies f1 f2)) with (Implies (lift f1) (lift f2)) by auto.
      intros ?H.
      apply IHf2.
      apply H.
      apply IHf1.
      assumption.
    - replace (lift (Implies f1 f2)) with (Implies (lift f1) (lift f2)) in H by auto.
      intros ?H.
      apply IHf2.
      apply H.
      apply IHf1.
      assumption.
  Qed.

  (* Same as before, but now for frame2 *)
  Lemma split_frame2:
    FrameF -> Frame2.
  Proof.
    intros F.
    destruct F as (W, R).
    constructor 1 with W.
    intros idx w v.
    apply R.
    - destruct idx.
      constructor 1 with (index := inr index).
      assumption.
    - exact w.
    - exact v.
  Defined.

  Lemma split_model2:
    ModelF -> Model2.
  Proof.
    intros M.
    destruct M as (F, v).
    constructor 1 with (F := split_frame2 F).
    destruct F; simpl in *.
    exact v.
  Defined.

  Instance lift_split_model2 M: @lift_conv (W (F (split_model2 M))) (W (F M)).
  Proof.
    constructor; intros.
    destruct M as ((W, R), v);
    simpl in *.
    assumption.
  Defined.

  Lemma split_model2_coherence:
    forall M f w,
    fun_validation (split_model2 M) w f <->
      fun_validation M (lift w) (lift f).
  Proof.
    intros until f.
    destruct M as ((W, R), v).
    set (F := Build_Frame W R).
    set (M := Build_Model F v).
    fold M in v; simpl in v.
    induction f; split; intros.
    - assumption.
    - assumption.
    - replace (lift (Neg f)) with (Neg (lift f)) by auto.
      intros ?H.
      eapply H.
      apply IHf.
      assumption.
    - replace (lift (Neg f)) with (Neg (lift f)) in H by auto.
      intros ?H.
      eapply H.
      apply IHf.
      assumption.
    - replace (lift (Box m f)) with (Box (lift m) (lift f)) by auto.
      intros w' ?.
      apply IHf.
      apply H.
      assumption.
    - replace (lift (Box m f)) with (Box (lift m) (lift f)) in H by auto.
      intros w' ?.
      apply IHf.
      apply H.
      assumption.
    - replace (lift (Dia m f)) with (Dia (lift m) (lift f)) by auto.
      destruct H as (w', ?, ?).
      exists w'; 
      [ | apply IHf]; assumption.
    - replace (lift (Dia m f)) with (Dia (lift m) (lift f)) in H by auto.
      destruct H as (w', ?, ?).
      exists w'; 
      [ | apply IHf]; assumption.
    - replace (lift (And f1 f2)) with (And (lift f1) (lift f2)) by auto.
      destruct H; constructor;
      [ apply IHf1 | apply IHf2 ];
      assumption.
    - replace (lift (And f1 f2)) with (And (lift f1) (lift f2)) in H by auto.
      destruct H; constructor;
      [ apply IHf1 | apply IHf2 ];
      assumption.
    - replace (lift (Or f1 f2)) with (Or (lift f1) (lift f2)) by auto.
      destruct H;
      [left; apply IHf1 | right; apply IHf2];
      assumption.
    - replace (lift (Or f1 f2)) with (Or (lift f1) (lift f2)) in H by auto.
      destruct H;
      [left; apply IHf1 | right; apply IHf2];
      assumption.
    - replace (lift (Implies f1 f2)) with (Implies (lift f1) (lift f2)) by auto.
      intros ?H.
      apply IHf2.
      apply H.
      apply IHf1.
      assumption.
    - replace (lift (Implies f1 f2)) with (Implies (lift f1) (lift f2)) in H
        by auto.
      intros ?H.
      apply IHf2.
      apply H.
      apply IHf1.
      assumption.
  Qed.

  (* Classes of Frames of either logic and the logic resulting from their fusion *)
  Variable P1: Frame1 -> Prop.
  Variable P2: Frame2 -> Prop.

  Definition PF: FrameF -> Prop :=
    fun F =>
      P1 (split_frame1 F) /\ P2 (split_frame2 F).

  (* Axiom Systems of either logic and the axiom system resulting from fusion *)
  Variable A1: axiom1 -> Prop.
  Variable A2: axiom2 -> Prop.

  Inductive fusion_axioms: axiomF -> Prop :=
    | fusion_axioms1:
      forall p, A1 p -> fusion_axioms (lift p)
    | fusion_axioms2:
      forall p, A2 p -> fusion_axioms (lift p).

End Fusion.

(* Generic Definition of Soundness (in the base library we only have this definition for K) *)
Definition sound I `{X: @modal_index_set I} P A: Prop :=
  forall G p,
  (A; G |-- p) -> entails_modal_class P G p.

(* Proof of transfer of soundness by the fusion *)
Theorem soundness_transfer:
  forall I1 `{X1: @modal_index_set I1} P1 A1,
  forall I2 `{X2: @modal_index_set I2} P2 A2,
  sound I1 P1 A1 ->
  sound I2 P2 A2 ->
  sound fusion (PF P1 P2) (fusion_axioms A1 A2).
Proof.
  intros.
  intros G p ?H M ?H ?H.
  (* 
    The original soundness goal is of the form:
    (fusion_axioms A1 A2; G |-- p) -> entails_modal_class (PF P1 P2) G p.
    As we've introduced the premisse of the ->, we must prove that entails_modal_class (PF P1 P2) G p
      Given the hypothesis that fusion_axioms A1 A2; G |-- p
    We proced by induction on this hypothesis
  *)
  induction H1; intro.
  - (* Case 0: Premisse *)
    now apply H3.
  - (* 
      Case 1: Instance of an Axiom
      We proceed by analising from which system the axiom comes from 
    *)
    destruct H1.
    + (* Either A1 *)
      apply instantiate_lift_inversion1 in H4; subst.
      assert (A1; Empty |-- instantiate p) by now constructor 2 with p.
      set (M1 := split_model1 M).
      specialize (H Empty _ H4 M1).
      assert (P1 (F M1)).
      * destruct M as ((W, F), v).
        apply H2.
      * specialize (H H5).
        assert (theory_modal M1 Empty) by inversion 1.
        specialize (H H6).
        destruct M as ((W, F), v).
        simpl in H, H2, H3, w.
        specialize (H w).
        apply split_model1_coherence in H.
        assumption.
    + (* Or A2 *)
      apply instantiate_lift_inversion2 in H4; subst.
      assert (A2; Empty |-- instantiate p) by now constructor 2 with p.
      set (M2 := split_model2 M).
      specialize (H0 Empty _ H4 M2).
      assert (P2 (F M2)).
      * destruct M as ((W, F), v).
        apply H2.
      * specialize (H0 H5).
        assert (theory_modal M2 Empty) by inversion 1.
        specialize (H0 H6).
        destruct M as ((W, F), v).
        simpl in H0, H2, H3, w.
        specialize (H0 w).
        apply split_model2_coherence in H0.
        assumption.
  - (* Case 2: Modus Ponens *)
    apply IHdeduction1;
    [ | apply IHdeduction2];
    assumption.
  - (* Case 3: Necessitation *)
    intros w' ?.
    apply IHdeduction.
    inversion 1.
Qed.

(* For the example *)
Require Import Soundness Modal_Notations.

(* TODO: Figure out were to put these examples! *)

Section Soundness_Transfer_Example.

  Local Instance unit_index: @modal_index_set unit := {|
    (* Use the whole universe (i.e., unit). *)
    C x := True
  |}.

  (* The only possible index in the system. *)
  Local Definition idx: modal_index :=
    Build_modal_index tt I.

  (* We define X as the fusion of two copies of System S4 on idx. *)
  Local Definition X :=
    fusion_axioms (S4 idx) (S4 idx).

  (* Condition on frames: both need to be pre-orders. *)
  Local Definition P: Frame -> Prop :=
    fun F => preorder_frame F idx.

  (* We prove System X is sound from soundness of System S4 alone. *)
  Goal
    sound fusion (PF P P) X.
  Proof.
    apply soundness_transfer.
    - intros G p ? M ?.
      now apply soundness_S4 with (idx := idx).
    - intros G p ? M ?.
      now apply soundness_S4 with (idx := idx).
  Qed.

End Soundness_Transfer_Example.
