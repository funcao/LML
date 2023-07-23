Require Import Sets Modal_Library Modal_Notations Classical List.

Lemma singleton_formula:
  forall M p,
  theoryModal M (Singleton p) -> M |= p.
Proof.
  intros.
  apply H.
  constructor.
Qed.

Theorem implies_to_or_modal:
  forall φ ψ,
  [! φ -> ψ !] =|= [! ~φ \/ ψ !].
Proof.
  split.
  - unfold entails_modal, validate_model in *. 
    intros; simpl in *.
    apply singleton_formula in H.
    destruct classic with (M ' w ||- φ); firstorder.
  - unfold entails_modal in *. 
    intros; simpl in *.
    apply singleton_formula in H.
    intro w.
    specialize (H w).
    simpl in H.
    destruct H.
    + simpl; intros.
      exfalso; firstorder.
    + simpl; firstorder.
Qed.

Theorem double_neg_modal:
  forall φ,
  [! ~~φ !] =|= φ.
Proof.
  split.
  - unfold entails_modal.
    simpl in *.
    unfold validate_model.
    intros.
    apply singleton_formula in H.
    specialize (H w); simpl in H.
    apply NNPP; auto.
  - unfold entails_modal.
    simpl in *.
    unfold validate_model.
    intros; simpl in *.
    apply singleton_formula in H.
    edestruct classic.
    + exact H0.
    + apply NNPP in H0.
      exfalso; eauto.
Qed.

Theorem and_to_implies_modal:
  forall φ ψ,
  [! φ /\ ψ !] =|= [! ~(φ -> ~ψ) !].
Proof.
  split.
  - unfold entails_modal, validate_model.
    simpl in *; intros.
    unfold validate_model in *.
    simpl in *.
    apply singleton_formula in H.
    unfold not; intros; apply H0.
    + destruct H with (w:=w); auto.
    + destruct H with (w:=w); auto.
  - unfold entails_modal.
    simpl in *; intros.
    unfold validate_model in *.
    intros; simpl in *.
    apply singleton_formula in H.
    specialize (H w); simpl in H.
    split.
    + edestruct classic.
      * exact H0.
      * exfalso.
        firstorder.
    + edestruct classic.
      * exact H0.
      * firstorder.
Qed.

Theorem diamond_to_box_modal:
  forall φ,
  [! <>φ !] =|= [! ~[]~φ !].
Proof.
  split.
  - unfold entails_modal, validate_model in *.
    simpl in *; intros.
    apply singleton_formula in H.
    specialize (H w); simpl in H.
    edestruct classic.
    + exact H0.
    + firstorder.
  - intros.
    unfold entails_modal in *.
    simpl in *.
    unfold validate_model in *.
    simpl in *.
    unfold not in *.
    intros.
    apply singleton_formula in H.
    specialize (H w); simpl in H.
    edestruct classic.
    + exact H0.
    + exfalso.
      firstorder.
Qed.
