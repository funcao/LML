Require Import Arith List Notations Modal_Library Modal_Notations Deductive_System Soundness Frame_Validation PoCBasicComponents PoCSemanticComponents.
Export ListNotations.

(**
  TODO: Improve comments
**)

(* Translating Theories does not change which formulas are in the theories*)
Lemma KT_theory_to_KT4theory_preserves_In: forall t φ,
  In φ t -> In (KTformula_to_KT4formula φ) (KT_theory_to_KT4theory t).
Proof.
  intros t φ H0.
  induction t.
  - inversion H0.
  - destruct H0; simpl in *.
    + left; subst; reflexivity.
    + right; apply IHt; assumption.
Qed.

Lemma K4_theory_to_KT4theory_preserves_In: forall t φ,
  In φ t -> In (K4formula_to_KT4formula φ) (K4_theory_to_KT4theory t).
Proof.
  intros t φ H0.
  induction t.
  - inversion H0.
  - destruct H0; simpl in *.
    + left; subst; reflexivity.
    + right; apply IHt; assumption.
Qed.

(* Translating Theories does not change length *)
Lemma KT_theory_to_KT4theory_same_lenght: forall t,
  length t = length (KT_theory_to_KT4theory t).
Proof.
  intros t.
  induction t.
  - reflexivity.
  - simpl; rewrite IHt;
    reflexivity.
Qed.

Lemma K4_theory_to_KT4theory_same_lenght: forall t,
  length t = length (K4_theory_to_KT4theory t).
Proof.
  intros t.
  induction t.
  - reflexivity.
  - simpl; rewrite IHt;
    reflexivity.
Qed.

(* Translating theories does not change order of formulas *)
Lemma KT_theory_to_KT4theory_nth_error: forall t n φ,
  nth_error t n = Some φ <->
  nth_error (KT_theory_to_KT4theory t) n = Some (KTformula_to_KT4formula φ).
Proof.
  intros t; induction t.
  - intros n φ; split; intros H0.
    + apply nth_error_In in H0; inversion H0.
    + simpl in H0; destruct n; inversion H0.
  - intros n φ; split; intros H0.
    + destruct n; simpl in *.
      * inversion H0; auto.
      * rewrite <- IHt; assumption.
    + destruct n; simpl in *.
      * inversion H0; apply KTformula_to_KT4formula_injective in H1; subst; auto.
      * apply IHt in H0; assumption.
Qed.

Lemma K4_theory_to_KT4theory_nth_error: forall t n φ,
  nth_error t n = Some φ <->
  nth_error (K4_theory_to_KT4theory t) n = Some (K4formula_to_KT4formula φ).
Proof.
  intros t; induction t.
  - intros n φ; split; intros H0.
    + apply nth_error_In in H0; inversion H0.
    + simpl in H0; destruct n; inversion H0.
  - intros n φ; split; intros H0.
    + destruct n; simpl in *.
      * inversion H0; auto.
      * rewrite <- IHt; assumption.
    + destruct n; simpl in *.
      * inversion H0; apply K4formula_to_KT4formula_injective in H1; subst; auto.
      * apply IHt in H0; assumption.
Qed.

(* If a formula is in the premises of a derivation, then it is derivable *)
Theorem deduction_in_premise: forall A T φ,
  In φ T -> KT4deduction A T φ.
Proof.
  intros A T φ H0.
  eapply In_nth_error in H0; destruct H0 as [i].
  apply PremKT4 with i; assumption.
Qed.

(* Weakeaning of a deduction, if a theory T1 is a subset of a theory T2 and T1 derives φ, then so does T2*)
Theorem deduction_weakeaning: forall A T1 T2 φ,
  subset T1 T2 -> KT4deduction A T1 φ -> KT4deduction A T2 φ.
Proof.
  intros A T1 T2 φ H0 H1.
  induction H1 as [ | | T1' φ1 φ2 IH0 IH1 IH2 IH3 | T1' φ IH0 IH1 | T1' φ IH0 IH1 ].
  - (*Premise*)
    unfold subset in H0; eapply nth_error_In in H.
    apply H0 in H; apply deduction_in_premise; auto.
  - (*Axiom*)
    apply AxKT4 with a; auto.
  - (*Modus Ponens*)
    apply MpKT4 with (φ1); [ apply IH1 | apply IH3]; assumption.
  - (*Necessitation for T*)
    apply Nec_T; auto.
  - (*Necessitation for 4*)
    apply Nec_4; auto.
Qed.

(* Deduction is monotone, if a theory T1 derives φ then adding theory T2 to T1 does not change the deduction *)
Theorem deduction_monotone: forall A T1 T2 φ,
  KT4deduction A T1 φ -> KT4deduction A (T1 ++ T2) φ.
Proof.
  intros A T1 T2 φ H0.
  apply deduction_weakeaning with (T1); try easy.
  unfold subset; intros.
  apply in_or_app; auto.
Qed.

(*
  Now we must show that deductions in KT4 are generalizations of deduction in KT / K4

  Definitions of the systems in the base library:
    Inductive T: axiom -> Prop :=
      | T_K:   forall φ, K φ -> T φ
      | T_axT: forall φ , T (axT φ).

    Inductive K4: axiom -> Prop :=
      | K4_K:    forall φ, K φ -> K4 φ
      | K4_axK4: forall φ , K4 (axK4 φ).
*)

Require Import Equality. (* For dependent induction *)

Theorem KTdeduction_generalization: forall Γ φ,
  let KT_to_KT4 := KTformula_to_KT4formula in
  deduction T Γ φ -> KT4deduction KT4Ax (KT_theory_to_KT4theory Γ) (KT_to_KT4 φ).
Proof.
  intros Γ φ KT_to_KT4 H0;
  dependent induction H0.
  - (* Premise *)
    apply PremKT4 with i;
    apply KT_theory_to_KT4theory_nth_error; assumption.
  - (*Axiom*)
    destruct H as [a H | φ]; [destruct H |].
    (* This applies destruct H on the first subgoal and leaves the second unchanged, this is done
    to avoid 3 levels of bullets*)
    + apply KT_axiom_to_KT4axiom_sound with (ax1 φ ψ) (KT4ax1 (KT_to_KT4 φ) (KT_to_KT4 ψ)) (f) in H0;
      try constructor.
      apply AxKT4 with (KT4ax1 (KT_to_KT4 φ) (KT_to_KT4 ψ)); [constructor | easy].
    + apply KT_axiom_to_KT4axiom_sound with (ax2 φ ψ Ɣ) (KT4ax2 (KT_to_KT4 φ) (KT_to_KT4 ψ) (KT_to_KT4 Ɣ)) (f) in H0;
      try constructor.
      apply AxKT4 with (KT4ax2 (KT_to_KT4 φ) (KT_to_KT4 ψ) (KT_to_KT4 Ɣ)); [constructor | easy].
    + apply KT_axiom_to_KT4axiom_sound with (ax3 φ ψ) (KT4ax3 (KT_to_KT4 φ) (KT_to_KT4 ψ)) (f) in H0;
      try constructor.
      apply AxKT4 with (KT4ax3 (KT_to_KT4 φ) (KT_to_KT4 ψ)); [constructor | easy].
    + apply KT_axiom_to_KT4axiom_sound with (ax4 φ ψ) (KT4ax4 (KT_to_KT4 φ) (KT_to_KT4 ψ)) (f) in H0;
      try constructor.
      apply AxKT4 with (KT4ax4 (KT_to_KT4 φ) (KT_to_KT4 ψ)); [constructor | easy].
    + apply KT_axiom_to_KT4axiom_sound with (ax5 φ ψ) (KT4ax5 (KT_to_KT4 φ) (KT_to_KT4 ψ)) (f) in H0;
      try constructor.
      apply AxKT4 with (KT4ax5 (KT_to_KT4 φ) (KT_to_KT4 ψ)); [constructor | easy].
    + apply KT_axiom_to_KT4axiom_sound with (ax6 φ ψ) (KT4ax6 (KT_to_KT4 φ) (KT_to_KT4 ψ)) (f) in H0;
      try constructor.
      apply AxKT4 with (KT4ax6 (KT_to_KT4 φ) (KT_to_KT4 ψ)); [constructor | easy].
    + apply KT_axiom_to_KT4axiom_sound with (ax7 φ ψ) (KT4ax7 (KT_to_KT4 φ) (KT_to_KT4 ψ)) (f) in H0;
      try constructor.
      apply AxKT4 with (KT4ax7 (KT_to_KT4 φ) (KT_to_KT4 ψ)); [constructor | easy].
    + apply KT_axiom_to_KT4axiom_sound with (ax8 φ ψ) (KT4ax8 (KT_to_KT4 φ) (KT_to_KT4 ψ)) (f) in H0;
      try constructor.
      apply AxKT4 with (KT4ax8 (KT_to_KT4 φ) (KT_to_KT4 ψ)); [constructor | easy].
    + apply KT_axiom_to_KT4axiom_sound with (ax9 φ ψ Ɣ) (KT4ax9 (KT_to_KT4 φ) (KT_to_KT4 ψ) (KT_to_KT4 Ɣ)) (f) in H0;
      try constructor.
      apply AxKT4 with (KT4ax9 (KT_to_KT4 φ) (KT_to_KT4 ψ) (KT_to_KT4 Ɣ)); [constructor | easy].
    + apply KT_axiom_to_KT4axiom_sound with (ax10 φ ψ) (KT4ax10 (KT_to_KT4 φ) (KT_to_KT4 ψ)) (f) in H0;
      try constructor.
      apply AxKT4 with (KT4ax10 (KT_to_KT4 φ) (KT_to_KT4 ψ)); [constructor | easy].
    + apply KT_axiom_to_KT4axiom_sound with (axK φ ψ) (KT4axK_T (KT_to_KT4 φ) (KT_to_KT4 ψ)) (f) in H0;
      try constructor.
      apply AxKT4 with (KT4axK_T (KT_to_KT4 φ) (KT_to_KT4 ψ)); [constructor | easy].
    + apply KT_axiom_to_KT4axiom_sound with (axPos φ ψ) (KT4axPos_T (KT_to_KT4 φ) (KT_to_KT4 ψ)) (f) in H0;
      try constructor.
      apply AxKT4 with (KT4axPos_T (KT_to_KT4 φ) (KT_to_KT4 ψ)); [constructor | easy].
    + apply KT_axiom_to_KT4axiom_sound with (axT φ) (KT4axT (KT_to_KT4 φ)) (f) in H0;
      try constructor.
      apply AxKT4 with (KT4axT (KT_to_KT4 φ)); [constructor | easy].
  - (* Modus Ponens *)
    apply MpKT4 with (KT_to_KT4 f); assumption.
  - (* Necessitation (for T)*)
    apply Nec_T with (φ := (KT_to_KT4 f)); assumption.
    (* For some reason, Coq wasn't able to correctly infer the type of φ in the above expression, so it was necessary
    to explicitly state it*)
Qed.

Theorem K4deduction_generalization: forall Γ φ,
  let K4_to_KT4 := K4formula_to_KT4formula in
  deduction K4 Γ φ -> KT4deduction KT4Ax (K4_theory_to_KT4theory Γ) (K4_to_KT4 φ).
Proof.
  intros Γ φ K4_to_KT4 H0;
  dependent induction H0.
  - (* Premise *)
    apply PremKT4 with i;
    apply K4_theory_to_KT4theory_nth_error; assumption.
  - (*Axiom*)
    destruct H as [a H | φ]; [destruct H |].
    (* This applies destruct H on the first subgoal and leaves the second unchanged, this is done
    to avoid 3 levels of bullets*)
    + apply K4_axiom_to_KT4axiom_sound with (ax1 φ ψ) (KT4ax1 (K4_to_KT4 φ) (K4_to_KT4 ψ)) (f) in H0;
      try constructor.
      apply AxKT4 with (KT4ax1 (K4_to_KT4 φ) (K4_to_KT4 ψ)); [constructor | easy].
    + apply K4_axiom_to_KT4axiom_sound with (ax2 φ ψ Ɣ) (KT4ax2 (K4_to_KT4 φ) (K4_to_KT4 ψ) (K4_to_KT4 Ɣ)) (f) in H0;
      try constructor.
      apply AxKT4 with (KT4ax2 (K4_to_KT4 φ) (K4_to_KT4 ψ) (K4_to_KT4 Ɣ)); [constructor | easy].
    + apply K4_axiom_to_KT4axiom_sound with (ax3 φ ψ) (KT4ax3 (K4_to_KT4 φ) (K4_to_KT4 ψ)) (f) in H0;
      try constructor.
      apply AxKT4 with (KT4ax3 (K4_to_KT4 φ) (K4_to_KT4 ψ)); [constructor | easy].
    + apply K4_axiom_to_KT4axiom_sound with (ax4 φ ψ) (KT4ax4 (K4_to_KT4 φ) (K4_to_KT4 ψ)) (f) in H0;
      try constructor.
      apply AxKT4 with (KT4ax4 (K4_to_KT4 φ) (K4_to_KT4 ψ)); [constructor | easy].
    + apply K4_axiom_to_KT4axiom_sound with (ax5 φ ψ) (KT4ax5 (K4_to_KT4 φ) (K4_to_KT4 ψ)) (f) in H0;
      try constructor.
      apply AxKT4 with (KT4ax5 (K4_to_KT4 φ) (K4_to_KT4 ψ)); [constructor | easy].
    + apply K4_axiom_to_KT4axiom_sound with (ax6 φ ψ) (KT4ax6 (K4_to_KT4 φ) (K4_to_KT4 ψ)) (f) in H0;
      try constructor.
      apply AxKT4 with (KT4ax6 (K4_to_KT4 φ) (K4_to_KT4 ψ)); [constructor | easy].
    + apply K4_axiom_to_KT4axiom_sound with (ax7 φ ψ) (KT4ax7 (K4_to_KT4 φ) (K4_to_KT4 ψ)) (f) in H0;
      try constructor.
      apply AxKT4 with (KT4ax7 (K4_to_KT4 φ) (K4_to_KT4 ψ)); [constructor | easy].
    + apply K4_axiom_to_KT4axiom_sound with (ax8 φ ψ) (KT4ax8 (K4_to_KT4 φ) (K4_to_KT4 ψ)) (f) in H0;
      try constructor.
      apply AxKT4 with (KT4ax8 (K4_to_KT4 φ) (K4_to_KT4 ψ)); [constructor | easy].
    + apply K4_axiom_to_KT4axiom_sound with (ax9 φ ψ Ɣ) (KT4ax9 (K4_to_KT4 φ) (K4_to_KT4 ψ) (K4_to_KT4 Ɣ)) (f) in H0;
      try constructor.
      apply AxKT4 with (KT4ax9 (K4_to_KT4 φ) (K4_to_KT4 ψ) (K4_to_KT4 Ɣ)); [constructor | easy].
    + apply K4_axiom_to_KT4axiom_sound with (ax10 φ ψ) (KT4ax10 (K4_to_KT4 φ) (K4_to_KT4 ψ)) (f) in H0;
      try constructor.
      apply AxKT4 with (KT4ax10 (K4_to_KT4 φ) (K4_to_KT4 ψ)); [constructor | easy].
    + apply K4_axiom_to_KT4axiom_sound with (axK φ ψ) (KT4axK_4 (K4_to_KT4 φ) (K4_to_KT4 ψ)) (f) in H0;
      try constructor.
      apply AxKT4 with (KT4axK_4 (K4_to_KT4 φ) (K4_to_KT4 ψ)); [constructor | easy].
    + apply K4_axiom_to_KT4axiom_sound with (axPos φ ψ) (KT4axPos_4 (K4_to_KT4 φ) (K4_to_KT4 ψ)) (f) in H0;
      try constructor.
      apply AxKT4 with (KT4axPos_4 (K4_to_KT4 φ) (K4_to_KT4 ψ)); [constructor | easy].
    + apply K4_axiom_to_KT4axiom_sound with (axK4 φ) (KT4axK4 (K4_to_KT4 φ)) (f) in H0;
      try constructor.
      apply AxKT4 with (KT4axK4 (K4_to_KT4 φ)); [constructor | easy].
  - (* Modus Ponens *)
    apply MpKT4 with (K4_to_KT4 f); assumption.
  - (* Necessitation (for 4)*)
    apply Nec_4 with (φ := (K4_to_KT4 f)); assumption.
    (* For some reason, Coq wasn't able to correctly infer the type of φ in the above expression, so it was necessary
    to explicitly state it*)
Qed.

(*** Transfer of Soundness ***)

(** System KT is Sound **)
Theorem KT_soundness:
  relative_soundness T reflexivity_frame.
Proof.
  intros Γ φ H0 F V H1 H2;
  induction H0. (*Induction on the deduction*)
  - (*Premise*)
    apply exact_deduction with t; try assumption;
    apply nth_error_In with i; assumption.
  - (*Axiom instance*)
    destruct H.
    + apply Ax with (K) (t) (φ) (f) in H; try auto;
      apply soundness in H; auto. (*Other Axioms*)
    + unfold instantiate in H1; subst. (*Axiom T*)
      eapply reflexive_frame_implies_axiomT;
      assumption.
  - (*Modus Ponens*)
    intros w; apply Modus_Ponens_soundness with f; split;
    [apply IHdeduction2 | apply IHdeduction1]; auto.
  - (*Necessitation*)
    intros w; apply Necessitation_soundness;
    apply IHdeduction; assumption.
Qed.

(** System K4 is Sound **)
Theorem K4_soundness:
  relative_soundness K4 transitivity_frame.
Proof.
  intros Γ φ H0 F V H1 H2;
  induction H0. (*Induction on the deduction*)
  - (*Premise*)
    apply exact_deduction with t; try assumption;
    apply nth_error_In with i; assumption.
  - (*Axiom instance*)
    destruct H.
    + apply Ax with (K) (t) (φ) (f) in H; try auto;
      apply soundness in H; auto. (*Other Axioms*)
    + unfold instantiate in H1; subst. (*Axiom 4*)
      eapply transitive_frame_implies_axiom4;
      assumption.
  - (*Modus Ponens*)
    intros w; apply Modus_Ponens_soundness with f; split;
    [apply IHdeduction2 | apply IHdeduction1]; auto.
  - (*Necessitation*)
    intros w; apply Necessitation_soundness;
    apply IHdeduction; assumption.
Qed.

Theorem KT4_soundness:
  relative_KT4soundness KT4Ax anyKT4Frame.
Proof.
  intros Gamma phi H0 FT4 VT4 _.
  assert(HKT: relative_soundness T (fun F => F = KT4_frame_into_KT FT4))
    by (intros ?x ?x ?x F ?x H3; assert (H4: KTFrame F) by (rewrite H3; apply KT4_frame_into_KT_sound);
        eapply KT_soundness in H4; eauto).
  assert(HK4: relative_soundness K4 (fun F => F = KT4_frame_into_K4 FT4))
    by (intros ?x ?x ?x F ?x H4; assert (H5: K4Frame F) by (rewrite H4; apply KT4_frame_into_K4_sound);
        eapply K4_soundness in H5; eauto).
  (* Clean up hypotheses. *)
  unfold relative_soundness in HKT, HK4.
  destruct FT4; simpl in VT4, HKT, HK4.
  (* Proceed by induction. *)
  induction H0.
  - (* Premisses *)
    intros ?H; apply entailment_in_theory with (T); try assumption;
    apply nth_error_In with (i); assumption.
  - (* Axioms instances *)

  (*

    (* ! Trying to prove by means of the assumptions that KT and K4 are sound ! *)

    destruct H.
    + apply KT4_axiom_to_KTaxiom_sound with (b:=ax1 (KT4formula_to_formula φ0) (KT4formula_to_formula ψ)) in H1;
      try constructor. (* Translate axiom instance to KT/K4 *)
      assert(H2: forall Γ, Deductive_System.T; Γ |-- KT4formula_to_formula φ)
        by (intros Γ; rewrite <- H1; apply Ax with (ax1 (KT4formula_to_formula φ0) (KT4formula_to_formula ψ));
            try auto; apply T_K; constructor). (* Show that this instance is derivable in KT/K4 *)
      pose H2 as H3.
      apply HKT with (F:=KT4_frame_into_KT (Build_KT4Frame WT4 RT RT_refl R4 R4_trans)) (Γ:=KT4theory_to_theory T) (V:=VT4) in H3;
      try auto; simpl in H3. (* Show entailment from the soundness of KT/K4*)
      apply KTdeduction_generalization with (Γ:=KT4theory_to_theory T) in H2.
      apply KT_semantic_entail_generalization with (RTR:=RT_refl) (R4R:=R4_trans) in H3.

      (* !! Stuck !! *)
  *)

    do 2 intro; simpl in *.
    dependent destruction H0.
    destruct a; simpl;
    try (firstorder; tauto); (* Proving most cases *)
    intros; apply H0; (* Proving case for axiom 4 *)
    eapply R4_trans; eauto.
  - (* Modus Ponens *)
    intros H1; pose H1 as H2.
    apply IHKT4deduction1 in H2;
    apply IHKT4deduction2 in H1.
    intros w; apply H2; apply H1.
  - (* Necessitation for T *)
    intros H1 w0 w1 H2; simpl in *;
    apply IHKT4deduction in H1; auto.
  - (* Necessitation for 4 *)
    intros H1 w0 w1 H2; simpl in *;
    apply IHKT4deduction in H1; auto.
Qed.
