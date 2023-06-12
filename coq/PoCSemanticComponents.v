Require Import Arith List Notations Classical Modal_Library Modal_Notations PoCBasicComponents.
Export ListNotations.

(**
  TODO: Improve comments
**)

(*** Proofs of KT4 Semantic Properties ***)

(* If a formula φ is in a theory T, then the T entails φ*)
Theorem entailment_in_theory: forall T φ,
  In φ T -> forall M, KT4entails M T φ.
Proof.
  intros T φ H0 M.
  induction T.
  - inversion H0.
  - simpl in H0. 
    destruct H0 as [H0 | H0].
    + subst; unfold KT4entails; intros H1.
      destruct H1; assumption.
    + unfold KT4entails in *; intros [H1 H2].
      apply IHT; auto.
Qed.

(* Auxiliary Lemma: If the union of two theories T1 and T2, is satisfiable, then each theory is too*)
Lemma theory_union_satisfiable: forall M T1 T2,
  theorySatisfiable M (T1 ++ T2) -> 
  theorySatisfiable M T1 /\ theorySatisfiable M T2.
Proof.
  intros.
  induction T1; simpl; try eauto.
  destruct H as [H0 H1].
  repeat (split; auto);
  apply IHT1; assumption.
Qed.

(* Semantic Entailment is Transitive - TODO: Improve this to a more generic version, remove ψ from T2*)
Theorem entailment_transitive: forall M T1 T2 φ ψ Ɣ,
  KT4entails M (φ :: T1) ψ /\ KT4entails M (ψ :: T2) Ɣ ->
  KT4entails M (φ :: (T1 ++ T2)) Ɣ.
Proof.
  unfold KT4entails in *; simpl in *.
  intros M T1 T2 φ ψ Ɣ [H0 H1].
  unfold KT4entails in *; simpl in *.
  intros [H2 H3]; apply theory_union_satisfiable in H3; destruct H3 as [H3 H4].
  apply H1; split; auto.
Qed.

(* Semantic Entailment respects exchange of terms, i.e., the order of elements in an entailment does not matter *)
Theorem entailment_exchange: forall M T1 φ ψ Ɣ,
  KT4entails M (φ :: ψ :: T1) Ɣ ->
  KT4entails M (ψ :: φ :: T1) Ɣ.
Proof.
  unfold KT4entails in *; simpl in *.
  intros M T1 φ ψ Ɣ H0 [H1 [H2 H3]].
  apply H0; auto.
Qed.

(* If two theories are transposes (i.e. contain the same terms in not necessarily the same order) 
then they both entail the same things *)
Theorem entailment_transposition: forall M T1 T2 φ,
  transpose T1 T2 -> 
  KT4entails M T1 φ <-> KT4entails M T2 φ.
Proof.
  intros M T1 T2 φ H0; induction H0; try easy.
  - split; intros H0; simpl in *; apply entailment_exchange; assumption.
  - split; unfold KT4entails in *; intros H3 H4; destruct H4 as [H4 H5];
    edestruct IHtranspose as [H1 H2]; [apply H1 | apply H2]; 
    intros; try (auto; apply H3; split; auto).
  - split; intros;
    [
      apply IHtranspose2; apply IHtranspose1 |
      apply IHtranspose1; apply IHtranspose2 
    ]; assumption.
Qed.

(* Repetitions of formulas in theories does not affect entailment *)
Theorem entailment_idempotence: forall M T φ ψ,
  KT4entails M (φ :: φ :: T) ψ <->
  KT4entails M (φ :: T) ψ.
Proof.
  intros M T φ ψ; split; unfold KT4entails in *; simpl in *; intros H0 [H1 H2];
  apply H0; try (auto); split; auto.
Qed.

(* If a theory entails a formula, then adding more formulas to that theory does not affect entailment *)
Theorem entailment_monotone: forall M T1 T2 φ,
  KT4entails M T1 φ ->
  KT4entails M (T1 ++ T2) φ.
Proof.
  intros M T1 T2 φ H0 H1.
  apply H0; apply theory_union_satisfiable in H1; intuition.
Qed.

(*** Proofs of Equivalence Between KT4 and KT/K4 semantics ***)

(*
  We must show that evaluating a formula in a KT/K4 model is the same as evaluating the
  corresponding KT4formula in the corresponding KT4 model

  First, proving for KT

  Coq can't check wether two records are built the same, so we must explicitly tell it how to build
  both of them to convince the type checker that they're built the same way ...
*)
Theorem KT_eval_generalization: forall W RT RTR R4 R4R V φ,
  let FT4 := Build_KT4Frame W RT RTR R4 R4R in
  let MT4 := Build_KT4Model FT4 V in
  let M := KT4_model_into_KT MT4 in
  forall w, fun_validation M w φ <-> 
  KT4eval MT4 w (KTformula_to_KT4formula φ).
Proof. (*...which leads to some rather ugly proofs and proof terms*)
  intros W RT RT_refl R4 R4_trans V φ FT4 MT4 M w; simpl in *.
  generalize dependent w.
  induction φ; simpl; intros.
  - (*Lit*) split; trivial.
  - (*Neg*)
    split; intros;
    intros H0;
    destruct H;
    apply IHφ; assumption.
  - (*Box*)
    split; intros;
    apply H in H0;
    apply IHφ in H0;
    assumption.
  - (*Dia*) 
    split; intros [w' [H0 H1]];
    apply IHφ in H1;
    exists w'; split; assumption.
  - (*And*) 
    split; intros [H0 H1];
    apply IHφ1 in H0;
    apply IHφ2 in H1;
    split; assumption.
  - (*Or*) 
    split; intros [H0 | H1];
    [
      left;  apply IHφ1 in H0 |
      right; apply IHφ2 in H1 |
      left;  apply IHφ1 in H0 |
      right; apply IHφ2 in H1
    ]; assumption.
  - (*Implies*) 
    split; intros H0 H1;
    apply IHφ2;
    apply H0;
    apply IHφ1 in H1;
    assumption.
Qed.

(* Next, proving for K4 *)
Theorem K4_eval_generalization: forall W RT RTR R4 R4R V φ,
  let FT4 := Build_KT4Frame W RT RTR R4 R4R in
  let MT4 := Build_KT4Model FT4 V in
  let M := KT4_model_into_K4 MT4 in
  forall w, fun_validation M w φ <-> 
  KT4eval MT4 w (K4formula_to_KT4formula φ).
Proof.
  intros W RT RT_refl R4 R4_trans V φ FT4 MT4 M w; simpl in *.
  generalize dependent w.
  induction φ; simpl; intros.
  - (*Lit*) split; trivial.
  - (*Neg*)
    split; intros;
    intros H0;
    destruct H;
    apply IHφ; assumption.
  - (*Box*)
    split; intros;
    apply IHφ;
    apply H;
    apply H0.
  - (*Dia*) 
    split; intros [w' [H0 H1]];
    apply IHφ in H1;
    exists w'; split; assumption.
  - (*And*) 
    split; intros [H0 H1];
    apply IHφ1 in H0;
    apply IHφ2 in H1;
    split; assumption.
  - (*Or*) 
    split; intros [H0 | H1];
    [
      left;  apply IHφ1 in H0 |
      right; apply IHφ2 in H1 |
      left;  apply IHφ1 in H0 |
      right; apply IHφ2 in H1
    ]; assumption.
  - (*Implies*)
    split; intros H0 H1;
    apply IHφ2;
    apply H0;
    apply IHφ1 in H1;
    assumption.
Qed.

(** Proving that Model Satisfiability in KT4 is a generalization of Model Satisfiability in KT/K4 **)

(* First for KT *)
Theorem KT_model_validity_generalization: forall W RT RTR R4 R4R V φ, 
  let FT4 := Build_KT4Frame W RT RTR R4 R4R in
  let MT4 := Build_KT4Model FT4 V in
  let M := KT4_model_into_KT MT4 in
  validate_model M φ <-> 
  model_validity MT4 (KTformula_to_KT4formula φ).
Proof.
  intros W RT RT_refl R4 R4_trans V φ FT4 MT4 M; simpl in *.
  destruct φ; intros; unfold validate_model in *;
  unfold model_validity in *; simpl in *.
  - (*Lit*) split; trivial.
  - (*Neg*) 
    split; intros H0;
    apply not_ex_all_not; intros H1;
    apply all_not_not_ex in H0;
    destruct H1 as [w H1];
    destruct H0; exists w;
    eapply KT_eval_generalization;
    eassumption.
  - (*Box*)
    split; intros H0 w w' H1;
    eapply KT_eval_generalization;
    eapply H0; exact H1.
  - (*Dia*)
    split; intros H0 w; unfold reflexive_rel in RT_refl;
    destruct H0 with w as [w' [H2 H3]];
    exists w'; split; try eapply KT_eval_generalization; eassumption.
  - (*And*)
    split; intros H0 w; destruct H0 with w as [H1 H2];
    split; eapply KT_eval_generalization; eassumption.
  - (*Or*)
    split; intros H0 w; destruct H0 with w as [H1 | H1];
    [left | right | left | right]; eapply KT_eval_generalization; eassumption.
  - (*Implies*)
    split; intros H0 w H1;
    eapply KT_eval_generalization in H1;
    eapply KT_eval_generalization;
    eapply H0;
    eassumption.
Qed.

(* Then for K4 *)
Theorem K4_model_validity_generalization: forall W RT RTR R4 R4R V φ, 
  let FT4 := Build_KT4Frame W RT RTR R4 R4R in
  let MT4 := Build_KT4Model FT4 V in
  let M := KT4_model_into_K4 MT4 in
  validate_model M φ <-> 
  model_validity MT4 (K4formula_to_KT4formula φ).
Proof.
  intros W RT RT_refl R4 R4_trans V φ FT4 MT4 M; simpl in *.
  destruct φ; intros; unfold validate_model in *;
  unfold model_validity in *; simpl in *.
  - (*Lit*) split; trivial.
  - (*Neg*) 
    split; intros H0;
    apply not_ex_all_not; intros H1;
    apply all_not_not_ex in H0;
    destruct H1 as [w H1];
    destruct H0; exists w;
    eapply K4_eval_generalization;
    eassumption.
  - (*Box*)
    split; intros H0 w w' H1;
    eapply K4_eval_generalization;
    eapply H0; exact H1.
  - (*Dia*)
    split; intros H0 w; unfold reflexive_rel in RT_refl;
    destruct H0 with w as [w' [H2 H3]];
    exists w'; split; try eapply K4_eval_generalization; eassumption.
  - (*And*)
    split; intros H0 w; destruct H0 with w as [H1 H2];
    split; eapply K4_eval_generalization; eassumption.
  - (*Or*)
    split; intros H0 w; destruct H0 with w as [H1 | H1];
    [left | right | left | right]; eapply K4_eval_generalization; eassumption.
  - (*Implies*)
    split; intros H0 w H1;
    eapply K4_eval_generalization in H1;
    eapply K4_eval_generalization;
    eapply H0;
    eassumption.
Qed.

(*
  To prove that semantic entailment in KT4 is a generalization of semantic entailment in KT/K4
  we must first show that, if a theory is valid in KT/K4, then it's translation is valid in KT4
*)

(* First for KT *)
Lemma KT_theory_validity_generalization: forall W RT RTR R4 R4R V T, 
  let FT4 := Build_KT4Frame W RT RTR R4 R4R in
  let MT4 := Build_KT4Model FT4 V in
  let M := KT4_model_into_KT MT4 in
  theoryModal M T <-> theorySatisfiable MT4 (KT_theory_to_KT4theory T).
Proof.
  intros W RT RT_refl R4 R4_trans V T FT4 MT4 M; simpl in *.
  induction T as [ | φ T IHT]; split; intros; try easy; 
  destruct H as [H0 H1]; split; try (apply IHT; assumption);
  eapply KT_model_validity_generalization;
  eapply H0.
Qed.

(* Then for K4 *)
Lemma K4_theory_validity_generalization: forall W RT RTR R4 R4R V T, 
  let FT4 := Build_KT4Frame W RT RTR R4 R4R in
  let MT4 := Build_KT4Model FT4 V in
  let M := KT4_model_into_K4 MT4 in
  theoryModal M T <-> theorySatisfiable MT4 (K4_theory_to_KT4theory T).
Proof.
  intros W RT RT_refl R4 R4_trans V T FT4 MT4 M; simpl in *.
  induction T as [ | φ T IHT]; split; intros; try easy; 
  destruct H as [H0 H1]; split; try (apply IHT; assumption);
  eapply K4_model_validity_generalization;
  eapply H0.
Qed.

(*
  Now we may prove that semantic entailment in KT4 is a generalization of semantic entailment in KT/K4
*)

(* First for KT *)
Theorem KT_semantic_entail_generalization: forall W RT RTR R4 R4R V T φ, 
  let FT4 := Build_KT4Frame W RT RTR R4 R4R in
  let MT4 := Build_KT4Model FT4 V in
  let M := KT4_model_into_KT MT4 in
  entails M T φ <-> 
  KT4entails MT4 (KT_theory_to_KT4theory T) (KTformula_to_KT4formula φ).
Proof.
  intros W RT RT_refl R4 R4_trans V T φ FT4 MT4 M; simpl in *.
  destruct φ; intros; unfold entails in *; unfold KT4entails in *;
  unfold validate_model in *; unfold model_validity in *;
  simpl in *.
  - (*Lit*) 
    split; intros H0 H1;
    apply H0;
    eapply KT_theory_validity_generalization;
    eapply H1.
  - (* Neg *)
    split; intros H0 H1 w H2;
    eapply KT_eval_generalization in H2; simpl in H2;
    destruct H0 with w; try eassumption;
    eapply KT_theory_validity_generalization; eapply H1.
  - (* Box *)
    split; intros H0 H1 w0 w1 H2;
    eapply KT_eval_generalization; simpl;
    eapply KT_theory_validity_generalization in H1; simpl in H1;
    eapply H0 with w0; eassumption.
  - (* Dia *)
    split; intros H0 H1 w;
    edestruct H0; 
    eapply KT_theory_validity_generalization in H1; simpl in H1; try eassumption;
    destruct H as [H2 H3]; exists x; split; try eassumption;
    eapply KT_eval_generalization; eassumption.
  - (* And *)
    split; intros H0 H1 w;
    destruct H0 with w; try (eapply KT_theory_validity_generalization; eassumption);
    split; repeat (eapply KT_eval_generalization; eassumption).
  - (* Or *)
    split; intros H0 H1 w;
    destruct H0 with w; try (eapply KT_theory_validity_generalization; eassumption);
    [left | right | left | right]; eapply KT_eval_generalization; eassumption.
  - (* Implies *)
    split; intros H0 H1 w H2;
    eapply KT_eval_generalization; simpl;
    apply H0; try (eapply KT_theory_validity_generalization; eassumption);
    eapply KT_eval_generalization; eassumption.
    Unshelve. assumption. assumption. assumption. 
    (* Something gets shelved on this proof, this final step solves that*)
Qed.

(* Then for K4 *)
Theorem K4_semantic_entail_generalization: forall W RT RTR R4 R4R V T φ, 
  let FT4 := Build_KT4Frame W RT RTR R4 R4R in
  let MT4 := Build_KT4Model FT4 V in
  let M := KT4_model_into_K4 MT4 in
  entails M T φ <-> 
  KT4entails MT4 (K4_theory_to_KT4theory T) (K4formula_to_KT4formula φ).
Proof.
  intros W RT RT_refl R4 R4_trans V T φ FT4 MT4 M; simpl in *.
  destruct φ; intros; unfold entails in *; unfold KT4entails in *;
  unfold validate_model in *; unfold model_validity in *;
  simpl in *.
  - (*Lit*) 
    split; intros H0 H1;
    apply H0;
    eapply K4_theory_validity_generalization;
    eapply H1.
  - (* Neg *)
    split; intros H0 H1 w H2;
    eapply K4_eval_generalization in H2; simpl in H2;
    destruct H0 with w; try eassumption;
    eapply K4_theory_validity_generalization; eapply H1.
  - (* Box *)
    split; intros H0 H1 w0 w1 H2;
    eapply K4_eval_generalization; simpl;
    eapply K4_theory_validity_generalization in H1; simpl in H1;
    eapply H0 with w0; eassumption.
  - (* Dia *)
    split; intros H0 H1 w;
    edestruct H0; 
    eapply K4_theory_validity_generalization in H1; simpl in H1; try eassumption;
    destruct H as [H2 H3]; exists x; split; try eassumption;
    eapply K4_eval_generalization; eassumption.
  - (* And *)
    split; intros H0 H1 w;
    destruct H0 with w; try (eapply K4_theory_validity_generalization; eassumption);
    split; repeat (eapply K4_eval_generalization; eassumption).
  - (* Or *)
    split; intros H0 H1 w;
    destruct H0 with w; try (eapply K4_theory_validity_generalization; eassumption);
    [left | right | left | right]; eapply K4_eval_generalization; eassumption.
  - (* Implies *)
    split; intros H0 H1 w H2;
    eapply K4_eval_generalization; simpl;
    apply H0; try (eapply K4_theory_validity_generalization; eassumption);
    eapply K4_eval_generalization; eassumption.
    Unshelve. exact RT. assumption. assumption. 
    (* Something gets shelved on this proof, this final step solves that*)
Qed.

(* Proving that Validity in KT4 is a generalization of Validity in KT/K4 *)

(* First for KT *)
Theorem KT_validity_generalization: forall Γ φ, 
  entails_modal Γ φ -> KT4validity (KT_theory_to_KT4theory Γ) (KTformula_to_KT4formula φ).
Proof.
  intros.
  generalize dependent Γ.
  destruct φ; simpl; intros;
  (* 
    These following steps are necessary to convince Coq that the we can convert models from the
    core library into KT4 models, doing that, the rest of the proof is not dificult
  *)
  intros M H0 w; simpl;
  unfold entails_modal in H;
  unfold validate_model in H;
  specialize (H (KT4_model_into_KT M));
  assert (theoryModal (KT4_model_into_KT M) Γ) by
  ( 
    destruct M as ((WT4, RT, RT_refl, R4, R4_trans), VT4); simpl in *;
    eapply KT_theory_validity_generalization with
      (RT := RT) (RTR := RT_refl) (R4 := R4) (R4R := R4_trans); easy
  );
  specialize (H H1); clear H0 H1;
  destruct M as ((WT4, RT, RT_refl, R4, R4_trans), VT4); simpl in *.
  (* Now for the proof itself *)
  - apply H.
  - intros H1; apply KT_eval_generalization in H1;
    apply H in H1; contradiction.
  - intros; apply H in H0; 
    apply KT_eval_generalization; assumption.
  - destruct H with w as [w' [H0 H1]];
    exists w'; split; try apply KT_eval_generalization; assumption.
  - destruct H with w as [H0 H1]; split; 
    apply KT_eval_generalization; assumption.
  - destruct H with w as [H0 | H1]; 
    [left | right]; 
    apply KT_eval_generalization; assumption.
  - intros H0; apply KT_eval_generalization in H0; 
    apply H in H0; 
    apply KT_eval_generalization; assumption.
Qed.

(* Then for K4 *)
Theorem K4_validity_generalization: forall Γ φ, 
  entails_modal Γ φ -> KT4validity (K4_theory_to_KT4theory Γ) (K4formula_to_KT4formula φ).
Proof.
  intros.
  generalize dependent Γ.
  induction φ; simpl; intros;
  (* 
    These following steps are necessary to convince Coq that the we can convert models from the
    core library into KT4 models, doing that, the rest of the proof is not dificult
  *)
  intros M H0 w; simpl;
  unfold entails_modal in H;
  unfold validate_model in H;
  specialize (H (KT4_model_into_K4 M));
  assert (theoryModal (KT4_model_into_K4 M) Γ) by
  ( 
    destruct M as ((WT4, RT, RT_refl, R4, R4_trans), VT4); simpl in *;
    eapply K4_theory_validity_generalization with
      (RT := RT) (RTR := RT_refl) (R4 := R4) (R4R := R4_trans); easy
  );
  specialize (H H1); clear H0 H1;
  destruct M as ((WT4, RT, RT_refl, R4, R4_trans), VT4); simpl in *.
  
  (* Now for the proof itself *)
  - apply H.
  - intros H0; apply K4_eval_generalization in H0;
    apply H in H0; contradiction.
  - intros; apply H in H0; 
    apply K4_eval_generalization; assumption.
  - destruct H with w as [w' [H0 H1]];
    exists w'; split; try apply K4_eval_generalization; assumption.
  - destruct H with w as [H0 H1]; split; 
    apply K4_eval_generalization; assumption.
  - destruct H with w as [H0 | H1]; 
    [left | right]; 
    apply K4_eval_generalization; assumption.
  - intros H0; apply K4_eval_generalization in H0; 
    apply H in H0; 
    apply K4_eval_generalization; assumption.
Qed.
