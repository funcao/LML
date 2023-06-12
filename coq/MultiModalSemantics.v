Require Import Arith List Notations Classical MultiModalCore Modal_Library Modal_Notations.
Export ListNotations.

(**
  Proofs of equivalence between multimodal and monomodal systems

  In this file, we will prove that (for the most cases) formulas that can be derived in the
  monomodal system can too be derived in the multimodal system
**)

(*
  Firstly, semantic evaluation
    If a formula φ is evaluated as X in some world w in a model M based on a multimodal model M',
    then it's translated formula f(φ) is evaluated as X in the same world w in M'
*)

Theorem MMvaluation_generalization: forall modalities W lR RC V φ n,
  let NF := Build_nFrame modalities W lR RC in
  let NM := Build_nModel modalities NF V in
  let M := (nModel_to_Model modalities NM n) in
  deducible_formula modalities (formula_to_MMformula φ n) ->
    forall w, fun_validation M w φ <->
    valuation modalities NM w (formula_to_MMformula φ n).
Proof.
  intros modalities W lR RC V φ n NF NM M H0; simpl in *.
  induction φ; simpl in H0 |-*.
  - (*Lit*)
    intuition.
  - (*Neg*)
    split; intros H1 H2.
    + intros H3; destruct H1.
      apply IHφ with (w) in H2;
      apply H2; assumption.
    + pose H0 as H3;
      simpl in H0, H3; apply H1 in H3.
      destruct H3; apply IHφ;
      assumption.
  - (*Box*)
    split; intros H1.
    + intros [H2 H3] w' H4;
      apply IHφ with (w') in H3.
      rewrite <- H3; apply H1;
      assumption.
    + intros w' H2; pose H0 as H3.
      apply H1 with (w') in H3; try assumption;
      apply IHφ in H3; try assumption;
      destruct H0; assumption.
  - (*Dia*)
    split.
    + intros [w' [H1 H2]] [H3 H4]; exists w';
      split; try assumption.
      apply IHφ; assumption.
    + intros [w' [H1 H2]]; try assumption.
      exists w'; split; try assumption.
      apply IHφ; try assumption; apply H0.
  - (*And*)
    split; intros [H1 H2]; try auto.
    + intros [H3 H4];
      apply IHφ1 in H1; apply IHφ2 in H2; try assumption.
      split; auto.
    + apply IHφ1 in H1; apply IHφ2 in H2; try(split; auto);
      destruct H0; auto.
  - (*Or*)
    split; destruct H0.
    + intros [H1 | H2] [H3 H4];
      [
        apply IHφ1 in H1; try left;  auto |
        apply IHφ2 in H2; try right; auto
      ].
    + intros [H1 | H2]; try auto;
      [
        apply IHφ1 in H1; try left;  auto |
        apply IHφ2 in H2; try right; auto
      ].
  - (*Impl*)
    split; intros H1.
    + intros [H2 H3] H4;
      rewrite <- IHφ2; try auto.
      apply H1; rewrite IHφ1; auto.
    + intros H2; pose H0 as H3;
      destruct H0 as [H0 H0'];
      apply IHφ1 in H2; try assumption.
      apply H1 in H3; try assumption;
      rewrite IHφ2; assumption.
Qed.

(*
  Next, validity in models
    If a formula φ is valid a model M based on a multimodal model M',
    then it's translated formula f(φ) is valid in M'
*)

Theorem MMvalidity_in_model_generalization: forall modalities W lR RC V φ n,
  let NF := Build_nFrame modalities W lR RC in
  let NM := Build_nModel modalities NF V in
  let M := (nModel_to_Model modalities NM n) in
  deducible_formula modalities (formula_to_MMformula φ n) ->
    validate_model M φ <->
    validity_in_model modalities NM (formula_to_MMformula φ n).
Proof.
  intros modalities W lR RC V φ n NF NM M H0; simpl in *.
  unfold validate_model, validity_in_model in *; destruct φ; simpl in H0 |-*.
  - (*Lit*)
    intuition.
  - (*Neg*)
    split; intros H1 w0 H2.
    + intros H3; apply MMvaluation_generalization in H3; simpl in H3;
      try assumption; apply H1 in H3; contradiction.
    + apply MMvaluation_generalization
        with (modalities:=modalities) (RC:=RC) in H2;
      try assumption; destruct H1 with (w0); assumption.
  - (*Box*)
    split; intros H1 w0; try intros; destruct H0;
    apply MMvaluation_generalization
      with (modalities:=modalities) (RC:=RC); try assumption;
    apply H1 with (w0); try split; assumption.
  - (*Dia*)
    split; intros H w0; destruct H with (w0) as [w1 [H1 H2]];
    clear H; try assumption; apply MMvaluation_generalization
      with (modalities:=modalities) (RC:=RC) in H2;
    destruct H0; try assumption; try intros;
    exists w1; split; assumption.
  - (*And*)
    split; intros H w0; destruct H with (w0) as [H1 H2]; clear H; try assumption;
    try intros; split; apply MMvaluation_generalization
      with (modalities:=modalities) (RC:=RC);
    destruct H0; assumption.
  - (*Or*)
    split; intros H w0; try intros; destruct H with (w0);
    try assumption; [left | right | left | right];
    apply MMvaluation_generalization
      with (modalities:=modalities) (RC:=RC);
    destruct H0; assumption.
  - (*Impl*)
    split; intro H1; intros; destruct H0;
    apply MMvaluation_generalization
      with (modalities:=modalities) (RC:=RC); try assumption;
    apply H1; try apply MMvaluation_generalization
      with (modalities:=modalities) (RC:=RC); try split; assumption.
Qed.

(*
  Small auxiliary result, validity of theories in models
    If a theory Γ is valid a model M based on a multimodal model M',
    then it's translated theory f(Γ) is valid in M'
*)

Lemma MMtheory_valid_generalization: forall modalities W lR RC V Γ n,
  let NF := Build_nFrame modalities W lR RC in
  let NM := Build_nModel modalities NF V in
  let M := (nModel_to_Model modalities NM n) in
  deducible_theory modalities (theory_to_MMtheory Γ n) ->
    theoryModal M Γ <->
    theory_is_valid modalities NM (theory_to_MMtheory Γ n).
Proof.
  intros modalities W lR RC V Γ n NF NM M H0; simpl in *.
  induction Γ as [ | φ Γ IHΓ]; split; repeat firstorder;
  intros [H H']; split; try apply MMvalidity_in_model_generalization
    with (modalities:=modalities) (RC:=RC);
  destruct H0; try apply IHΓ; assumption.
Qed.

(*
  Next, entailment in a model
    If a formula φ is entailed by theory Γ in a model M based on a multimodal model M',
    then it's translated formula f(φ) is entailed by the translated theory f(Γ) in M'
*)

Theorem MMentailment_generalization: forall modalities W lR RC V φ Γ n,
  let NF := Build_nFrame modalities W lR RC in
  let NM := Build_nModel modalities NF V in
  let M := (nModel_to_Model modalities NM n) in
  deducible_formula modalities (formula_to_MMformula φ n) ->
  deducible_theory modalities (theory_to_MMtheory Γ n) ->
    entails M Γ φ <->
    entailment modalities NM (theory_to_MMtheory Γ n) (formula_to_MMformula φ n).
Proof.
  intros modalities W lR RC V φ Γ n NF NM M H0 H1; simpl in *.
  unfold entails, entailment in *; destruct φ; simpl in H0 |-*;
  split; intros H2 H3; repeat
  ( (*Solves the left to right side*)
    intros H4; apply MMtheory_valid_generalization in H4; simpl in H4;
    try assumption; apply H2 in H4; apply MMvalidity_in_model_generalization
      with (modalities:=modalities) (RC:=RC) in H4; simpl in H4;
    assumption
  ); repeat
  ( (*Solves the right to left side*)
    apply MMvalidity_in_model_generalization
      with (modalities:=modalities) (RC:=RC);
    try apply H2; try apply MMtheory_valid_generalization; assumption
  ).
Qed.

(*
  Finally, entailment in all models
    If a formula φ is entailed by theory Γ in all models M based on multimodal models M',
    then it's translated formula f(φ) is entailed by the translated theory f(Γ) in all M'
*)

Theorem MMsemantic_entailment_generalization: forall modalities Γ φ n,
    entails_modal Γ φ -> semantic_entailment modalities (theory_to_MMtheory Γ n) (formula_to_MMformula φ n).
Proof.
  intros modalities Γ φ n H0;
  generalize dependent Γ; destruct φ; intros Γ H0 M H1 H2 w0; simpl;

  (*
    To carry out the proof, we must first show Coq that the two types of models can
    be transformed into one another, similarly to what was done in the previous proofs
    with all the let ... in statements
  *)
  unfold entails_modal in H0; unfold validate_model in H0;
  specialize (H0 (nModel_to_Model modalities M n));
  assert (H': theoryModal (nModel_to_Model modalities M n) Γ) by
  (
    destruct M as ((W, lR, RC), V); simpl in *;
    eapply MMtheory_valid_generalization; eauto
  );
  specialize (H0 H'); clear H';
  destruct M as ((W, lR, RC), V); simpl in *.

  - (*Lit*)
    auto.
  - (*Neg*)
    intros H3 H4. destruct H0 with (w0); apply MMvaluation_generalization
      with (modalities:=modalities) (RC:=RC);
    assumption.
  - (*Box*)
    intros [H3 H4] w1 H5. apply MMvaluation_generalization
      with (modalities:=modalities) (RC:=RC);
    try apply H0 with (w0); assumption.
  - (*Dia*)
    intros [H4 H5]. destruct H0 with (w0) as [w1 [H' H3]]; clear H0; rename H' into H0;
    exists w1; split; try apply MMvaluation_generalization
      with (modalities:=modalities) (RC:=RC);
    assumption.
  - (*And*)
    intros [H5 H6]. destruct H0 with (w0) as [H3 H4]; split;
    apply MMvaluation_generalization
      with (modalities:=modalities) (RC:=RC);
    assumption.
  - (*Or*)
    intros [H4 H5]. destruct H0 with (w0) as [H3 | H3]; [left | right ];
    apply MMvaluation_generalization
      with (modalities:=modalities) (RC:=RC);
    assumption.
  - (*Impl*)
    intros [H5 H6] H3. apply MMvaluation_generalization
      with (modalities:=modalities) (RC:=RC);
    apply MMvaluation_generalization
      with (modalities:=modalities) (RC:=RC) in H3;
    try apply H0; assumption.
Qed.

(*
  Now, we show some properties of semantic entailment
*)

(*
  If a formula is in a theory, then it is entailed by that theory
*)
Theorem semantic_entailment_in_theory: forall modalities Γ φ,
  In φ Γ -> semantic_entailment modalities Γ φ.
Proof.
  intros modalities Γ φ H0; induction Γ.
  - inversion H0.
  - destruct H0 as [H0 | H0];
    unfold semantic_entailment in *;
    intros ? [? ?] [? ?]; [subst; assumption |].
    eapply IHΓ in H0; unfold entailment in H0 |-*;
    apply H0; auto.
Qed.

(*
  If the union (concatenation) of two theories is valid, then each theory is valid too
*)
Lemma theory_union_valid: forall modalities M Γ1 Γ2,
  theory_is_valid modalities M (Γ1 ++ Γ2) ->
    theory_is_valid modalities M Γ1 /\ theory_is_valid modalities M Γ2.
Proof.
  intros modalities M Γ1 Γ2; induction Γ1;
  simpl; try eauto.
  intros [H0 H1]; repeat (split; auto);
  apply IHΓ1; assumption.
Qed.

(*
  If a theory, which contains a formula φ, derives ψ and another theory, which contains ψ,
  derives Ɣ, then the union of both theories, containing φ, derives Ɣ
*)
Theorem entailment_transitive: forall modalities M Γ1 Γ2 φ ψ Ɣ,
  (deducible_formula modalities ψ) -> (deducible_formula modalities Ɣ) ->
  (entailment modalities M (φ :: Γ1) ψ) /\ (entailment modalities M (ψ :: Γ2) Ɣ) ->
  entailment modalities M (φ :: (Γ1 ++ Γ2)) Ɣ.
Proof.
  intros modalities M Γ1 Γ2 φ ψ Ɣ H H' [H0 H1] [H2 H3] [H4 H5];
  unfold entailment in *; simpl in *.
  apply theory_union_valid in H5; destruct H5 as [H5 H6].
  apply H1; split; try assumption; apply deducible_theory_union in H3;
  destruct H3 as [H3 H7]; try assumption;
  apply H0; repeat split; auto.
Qed.

(*
  The order of formulas in a theory does not matter for entailment
*)
Theorem entailment_exchange: forall modalities M Γ φ ψ Ɣ,
  entailment modalities M (φ :: ψ :: Γ) Ɣ ->
  entailment modalities M (ψ :: φ :: Γ) Ɣ.
Proof.
  intros modalities M Γ φ ψ Ɣ H0 [H1 [H2 H3]] [H4 [H5 H6]];
  unfold entailment in *; simpl in *; apply H0; auto.
Qed.

(*
  If two theories are transpose (contain the same terms in not necessarily the same order)
  then they both entail the same things
*)
Theorem entailment_transposition: forall modalities M Γ1 Γ2 φ,
  transpose Γ1 Γ2 ->
    (entailment modalities M Γ1 φ) <-> (entailment modalities M Γ2 φ).
Proof.
  intros modalities M Γ1 Γ2 φ H0; induction H0; try easy.
  - split; intros; apply entailment_exchange; assumption.
  - split; unfold entailment in *; intros H1 [H2 H2'] [H3 H4];
    edestruct IHtranspose as [IH1 IH2]; clear IHtranspose; [apply IH1 | apply IH2];
    try assumption; intros; apply H1; simpl; try split; assumption.
  - split; intros;
    [
      apply IHtranspose2; apply IHtranspose1 |
      apply IHtranspose1; apply IHtranspose2
    ]; assumption.
Qed.

(*
  Repetitions of formulas does not affect entailment
*)
Theorem entailment_idempotence: forall modalities M Γ φ ψ,
  entailment modalities M (φ :: φ :: Γ) ψ <->
  entailment modalities M (φ :: Γ) ψ.
Proof.
  intros modalities M Γ φ ψ; unfold entailment; split;
  simpl; intros H0 [H1 H2] [H3 H4]; try destruct H2, H4; apply H0;
  repeat split; auto.
Qed.

(*
  If a theory entails some formula, then adding more formulas to this theory
  preserves the entailment
*)
Theorem entailment_monotone: forall modalities M Γ1 Γ2 φ,
  entailment modalities M Γ1 φ ->
  entailment modalities M (Γ1 ++ Γ2) φ.
Proof.
  intros modalities M Γ1 Γ2 φ H0 H1 H2.
  apply H0; apply theory_union_valid in H2; apply deducible_theory_union in H1;
  intuition.
Qed.