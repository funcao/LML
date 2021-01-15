Require Import Modal_Library Classical List Deductive_System.

(* p -> (q -> p) *)
Lemma Hilbert_Axiom_1_soundness:
  forall M w phi psi,
  M; w ||- [! phi -> (psi -> phi) !].
Proof.
  simpl; intros.
  assumption.
Qed.

(* (p -> (q -> r)) -> ((p -> q) -> (p -> r)) *)
Lemma Hilbert_Axiom_2_soundness:
  forall M w phi psi gamma,
  M; w ||- [! (phi -> (psi -> gamma)) -> ((phi -> psi) -> (phi -> gamma)) !].
Proof.
  simpl; intros.
  apply H.
  - auto.
  - apply H0; auto.
Qed.

(* (~ q -> ~ p) -> (p -> q) *)
Lemma Hilbert_Axiom_3_soundness:
  forall M w phi psi,
  M; w ||- [! (~ psi -> ~ phi) -> (phi -> psi) !].
Proof.
  simpl; intros.
  pose (classic (M; w ||- [! psi !])) as Hip.
  destruct Hip.
  - auto.
  - apply H in H1.
    contradiction.
Qed.

(* p -> (q -> (p /\ q)) *)
Lemma Hilbert_Axiom_4_soundness: 
  forall M w phi psi,
  M; w ||- [! phi -> (psi -> (phi /\ psi)) !].
Proof.
  simpl; intros.
  split; auto.
Qed.

(* (p /\ q) -> p *)
Lemma Hilbert_Axiom_5_soundness: 
  forall M w phi psi,
  M; w ||- [! (phi /\ psi) -> phi !].
Proof.
  simpl; intros.
  destruct H as [Hip1 Hip2].
  assumption.
Qed.

(* (p /\ q) -> q *)
Lemma Hilbert_Axiom_6_soundness: 
  forall M w phi psi,
  M; w ||- [! (phi /\ psi) -> psi !].
Proof.
  simpl; intros.
  destruct H as [Hip1 Hip2].
  assumption.
Qed.

(* p -> (p \/ q) *)
Lemma Hilbert_Axiom_7_soundness: 
  forall M w phi psi,
  M; w ||- [! (phi -> (phi \/ psi)) !].
Proof.
  simpl; intros.
  left.
  assumption.
Qed.

(* q -> (p \/ q) *)
Lemma Hilbert_Axiom_8_soundness: 
  forall M w phi psi,
  M; w ||- [! (psi -> (phi \/ psi)) !].
Proof.
  simpl; intros.
  right.
  assumption.
Qed.

(* (p -> r) -> (q -> r) -> (p \/ q) -> r *)
Lemma Hilbert_Axiom_9_soundness: 
  forall M w phi psi gamma,
  M; w ||- [! (phi -> gamma) -> (psi -> gamma) -> (phi \/ psi) -> gamma !].
Proof.
  simpl; intros.
  destruct H1.
  - apply H.
    assumption.
  - apply H0.
    assumption.
Qed.

(* ~~p -> p *)
Lemma Hilbert_Axiom_10_soundness: 
  forall M w phi,
  M; w ||- [! ~~phi -> phi !].
Proof.
  simpl; intros.
  apply NNPP in H.
  assumption.
Qed.

(* <>(p \/ q) -> (<>p \/ <>q) *)
Lemma Axiom_Possibility_soundness:
  forall M w phi psi,
  M; w ||- [! <> (phi \/ psi) -> (<> phi \/ <> psi) !].
Proof.
  simpl; intros.
  destruct H as [ w' [ Hip1 [ Hip2 | Hip3 ] ]].
  - left; exists w'; split.
    + assumption.
    + assumption.
  - right; exists w'; split.
    + assumption.
    + assumption.
Qed.

(* [](p -> q) -> ([]p -> []q) *)
Lemma Axiom_K_soundness:
  forall M w phi psi,
  M; w ||- [! [](phi -> psi) -> ([]phi -> []psi) !].
Proof.
  simpl; intros.
  apply H.
  - assumption.
  - apply H0.
    assumption.
Qed.

(* phi ∈ Delta -> Delta ||= phi  *)
Lemma case_two :
  forall Delta phi,
  In phi Delta -> 
  Delta |= [! phi !].
Proof.
  unfold theory_valid_in_frame, valid_in_model; intros.
  apply entailment_valid_in_model with Delta.
  - assumption.
  - assumption.
Qed.

(* a /\ (a -> b) -> b *)
Lemma Modus_Ponens_soundness:
  forall M w phi psi,
  ((M; w ||- [! phi !]) /\ 
   (M; w ||- [! phi -> psi !])) -> 
   (M; w ||- [! psi !]).
Proof.
  simpl; intros.
  destruct H.
  apply H0; auto.
Qed.

Lemma Necessitation_soundness:
  forall M phi,
  (M ||= [! phi !]) -> 
  (M ||= [! []phi !]).
Proof.
  unfold valid_in_model; simpl; intros.
  apply H.
Qed.

Theorem soundness:
  forall (G: theory) (phi: modalFormula),
  (K; G |-- [! phi !]) -> 
  (G |= [! phi !]).
Proof.
  induction 1.
  - intros M ?H.
    apply entailment_valid_in_model with t.
    + apply nth_error_In with i.
      assumption.
    + assumption.
  - destruct H; destruct H0; simpl.
    + intros M ?H w.
      apply Hilbert_Axiom_1_soundness.
    + intros M ?H w.
      apply Hilbert_Axiom_2_soundness.
    + intros M ?H w.
      apply Hilbert_Axiom_3_soundness.
    + intros M ?H w.
      apply Hilbert_Axiom_4_soundness.
    + intros M ?H w.
      apply Hilbert_Axiom_5_soundness.
    + intros M ?H w.
      apply Hilbert_Axiom_6_soundness.
    + intros M ?H w.
      apply Hilbert_Axiom_7_soundness.
    + intros M ?H w.
      apply Hilbert_Axiom_8_soundness.
    + intros M ?H w.
      apply Hilbert_Axiom_9_soundness.
    + intros M ?H w.
      apply Hilbert_Axiom_10_soundness.
    + intros M ?H w.
      apply Axiom_K_soundness.
    + intros M ?H w.
      apply Axiom_Possibility_soundness.
  - intros M ?H w.
    apply Modus_Ponens_soundness with f.
    split.
    + apply IHdeduction2.
      assumption.
    + apply IHdeduction1.
      assumption.
  - intros M ?H w.
    apply Necessitation_soundness.
    apply IHdeduction.
    assumption.
Qed.

Corollary soundness2:
  forall M G w phi, 
  theory_valid_in_model M G -> 
  (K; G |-- [! phi !]) -> M; w ||- [! phi !].
Proof.
  intros.
  eapply soundness.
  - eassumption.
  - assumption.
Qed.