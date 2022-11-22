Require Import Modal_Library Modal_Notations Classical List Deductive_System.

(** Soundness of system K **)

(*
  In what follows, there are proofs that all Hilbert axioms are true in system K and that all
  deduction rules preserve validity. This proves the soundness of K
*)

(* Axiom 1: p -> (q -> p) is a tautology *)
Lemma Hilbert_Axiom_1_soundness:
  forall M w φ ψ,
  M ' w ||- [! φ -> (ψ -> φ) !].
Proof.
  simpl; intros.
  assumption.
Qed.

(* Axiom 2: (p -> (q -> r)) -> ((p -> q) -> (p -> r)) is a tautology *)
Lemma Hilbert_Axiom_2_soundness:
  forall M w φ ψ Ɣ,
  M ' w ||- [! (φ -> (ψ -> Ɣ)) -> ((φ -> ψ) -> (φ -> Ɣ)) !].
Proof.
  simpl; intros.
  apply H; auto.
  (* - auto.
  - apply H0; auto. *)
Qed.

(* Axiom 3: (~ q -> ~ p) -> (p -> q) is a tautology *)
Lemma Hilbert_Axiom_3_soundness:
  forall M w φ ψ,
  M ' w ||- [! (~ψ -> ~φ) -> (φ -> ψ) !].
Proof.
  simpl; intros.
  pose (classic (M ' w ||- ψ)) as Hip.
  destruct Hip.
  - assumption.
  - apply H in H1.
    contradiction.
Qed.

(* Axiom 4: p -> (q -> (p /\ q)) is a tautology *)
Lemma Hilbert_Axiom_4_soundness: 
  forall M w φ ψ,
  M ' w ||- [! φ -> (ψ -> (φ /\ ψ)) !].
Proof.
  simpl; intros.
  split; auto.
Qed.

(* Axiom 5: (p /\ q) -> p is a tautology *)
Lemma Hilbert_Axiom_5_soundness:
  forall M w φ ψ,
  M ' w ||- [! (φ /\ ψ) -> φ !].
Proof.
  simpl; intros.
  destruct H as [Hip1 Hip2].
  assumption.
Qed.

(* Axiom 6: (p /\ q) -> q is a tautology *)
Lemma Hilbert_Axiom_6_soundness:
  forall M w φ ψ,
  M ' w ||- [! (φ /\ ψ) -> ψ !].
Proof.
  simpl; intros.
  destruct H as [Hip1 Hip2].
  assumption.
Qed.

(* Axiom 7: p -> (p \/ q) is a tautology *)
Lemma Hilbert_Axiom_7_soundness:
  forall M w φ ψ,
  M ' w ||- [! φ -> (φ \/ ψ) !].
Proof.
  simpl; intros.
  left.
  assumption.
Qed.

(* Axiom 8: q -> (p \/ q) is a tautology *)
Lemma Hilbert_Axiom_8_soundness: 
  forall M w φ ψ,
  M ' w ||- [! ψ -> (φ \/ ψ) !].
Proof.
  simpl; intros.
  right.
  assumption.
Qed.

(* Axiom 9: (p -> r) -> (q -> r) -> (p \/ q) -> r is a tautology *)
Lemma Hilbert_Axiom_9_soundness: 
  forall M w φ ψ Ɣ,
  M ' w ||- [! (φ -> Ɣ) -> (ψ -> Ɣ) -> (φ \/ ψ) -> Ɣ !].
Proof.
  simpl; intros.
  destruct H1.
  - apply H.
    assumption.
  - apply H0.
    assumption.
Qed.

(* Axiom 10: ~~p -> p is a tautology *)
Lemma Hilbert_Axiom_10_soundness:
  forall M w φ,
  M ' w ||- [! ~~φ -> φ !].
Proof.
  simpl; intros.
  apply NNPP in H.
  assumption.
Qed.

(* Possibility Axiom: <>(p \/ q) -> (<>p \/ <>q) is a tautology *)
Lemma Axiom_Possibility_soundness:
  forall M w φ ψ,
  M ' w ||- [! <>(φ \/ ψ) -> (<>φ \/ <>ψ) !].
Proof.
  simpl; intros.
  destruct H as [ w' [ Hip1 [ Hip2 | Hip3 ] ]].
  - left; exists w'; split; assumption.
    (* + assumption.
    + assumption. *)
  - right; exists w'; split; assumption.
    (* + assumption.
    + assumption. *)
Qed.

(* K Axiom: [](p -> q) -> ([]p -> []q) is a tautology *)
Lemma Axiom_K_soundness:
  forall M w φ ψ,
  M ' w ||- [! [](φ -> ψ) -> ([]φ -> []ψ) !].
Proof.
  simpl; intros.
  apply H.
  - assumption.
  - apply H0.
    assumption.
Qed.

(* φ ∈ Γ -> Γ ||= φ  *)
(* If phi is in a theory Gamma, then Gamma entails phi *)
Lemma case_two :
  forall Γ φ,
  In φ Γ ->
  Γ ||= φ.
Proof.
  unfold entails_modal, validate_model; intros.
  apply exact_deduction with Γ; assumption.
  (* - assumption.
  - assumption. *)
Qed.

(* a /\ (a -> b) -> b *)
(* Rule of Modus Ponens Preserves Validity *)
Lemma Modus_Ponens_soundness:
  forall M w φ ψ,
  ((M ' w ||- φ) /\
  (M ' w ||- [! φ -> ψ !])) ->
  (M ' w ||- ψ).
Proof.
  simpl; intros.
  destruct H.
  apply H0; auto.
Qed.

(* Rule of Necessitation Preserves Validity *)
Lemma Necessitation_soundness:
  forall M φ,
  (M |= φ) ->
  (M |= [! []φ !]).
Proof.
  unfold validate_model; simpl; intros.
  apply H.
Qed.

(* K is Sound *)
Theorem soundness:
  forall (G: theory) (φ: formula),
  (K; G |-- φ) ->
  (G ||= φ).
Proof.
  induction 1.
  (*Applies induction on the first non dependent hypothesis in the context, this being (K; G |-- φ)*)
  - intros M ?H. (*Base case of induction*)
    apply exact_deduction with t; try assumption.
    apply nth_error_In with i; assumption.
  - destruct H; destruct H0; simpl. (*Soundness of axioms*)
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

(* If G is satisfiable in M and if G can prove phi in K then phi is true at M*)
Corollary soundness2:
  forall M G w φ, 
  theoryModal M G -> 
  (K; G |-- φ) -> M ' w ||- φ.
Proof.
  intros.
  eapply soundness.
  - eassumption.
  - assumption.
Qed.
