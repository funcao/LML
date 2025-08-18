Require Import Modal_Library Modal_Notations Classical List Deductive_System.

Section Soundness.

Context `{X: modal_index_set}.

(* p -> (q -> p) *)
Lemma Hilbert_Axiom_1_soundness:
  forall M w φ ψ,
  M ' w ||- [! φ -> (ψ -> φ) !].
Proof.
  simpl; intros.
  assumption.
Qed.

(* (p -> (q -> r)) -> ((p -> q) -> (p -> r)) *)
Lemma Hilbert_Axiom_2_soundness:
  forall M w φ ψ Ɣ,
  M ' w ||- [! (φ -> (ψ -> Ɣ)) -> ((φ -> ψ) -> (φ -> Ɣ)) !].
Proof.
  simpl; intros.
  apply H.
  - auto.
  - apply H0; auto.
Qed.

(* (~ q -> ~ p) -> (p -> q) *)
Lemma Hilbert_Axiom_3_soundness:
  forall M w φ ψ,
  M ' w ||- [! (~ψ -> ~φ) -> (φ -> ψ) !].
Proof.
  simpl; intros.
  pose (classic (M ' w ||- ψ)) as Hip.
  destruct Hip.
  - auto.
  - apply H in H1.
    contradiction.
Qed.

(* p -> (q -> (p /\ q)) *)
Lemma Hilbert_Axiom_4_soundness: 
  forall M w φ ψ,
  M ' w ||- [! φ -> (ψ -> (φ /\ ψ)) !].
Proof.
  simpl; intros.
  split; auto.
Qed.

(* (p /\ q) -> p *)
Lemma Hilbert_Axiom_5_soundness:
  forall M w φ ψ,
  M ' w ||- [! (φ /\ ψ) -> φ !].
Proof.
  simpl; intros.
  destruct H as [Hip1 Hip2].
  assumption.
Qed.

(* (p /\ q) -> q *)
Lemma Hilbert_Axiom_6_soundness:
  forall M w φ ψ,
  M ' w ||- [! (φ /\ ψ) -> ψ !].
Proof.
  simpl; intros.
  destruct H as [Hip1 Hip2].
  assumption.
Qed.

(* p -> (p \/ q) *)
Lemma Hilbert_Axiom_7_soundness:
  forall M w φ ψ,
  M ' w ||- [! φ -> (φ \/ ψ) !].
Proof.
  simpl; intros.
  left.
  assumption.
Qed.

(* q -> (p \/ q) *)
Lemma Hilbert_Axiom_8_soundness: 
  forall M w φ ψ,
  M ' w ||- [! ψ -> (φ \/ ψ) !].
Proof.
  simpl; intros.
  right.
  assumption.
Qed.

(* (p -> r) -> (q -> r) -> (p \/ q) -> r *)
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

(* ~~p -> p *)
Lemma Hilbert_Axiom_10_soundness:
  forall M w φ,
  M ' w ||- [! ~~φ -> φ !].
Proof.
  simpl; intros.
  apply NNPP in H.
  assumption.
Qed.

(* <>(p \/ q) -> (<>p \/ <>q) *)
Lemma Axiom_Possibility_soundness:
  forall M w φ ψ idx,
  M ' w ||- [! <idx>(φ \/ ψ) -> (<idx>φ \/ <idx>ψ) !].
Proof.
  simpl; intros.
  destruct H as (w', ?H, [ ?H | ?H ]).
  - left; exists w'.
    + assumption.
    + assumption.
  - right; exists w'.
    + assumption.
    + assumption.
Qed.

(* [](p -> q) -> ([]p -> []q) *)
Lemma Axiom_K_soundness:
  forall M w φ ψ idx,
  M ' w ||- [! [idx](φ -> ψ) -> ([idx]φ -> [idx]ψ) !].
Proof.
  simpl; intros.
  apply H.
  - assumption.
  - apply H0.
    assumption.
Qed.

(* <>p <-> ~[]~p *)
Lemma Axiom_Dual_soundness:
  forall M w φ idx,
  M ' w ||- [! <idx>φ <-> ~[idx]~φ !].
Proof.
  simpl; split; intros.
  - destruct H as (w', ?, ?).
    intro; apply H1 with w'.
    + assumption.
    + assumption.
  - edestruct classic.
    + eassumption.
    + exfalso.
      apply H; intros; intro.
      apply H0.
      exists w'.
      * assumption.
      * assumption.
Qed.

Require Import Relations.

Lemma T_soundness:
  forall M w φ idx,
  reflexive_frame (F M) idx ->
  M ' w ||- [! [idx]φ -> φ !].
Proof.
  simpl; intros.
  apply H0.
  apply H.
Qed.

Lemma K4_soundness:
  forall M w φ idx,
  transitive_frame (F M) idx ->
  M ' w ||- [! [idx]φ -> [idx][idx]φ !].
Proof.
  simpl; intros.
  apply H0.
  apply H with w'.
  now split.
Qed.

(* a /\ (a -> b) -> b *)
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

Lemma Necessitation_soundness:
  forall M φ idx,
  (M |= φ) ->
  (M |= [! [idx]φ !]).
Proof.
  unfold validate_model; simpl; intros.
  apply H.
Qed.

(* K is sound for every frame. *)

Theorem soundness:
  forall (G: theory) (φ: formula) idx,
  (K idx; G |-- φ) ->
  (G ||= φ).
Proof.
  induction 1.
  - intros M ?H.
    apply H0; auto.
  - destruct H.
    + destruct H; subst; simpl.
      * intros M ?H w.
        apply Hilbert_Axiom_1_soundness.
      * intros M ?H w.
        apply Hilbert_Axiom_2_soundness.
      * intros M ?H w.
        apply Hilbert_Axiom_3_soundness.
      * intros M ?H w.
        apply Hilbert_Axiom_4_soundness.
      * intros M ?H w.
        apply Hilbert_Axiom_5_soundness.
      * intros M ?H w.
        apply Hilbert_Axiom_6_soundness.
      * intros M ?H w.
        apply Hilbert_Axiom_7_soundness.
      * intros M ?H w.
        apply Hilbert_Axiom_8_soundness.
      * intros M ?H w.
        apply Hilbert_Axiom_9_soundness.
      * intros M ?H w.
        apply Hilbert_Axiom_10_soundness.
    + intros M ?H w; subst; simpl instantiate.
      apply Axiom_K_soundness.
    + intros M ?H w; subst; simpl instantiate.
      apply Axiom_Dual_soundness.
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
    intros p ? ?.
    inversion H1.
Qed.

(* S4 is sound for equivalence frames. *)

Theorem soundness_S4:
  forall (G: theory) (φ: formula) idx,
  (S4 idx; G |-- φ) ->
  (* TODO: we might wanna change the order of arguments. *)
  entails_modal_class (fun F => preorder_frame F idx) G φ.
Proof.
  unfold entails_modal_class, entails.
  induction 1; intros.
  - apply H1; auto.
  - destruct H.
    + destruct H.
      * intro w.
        apply (soundness t f idx); auto.
        now constructor 2 with (a := φ).
      * subst; simpl; intro.
        apply T_soundness.
        now destruct H1.
    + subst; simpl; intro.
      apply K4_soundness.
      now destruct H1.
  - intros w.
    apply Modus_Ponens_soundness with f.
    split.
    + now apply IHdeduction2.
    + now apply IHdeduction1.
  - intros w.
    apply Necessitation_soundness.
    apply IHdeduction.
    + assumption.
    + intros p ? ?.
      inversion H2.
Qed.

End Soundness.
