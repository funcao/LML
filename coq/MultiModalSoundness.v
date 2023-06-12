Require Import List Notations Deductive_System Soundness Modal_Library Modal_Notations MultiModalCore MultiModalSyntax MultiModalSemantics.
Export ListNotations.

(**
  Some steps towards the proof of transfer of soundness
**)

(*
  First, a generic definition of soundness for frames of the base library
*)
Definition relative_soundness (A: axiom -> Prop) (R: Frame -> Prop) :=
  forall Γ φ, (A; Γ |-- φ) -> forall F V, R F -> entails (Build_Model F V) Γ φ.

Inductive anyFrame (F: Frame): Prop := anyFrameMk: anyFrame F.
Inductive anyRel (X: Set) (R: X -> X -> Prop): Prop := anyRelMk: anyRel X R.

(* Proving that this definition of soundness is correct*)
Lemma relative_soundness_correct:
  relative_soundness K anyFrame <-> (forall (G: theory) (φ: formula), (K; G |-- φ) -> (G ||= φ)).
Proof.
  split.
  - intros H0 Γ φ H1 [F V] T;
    unfold relative_soundness in H0.
    apply H0 with (F:=F) (V:=V) in H1; try constructor.
    auto.
  - intros H0;
    unfold relative_soundness;
    intros Γ φ H1 F V H2 H3.
    apply H0 with (G:=Γ);
    assumption.
Qed.

(*
  Next, a generic definition of soundness for frames of this multimodal library
*)
Definition relative_MMsoundness (modalities: nat) (A: MMaxiom -> Prop) (R: (nFrame modalities) -> Prop) :=
  forall Γ φ, (MMdeduction modalities A Γ φ) -> forall F V, R F ->
    entailment modalities (Build_nModel modalities F V) Γ φ.

Definition anyNFrame := fun n: nat => fun F: nFrame n => True.

(* Check nFrame_to_Frame. *)

(* Lemma teste: forall modalities dummyRel dummyFrame F,
  let LF := nFrame_to_list_Frame modalities dummyRel dummyFrame F in
  length LF > 0.
Proof.

Abort. *)

(* Definition restricted_nFrame (n: nat) (F: nFrame n) (P: (Set -> Set -> Prop) -> Prop): Prop :=
  exists i R, nth_error (nR n F) i = Some R -> P R. *)

(*
  Definition split_frame (F: nFrame): list Frame:=
    match F with
      | Build_nFrame nW nR _ => map (Build_Frame nW) nR
    end.

  Definition nFrame_to_Frame (F: nFrame) (index: nat): Frame :=
    match F with
      | Build_nFrame nW nR _ => Build_Frame nW (get_rel nW nR index)
    end.

  Inductive join (S1 S2: axiom -> Prop) (index1 index2: nat): MMaxiom -> Prop :=
    | derivable_S1: forall a b, S1 a -> axiom_to_MMaxiom index1 a b ->
      deducible_formula (MMinstance b) -> join S1 S2 index1 index2 b
    | derivable_S2: forall a b, S2 a -> axiom_to_MMaxiom index2 a b ->
      deducible_formula (MMinstance b) -> join S1 S2 index1 index2 b.

  Inductive join_one (S1: axiom -> Prop) (S2: MMaxiom -> Prop) (index: nat): MMaxiom -> Prop :=
    | derivable_S1_one: forall a b, S1 a -> axiom_to_MMaxiom index a b ->
      deducible_formula (MMinstance b) -> join_one S1 S2 index b
    | derivable_S2_one: forall a, S2 a -> join_one S1 S2 index a.

  Inductive join_two (S1 S2: MMaxiom -> Prop): MMaxiom -> Prop :=
    | derivable_S1_two: forall a, S1 a -> join_two S1 S2 a
    | derivable_S2_two: forall a, S2 a -> join_two S1 S2 a.
*)