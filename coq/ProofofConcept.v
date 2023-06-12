Require Import Arith List Notations Classical Relations Modal_Library Modal_Notations.
Export ListNotations.

(*** Proof of Concept of fusions in the library - Fusion of Systems K4 and T (or KT) ***)

(* 
  TODO: Separate into multiple files
*)

(* 
  Definition of formulas of the multimodal language KT4 obtained by combining KT with K4 
  That is, this language contains modalities that behave like modalities of KT and K4
*)
Inductive KT4formula : Set :=
  | T4Lit    : nat        -> KT4formula
  | T4Neg    : KT4formula -> KT4formula
  | TBox     : KT4formula -> KT4formula
  | TDia     : KT4formula -> KT4formula
  | K4Box    : KT4formula -> KT4formula
  | K4Dia    : KT4formula -> KT4formula
  | T4And    : KT4formula -> KT4formula -> KT4formula
  | T4Or     : KT4formula -> KT4formula -> KT4formula
  | T4Implies: KT4formula -> KT4formula -> KT4formula.

(** 
  Definition of frames for KT4 -- frames with two accessibility relations, 
    One for the KT fragment, that is reflexive
    One for the K4 fragment, that is transitive
**)

(* 
  First, we must define generic representations for the types of 
  relations we're interested 
*)

(* Generic definition of reflexivity of relations defined over a given Set X *)
Definition reflexive_rel (X: Set) (R: X -> X -> Prop): Prop :=
  forall w, R w w.

(* Generic definition of transitivity of relations defined over a given Set X *)
Definition transitive_rel (X: Set) (R: X -> X -> Prop): Prop :=
  forall w0 w1 w2, (R w0 w1 /\ R w1 w2) -> R w0 w2.

(*
  Next, we must prove that those definitions are sound, i.e., they mean the 
  same as the definitions on the core library

  Proving that, forall (basic) frames, the generic reflexivity relation defined above 
  is the same as stating that a frame is reflexive
*)
Theorem refl_equivalence: forall F W R,
  F = Build_Frame W R ->
  reflexivity_frame F <-> reflexive_rel W R.
Proof.
  intros F W R H0; split; intros H1.
  - unfold reflexive_rel.
    unfold reflexivity_frame in H1.
    rewrite H0 in H1;
    simpl in H1.
    assumption.
  - unfold reflexivity_frame.
    unfold reflexive_rel in H1.
    rewrite H0; simpl.
    assumption.
Qed.

(* 
  Proving that, forall (basic) frames, the generic transitivity relation defined above 
  is the same as stating that a frame is transitive
*)
Theorem trans_equivalence: forall F W R,
  F = Build_Frame W R ->
  transitivity_frame F <-> transitive_rel W R.
Proof.
  intros F W R H0; split; intros H1.
  - unfold transitivity_frame in H1;
    rewrite H0 in H1; simpl in H1.
    unfold transitive_rel.
    assumption.
  - unfold transitivity_frame; rewrite H0; simpl.
    unfold transitive_rel in H1.
    assumption.
Qed.

(* 
  Now we may define frames and models for KT4, using Record for the sake of 
  consistency with the core library
*)

Record KT4Frame: Type := {
  WT4: Set; (* Can't use the name W as this would conflict with the *)
  RT: WT4 -> WT4 -> Prop; (* definition of frames in the core library *)
  RT_refl: reflexive_rel WT4 RT;
  R4: WT4 -> WT4 -> Prop;
  R4_trans: transitive_rel WT4 R4
}.

(* Definition of models for KT4 -- models that are built over KT4Frames *)
Record KT4Model: Type := {
  FT4: KT4Frame; (* Same here with the names F and V *)
  VT4: nat -> (WT4 FT4) -> Prop
}.

(** 
  Explicity Definitions of Frames/Models for KT and K4, based on the 
  definitions on the core library -- This is so we may prove that KT4 frames defined
  above are correct w.r.t. the basic frames in the core library
**)

Definition KTFrame (F: Frame) := reflexivity_frame F. 
(*Every reflexive frame is a frame for KT*)
Definition KTModel (M: Model) := exists F v, M = [F -- v] /\ KTFrame F. 
(*Every model built with a reflexive frame is a model for KT*)

Definition K4Frame (F: Frame) := transitivity_frame F. 
(*Every transitive frame is a frame for K4*)
Definition K4Model (M: Model) := exists F v, M = [F -- v] /\ K4Frame F.
(*Every model built with a transitive frame is a model for K4*)

(** Proving that any KT4 Frame implies a KT Frame and a K4 Frame **)

(* First, we must define a function that transforms any given KT4 frame into a KT frame...*)
Definition KT4_frame_into_KT (F: KT4Frame): Frame := 
  match F with
  | Build_KT4Frame W RT RT_refl _ _ => Build_Frame W RT
  end.

(*... and one that transforms any given KT4 frame into a K4 frame *)
Definition KT4_frame_into_K4 (F: KT4Frame): Frame :=
	match F with
	| Build_KT4Frame W _ _ R4 R4_trans => Build_Frame W R4
	end.

(* 
	Then, we must prove that those definitions are sound, i.e., that they in fact transform
	frames of a type into frames of another type
 *)

(* First for KT *)
Theorem KT4_frame_into_KT_sound: forall F, 
  KTFrame (KT4_frame_into_KT F).
Proof.
  intros [W RT H0 R4 H1].
  unfold KTFrame.
  simpl.
  rewrite refl_equivalence; eauto.
Qed.

(* Then for K4 *)
Theorem KT4_frame_into_K4_sound: forall F, 
  K4Frame (KT4_frame_into_K4 F).
Proof.
  intros [W RT H0 R4 H1].
	unfold K4Frame.
  simpl.
  rewrite trans_equivalence; eauto.
Qed.

(** Proving that any KT4 Model imples a KT Model and a K4 Model **)

(* First, we must define a function that transforms any given KT4 Model into a KT Model... *)
Definition KT4_model_into_KT (M: KT4Model): Model := 
  match M with
  (* We must convince the type checker it is possible to convert one kind of frame to another *)
  | Build_KT4Model (Build_KT4Frame W RT _ R4 _ as F) V => Build_Model (KT4_frame_into_KT F) V
  end.

(*... and one that transforms any given KT4 Model into a K4 Model *)
Definition KT4_model_into_K4 (M: KT4Model): Model := 
  match M with
  | Build_KT4Model (Build_KT4Frame W RT _ R4 _ as F) V => Build_Model (KT4_frame_into_K4 F) V
  end.

(* 
	Then, we must prove that those definitions are sound, i.e., that they in fact transform
	models of a type into models of another type
*)

(* First for KT *)
Theorem KT4_model_into_KT_sound: forall M,
  KTModel (KT4_model_into_KT M).
Proof.
  intros [[W RT H0 R4 H1] V];
  simpl in *. 
  unfold KTModel.
  exists (Build_Frame W RT);
  exists V.
  split; try reflexivity.
  unfold KTFrame.
  rewrite refl_equivalence; eauto.
Qed.

(* Then for K4 *)
Theorem KT4_model_into_K4_sound: forall M,
  K4Model (KT4_model_into_K4 M).
Proof.
  intros [[W RT H0 R4 H1] V];
  simpl in *.
  unfold K4Model. 
  exists (Build_Frame W R4);
  exists V.
  split; try reflexivity.
  unfold K4Frame.
  rewrite trans_equivalence; eauto.
Qed.

(** Defining Notations for KT4 Formulas **)

(* 
  This notation will be as close as possible to the notation of the core
  library, while being easily distinctive
*)
Declare Custom Entry multi_modal.
Declare Scope multi_modal_scope.

Notation "x" := x
    (in custom multi_modal at level 0, x ident).
Notation "( x )" := x
    (in custom multi_modal, x at level 90).
Notation "<! m !>" := m
    (at level 0, m custom multi_modal at level 99, format "<!  m  !>").
Notation " p -> q " :=
    (T4Implies p q) (in custom multi_modal at level 13, right associativity).
Notation " p \/ q " :=
    (T4Or p q) (in custom multi_modal at level 12, left associativity).
Notation " p /\ q " :=
    (T4And p q) (in custom multi_modal at level 11, left associativity).
Notation " ~ p " := (T4Neg p)
    (in custom multi_modal at level 9, right associativity, format "~ p").
Notation " [T] p " := (TBox p)
    (in custom multi_modal at level 9, right associativity, format "[T] p").
Notation " <T> p " := (TDia p)
    (in custom multi_modal at level 9, right associativity, format "<T> p").
Notation " [4] p " := (K4Box p)
    (in custom multi_modal at level 9, right associativity, format "[4] p").
Notation " <4> p " := (K4Dia p)
    (in custom multi_modal at level 9, right associativity, format "<4> p").
Notation " # p " := (T4Lit p)
    (in custom multi_modal at level 2, no associativity, p constr at level 1, format "# p").

(** Definition of evaluation of formulas for KT4 **)

(* 
  Note that KT modalities are evaluated w.r.t. refl relations 
  and K4 modalities are evaluated w.r.t. trans relations 
*)
Fixpoint KT4eval (M: KT4Model) (w: WT4 (FT4 M)) (φ: KT4formula): Prop :=
  match φ with
  | T4Lit     x    => VT4 M x w 
  | TBox      ψ    => forall w', RT (FT4 M) w w' -> KT4eval M w' ψ
  | TDia      ψ    => exists w', RT (FT4 M) w w' /\ KT4eval M w' ψ
  | K4Box     ψ    => forall w', R4 (FT4 M) w w' -> KT4eval M w' ψ
  | K4Dia     ψ    => exists w', R4 (FT4 M) w w' /\ KT4eval M w' ψ
  | T4Neg     ψ    => ~KT4eval M w ψ
  | T4And     ψ Ɣ  => KT4eval M w ψ /\ KT4eval M w Ɣ
  | T4Or      ψ Ɣ  => KT4eval M w ψ \/ KT4eval M w Ɣ
  | T4Implies ψ Ɣ  => KT4eval M w ψ -> KT4eval M w Ɣ
  end.

(* 
  We must show that, semantically, KT4 is extension of KT and K4, to do so, we must
  prove that evaluating a KT4 formula is a generalization of the 
  evaluation of KT and K4 formulas, prove that model satisfiability in KT4 is a generalization
  of model satisfiability in KT and KT4 and prove that semantic entailment in KT4 is a generalization
  of semantic entailment in KT and K4
  
  To do so, we must show that if a formula φ is true in some
  KT/K4 model M, then it'll be true in some KT4 model M1

  First show that we can transform formulas from the base library into KT4formulas
*)
Fixpoint KTformula_to_KT4formula (φ: formula): KT4formula := 
  match φ with
  | Lit     x    => T4Lit     x
  | Dia     ψ    => TDia      (KTformula_to_KT4formula ψ)
  | Box     ψ    => TBox      (KTformula_to_KT4formula ψ)
  | Neg     ψ    => T4Neg     (KTformula_to_KT4formula ψ)
  | And     ψ Ɣ  => T4And     (KTformula_to_KT4formula ψ) (KTformula_to_KT4formula Ɣ)
  | Or      ψ Ɣ  => T4Or      (KTformula_to_KT4formula ψ) (KTformula_to_KT4formula Ɣ)
  | Implies ψ Ɣ  => T4Implies (KTformula_to_KT4formula ψ) (KTformula_to_KT4formula Ɣ)
  end.

Fixpoint K4formula_to_KT4formula (φ: formula): KT4formula := 
  match φ with
  | Lit     x    => T4Lit     x
  | Dia     ψ    => K4Dia     (K4formula_to_KT4formula ψ)
  | Box     ψ    => K4Box     (K4formula_to_KT4formula ψ)
  | Neg     ψ    => T4Neg     (K4formula_to_KT4formula ψ)
  | And     ψ Ɣ  => T4And     (K4formula_to_KT4formula ψ) (K4formula_to_KT4formula Ɣ)
  | Or      ψ Ɣ  => T4Or      (K4formula_to_KT4formula ψ) (K4formula_to_KT4formula Ɣ)
  | Implies ψ Ɣ  => T4Implies (K4formula_to_KT4formula ψ) (K4formula_to_KT4formula Ɣ)
  end.

Theorem KTformula_to_KT4formula_injective: forall φ1 φ2,
  KTformula_to_KT4formula φ1 = KTformula_to_KT4formula φ2 ->
    φ1 = φ2.
Proof.
  intros φ1 φ2 H0;
  generalize dependent φ2.
  induction φ1; intros φ2 H0; destruct φ2; 
  try discriminate; inversion H0; try auto; (*auto solves the case for Lit*)
  repeat(rewrite IHφ1 with φ2; auto); (* solves the cases for Neg, Box and Dia*)
  repeat(rewrite IHφ1_1 with φ2_1; try assumption; rewrite IHφ1_2 with φ2_2; easy).
  (*solves the cases for And, Or and Impl*)
Qed.

Theorem K4formula_to_KT4formula_injective: forall φ1 φ2,
  K4formula_to_KT4formula φ1 = K4formula_to_KT4formula φ2 ->
    φ1 = φ2.
Proof.
  intros φ1 φ2 H0;
  generalize dependent φ2.
  induction φ1; intros φ2 H0; destruct φ2; 
  try discriminate; inversion H0; try auto; (*auto solves the case for Lit*)
  repeat(rewrite IHφ1 with φ2; auto); (* solves the cases for Neg, Box and Dia*)
  repeat(rewrite IHφ1_1 with φ2_1; try assumption; rewrite IHφ1_2 with φ2_2; easy).
  (*solves the cases for And, Or and Impl*)
Qed.

(*
  Note that the other way around is impossible, as the base formulas have a single modality, where as 
  the KT4formulas have two
*)

(*** Model Satisfiability and Semantic Entailment in KT4 ***)

(* 
  Defining Model Validity - a formula is valid in a model if 
  it is true in every world of that model 
*)
Definition model_validity (M: KT4Model) (φ: KT4formula) := 
    forall w, KT4eval M w φ.

(* Notation for Model Satisfiability in KT4 *)
Notation "M |=t4 f" := (model_validity M f)
  (at level 110, no associativity).

(* Theories are (finite) lists of formulas *)
Definition KT4theory := list KT4formula.

(* 
  Helper function for the definition of semantic entailment 
  Verifies if a theory is satisfiable in a given model
*)
Fixpoint theorySatisfiable (M: KT4Model) (T: KT4theory): Prop :=
  match T with
  | [ ]    => True
  | h :: t => (model_validity M h) /\ (theorySatisfiable M t)
  end.

(** Definition of Entailment **)
Definition KT4entails (M: KT4Model) (T: KT4theory) (φ: KT4formula): Prop :=
  theorySatisfiable M T -> model_validity M φ.

(* Notation for Entailment in KT4 *)
Notation "M T ||=t4 f" := (KT4entails M T f)
  (at level 110, no associativity).

(* 
  To prove the generalization of semantic entailment, we must define a way of translating
  KT/K4 theories to KT4 theories
*)
Fixpoint KT_theory_to_KT4theory (T: theory): KT4theory :=
  match T with
  | [ ]    => [ ]
  | h :: t => (KTformula_to_KT4formula h) :: KT_theory_to_KT4theory t
  end.

Fixpoint K4_theory_to_KT4theory (T: theory): KT4theory :=
  match T with
  | [ ]    => [ ]
  | h :: t => (K4formula_to_KT4formula h) :: K4_theory_to_KT4theory t
  end.

Definition subset {T: Type} (L1 L2: list T): Prop :=
  forall x, In x L1 -> In x L2.

(*** Validity and Equivalence in KT4 ***)

(* Valid formulas are formulas which are entailed in all models *)
Definition KT4validity (T: KT4theory) (φ: KT4formula): Prop := 
  forall M, theorySatisfiable M T -> model_validity M φ.

(* Notation for Validity in KT4 *)
Notation "T ||=t4 f" := (KT4validity T f)
  (at level 110, no associativity).

(* Formulas are equivalent if they entail one another in all models *)
Definition KT4equivalence (φ ψ: KT4formula):= 
  KT4validity [φ] ψ /\  KT4validity [ψ] φ.

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

(*** Defining Axiomatic System for KT4 ***)

(*
  First, we must define the set of axioms we'll be using, much like formulas, they are defined as an inductive type
*)

Require Import Deductive_System. 
(* 
  Importing the deductive system from the base library, doing this in the begining of the file
  causes a weird error
*)

Inductive KT4axiom : Set :=
  | KT4ax1    : KT4formula -> KT4formula -> KT4axiom
  | KT4ax2    : KT4formula -> KT4formula -> KT4formula -> KT4axiom
  | KT4ax3    : KT4formula -> KT4formula -> KT4axiom
  | KT4ax4    : KT4formula -> KT4formula -> KT4axiom
  | KT4ax5    : KT4formula -> KT4formula -> KT4axiom
  | KT4ax6    : KT4formula -> KT4formula -> KT4axiom
  | KT4ax7    : KT4formula -> KT4formula -> KT4axiom
  | KT4ax8    : KT4formula -> KT4formula -> KT4axiom
  | KT4ax9    : KT4formula -> KT4formula -> KT4formula -> KT4axiom
  | KT4ax10   : KT4formula -> KT4formula -> KT4axiom
  | KT4axK_T  : KT4formula -> KT4formula -> KT4axiom
  | KT4axK_4  : KT4formula -> KT4formula -> KT4axiom
  | KT4axPos_T: KT4formula -> KT4formula -> KT4axiom
  | KT4axPos_4: KT4formula -> KT4formula -> KT4axiom
  | KT4axT    : KT4formula -> KT4axiom
  | KT4axK4   : KT4formula -> KT4axiom.

(*
  Next, we must define a function that "transforms" axioms into formulas, so as to give a meaning to objects of the axiom type
*)

Definition KT4instantiate (a: KT4axiom): KT4formula :=
  match a with
  | KT4ax1     φ ψ   => <! φ -> (ψ -> φ) !>
  | KT4ax2     φ ψ Ɣ => <! (φ -> (ψ -> Ɣ)) -> ((φ -> ψ) -> (φ -> Ɣ)) !>
  | KT4ax3     φ ψ   => <! (~ψ -> ~φ) -> (φ -> ψ) !>
  | KT4ax4     φ ψ   => <! φ -> (ψ -> (φ /\ ψ)) !>
  | KT4ax5     φ ψ   => <! (φ /\ ψ) -> φ !>
  | KT4ax6     φ ψ   => <! (φ /\ ψ) -> ψ !>
  | KT4ax7     φ ψ   => <! φ -> (φ \/ ψ) !>
  | KT4ax8     φ ψ   => <! ψ -> (φ \/ ψ) !>
  | KT4ax9     φ ψ Ɣ => <! (φ -> Ɣ) -> ((ψ -> Ɣ) -> ((φ \/ ψ) -> Ɣ)) !>
  | KT4ax10    φ ψ   => <! ~~φ -> φ !>
  | KT4axK_T   φ ψ   => <! [T](φ -> ψ) -> ([T] φ -> [T] ψ) !>
  | KT4axK_4   φ ψ   => <! [4](φ -> ψ) -> ([4] φ -> [4] ψ) !>
  | KT4axPos_T φ ψ   => <! <T> (φ \/ ψ) -> (<T> φ \/ <T> ψ) !>
  | KT4axPos_4 φ ψ   => <! <4> (φ \/ ψ) -> (<4> φ \/ <4> ψ) !>
  | KT4axT     φ     => <! [T]φ -> φ !>
  | KT4axK4    φ     => <! [4] φ -> [4][4] φ !>
  end.

(*
  And a function that translates axioms from the base library into KT4 axioms
*)

Inductive KT_axiom_to_KT4axiom: axiom -> KT4axiom -> Prop := 
  | transformT_ax1  : forall φ ψ,   KT_axiom_to_KT4axiom (ax1 φ ψ)   (KT4ax1     (KTformula_to_KT4formula φ) (KTformula_to_KT4formula ψ))
  | transformT_ax2  : forall φ ψ Ɣ, KT_axiom_to_KT4axiom (ax2 φ ψ Ɣ) (KT4ax2     (KTformula_to_KT4formula φ) (KTformula_to_KT4formula ψ) (KTformula_to_KT4formula Ɣ))
  | transformT_ax3  : forall φ ψ,   KT_axiom_to_KT4axiom (ax3 φ ψ)   (KT4ax3     (KTformula_to_KT4formula φ) (KTformula_to_KT4formula ψ))
  | transformT_ax4  : forall φ ψ,   KT_axiom_to_KT4axiom (ax4 φ ψ)   (KT4ax4     (KTformula_to_KT4formula φ) (KTformula_to_KT4formula ψ))
  | transformT_ax5  : forall φ ψ,   KT_axiom_to_KT4axiom (ax5 φ ψ)   (KT4ax5     (KTformula_to_KT4formula φ) (KTformula_to_KT4formula ψ))
  | transformT_ax6  : forall φ ψ,   KT_axiom_to_KT4axiom (ax6 φ ψ)   (KT4ax6     (KTformula_to_KT4formula φ) (KTformula_to_KT4formula ψ))
  | transformT_ax7  : forall φ ψ,   KT_axiom_to_KT4axiom (ax7 φ ψ)   (KT4ax7     (KTformula_to_KT4formula φ) (KTformula_to_KT4formula ψ))
  | transformT_ax8  : forall φ ψ,   KT_axiom_to_KT4axiom (ax8 φ ψ)   (KT4ax8     (KTformula_to_KT4formula φ) (KTformula_to_KT4formula ψ))
  | transformT_ax9  : forall φ ψ Ɣ, KT_axiom_to_KT4axiom (ax9 φ ψ Ɣ) (KT4ax9     (KTformula_to_KT4formula φ) (KTformula_to_KT4formula ψ) (KTformula_to_KT4formula Ɣ))
  | transformT_ax10 : forall φ ψ,   KT_axiom_to_KT4axiom (ax10 φ ψ)  (KT4ax10    (KTformula_to_KT4formula φ) (KTformula_to_KT4formula ψ))
  | transformT_axK  : forall φ ψ,   KT_axiom_to_KT4axiom (axK φ ψ)   (KT4axK_T   (KTformula_to_KT4formula φ) (KTformula_to_KT4formula ψ))
  | transformT_axPos: forall φ ψ,   KT_axiom_to_KT4axiom (axPos φ ψ) (KT4axPos_T (KTformula_to_KT4formula φ) (KTformula_to_KT4formula ψ))
  | transformT_axT  : forall φ,     KT_axiom_to_KT4axiom (axT φ)     (KT4axT     (KTformula_to_KT4formula φ)).

Inductive K4_axiom_to_KT4axiom: axiom -> KT4axiom -> Prop := 
  | transform4_ax1  : forall φ ψ,   K4_axiom_to_KT4axiom (ax1 φ ψ)   (KT4ax1     (K4formula_to_KT4formula φ) (K4formula_to_KT4formula ψ))
  | transform4_ax2  : forall φ ψ Ɣ, K4_axiom_to_KT4axiom (ax2 φ ψ Ɣ) (KT4ax2     (K4formula_to_KT4formula φ) (K4formula_to_KT4formula ψ) (K4formula_to_KT4formula Ɣ))
  | transform4_ax3  : forall φ ψ,   K4_axiom_to_KT4axiom (ax3 φ ψ)   (KT4ax3     (K4formula_to_KT4formula φ) (K4formula_to_KT4formula ψ))
  | transform4_ax4  : forall φ ψ,   K4_axiom_to_KT4axiom (ax4 φ ψ)   (KT4ax4     (K4formula_to_KT4formula φ) (K4formula_to_KT4formula ψ))
  | transform4_ax5  : forall φ ψ,   K4_axiom_to_KT4axiom (ax5 φ ψ)   (KT4ax5     (K4formula_to_KT4formula φ) (K4formula_to_KT4formula ψ))
  | transform4_ax6  : forall φ ψ,   K4_axiom_to_KT4axiom (ax6 φ ψ)   (KT4ax6     (K4formula_to_KT4formula φ) (K4formula_to_KT4formula ψ))
  | transform4_ax7  : forall φ ψ,   K4_axiom_to_KT4axiom (ax7 φ ψ)   (KT4ax7     (K4formula_to_KT4formula φ) (K4formula_to_KT4formula ψ))
  | transform4_ax8  : forall φ ψ,   K4_axiom_to_KT4axiom (ax8 φ ψ)   (KT4ax8     (K4formula_to_KT4formula φ) (K4formula_to_KT4formula ψ))
  | transform4_ax9  : forall φ ψ Ɣ, K4_axiom_to_KT4axiom (ax9 φ ψ Ɣ) (KT4ax9     (K4formula_to_KT4formula φ) (K4formula_to_KT4formula ψ) (K4formula_to_KT4formula Ɣ))
  | transform4_ax10 : forall φ ψ,   K4_axiom_to_KT4axiom (ax10 φ ψ)  (KT4ax10    (K4formula_to_KT4formula φ) (K4formula_to_KT4formula ψ))
  | transform4_axK  : forall φ ψ,   K4_axiom_to_KT4axiom (axK φ ψ)   (KT4axK_4   (K4formula_to_KT4formula φ) (K4formula_to_KT4formula ψ))
  | transform4_axPos: forall φ ψ,   K4_axiom_to_KT4axiom (axPos φ ψ) (KT4axPos_4 (K4formula_to_KT4formula φ) (K4formula_to_KT4formula ψ))
  | transform4_axK4 : forall φ,     K4_axiom_to_KT4axiom (axK4 φ)    (KT4axK4    (K4formula_to_KT4formula φ)).

(* Proving that instances of axioms carry over *)
Lemma KT_axiom_to_KT4axiom_sound: forall a b φ,
  instantiate a = φ -> KT_axiom_to_KT4axiom a b -> 
    KT4instantiate b = (KTformula_to_KT4formula φ).
Proof.
  intros a b φ H0 H1.
  destruct a; simpl in *;
  repeat (inversion H1; subst; reflexivity).
Qed.

Lemma K4_axiom_to_KT4axiom_sound: forall a b φ,
  instantiate a = φ -> K4_axiom_to_KT4axiom a b -> 
    KT4instantiate b = (K4formula_to_KT4formula φ).
Proof.
  intros a b φ H0 H1.
  destruct a; simpl in *; 
  repeat (inversion H1; subst; reflexivity).
Qed.

(*
  Next, we must define how to make derivations from said axioms, this is done by this inductively defined relation
  bellow. A deduction of a formula ψ in a Hilbert System is a sequence of formulas φ0, ..., φn, ψ
  such that each φ0, ..., φn is either: 
  - A Premise, i.e., is in the set of premises for a deduction
  - An Instance of an Axiom 
  - The result of applying the rule of Modus Ponens to any two previous formulas
  - The result of applying the rule of Necessitation for the T modality to any previous formula
  - The result of applying the rule of Necessitation for the 4 modality to any previous formula
  Note how there are two cases for the rule of necessitation
*)

Inductive KT4deduction (A: KT4axiom -> Prop): KT4theory -> KT4formula -> Prop :=
  (* Premises *)
  | PremKT4: forall (T: KT4theory) (φ: KT4formula) (i: nat),
                 (nth_error T i = Some φ) -> KT4deduction A T φ
  (* Instances of an Axiom *)
  | AxKT4: forall (T: KT4theory) (a: KT4axiom) (φ: KT4formula),
               A a -> KT4instantiate a = φ -> KT4deduction A T φ
  (* Modus Ponens *)
  | MpKT4: forall (T: KT4theory) (φ ψ: KT4formula),
               KT4deduction A T <! φ -> ψ !> -> KT4deduction A T φ -> KT4deduction A T ψ
  (* Necessitation for T *)
  | Nec_T: forall (T: KT4theory)
                  (φ: KT4formula), 
                  KT4deduction A T φ -> KT4deduction A T <! [T]φ !>
  (* Necessitation for 4 *)
  | Nec_4: forall (T: KT4theory)
                  (φ: KT4formula), 
                  KT4deduction A T φ -> KT4deduction A T <! [4]φ !>.

(* Notation for derivations *)
Notation "A ; G |--t4 p" := (KT4deduction A G p)
  (at level 110, no associativity).

(* 
  Next, we define the axiomatic system for our logic. As we're dealing with a bimodal logic, we need only
  define a single system, which has rules/axioms for K, T and 4 (rules/axioms for K would be in T/4 even in the
  monomodal case)
  In what follows "forall a b c, KT4Ax (KT4axY a b c ...)" is to be read as:
  "In System KT4, all instances of axiom Y are axioms of this system"
*)

(* System KT4 *)
Inductive KT4Ax: KT4axiom -> Prop :=
  | KT4_ax1:    forall φ ψ,   KT4Ax (KT4ax1 φ ψ)
  | KT4_ax2:    forall φ ψ Ɣ, KT4Ax (KT4ax2 φ ψ Ɣ)
  | KT4_ax3:    forall φ ψ,   KT4Ax (KT4ax3 φ ψ)
  | KT4_ax4:    forall φ ψ,   KT4Ax (KT4ax4 φ ψ)
  | KT4_ax5:    forall φ ψ,   KT4Ax (KT4ax5 φ ψ)
  | KT4_ax6:    forall φ ψ,   KT4Ax (KT4ax6 φ ψ)
  | KT4_ax7:    forall φ ψ,   KT4Ax (KT4ax7 φ ψ)
  | KT4_ax8:    forall φ ψ,   KT4Ax (KT4ax8 φ ψ)
  | KT4_ax9:    forall φ ψ Ɣ, KT4Ax (KT4ax9 φ ψ Ɣ)
  | KT4_ax10:   forall φ ψ,   KT4Ax (KT4ax10 φ ψ)
  | KT4_axKT:   forall φ ψ,   KT4Ax (KT4axK_T φ ψ)
  | KT4_axK_4:  forall φ ψ,   KT4Ax (KT4axK_4 φ ψ)
  | KT4_axPosT: forall φ ψ,   KT4Ax (KT4axPos_T φ ψ)
  | KT4_axPos4: forall φ ψ,   KT4Ax (KT4axPos_4 φ ψ)
  | KT4_axT:    forall φ,     KT4Ax (KT4axT φ)
  | KT4_axK4:   forall φ,     KT4Ax (KT4axK4 φ).

(* For the following proofs, we will need so additional facts *)

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
  intros A T φ H0. eapply In_nth_error in H0; destruct H0 as [i].
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

Require Import Soundness.

(* 
  To show that KT4 is sound, we must first show that both KT and K4 are sound 
  As there is no "soundness" property in the core library, it will be stated here
*)

Definition relative_soundness (A: axiom -> Prop) (R: Frame -> Prop) := 
  forall Γ φ, (A; Γ |-- φ) -> forall F V, R F -> entails (Build_Model F V) Γ φ.
(* 
  This states that a axiomatic system A is sound relative to a (set) of frames 
  {F | F satisfies condition R}
  For KT frames, R is the condition that the frame is reflexive
  For K4 frames, R is the condition that the frame is transitive
  For K frames,  R is the condition that F is any frame, defined below
*)

Inductive anyFrame (F: Frame): Prop :=
  anyFrameMk: anyFrame F.

(* Proving that this definition of soundness is correct
    TODO: Conferir se isso está certo
*)
Lemma relative_soundness_correct:
  relative_soundness K anyFrame.
Proof.
  intros Γ φ H0 F V H1.
  apply soundness in H0;
  unfold entails_modal in H0.
  intros H2; apply H0;
  assumption.
Qed.

Require Import Frame_Validation.
(* This file has proofs of the soundness of the other systems of modal logic *)

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

(*
  Now that we have shown that KT and K4 are sound with respect to the classes of
  reflexive and transitive frames respectivelly, we must show that KT4 is sound with respect
  to the class of reflexive and transitive 2-frames
*)

Fixpoint KT4formula_to_formula (φ: KT4formula): formula :=
  match φ with
  | T4Lit     x    => Lit     x
  | TBox      ψ    => Box     (KT4formula_to_formula ψ)
  | TDia      ψ    => Dia     (KT4formula_to_formula ψ)
  | K4Box     ψ    => Box     (KT4formula_to_formula ψ)
  | K4Dia     ψ    => Dia     (KT4formula_to_formula ψ)
  | T4Neg     ψ    => Neg     (KT4formula_to_formula ψ)
  | T4And     ψ Ɣ  => And     (KT4formula_to_formula ψ) (KT4formula_to_formula Ɣ)
  | T4Or      ψ Ɣ  => Or      (KT4formula_to_formula ψ) (KT4formula_to_formula Ɣ)
  | T4Implies ψ Ɣ  => Implies (KT4formula_to_formula ψ) (KT4formula_to_formula Ɣ)
  end.

Fixpoint KT4theory_to_theory (T: KT4theory): theory :=
  match T with
  | [ ]    => [ ]
  | h :: t => (KT4formula_to_formula h) :: KT4theory_to_theory t
  end.

Lemma KT4formula_to_KTformula_reversible: 
  forall φ,  KT4formula_to_formula (KTformula_to_KT4formula φ) = φ.
Proof.
  induction φ;
  try (reflexivity); (*Atom*)
  try (simpl; rewrite IHφ; reflexivity); (*Unary connectives*)
  try (simpl; rewrite IHφ1; rewrite IHφ2; reflexivity). (*Binary connectives*)
Qed.

Lemma KT4formula_to_K4formula_reversible: 
  forall φ, KT4formula_to_formula (K4formula_to_KT4formula φ) = φ.
Proof.
  induction φ;
  try (reflexivity); (*Atom*)
  try (simpl; rewrite IHφ; reflexivity); (*Unary connectives*)
  try (simpl; rewrite IHφ1; rewrite IHφ2; reflexivity). (*Binary connectives*)
Qed.

Lemma KT4theory_to_KTtheory_reversible: 
  forall Γ, KT4theory_to_theory (KT_theory_to_KT4theory Γ) = Γ.
Proof.
  induction Γ; try (reflexivity);
  simpl; rewrite KT4formula_to_KTformula_reversible;
  rewrite IHΓ; reflexivity.
Qed.

Lemma KT4theory_to_K4theory_reversible: 
  forall Γ, KT4theory_to_theory (K4_theory_to_KT4theory Γ) = Γ.
Proof.
  induction Γ; try (reflexivity);
  simpl; rewrite KT4formula_to_K4formula_reversible;
  rewrite IHΓ; reflexivity.
Qed.

Inductive KT4_axiom_to_ProppositionalAxiom: KT4axiom -> axiom -> Prop :=
| transformKT4_to_ax1  : forall φ ψ,   KT4_axiom_to_ProppositionalAxiom (KT4ax1 φ ψ)     (ax1   (KT4formula_to_formula φ) (KT4formula_to_formula ψ))
| transformKT4_to_ax2  : forall φ ψ Ɣ, KT4_axiom_to_ProppositionalAxiom (KT4ax2 φ ψ Ɣ)   (ax2   (KT4formula_to_formula φ) (KT4formula_to_formula ψ) (KT4formula_to_formula Ɣ))
| transformKT4_to_ax3  : forall φ ψ,   KT4_axiom_to_ProppositionalAxiom (KT4ax3 φ ψ)     (ax3   (KT4formula_to_formula φ) (KT4formula_to_formula ψ))
| transformKT4_to_ax4  : forall φ ψ,   KT4_axiom_to_ProppositionalAxiom (KT4ax4 φ ψ)     (ax4   (KT4formula_to_formula φ) (KT4formula_to_formula ψ))
| transformKT4_to_ax5  : forall φ ψ,   KT4_axiom_to_ProppositionalAxiom (KT4ax5 φ ψ)     (ax5   (KT4formula_to_formula φ) (KT4formula_to_formula ψ))
| transformKT4_to_ax6  : forall φ ψ,   KT4_axiom_to_ProppositionalAxiom (KT4ax6 φ ψ)     (ax6   (KT4formula_to_formula φ) (KT4formula_to_formula ψ))
| transformKT4_to_ax7  : forall φ ψ,   KT4_axiom_to_ProppositionalAxiom (KT4ax7 φ ψ)     (ax7   (KT4formula_to_formula φ) (KT4formula_to_formula ψ))
| transformKT4_to_ax8  : forall φ ψ,   KT4_axiom_to_ProppositionalAxiom (KT4ax8 φ ψ)     (ax8   (KT4formula_to_formula φ) (KT4formula_to_formula ψ))
| transformKT4_to_ax9  : forall φ ψ Ɣ, KT4_axiom_to_ProppositionalAxiom (KT4ax9 φ ψ Ɣ)   (ax9   (KT4formula_to_formula φ) (KT4formula_to_formula ψ) (KT4formula_to_formula Ɣ))
| transformKT4_to_ax10 : forall φ ψ,   KT4_axiom_to_ProppositionalAxiom (KT4ax10 φ ψ)    (ax10  (KT4formula_to_formula φ) (KT4formula_to_formula ψ)).

Inductive KT4_axiom_to_KTaxiom: KT4axiom -> axiom -> Prop :=
  | transformKT4_toT_prop : forall φ ψ,   KT4_axiom_to_ProppositionalAxiom φ ψ  -> KT4_axiom_to_KTaxiom φ ψ
  | transformKT4_toT_axK  : forall φ ψ,   KT4_axiom_to_KTaxiom (KT4axK_T φ ψ)   (axK   (KT4formula_to_formula φ) (KT4formula_to_formula ψ))
  | transformKT4_toT_axPos: forall φ ψ,   KT4_axiom_to_KTaxiom (KT4axPos_T φ ψ) (axPos (KT4formula_to_formula φ) (KT4formula_to_formula ψ))
  | transformKT4_toT_axT  : forall φ,     KT4_axiom_to_KTaxiom (KT4axT φ)       (axT   (KT4formula_to_formula φ)).

Inductive KT4_axiom_to_K4axiom: KT4axiom -> axiom -> Prop :=
  | transformKT4_to4_prop : forall φ ψ,   KT4_axiom_to_ProppositionalAxiom φ ψ  -> KT4_axiom_to_K4axiom φ ψ
  | transformKT4_to4_axK  : forall φ ψ,   KT4_axiom_to_K4axiom (KT4axK_4 φ ψ)   (axK   (KT4formula_to_formula φ) (KT4formula_to_formula ψ))
  | transformKT4_to4_axPos: forall φ ψ,   KT4_axiom_to_K4axiom (KT4axPos_4 φ ψ) (axPos (KT4formula_to_formula φ) (KT4formula_to_formula ψ))
  | transformKT4_to4_axK4 : forall φ,     KT4_axiom_to_K4axiom (KT4axK4 φ)      (axK4  (KT4formula_to_formula φ)).

(* TODO: Arrumar essas provas *)
Lemma KT4_axiom_to_KTaxiom_sound: forall a b φ,
  KT4instantiate a = φ -> KT4_axiom_to_KTaxiom a b ->
    instantiate b = (KT4formula_to_formula φ).
Proof.
  intros a b φ H0 H1.
  destruct a; simpl in *;
  repeat (inversion H1; subst; reflexivity).
Admitted.

Lemma KT4_axiom_to_K4axiom_sound: forall a b φ,
  KT4instantiate a = φ -> KT4_axiom_to_K4axiom a b ->
    instantiate b = (KT4formula_to_formula φ).
Proof.
  intros a b φ H0 H1.
  destruct a; simpl in *;
  repeat (inversion H1; subst; reflexivity).
Admitted.

Theorem silly1: forall W RT RTR R4 R4R V φ a Γ,
  let FT4 := Build_KT4Frame W RT RTR R4 R4R in
    let MT4 := Build_KT4Model FT4 V in
      let M := KT4_model_into_KT MT4 in
        KT4instantiate a = φ ->
        entails M (KT4theory_to_theory Γ) (KT4formula_to_formula φ) ->
        KT4entails MT4 Γ φ.
Proof.
  intros W RT RTR R4 R4R V φ a Γ FT4 MT4 M H0 H1.
Abort.

Inductive anyKT4Frame (F: KT4Frame): Prop :=
  anyKT4FrameMk: anyKT4Frame F.

Definition relative_KT4soundness (A: KT4axiom -> Prop) (R: KT4Frame -> Prop) := 
  forall Γ φ, (A; Γ |--t4 φ) -> forall F V, R F -> KT4entails (Build_KT4Model F V) Γ φ.

Theorem KT4_soundness:
  relative_KT4soundness KT4Ax anyKT4Frame.
Proof.
  intros Γ φ H0 FT4 VT4 H1.
  assert(HKT: relative_soundness T (fun F => F = KT4_frame_into_KT FT4)) 
    by (intros ?x ?x ?x F ?x H3; assert (H4: KTFrame F) by (rewrite H3; apply KT4_frame_into_KT_sound);
        eapply KT_soundness in H4; eauto).
  assert(HK4: relative_soundness K4 (fun F => F = KT4_frame_into_K4 FT4)) 
    by (intros ?x ?x ?x F ?x H4; assert (H5: K4Frame F) by (rewrite H4; apply KT4_frame_into_K4_sound);
        eapply K4_soundness in H5; eauto).
  induction H0.
  - (*Premises*)
    intros ?H; apply entailment_in_theory with (T); 
    try assumption; apply nth_error_In with (i); 
    assumption.
  - (*Instance of Axioms*) 
    unfold relative_soundness in *.
    destruct FT4 as [WT4 RT RT_refl R4 R4_trans]; simpl in *.
    destruct H.
    + pose H0 as H2.
      apply KT4_axiom_to_KTaxiom_sound with (b:=ax1 (KT4formula_to_formula φ0) (KT4formula_to_formula ψ)) in H2; try constructor.
      assert(H3: forall Γ, Deductive_System.T; Γ |-- KT4formula_to_formula φ)
        by (intros Γ; rewrite <- H2; apply Ax with (ax1 (KT4formula_to_formula φ0) (KT4formula_to_formula ψ)); 
            try auto; apply T_K; constructor).
      apply HKT with (F:=KT4_frame_into_KT (Build_KT4Frame WT4 RT RT_refl R4 R4_trans)) (Γ:=KT4theory_to_theory T) (V:=VT4) in H3;
      try auto; simpl in H3.

      eapply KT_semantic_entail_generalization with (T:=(KT4theory_to_theory T)) (φ:=KT4formula_to_formula φ) in H3.
(* - (*Modus Ponens*) admit.
  - (*Necessitation for [T]*) admit.
  - (*Necessitation for [4]*) admit. *)
Abort.
