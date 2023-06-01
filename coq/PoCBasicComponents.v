Require Import Arith List Notations Classical Relations Modal_Library Modal_Notations.
Export ListNotations.

(**
  TODO: Improve comments
**)

(* Basic Components of the Proof of Components - Core definitions and notations *)

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
  intros [W RT H0 R4 H1];
  unfold KTFrame;
  simpl.
  rewrite refl_equivalence; eauto.
Qed.

(* Then for K4 *)
Theorem KT4_frame_into_K4_sound: forall F,
  K4Frame (KT4_frame_into_K4 F).
Proof.
  intros [W RT H0 R4 H1];
	unfold K4Frame;
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
  unfold KTModel;
  simpl in *.
  exists (Build_Frame W RT);
  exists V.
  split; try reflexivity;
  unfold KTFrame.
  rewrite refl_equivalence; eauto.
Qed.

(* Then for K4 *)
Theorem KT4_model_into_K4_sound: forall M,
  K4Model (KT4_model_into_K4 M).
Proof.
  intros [[W RT H0 R4 H1] V];
  unfold K4Model;
  simpl in *.
  exists (Build_Frame W R4);
  exists V.
  split; try reflexivity;
  unfold K4Frame.
  rewrite trans_equivalence; eauto.
Qed.

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
  First it's show that we can transform formulas from the base library into KT4formulas
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
  intros φ1 φ2;
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
  intros φ1 φ2;
  generalize dependent φ2.
  induction φ1; intros φ2 H0; destruct φ2;
  try discriminate; inversion H0; try auto; (*auto solves the case for Lit*)
  repeat(rewrite IHφ1 with φ2; auto); (* solves the cases for Neg, Box and Dia*)
  repeat(rewrite IHφ1_1 with φ2_1; try assumption; rewrite IHφ1_2 with φ2_2; easy).
  (*solves the cases for And, Or and Impl*)
Qed.

(* Theories are (finite) lists of formulas *)
Definition KT4theory := list KT4formula.

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
  try reflexivity; (*Atom*)
  try (simpl; rewrite IHφ; reflexivity); (*Unary connectives*)
  try (simpl; rewrite IHφ1; rewrite IHφ2; reflexivity). (*Binary connectives*)
Qed.

Lemma KT4formula_to_K4formula_reversible:
  forall φ, KT4formula_to_formula (K4formula_to_KT4formula φ) = φ.
Proof.
  induction φ;
  try reflexivity; (*Atom*)
  try (simpl; rewrite IHφ; reflexivity); (*Unary connectives*)
  try (simpl; rewrite IHφ1; rewrite IHφ2; reflexivity). (*Binary connectives*)
Qed.

Lemma KT4theory_to_KTtheory_reversible:
  forall Γ, KT4theory_to_theory (KT_theory_to_KT4theory Γ) = Γ.
Proof.
  induction Γ; try reflexivity;
  simpl; rewrite KT4formula_to_KTformula_reversible;
  rewrite IHΓ; reflexivity.
Qed.

Lemma KT4theory_to_K4theory_reversible:
  forall Γ, KT4theory_to_theory (K4_theory_to_KT4theory Γ) = Γ.
Proof.
  induction Γ; try reflexivity;
  simpl; rewrite KT4formula_to_K4formula_reversible;
  rewrite IHΓ; reflexivity.
Qed.

(*** Model Satisfiability and Semantic Entailment in KT4 ***)

(*
  Defining Model Validity - a formula is valid in a model if
  it is true in every world of that model
*)
Definition model_validity (M: KT4Model) (φ: KT4formula) :=
  forall w, KT4eval M w φ.

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

Definition subset {T: Type} (L1 L2: list T): Prop :=
  forall x, In x L1 -> In x L2.

(*** Validity and Equivalence in KT4 ***)

(* Valid formulas are formulas which are entailed in all models *)
Definition KT4validity (T: KT4theory) (φ: KT4formula): Prop :=
  forall M, theorySatisfiable M T -> model_validity M φ.

(* Formulas are equivalent if they entail one another in all models *)
Definition KT4equivalence (φ ψ: KT4formula):=
  KT4validity [φ] ψ /\  KT4validity [ψ] φ.

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
Notation "M |=t4 f" := (model_validity M f)
  (at level 110, no associativity).
Notation "M T ||=t4 f" := (KT4entails M T f)
  (at level 110, no associativity).
Notation "T ||=t4 f" := (KT4validity T f)
  (at level 110, no associativity).

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
  | KT4axK_T   φ ψ   => <! [T](φ -> ψ) -> ([T]φ -> [T]ψ) !>
  | KT4axK_4   φ ψ   => <! [4](φ -> ψ) -> ([4]φ -> [4]ψ) !>
  | KT4axPos_T φ ψ   => <! <T>(φ \/ ψ) -> (<T>φ \/ <T>ψ) !>
  | KT4axPos_4 φ ψ   => <! <4>(φ \/ ψ) -> (<4>φ \/ <4>ψ) !>
  | KT4axT     φ     => <! [T]φ -> φ !>
  | KT4axK4    φ     => <! [4]φ -> [4][4]φ !>
  end.

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
  | KT4_ax1:     forall φ ψ,   KT4Ax (KT4ax1 φ ψ)
  | KT4_ax2:     forall φ ψ Ɣ, KT4Ax (KT4ax2 φ ψ Ɣ)
  | KT4_ax3:     forall φ ψ,   KT4Ax (KT4ax3 φ ψ)
  | KT4_ax4:     forall φ ψ,   KT4Ax (KT4ax4 φ ψ)
  | KT4_ax5:     forall φ ψ,   KT4Ax (KT4ax5 φ ψ)
  | KT4_ax6:     forall φ ψ,   KT4Ax (KT4ax6 φ ψ)
  | KT4_ax7:     forall φ ψ,   KT4Ax (KT4ax7 φ ψ)
  | KT4_ax8:     forall φ ψ,   KT4Ax (KT4ax8 φ ψ)
  | KT4_ax9:     forall φ ψ Ɣ, KT4Ax (KT4ax9 φ ψ Ɣ)
  | KT4_ax10:    forall φ ψ,   KT4Ax (KT4ax10 φ ψ)
  | KT4_axK_T:   forall φ ψ,   KT4Ax (KT4axK_T φ ψ)
  | KT4_axK_4:   forall φ ψ,   KT4Ax (KT4axK_4 φ ψ)
  | KT4_axPos_T: forall φ ψ,   KT4Ax (KT4axPos_T φ ψ)
  | KT4_axPos_4: forall φ ψ,   KT4Ax (KT4axPos_4 φ ψ)
  | KT4_axT:     forall φ,     KT4Ax (KT4axT φ)
  | KT4_axK4:    forall φ,     KT4Ax (KT4axK4 φ).

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

(* Proving that translations of axioms are correct *)
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

Inductive KT4_axiom_to_KTaxiom: KT4axiom -> axiom -> Prop :=
  | transformKT4_toT_ax1  : forall φ ψ,   KT4_axiom_to_KTaxiom (KT4ax1 φ ψ)     (ax1   (KT4formula_to_formula φ) (KT4formula_to_formula ψ))
  | transformKT4_toT_ax2  : forall φ ψ Ɣ, KT4_axiom_to_KTaxiom (KT4ax2 φ ψ Ɣ)   (ax2   (KT4formula_to_formula φ) (KT4formula_to_formula ψ) (KT4formula_to_formula Ɣ))
  | transformKT4_toT_ax3  : forall φ ψ,   KT4_axiom_to_KTaxiom (KT4ax3 φ ψ)     (ax3   (KT4formula_to_formula φ) (KT4formula_to_formula ψ))
  | transformKT4_toT_ax4  : forall φ ψ,   KT4_axiom_to_KTaxiom (KT4ax4 φ ψ)     (ax4   (KT4formula_to_formula φ) (KT4formula_to_formula ψ))
  | transformKT4_toT_ax5  : forall φ ψ,   KT4_axiom_to_KTaxiom (KT4ax5 φ ψ)     (ax5   (KT4formula_to_formula φ) (KT4formula_to_formula ψ))
  | transformKT4_toT_ax6  : forall φ ψ,   KT4_axiom_to_KTaxiom (KT4ax6 φ ψ)     (ax6   (KT4formula_to_formula φ) (KT4formula_to_formula ψ))
  | transformKT4_toT_ax7  : forall φ ψ,   KT4_axiom_to_KTaxiom (KT4ax7 φ ψ)     (ax7   (KT4formula_to_formula φ) (KT4formula_to_formula ψ))
  | transformKT4_toT_ax8  : forall φ ψ,   KT4_axiom_to_KTaxiom (KT4ax8 φ ψ)     (ax8   (KT4formula_to_formula φ) (KT4formula_to_formula ψ))
  | transformKT4_toT_ax9  : forall φ ψ Ɣ, KT4_axiom_to_KTaxiom (KT4ax9 φ ψ Ɣ)   (ax9   (KT4formula_to_formula φ) (KT4formula_to_formula ψ) (KT4formula_to_formula Ɣ))
  | transformKT4_toT_ax10 : forall φ ψ,   KT4_axiom_to_KTaxiom (KT4ax10 φ ψ)    (ax10  (KT4formula_to_formula φ) (KT4formula_to_formula ψ))
  | transformKT4_toT_axK  : forall φ ψ,   KT4_axiom_to_KTaxiom (KT4axK_T φ ψ)   (axK   (KT4formula_to_formula φ) (KT4formula_to_formula ψ))
  | transformKT4_toT_axPos: forall φ ψ,   KT4_axiom_to_KTaxiom (KT4axPos_T φ ψ) (axPos (KT4formula_to_formula φ) (KT4formula_to_formula ψ))
  | transformKT4_toT_axT  : forall φ,     KT4_axiom_to_KTaxiom (KT4axT φ)       (axT   (KT4formula_to_formula φ)).

  Inductive KT4_axiom_to_K4axiom: KT4axiom -> axiom -> Prop :=
  | transformKT4_to4_ax1  : forall φ ψ,   KT4_axiom_to_K4axiom (KT4ax1 φ ψ)     (ax1   (KT4formula_to_formula φ) (KT4formula_to_formula ψ))
  | transformKT4_to4_ax2  : forall φ ψ Ɣ, KT4_axiom_to_K4axiom (KT4ax2 φ ψ Ɣ)   (ax2   (KT4formula_to_formula φ) (KT4formula_to_formula ψ) (KT4formula_to_formula Ɣ))
  | transformKT4_to4_ax3  : forall φ ψ,   KT4_axiom_to_K4axiom (KT4ax3 φ ψ)     (ax3   (KT4formula_to_formula φ) (KT4formula_to_formula ψ))
  | transformKT4_to4_ax4  : forall φ ψ,   KT4_axiom_to_K4axiom (KT4ax4 φ ψ)     (ax4   (KT4formula_to_formula φ) (KT4formula_to_formula ψ))
  | transformKT4_to4_ax5  : forall φ ψ,   KT4_axiom_to_K4axiom (KT4ax5 φ ψ)     (ax5   (KT4formula_to_formula φ) (KT4formula_to_formula ψ))
  | transformKT4_to4_ax6  : forall φ ψ,   KT4_axiom_to_K4axiom (KT4ax6 φ ψ)     (ax6   (KT4formula_to_formula φ) (KT4formula_to_formula ψ))
  | transformKT4_to4_ax7  : forall φ ψ,   KT4_axiom_to_K4axiom (KT4ax7 φ ψ)     (ax7   (KT4formula_to_formula φ) (KT4formula_to_formula ψ))
  | transformKT4_to4_ax8  : forall φ ψ,   KT4_axiom_to_K4axiom (KT4ax8 φ ψ)     (ax8   (KT4formula_to_formula φ) (KT4formula_to_formula ψ))
  | transformKT4_to4_ax9  : forall φ ψ Ɣ, KT4_axiom_to_K4axiom (KT4ax9 φ ψ Ɣ)   (ax9   (KT4formula_to_formula φ) (KT4formula_to_formula ψ) (KT4formula_to_formula Ɣ))
  | transformKT4_to4_ax10 : forall φ ψ,   KT4_axiom_to_K4axiom (KT4ax10 φ ψ)    (ax10  (KT4formula_to_formula φ) (KT4formula_to_formula ψ))
  | transformKT4_to4_axK  : forall φ ψ,   KT4_axiom_to_K4axiom (KT4axK_4 φ ψ)   (axK   (KT4formula_to_formula φ) (KT4formula_to_formula ψ))
  | transformKT4_to4_axPos: forall φ ψ,   KT4_axiom_to_K4axiom (KT4axPos_4 φ ψ) (axPos (KT4formula_to_formula φ) (KT4formula_to_formula ψ))
  | transformKT4_to4_axK4 : forall φ,     KT4_axiom_to_K4axiom (KT4axK4 φ)      (axK4  (KT4formula_to_formula φ)).

Lemma KT4_axiom_to_KTaxiom_sound: forall a b φ,
  KT4instantiate a = φ -> KT4_axiom_to_KTaxiom a b ->
    instantiate b = (KT4formula_to_formula φ).
Proof.
  intros a b φ H0 H1.
  destruct a; simpl in *;
  repeat (inversion H1; subst; reflexivity).
Qed.

Lemma KT4_axiom_to_K4axiom_sound: forall a b φ,
  KT4instantiate a = φ -> KT4_axiom_to_K4axiom a b ->
    instantiate b = (KT4formula_to_formula φ).
Proof.
  intros a b φ H0 H1.
  destruct a; simpl in *;
  repeat (inversion H1; subst; reflexivity).
Qed.

Inductive anyFrame (F: Frame): Prop :=
  anyFrameMk: anyFrame F.

Inductive anyKT4Frame (F: KT4Frame): Prop :=
  anyKT4FrameMk: anyKT4Frame F.

(*
  To show that KT4 is sound, we must first show that both KT and K4 are sound
  As there is no "soundness" property in the core library, it will be stated here
*)

Require Import Soundness.

Definition relative_soundness (A: axiom -> Prop) (R: Frame -> Prop) :=
  forall Γ φ, (A; Γ |-- φ) -> forall F V, R F -> entails (Build_Model F V) Γ φ.

Definition relative_KT4soundness (A: KT4axiom -> Prop) (R: KT4Frame -> Prop) :=
  forall Γ φ, (A; Γ |--t4 φ) -> forall F V, R F -> KT4entails (Build_KT4Model F V) Γ φ.

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

(* Completude? *)