Require Import List Notations Modal_Library.
Export ListNotations.

(*** Core File of the Multimodal / Fusion Part of the Library ***)

(*
  Definition of multimodal formulas - these are very similar to normal formula, but the modalities
  have a nat parameter to indicate which modality it is, so these formulas do not only have Box and Dia
  as modalities, but instead have Box 0, Box 1, ..., Dia 0, Dia 1,... as modalities
  This *could* be a problematic definition if there is no restriction on which kinds of formulas
  can be evaluated, e.g. if we are dealing with a language that has 2 modalities of each
  kind (Box/Dia 0 and Box/Dia 1), it would be senseless to be able to create and reason about
  a formula that has Box 5, so, to avoid these problems, on the definitions of valuation of formulas and
  deductions there is a restriction on which kinds of formulas can be evaluated/deduced, the ones whose
  index is less than the amout of modalities on the system that is being treated
*)

Inductive MMformula: Set :=
  | MMLit    : nat           -> MMformula
  | MMNeg    : MMformula     -> MMformula
  | MMBox    : nat (*index*) -> MMformula -> MMformula
  | MMDia    : nat (*index*) -> MMformula -> MMformula
  | MMAnd    : MMformula     -> MMformula -> MMformula
  | MMOr     : MMformula     -> MMformula -> MMformula
  | MMImplies: MMformula     -> MMformula -> MMformula.

Declare Custom Entry multi_modal.
Declare Scope multi_modal_scope.

(*
  Notation for formulas
  Using the same delimiters here as was used on the PoC, due to laziness
*)
Notation "x" := x
  (in custom multi_modal at level 0, x ident).
Notation "( x )" := x
  (in custom multi_modal, x at level 90).
Notation "<! m !>" := m
  (at level 0, m custom multi_modal at level 99, format "<!  m  !>").
Notation " # p " := (MMLit p)
  (in custom multi_modal at level 2, no associativity, p constr at level 1, format "# p").
Notation " p -> q " := (MMImplies p q)
  (in custom multi_modal at level 13, right associativity).
Notation " p \/ q " := (MMOr p q)
  (in custom multi_modal at level 12, left associativity).
Notation " p /\ q " := (MMAnd p q)
  (in custom multi_modal at level 11, left associativity).
Notation " ~ p " := (MMNeg p)
  (in custom multi_modal at level 9, right associativity, format "~ p").
Notation " '[' i ']' p " := (MMBox i p)
  (in custom multi_modal at level 9, i constr, p custom multi_modal,
    right associativity, format "[ i ] p").
Notation " '<<' i '>>' p " := (MMDia i p)
  (in custom multi_modal at level 0, i constr, p custom multi_modal,
    right associativity, format "<< i >> p").
    (*using < i > here would conflit with the notation for lt/gt*)

(** Frames and Models **)

Section MultiModal.

  Variable Modalities: nat.
  Hypothesis minimum_modalities: Modalities > 1.
  (*
    A variable that defines how many modalities would used on the multimodal system
    and a hypothesis that asserts that there is more than 1 modality in the multimodal system
      (a modal system that has no modalities is not a modal system, and a multimodal system
      that has only one modality is not multimodal)
  *)

  (*
    A multimodal frame is made up of a set of worlds and a set of N accessiblity relations,
    where N is the amount of modalities in the language
    Multimodal frames are also called nFrames (1Frames, 2Frames, etc.)
  *)
  Record nFrame: Type :={
    nW      : Set;                      (* Set of Worlds *)
    nR      : list (nW -> nW -> Prop);  (* Set of acc relations *)
    rel_cond: (length nR) = Modalities; (* restriction that there are as many relations as there are modalities *)
  }.

  (*
    A Multimodal model is a model built with a multimodal frame
  *)
  Record nModel: Type := {
    nF: nFrame;
    nV: nat -> (nW nF) -> Prop
  }.

  Definition dummyRel (X: Set) := (fun x: X => (fun y: X => False)).
  Variable dummyFrame: Frame.
  (* Variable dummyModel: Model. *)
  (*
    Dummy variables that are need by the nth function
    These will never actually be used, but are needed as a default return value by nth
  *)

  (*
    Some facts about those variables
    TODO: Verificar se isso aqui está correto

    Hypothesis dummyRel_not_In:   forall X lR, ~ In (dummyRel X) lR.
    Hypothesis dummyFrame_not_In: forall lF, ~ In dummyFrame lF.
    Hypothesis dummyModel_not_In: forall lM, ~ In dummyModel lM.
  *)

  (*
    Some useful definitions to clean up the code
  *)
  Definition get_rel (X: Set) (lR: list (X -> X -> Prop)) (index: nat) :=
      nth index lR (dummyRel X).
  (* Definition get_frame (lF: list Frame) (index: nat): Frame := nth index lF dummyFrame.
  Definition get_model (lM: list Model) (index: nat): Model := nth index lM dummyModel. *)

  Lemma get_rel_sound: forall X lR n,
    length lR < n -> (get_rel X lR n) = (dummyRel X).
  Proof.
    induction lR;
    intros n H; [destruct n; reflexivity |]. (*solves first subgoal*)
    simpl in H; destruct n;
    simpl; [inversion H |]. (*solves first subsubgoal*)
    unfold get_rel in *; simpl in *;
    apply IHlR; auto with arith.
  Qed.

  Lemma get_rel_sound2: forall X lR n,
    ~ In (dummyRel X) lR -> n < length lR -> (get_rel X lR n) <> (dummyRel X).
  Proof.
    intros X lR n H0 H1 H2; destruct H0.
    apply nth_error_In with (n:=n); unfold get_rel in H2.
    rewrite <- H2; eapply nth_error_nth' in H1.
    eassumption.
  Qed.

  (* Lemma get_frame_sound: forall lF n,
    length lF < n -> (get_frame lF n) = dummyFrame.
  Proof.
    induction lF;
    intros n H; [destruct n; reflexivity |]. (*solves first subgoal*)
    simpl in H; destruct n;
    simpl; [inversion H |]. (*solves first subsubgoal*)
    unfold get_frame in *; simpl in *;
    apply IHlF; auto with arith.
  Qed.

  Lemma get_frame_sound2: forall lF n,
    ~ In dummyFrame lF -> n < length lF -> (get_frame lF n) <> dummyFrame.
  Proof.
    intros lF n H0 H1 H2; destruct H0.
    apply nth_error_In with (n:=n); unfold get_frame in H2.
    rewrite <- H2; eapply nth_error_nth' in H1.
    eassumption.
  Qed.

  Lemma get_model_sound: forall lM n,
    length lM < n -> (get_model lM n) = dummyModel.
  Proof.
    induction lM;
    intros n H; [destruct n; reflexivity |]. (*solves first subgoal*)
    simpl in H; destruct n;
    simpl; [inversion H |]. (*solves first subsubgoal*)
    unfold get_model in *; simpl in *;
    apply IHlM; auto with arith.
  Qed.

  Lemma get_model_sound2: forall lM n,
    ~ In dummyModel lM -> n < length lM -> (get_model lM n) <> dummyModel.
  Proof.
    intros lF n H0 H1 H2; destruct H0.
    apply nth_error_In with (n:=n); unfold get_model in H2.
    rewrite <- H2; eapply nth_error_nth' in H1.
    eassumption.
  Qed. *)

  (*
    Defining a function that transforms a nFrame into several Frame's
  *)

  Definition split_frame (F: nFrame): list Frame:=
    match F with
      | Build_nFrame nW nR _ => map (Build_Frame nW) nR
    end.

  Definition nFrame_to_Frame (F: nFrame) (index: nat): Frame :=
    match F with
      | Build_nFrame nW nR _ => Build_Frame nW (get_rel nW nR index)
    end.

  Definition same_worlds (F1 F2: Frame): Prop := W F1 = W F2.

  Fixpoint same_worlds_recursive (l : list Frame) (F: Frame): Prop :=
    match l with
    | [ ]    => True
    | h :: t => same_worlds h F /\ same_worlds_recursive t F
    end.

  Definition same_world_frame_list (LF: list Frame): Prop := same_worlds_recursive LF (hd dummyFrame LF).

(*  Definition rel_from_frame_list (X: Set) (l : list Frame): list (X -> X -> Prop):
    match l with
    | [ ]      => [ ]
    | F :: t   =>
      match F with
      | Build_Frame X R => R :: (rel_from_frame_list X t)
      end
    end.

  Fail Inductive join_frames: Type:
    join_frames_mk: forall LF LP, length LF >= 2 -> length LF = length LP ->
    same_world_frame_list LF ->
    Build_nFrame W [R F1; R F2] LP. *)

  (*
    Defining a function that transforms a nModel into several Model's
  *)

  (*Fixpoint build_model_from_list (M: nModel) (lF: list Frame): list Model:=
    match M with
    | Build_nModel (Build_nFrame nW nR _) V =>
        match lF with
          | [ ]     => [ ]
          | f :: tf =>
            match f with
            | Build_Frame nW _ => Build_Model (Build_Frame nW _) V :: build_model_from_list tf V
            end
        end
    end.

  Definition split_model (M: nModel): list Model:=
    match M with
      | Build_nModel (Build_nFrame nW nR _ as F) V => map (Build_Model _ V) (split_frame F)
    end.*)

  (* Sinto que isso está errado, verificar *)
  Fixpoint split_model (M: nModel) (index: nat): list Model :=
    match M, index with
      | _                                    , O   => [ ]
      | Build_nModel (Build_nFrame nW nR _) V, S m => [Build_Model (Build_Frame nW (get_rel nW nR m)) V] ++ split_model M m
    end.

  Definition nModel_to_list_Model (M: nModel): list Model := split_model M Modalities.

  Definition nModel_to_Model (M: nModel) (index: nat): Model :=
    match M with
      | Build_nModel (Build_nFrame nW nR _) V => Build_Model (Build_Frame nW (get_rel nW nR index)) V
    end.

  (*
    Small recursive function that checks wether or not a given formula can be deduced
    (by syntatical ou semantical means) in a given modal system
    By "can be deduced" it is meant that the index of it's greatest modality is less than the
    maximum allowed number of modalities in a system
    Simply, if the index of each MMBox or MMDia is less than the Variable Modalities
  *)
  Fixpoint deducible_formula (φ: MMformula): Prop :=
    match φ with
    | MMLit _                              => True
    | MMNeg ψ                              => deducible_formula ψ
    | MMBox x ψ | MMDia x ψ                => x < Modalities /\ deducible_formula ψ
    | MMAnd ψ Ɣ | MMOr ψ Ɣ | MMImplies ψ Ɣ => deducible_formula ψ /\ deducible_formula Ɣ
    end.
  (*
    Function that evaluates formulas in a given world, behaves just like the one in the base library,
    except that formulas that cannot exist in a given system (i.e. whose index for MMBox or MMDia is
    greater than the value of the variable Modalities) are always evaluated as False
  *)
  Fixpoint valuation (M: nModel) (w: nW (nF M)) (φ: MMformula): Prop:=
    match φ with
    | MMLit     x   => nV M x w
    | MMNeg     ψ   => deducible_formula ψ               -> (~ valuation M w ψ)
    | MMBox     x ψ => deducible_formula (MMBox x ψ)     -> (forall w', (get_rel (nW (nF M)) (nR (nF M)) x) w w' -> valuation M w' ψ)
    | MMDia     x ψ => deducible_formula (MMDia x ψ)     -> (exists w', (get_rel (nW (nF M)) (nR (nF M)) x) w w' /\ valuation M w' ψ)
    | MMAnd     ψ Ɣ => deducible_formula (MMAnd ψ Ɣ)     -> (valuation M w ψ /\ valuation M w Ɣ)
    | MMOr      ψ Ɣ => deducible_formula (MMOr ψ Ɣ)      -> (valuation M w ψ \/ valuation M w Ɣ)
    | MMImplies ψ Ɣ => deducible_formula (MMImplies ψ Ɣ) -> (valuation M w ψ -> valuation M w Ɣ)
    end.
  Notation "X ; w ||-M φ" := (valuation X w φ) (at level 110, right associativity).

  Definition MMtheory := list MMformula. (* Multimodal theories are finite lists of MMformula's *)

  (*
    Same idea as deductibility as before, but for theories
  *)
  Fixpoint deducible_theory (Γ: MMtheory): Prop :=
    match Γ with
    | [ ]    => True
    | h :: t => (deducible_formula h) /\ (deducible_theory t)
    end.

  Lemma deducible_theory_union: forall Γ1 Γ2,
    deducible_theory Γ1 /\ deducible_theory Γ2 <->
      deducible_theory (Γ1 ++ Γ2).
  Proof.
    split; intros H0; induction Γ1; try destruct H0 as [H' H0];
    simpl in H0 |-*; try auto; try destruct H';
    repeat split; try auto; apply IHΓ1 in H0;
    destruct H0; assumption.
  Qed.

  Lemma deducible_formula_in_deducible_theory: forall Γ φ,
    In φ Γ -> deducible_theory Γ -> deducible_formula φ.
  Proof.
    intros Γ φ H0 H1; induction Γ; [inversion H0 |];
    destruct H1; destruct H0;
    [subst; auto | apply IHΓ in H0; auto].
  Qed.

  (*
    Translation function that transforms formulas from the base library to multimodal formulas
    of a given modality, defined by the argument 'index'
  *)
  Fixpoint formula_to_MMformula (φ: formula) (index: nat): MMformula :=
    match φ with
    | Lit     x    => MMLit x
    | Neg     ψ    => MMNeg       (formula_to_MMformula ψ index)
    | Dia     ψ    => MMDia index (formula_to_MMformula ψ index)
    | Box     ψ    => MMBox index (formula_to_MMformula ψ index)
    | And     ψ Ɣ  => MMAnd       (formula_to_MMformula ψ index) (formula_to_MMformula Ɣ index)
    | Or      ψ Ɣ  => MMOr        (formula_to_MMformula ψ index) (formula_to_MMformula Ɣ index)
    | Implies ψ Ɣ  => MMImplies   (formula_to_MMformula ψ index) (formula_to_MMformula Ɣ index)
    end.

  (*
    Proof of injectivity of the above function
  *)
  Theorem formula_to_MMformula_injective: forall φ1 φ2 n,
    formula_to_MMformula φ1 n = formula_to_MMformula φ2 n ->
    φ1 = φ2.
  Proof.
    intros φ1 φ2 n; generalize dependent φ2;
    induction φ1; intros φ2 H0; destruct φ2;
    inversion H0; try auto;
    repeat(rewrite IHφ1 with φ2; auto);
    repeat(rewrite IHφ1_1 with φ2_1; try assumption; rewrite IHφ1_2 with φ2_2; easy).
  Qed.

  (*
    Translation function for theories, works the same as the previous one
  *)
  Fixpoint theory_to_MMtheory (Γ: theory) (index: nat): MMtheory :=
    match Γ with
    | [ ]    => [ ]
    | h :: t => (formula_to_MMformula h index) :: (theory_to_MMtheory t index)
    end.

  (*
    Forgetful translation function from multimodal formulas to formulas from the
    base library
  *)
  Fixpoint MMformula_to_formula (φ: MMformula): formula :=
    match φ with
    | MMLit     x   => Lit x
    | MMDia     _ ψ => Dia     (MMformula_to_formula ψ)
    | MMBox     _ ψ => Box     (MMformula_to_formula ψ)
    | MMNeg     ψ   => Neg     (MMformula_to_formula ψ)
    | MMAnd     ψ Ɣ => And     (MMformula_to_formula ψ) (MMformula_to_formula Ɣ)
    | MMOr      ψ Ɣ => Or      (MMformula_to_formula ψ) (MMformula_to_formula Ɣ)
    | MMImplies ψ Ɣ => Implies (MMformula_to_formula ψ) (MMformula_to_formula Ɣ)
    end.

  (*
    Same as before, but for theories
  *)
  Fixpoint MMtheory_to_theory (Γ: MMtheory): theory :=
    match Γ with
    | [ ]    => [ ]
    | h :: t => (MMformula_to_formula h) :: (MMtheory_to_theory t)
    end.

  (*
    Proof that translating formula's -> MMformula's -> formula's yields back the original
    formula
  *)
  Theorem MMformula_to_formula_reversible:
    forall φ n, MMformula_to_formula (formula_to_MMformula φ n) = φ.
  Proof.
    intros φ n; induction φ;
    try reflexivity; (*Literal*)
    try (simpl; rewrite IHφ; reflexivity); (*Unary connectives*)
    try (simpl; rewrite IHφ1; rewrite IHφ2; reflexivity). (*Binary connectives*)
  Qed.

  (*
    Same as above, but for theories
  *)
  Theorem MMtheory_to_theory_reversible:
    forall Γ n, MMtheory_to_theory (theory_to_MMtheory Γ n) = Γ.
  Proof.
    intros Γ n; induction Γ;
    try reflexivity; simpl;
    rewrite MMformula_to_formula_reversible, IHΓ;
    reflexivity.
  Qed.

  (*
    Definition of validity in a model for formulas
    A formula is said valid in a model if it is true in all worlds of that model
  *)
  Definition validity_in_model (M: nModel) (φ: MMformula) :=
    forall w, valuation M w φ.
  Notation "X |=M φ" := (validity_in_model X φ) (at level 110, right associativity).

  (*
    Validity in a model for theories
  *)
  Fixpoint theory_is_valid (M: nModel) (Γ: MMtheory) :=
    match Γ with
    | [ ]    => True
    | h :: t => (validity_in_model M h) /\ (theory_is_valid M t)
    end.

  (*
    Definition of semantic entailment - same as in the base library
    Note that it requires a proof that the theory is deducible in the system
    (but not the formula, as undeducible formulas will always be False, so the entailmente
    won't be valid)
  *)
  Definition entailment (M: nModel) (Γ: MMtheory) (φ: MMformula) :=
    deducible_theory Γ -> theory_is_valid M Γ -> validity_in_model M φ.

  (*
    Definition of subsets of lists of arbritrary types
  *)
  Definition subset {T: Type} (L1 L2: list T): Prop :=
    forall x, In x L1 -> In x L2.

  (*
    Definition of semantic entailment in all models
  *)
  Definition semantic_entailment (Γ: MMtheory) (φ: MMformula) :=
    forall M, entailment M Γ φ.
  Notation "Γ ||=M φ" := (semantic_entailment Γ φ) (at level 110, no associativity).

  (*
    Definition of equivalence of MMformula's
  *)
  Definition MMequivalence (φ ψ: MMformula) :=
    semantic_entailment [φ] ψ /\ semantic_entailment [ψ] φ.

  (*
    Definition of multimodal axioms, pretty much the same as in the base library, but with
    and additional nat argument for the axioms that have modalities
  *)
  Inductive MMaxiom : Set :=
    | MMax1  : MMformula -> MMformula -> MMaxiom
    | MMax2  : MMformula -> MMformula -> MMformula -> MMaxiom
    | MMax3  : MMformula -> MMformula -> MMaxiom
    | MMax4  : MMformula -> MMformula -> MMaxiom
    | MMax5  : MMformula -> MMformula -> MMaxiom
    | MMax6  : MMformula -> MMformula -> MMaxiom
    | MMax7  : MMformula -> MMformula -> MMaxiom
    | MMax8  : MMformula -> MMformula -> MMaxiom
    | MMax9  : MMformula -> MMformula -> MMformula -> MMaxiom
    | MMax10 : MMformula -> MMformula -> MMaxiom
    | MMaxK  : nat       -> MMformula -> MMformula -> MMaxiom
    | MMaxPos: nat       -> MMformula -> MMformula -> MMaxiom
    | MMaxT  : nat       -> MMformula -> MMaxiom
    | MMaxB  : nat       -> MMformula -> MMaxiom
    | MMaxK4 : nat       -> MMformula -> MMaxiom
    | MMaxD  : nat       -> MMformula -> MMaxiom
    | MMaxK5 : nat       -> MMformula -> MMaxiom
    | MMaxGL : nat       -> MMformula -> MMaxiom.

  (*
    Definition of a function that, given an axioms, returns it's corresponding formula,
    with appropriate modalities
  *)
  Definition MMinstance (a: MMaxiom): MMformula :=
    match a with
    | MMax1   φ ψ   => <! φ -> (ψ -> φ) !>
    | MMax2   φ ψ Ɣ => <! (φ -> (ψ -> Ɣ)) -> ((φ -> ψ) -> (φ -> Ɣ)) !>
    | MMax3   φ ψ   => <! (~ψ -> ~φ) -> (φ -> ψ) !>
    | MMax4   φ ψ   => <! φ -> (ψ -> (φ /\ ψ)) !>
    | MMax5   φ ψ   => <! (φ /\ ψ) -> φ !>
    | MMax6   φ ψ   => <! (φ /\ ψ) -> ψ !>
    | MMax7   φ ψ   => <! φ -> (φ \/ ψ) !>
    | MMax8   φ ψ   => <! ψ -> (φ \/ ψ) !>
    | MMax9   φ ψ Ɣ => <! (φ -> Ɣ) -> ((ψ -> Ɣ) -> ((φ \/ ψ) -> Ɣ)) !>
    | MMax10  φ ψ   => <! ~~φ -> φ !>
    | MMaxK   i φ ψ => <! [i](φ -> ψ) -> ([i] φ -> [i] ψ) !>
    | MMaxPos i φ ψ => <! <<i>> (φ \/ ψ) -> (<<i>> φ \/ <<i>> ψ) !>
    | MMaxT   i φ   => <! [i]φ -> φ !>
    | MMaxB   i φ   => <! φ -> [i] <<i>> φ !>
    | MMaxK4  i φ   => <! [i] φ -> [i] [i] φ !>
    | MMaxD   i φ   => <! [i] φ -> <<i>> φ !>
    | MMaxK5  i φ   => <! <<i>> φ -> [i] <<i>> φ !>
    | MMaxGL  i φ   => <! [i]([i]φ -> φ) -> [i]φ !>
    end.

  (*
    Definition of the deductive system of multimodal systems, same as in the base library,
    but with the appropriate changes to assert that no formula that has a unintended modality
    be derivable
    The Notation was defined together with the Inductive relation itself, to simplify
    reading and the definitions
  *)
  Reserved Notation "A ; G |--M p" (at level 110, no associativity).
  Inductive MMdeduction (A: MMaxiom -> Prop): MMtheory -> MMformula -> Prop :=
    (* Premise. *)
    | MMPrem: forall (Γ: MMtheory) (φ: MMformula) (i: nat),
                     (deducible_theory Γ) -> (nth_error Γ i = Some φ) -> A; Γ |--M φ
    (* Axiom. *)
    | MMAx: forall (Γ: MMtheory) (a: MMaxiom) (φ: MMformula),
                   A a -> (deducible_formula φ) -> MMinstance a = φ ->
                   (deducible_theory Γ) -> A; Γ |--M φ
    (* Modus Ponens. *)
    | MMMp: forall (Γ: MMtheory) (φ ψ: MMformula),
                   (deducible_formula <!φ -> ψ!>) -> (deducible_theory Γ) ->
                   (A; Γ |--M (<!φ -> ψ!>)) -> (A; Γ |--M φ) -> (A; Γ |--M ψ)
    (* Necessitation. *)
    | MMNec: forall (Γ: MMtheory) (φ: MMformula) (i: nat),
                    i < Modalities -> (deducible_formula φ) -> (deducible_theory Γ) ->
                    (A; Γ |--M φ) -> (A; Γ |--M <![i]φ!>)
  where "A ; G |--M p" := (MMdeduction A G p).

  Lemma deduction_implies_deductibility: forall A Γ φ,
    (A; Γ |--M φ) -> deducible_formula φ.
  Proof.
    intros A Γ φ H0.
    induction H0; try firstorder;
    apply nth_error_In in H0;
    eapply deducible_formula_in_deducible_theory in H0;
    eassumption.
  Qed.

  (*
    Multimodal axiomatic systems
    Each system is indexed by a list of nat, which are the indexes of the modalities of that system
    So we may have e.g. Kn [0; 1; 2] to represent that the system Kn (n-modal K) has modalities 0, 1 and 2
    This is most useful for defining joins of axiomatic systems, as we may have something e.g.
      Kn [0; 2] Tn [1; 3] to define the system resulting of the join of Kn and Tn and has modalities 0, 1, 2 and 3
    To garantee that indexes are valid, we add the condition of that forall i in the list of indexes,
      every instance of an axiom with modalities with index i are deducible
    To define a multimodal system that has all modalities availible, simply define S (seq 0 Modalities), where S is
      your system in question
  *)
  Inductive Kn (index: list nat): MMaxiom -> Prop :=
    | Kn_ax1:   forall φ ψ,   (deducible_formula (MMinstance (MMax1 φ ψ)))      -> Kn index (MMax1   φ ψ)
    | Kn_ax2:   forall φ ψ Ɣ, (deducible_formula (MMinstance (MMax2 φ ψ Ɣ)))    -> Kn index (MMax2   φ ψ Ɣ)
    | Kn_ax3:   forall φ ψ,   (deducible_formula (MMinstance (MMax3 φ ψ)))      -> Kn index (MMax3   φ ψ)
    | Kn_ax4:   forall φ ψ,   (deducible_formula (MMinstance (MMax4 φ ψ)))      -> Kn index (MMax4   φ ψ)
    | Kn_ax5:   forall φ ψ,   (deducible_formula (MMinstance (MMax5 φ ψ)))      -> Kn index (MMax5   φ ψ)
    | Kn_ax6:   forall φ ψ,   (deducible_formula (MMinstance (MMax6 φ ψ)))      -> Kn index (MMax6   φ ψ)
    | Kn_ax7:   forall φ ψ,   (deducible_formula (MMinstance (MMax7 φ ψ)))      -> Kn index (MMax7   φ ψ)
    | Kn_ax8:   forall φ ψ,   (deducible_formula (MMinstance (MMax8 φ ψ)))      -> Kn index (MMax8   φ ψ)
    | Kn_ax9:   forall φ ψ Ɣ, (deducible_formula (MMinstance (MMax9 φ ψ Ɣ)))    -> Kn index (MMax9   φ ψ Ɣ)
    | Kn_ax10:  forall φ ψ,   (deducible_formula (MMinstance (MMax10 φ ψ)))     -> Kn index (MMax10  φ ψ)
    | Kn_axK:   forall i φ ψ, In i index ->
                               (deducible_formula (MMinstance (MMaxK i φ ψ)))   -> Kn index (MMaxK   i φ ψ)
    | Kn_axPos: forall i φ ψ, In i index ->
                               (deducible_formula (MMinstance (MMaxPos i φ ψ))) -> Kn index (MMaxPos i φ ψ).

  Inductive Tn (index: list nat): MMaxiom -> Prop :=
    | Tn_Kn : forall φ, Kn index φ -> Tn index φ
    | Tn_axT: forall i φ, In i index -> (deducible_formula (MMinstance (MMaxT i φ))) -> Tn index (MMaxT i φ).

  Inductive Bn (index: list nat): MMaxiom -> Prop :=
    | Bn_Tn : forall φ, Tn index φ -> Bn index φ
    | Bn_axB: forall i φ, In i index -> (deducible_formula (MMinstance (MMaxB i φ))) -> Bn index (MMaxB i φ).

  Inductive K4n (index: list nat): MMaxiom -> Prop :=
    | K4n_Kn : forall φ, Kn index φ -> K4n index φ
    | K4n_axK4: forall i φ, In i index -> (deducible_formula (MMinstance (MMaxK4 i φ))) -> K4n index (MMaxK4 i φ).

  Inductive Dn (index: list nat): MMaxiom -> Prop :=
    | Dn_Kn : forall φ, Kn index φ -> Dn index φ
    | Dn_axD: forall i φ, In i index -> (deducible_formula (MMinstance (MMaxD i φ))) -> Dn index (MMaxD i φ).

  Inductive K5n (index: list nat): MMaxiom -> Prop :=
    | K5n_Kn : forall φ, Kn index φ -> K5n index φ
    | K5n_axK5: forall i φ, In i index -> (deducible_formula (MMinstance (MMaxK5 i φ))) -> K5n index (MMaxK5 i φ).

  Inductive S4n (index: list nat): MMaxiom -> Prop :=
    | S4n_Tn : forall φ, Tn index φ -> S4n index φ
    | S4n_axK4: forall i φ, In i index -> (deducible_formula (MMinstance (MMaxK4 i φ))) -> S4n index (MMaxK4 i φ).

  Inductive S5n (index: list nat): MMaxiom -> Prop :=
    | S5n_Bn : forall φ, Bn  index φ -> S5n index φ
    | S5n_S4n: forall φ, S4n index φ -> S5n index φ.

  Inductive S5n_alt (index: list nat): MMaxiom -> Prop :=
    | S5n_alt_Tn : forall φ, Tn  index φ -> S5n_alt index φ
    | S5n_alt_K5n: forall φ, K5n index φ -> S5n_alt index φ.

  Inductive GLn (index: list nat): MMaxiom -> Prop :=
    | GLn_K4n : forall φ, K4n index φ -> GLn index φ
    | GLn_axGL: forall i φ, In i index -> (deducible_formula (MMinstance (MMaxGL i φ))) -> GLn index (MMaxGL i φ).

  Require Import Deductive_System. (* to define translations, importing earlier causes weird errors *)

  (*
    Function that translates axioms from the base library to the multimodal system, like the previous
    translation functions
    As before, this is indexed by a nat, that indicates which modality the translated formulas
    will have
  *)
  Inductive axiom_to_MMaxiom (index: nat): axiom -> MMaxiom -> Prop :=
    | transform_ax1  : forall φ ψ,   axiom_to_MMaxiom index (ax1 φ ψ)   (MMax1         (formula_to_MMformula φ index) (formula_to_MMformula ψ index))
    | transform_ax2  : forall φ ψ Ɣ, axiom_to_MMaxiom index (ax2 φ ψ Ɣ) (MMax2         (formula_to_MMformula φ index) (formula_to_MMformula ψ index) (formula_to_MMformula Ɣ index))
    | transform_ax3  : forall φ ψ,   axiom_to_MMaxiom index (ax3 φ ψ)   (MMax3         (formula_to_MMformula φ index) (formula_to_MMformula ψ index))
    | transform_ax4  : forall φ ψ,   axiom_to_MMaxiom index (ax4 φ ψ)   (MMax4         (formula_to_MMformula φ index) (formula_to_MMformula ψ index))
    | transform_ax5  : forall φ ψ,   axiom_to_MMaxiom index (ax5 φ ψ)   (MMax5         (formula_to_MMformula φ index) (formula_to_MMformula ψ index))
    | transform_ax6  : forall φ ψ,   axiom_to_MMaxiom index (ax6 φ ψ)   (MMax6         (formula_to_MMformula φ index) (formula_to_MMformula ψ index))
    | transform_ax7  : forall φ ψ,   axiom_to_MMaxiom index (ax7 φ ψ)   (MMax7         (formula_to_MMformula φ index) (formula_to_MMformula ψ index))
    | transform_ax8  : forall φ ψ,   axiom_to_MMaxiom index (ax8 φ ψ)   (MMax8         (formula_to_MMformula φ index) (formula_to_MMformula ψ index))
    | transform_ax9  : forall φ ψ Ɣ, axiom_to_MMaxiom index (ax9 φ ψ Ɣ) (MMax9         (formula_to_MMformula φ index) (formula_to_MMformula ψ index) (formula_to_MMformula Ɣ index))
    | transform_ax10 : forall φ ψ,   axiom_to_MMaxiom index (ax10 φ ψ)  (MMax10        (formula_to_MMformula φ index) (formula_to_MMformula ψ index))
    | transform_axK  : forall φ ψ,   axiom_to_MMaxiom index (axK φ ψ)   (MMaxK   index (formula_to_MMformula φ index) (formula_to_MMformula ψ index))
    | transform_axPos: forall φ ψ,   axiom_to_MMaxiom index (axPos φ ψ) (MMaxPos index (formula_to_MMformula φ index) (formula_to_MMformula ψ index))
    | transform_axT  : forall φ,     axiom_to_MMaxiom index (axT φ)     (MMaxT   index (formula_to_MMformula φ index))
    | transform_axB  : forall φ,     axiom_to_MMaxiom index (axB φ)     (MMaxB   index (formula_to_MMformula φ index))
    | transform_axD  : forall φ,     axiom_to_MMaxiom index (axD φ)     (MMaxD   index (formula_to_MMformula φ index))
    | transform_axK4 : forall φ,     axiom_to_MMaxiom index (axK4 φ)    (MMaxK4  index (formula_to_MMformula φ index))
    | transform_axK5 : forall φ,     axiom_to_MMaxiom index (axK5 φ)    (MMaxK5  index (formula_to_MMformula φ index))
    | transform_axGL : forall φ,     axiom_to_MMaxiom index (axGL φ)    (MMaxGL  index (formula_to_MMformula φ index)).

  (*
    Inductive definition of the join of two axiomatic systems
      be it two modal, one modal one multimodal or two multimodal
  *)
  Inductive join (S1 S2: axiom -> Prop) (index1 index2: nat): list nat -> MMaxiom -> Prop :=
    | derivable_S1: forall a b, S1 a -> axiom_to_MMaxiom index1 a b ->
      deducible_formula (MMinstance b) -> join S1 S2 index1 index2 (index1 :: index2 :: nil) b
    | derivable_S2: forall a b, S2 a -> axiom_to_MMaxiom index2 a b ->
      deducible_formula (MMinstance b) -> join S1 S2 index1 index2 (index1 :: index2 :: nil) b.

  Inductive join_one (S1: axiom -> Prop) (S2: list nat -> MMaxiom -> Prop) (index1: nat) (index2: list nat): list nat -> MMaxiom -> Prop :=
    | derivable_S1_one: forall a b, S1 a -> axiom_to_MMaxiom index1 a b ->
      deducible_formula (MMinstance b) -> join_one S1 S2 index1 index2 (index1 :: index2) b
    | derivable_S2_one: forall a, S2 index2 a -> join_one S1 S2 index1 index2 (index1 :: index2) a.

  Inductive join_two (S1 S2: list nat -> MMaxiom -> Prop) (index1 index2: list nat): list nat -> MMaxiom -> Prop :=
    | derivable_S1_two: forall a, S1 index1 a -> join_two S1 S2 index1 index2 (index1 ++ index2) a
    | derivable_S2_two: forall a, S2 index2 a -> join_two S1 S2 index1 index2 (index1 ++ index2) a.

  (*
    Proof of soundness of the previous definition
  *)
  Lemma axiom_to_MMaxiom_sound: forall a b φ n,
    instantiate a = φ -> axiom_to_MMaxiom n a b ->
    MMinstance b = (formula_to_MMformula φ n).
  Proof.
    intros a b φ n H0 H1;
    destruct a; simpl in *;
    repeat(inversion H1; subst; reflexivity).
  Qed.

  (*
    Function that translates multimodal axioms to axioms from the base library
  *)
  Inductive MMaxiom_to_axiom: MMaxiom -> axiom -> Prop :=
    | transform_MMax1  : forall φ ψ,   MMaxiom_to_axiom (MMax1 φ ψ)     (ax1   (MMformula_to_formula φ) (MMformula_to_formula ψ))
    | transform_MMax2  : forall φ ψ Ɣ, MMaxiom_to_axiom (MMax2 φ ψ Ɣ)   (ax2   (MMformula_to_formula φ) (MMformula_to_formula ψ) (MMformula_to_formula Ɣ))
    | transform_MMax3  : forall φ ψ,   MMaxiom_to_axiom (MMax3 φ ψ)     (ax3   (MMformula_to_formula φ) (MMformula_to_formula ψ))
    | transform_MMax4  : forall φ ψ,   MMaxiom_to_axiom (MMax4 φ ψ)     (ax4   (MMformula_to_formula φ) (MMformula_to_formula ψ))
    | transform_MMax5  : forall φ ψ,   MMaxiom_to_axiom (MMax5 φ ψ)     (ax5   (MMformula_to_formula φ) (MMformula_to_formula ψ))
    | transform_MMax6  : forall φ ψ,   MMaxiom_to_axiom (MMax6 φ ψ)     (ax6   (MMformula_to_formula φ) (MMformula_to_formula ψ))
    | transform_MMax7  : forall φ ψ,   MMaxiom_to_axiom (MMax7 φ ψ)     (ax7   (MMformula_to_formula φ) (MMformula_to_formula ψ))
    | transform_MMax8  : forall φ ψ,   MMaxiom_to_axiom (MMax8 φ ψ)     (ax8   (MMformula_to_formula φ) (MMformula_to_formula ψ))
    | transform_MMax9  : forall φ ψ Ɣ, MMaxiom_to_axiom (MMax9 φ ψ Ɣ)   (ax9   (MMformula_to_formula φ) (MMformula_to_formula ψ) (MMformula_to_formula Ɣ))
    | transform_MMax10 : forall φ ψ,   MMaxiom_to_axiom (MMax10 φ ψ)    (ax10  (MMformula_to_formula φ) (MMformula_to_formula ψ))
    | transform_MMaxK  : forall φ ψ n, MMaxiom_to_axiom (MMaxK n φ ψ)   (axK   (MMformula_to_formula φ) (MMformula_to_formula ψ))
    | transform_MMaxPos: forall φ ψ n, MMaxiom_to_axiom (MMaxPos n φ ψ) (axPos (MMformula_to_formula φ) (MMformula_to_formula ψ))
    | transform_MMaxT  : forall φ n,   MMaxiom_to_axiom (MMaxT n φ)     (axT   (MMformula_to_formula φ))
    | transform_MMaxB  : forall φ n,   MMaxiom_to_axiom (MMaxB n φ)     (axB   (MMformula_to_formula φ))
    | transform_MMaxD  : forall φ n,   MMaxiom_to_axiom (MMaxD n φ)     (axD   (MMformula_to_formula φ))
    | transform_MMaxK4 : forall φ n,   MMaxiom_to_axiom (MMaxK4 n φ)    (axK4  (MMformula_to_formula φ))
    | transform_MMaxK5 : forall φ n,   MMaxiom_to_axiom (MMaxK5 n φ)    (axK5  (MMformula_to_formula φ))
    | transform_MMaxGL : forall φ n,   MMaxiom_to_axiom (MMaxGL n φ)    (axGL  (MMformula_to_formula φ)).

  (*
    Proof of soundness of the previous definition
  *)
  Lemma MMaxiom_to_axiom_sound: forall a b φ,
    MMinstance a = φ -> MMaxiom_to_axiom a b ->
    instantiate b = (MMformula_to_formula φ).
  Proof.
    intros a b φ H0 H1;
    destruct a; simpl in *;
    repeat(inversion H1; subst; reflexivity).
  Qed.

End MultiModal.

(*
    Some assorted notations
    As these functions where defined in a Section that has some variables in it's scope, these variable
      get universally quantified when the function gets called outside the section, thus making
      the notation defined in the section unusable outside it (as the function now has more arguments)
    These notatios include these variables when the function is called, so they can be used outside
      the section
*)
Notation "X ; w ; n ||-M φ" := (valuation n X w φ) (at level 110, right associativity).
Notation "X ; n |=M φ"      := (validity_in_model n X φ) (at level 110, right associativity).
Notation "Γ ; X ; n ||=M φ" := (entailment n X Γ φ) (at level 110, no associativity).
Notation "Γ ; n ||=M φ"     := (semantic_entailment n Γ φ) (at level 110, no associativity).
Notation "A ; G ; n |--M p" := (MMdeduction n A G p) (at level 110, no associativity).

(*
  Properties of relations that were defined in the base library by means of frames,
  and their respective equivalence proofs with these generic definitions
*)

(* Unrestricted *)
(* Relations that define frames for K are unrestricted, this is why we need this definition *)
Definition unrestricted_rel (X: Set) (R: X -> X -> Prop): Prop := True.

(* Reflexivity *)
Definition reflexive_rel (X: Set) (R: X -> X -> Prop): Prop :=
  forall x, R x x.

(* Transitivity *)
Definition transitive_rel (X: Set) (R: X -> X -> Prop): Prop :=
  forall x0 x1 x2, (R x0 x1 /\ R x1 x2) -> R x0 x2.

  (* Simmetry *)
Definition symmetric_rel (X: Set) (R: X -> X -> Prop): Prop :=
  forall x0 x1, R x0 x1 -> R x1 x0.

(* Euclidianity *)
Definition euclidean_rel (X: Set) (R: X -> X -> Prop): Prop :=
  forall x0 x1 x2, (R x0 x1 /\ R x0 x2) -> R x1 x2.

(* Seriality *)
Definition serial_rel (X: Set) (R: X -> X -> Prop): Prop :=
  forall x0, exists x1, R x0 x1.

(* Functionality *)
Definition functional_rel (X: Set) (R: X -> X -> Prop): Prop :=
  forall x0 x1 x2, (R x0 x1 /\ R x0 x2) -> x1 = x2.

(* Density *)
Definition dense_rel (X: Set) (R: X -> X -> Prop): Prop :=
  forall x0 x1, exists x2, R x0 x1 -> (R x0 x2 /\ R x2 x1).

(* Convergence *)
Definition convergent_rel (X: Set) (R: X -> X -> Prop): Prop :=
  forall x0 x1 x2, exists x3, (R x0 x1 /\ R x0 x2) -> (R x1 x3 /\ R x2 x3).

(* Subset Relation of a Set (not an accesibility relation, just subset) *)
Definition SubsetOf (X: Set): Type := X -> Prop.

(* Conversely Well Foundedness - A relation whose converse is well founded *)
Definition conversely_well_founded_rel (Y: Set) (R: Y -> Y -> Prop): Prop :=
  (* Set-theoretic Definition *)
  forall X: SubsetOf Y, (exists x, X x) ->
  exists x0, X x0 /\ forall x1, X x1 -> ~ (R x0 x1).

(* Noetherianity (?) *)
Definition noetherian_rel (X: Set) (R: X -> X -> Prop): Prop :=
  transitive_rel X R /\ conversely_well_founded_rel X R.

(*
    Proofs that the above definitions are sound wrt the definitions in the base library
*)

Theorem refl_equivalence: forall F W R,
  F = Build_Frame W R ->
  reflexivity_frame F <-> reflexive_rel W R.
Proof.
  intros F W R H0;
  split; unfold reflexivity_frame, reflexive_rel;
  intros H1; [rewrite H0 in H1 | rewrite H0];
  auto.
Qed.

Theorem trans_equivalence: forall F W R,
  F = Build_Frame W R ->
  transitivity_frame F <-> transitive_rel W R.
Proof.
  intros F W R H0;
  split; unfold transitivity_frame, transitive_rel;
  intros H1; [rewrite H0 in H1 | rewrite H0];
  auto.
Qed.

Theorem symmetric_equivalence: forall F W R,
  F = Build_Frame W R ->
  simmetry_frame F <-> symmetric_rel W R.
Proof.
  intros F W R H0;
  split; unfold simmetry_frame, symmetric_rel;
  intros H1; [rewrite H0 in H1 | rewrite H0];
  auto.
Qed.

Theorem euclidean_equivalence: forall F W R,
  F = Build_Frame W R ->
  euclidian_frame F <-> euclidean_rel W R.
Proof.
  intros F W R H0;
  split; unfold euclidian_frame, euclidean_rel;
  intros H1; [rewrite H0 in H1 | rewrite H0];
  auto.
Qed.

Theorem serial_equivalence: forall F W R,
  F = Build_Frame W R ->
  serial_frame F <-> serial_rel W R.
Proof.
  intros F W R H0;
  split; unfold serial_frame, serial_rel;
  intros H1; [rewrite H0 in H1 | rewrite H0];
  auto.
Qed.

Theorem functional_equivalence: forall F W R,
  F = Build_Frame W R ->
  functional_frame F <-> functional_rel W R.
Proof.
  intros F W R H0;
  split; unfold functional_frame, functional_rel;
  intros H1; [rewrite H0 in H1 | rewrite H0];
  auto.
Qed.

Theorem dense_equivalence: forall F W R,
  F = Build_Frame W R ->
  dense_frame F <-> dense_rel W R.
Proof.
  intros F W R H0;
  split; unfold dense_frame, dense_rel;
  intros H1; [rewrite H0 in H1 | rewrite H0];
  auto.
Qed.

Theorem convergent_equivalence: forall F W R,
  F = Build_Frame W R ->
  convergente_frame F <-> convergent_rel W R.
Proof.
  intros F W R H0;
  split; unfold convergente_frame, convergent_rel;
  intros H1; [rewrite H0 in H1 | rewrite H0];
  auto.
Qed.

Theorem converse_wff_equivalence: forall F W R,
  F = Build_Frame W R ->
  conversely_well_founded_frame F <-> conversely_well_founded_rel W R.
Proof.
  intros F W R H0;
  split; unfold conversely_well_founded_frame, conversely_well_founded_rel;
  intros H1; [rewrite H0 in H1 | rewrite H0];
  auto.
Qed.

Theorem noetherian_equivalence: forall F W R,
  F = Build_Frame W R ->
  noetherian_frame F <-> noetherian_rel W R.
Proof.
  intros F W R H0;
  split; unfold noetherian_frame, noetherian_rel;
  intros H1; [rewrite H0 in H1 | rewrite H0];
  auto.
Qed.