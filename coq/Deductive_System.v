Require Import Modal_Library Modal_Notations List Classical Logic Equality.

(* Hilbert Style Axiomatic Derivation System *)

(* 
  Definition of the type of the axioms, there are countably many axioms schema, so defining a 
  type (a Set in this case) is necessary
*)
Inductive axiom : Set :=
  | ax1  : formula -> formula -> axiom
  | ax2  : formula -> formula -> formula -> axiom
  | ax3  : formula -> formula -> axiom
  | ax4  : formula -> formula -> axiom
  | ax5  : formula -> formula -> axiom
  | ax6  : formula -> formula -> axiom
  | ax7  : formula -> formula -> axiom
  | ax8  : formula -> formula -> axiom
  | ax9  : formula -> formula -> formula -> axiom
  | ax10 : formula -> formula -> axiom
  | axK  : formula -> formula -> axiom
  | axPos: formula -> formula -> axiom
  | axT  : formula -> axiom
  | axB  : formula -> axiom
  | axK4 : formula -> axiom
  | axD  : formula -> axiom
  | axK5 : formula -> axiom
  | axGL : formula -> axiom.

(* 
  Definition of a function that instanciates an axiom, that is, given an object of type axiom defined above,
  returns a formula that corresponds to the axiom  
*)
Definition instantiate (a: axiom): formula :=
  match a with
  | ax1   φ ψ   => [! φ -> (ψ -> φ) !]
  | ax2   φ ψ Ɣ => [! (φ -> (ψ -> Ɣ)) -> ((φ -> ψ) -> (φ -> Ɣ)) !]
  | ax3   φ ψ   => [! (~ψ -> ~φ) -> (φ -> ψ) !]
  | ax4   φ ψ   => [! φ -> (ψ -> (φ /\ ψ)) !]
  | ax5   φ ψ   => [! (φ /\ ψ) -> φ !]
  | ax6   φ ψ   => [! (φ /\ ψ) -> ψ !]
  | ax7   φ ψ   => [! φ -> (φ \/ ψ) !]
  | ax8   φ ψ   => [! ψ -> (φ \/ ψ) !]
  | ax9   φ ψ Ɣ => [! (φ -> Ɣ) -> ((ψ -> Ɣ) -> ((φ \/ ψ) -> Ɣ)) !]
  | ax10  φ ψ   => [! ~~φ -> φ !]
  | axK   φ ψ   => [! [](φ -> ψ) -> ([] φ -> [] ψ) !]
  | axPos φ ψ   => [! <> (φ \/ ψ) -> (<> φ \/ <> ψ) !]
  | axT   φ     => [! []φ -> φ !]
  | axB   φ     => [! φ -> [] <> φ !]
  | axK4  φ     => [! [] φ -> [] [] φ !]
  | axD   φ     => [! [] φ -> <> φ !]
  | axK5  φ     => [! <> φ -> [] <> φ !]
  | axGL  φ     => [! []([]φ -> φ) -> []φ !]
  end.

(* 
  Definition of a deduction in a Hilbert Axiomatic System  
  A deduction of psi in a Hilbert System is a sequence of formulas phi_0, ..., phi_n, psi
  such that each phi_0, ..., phi_n is either: 
  - A Premise
  - An Instance of an Axiom 
  - The result of applying the rule of Modus Ponens to any two previous formulas
  - The result of applying the rule of Necessitation to any previous formula
  In the constructors bellow, (t: theory) represents the set of premises of a deduction and (A: axiom -> Prop)
  represents the modal system where this deduction in "taking place", those are defined bellow

  Even though Hilbert style systems are not usually presented in a tree notation, a deduction in a Hilbert Style 
  System can be read as:

                -------------------- S, R
                      T |- phi_0
                -------------------- S, R
                          .
                          .
                          .
                -------------------- S, R
                       T |- phi_n
                -------------------- S, R
                       T |- psi
  
  Where T is our set of premises, S the system where this deduction is "taking place", R the rule that was applied
  and phi_0,...,phi_n, psi the formulas being deduced themselves
*)
Inductive deduction (A: axiom -> Prop): theory -> formula -> Prop :=
  (* Premise. *)
  | Prem: forall (t: theory)
                 (f: formula)
                 (i: nat),
          (nth_error t i = Some f) -> deduction A t f
  (* Axiom. *)
  | Ax: forall (t: theory)
               (a: axiom)
               (f: formula),
        A a -> instantiate a = f -> deduction A t f
  (* Modus Ponens. *)
  | Mp: forall (t: theory)
               (f g: formula)
               (d1: deduction A t [! f -> g !])
               (d2: deduction A t f),
        deduction A t g
  (* Necessitation. *)
  | Nec: forall (t: theory)
                (f: formula)
                (d1: deduction A t f),
         deduction A t [! []f !].

(** Systems of Modal Logic **)

(* 
  In what follows "forall a b c, A (axX a b c ...)" is to be read as:
  "In System A, all instances of axiom X are axioms of this system"
  Where as "forall x, A x -> B x" is to be read as:
  "All axioms of System A are axioms of System B"
*)

(* System K, the most basic systems *)
Inductive K: axiom -> Prop :=
  | K_ax1:   forall φ ψ,   K (ax1 φ ψ)
  | K_ax2:   forall φ ψ Ɣ, K (ax2 φ ψ Ɣ)
  | K_ax3:   forall φ ψ,   K (ax3 φ ψ)
  | K_ax4:   forall φ ψ,   K (ax4 φ ψ)
  | K_ax5:   forall φ ψ,   K (ax5 φ ψ)
  | K_ax6:   forall φ ψ,   K (ax6 φ ψ)
  | K_ax7:   forall φ ψ,   K (ax7 φ ψ)
  | K_ax8:   forall φ ψ,   K (ax8 φ ψ)
  | K_ax9:   forall φ ψ Ɣ, K (ax9 φ ψ Ɣ)
  | K_ax10:  forall φ ψ,   K (ax10 φ ψ)
  | K_axK:   forall φ ψ,   K (axK φ ψ)
  | K_axPos: forall φ ψ,   K (axPos φ ψ).

(* System T, where the accesibility relation is reflexive *)
Inductive T: axiom -> Prop :=
  | T_K:   forall φ, K φ -> T φ
  | T_axT: forall φ, T (axT φ).

(* System B, where the accesibility relation is reflexive and symmetric *)
Inductive B: axiom -> Prop :=
  | B_T:   forall φ, T φ -> B φ
  | B_axB: forall φ, B (axB φ).

(* System K4 (or simply 4), where the accesibility relation is transitive *)
Inductive K4: axiom -> Prop :=
  | K4_K:    forall φ, K φ -> K4 φ
  | K4_axK4: forall φ, K4 (axK4 φ).

(* System D, where the accesibility relation is serial *)
Inductive D: axiom -> Prop :=
  | D_K:   forall φ, K φ -> D φ
  | D_axD: forall φ, D (axD φ).

(* System K5 (or simply 5), where the accesibility relation is euclidean *)
Inductive K5: axiom -> Prop :=
  | K5_K:    forall φ, K φ -> K5 φ
  | K5_axK5: forall φ, K5 (axK5 φ).

(* System S4, where the accesibility relation is reflexive and transitive *)
Inductive S4: axiom -> Prop :=
  | S4_T:    forall φ, T φ -> S4 φ
  | S4_axK4: forall φ, S4 (axK4 φ).

(* System S5, where the accesibility relation is reflexive, transitive and symmetric *)
Inductive S5: axiom -> Prop :=
  | S5_B:  forall φ, B φ -> S5 φ
  | S5_S4: forall φ, S4 φ -> S5 φ.

(* Another way of defining S5, where the accesibility relation is reflexive and euclidean *)
Inductive S5_2: axiom -> Prop :=
  | S5_2_T:  forall φ, T φ -> S5_2 φ
  | S5_2_K5: forall φ, K5 φ -> S5_2 φ.

(* System GL, where the accesibility relation is converselly well founded and transitive *)
Inductive GL: axiom -> Prop :=
  | GL_K4:   forall φ, K4 φ -> GL φ
  | GL_axGL: forall φ, GL (axGL φ).

(* Notation 
  TODO: Move this out of this file
*)
Notation "A ; G |-- p" := (deduction A G p)
    (at level 110, no associativity).

(** Some properties of semantic deduction **)

(* phi -> phi is a theorem of K *)
Lemma derive_identity:
  forall Γ φ,
  K; Γ |-- [! φ -> φ !].
Proof.
  intros.
  apply Mp with (f := [! φ -> φ -> φ !]).
  - apply Mp with (f := [! φ -> (φ -> φ) -> φ !]).
    + apply Ax with (a := ax2 φ [! φ -> φ !] φ).
      * constructor.
      * reflexivity.
    + apply Ax with (a := ax1 φ [! φ -> φ !]).
      * constructor.
      * reflexivity.
  - apply Ax with (a := ax1 φ φ).
    + constructor.
    + reflexivity.
Qed.

(* If a formula is the head of the set(list) of premises of a derivation, then it is derivable *)
Lemma derive_refl:
  forall A Γ φ,
  A; φ :: Γ |-- φ.
Proof.
  intros.
  apply Prem with (i := 0).
  reflexivity.
Qed.

Definition subset {T: Type} (L1 L2: list T): Prop :=
  forall x, In x L1 -> In x L2.

(* If a formula is in the set of premises of a derivation, then it is derivable *)
Lemma derive_In:
  forall A Γ φ,
  In φ Γ ->
  A; Γ |-- φ.
Proof.
  intros; eapply In_nth_error in H.
  destruct H.
  apply Prem with (i := x).
  assumption.
Qed.

(* Weakeaning of derivation, if a set Gamma of premisses can derive a formula, 
  then any set containg Gamma can do so too *)
Lemma derive_weak:
  forall Γ ẟ,
  subset Γ ẟ ->
  forall A φ,
  (A; Γ |-- φ) ->
  (A; ẟ |-- φ).
Proof.
  intros.
  induction H0.
  - eapply derive_In; apply H.
    eapply nth_error_In.
    exact H0.
  - apply Ax with (a:= a); auto.
  - eapply Mp; eauto.
  - apply Nec; intuition.
Qed.

(* Monotonicity of derivations, if a set Gamma of premisses can derive a formula, 
  then adding any more formulas to Gamma preserves derivations *)
Lemma derive_monotonicity:
  forall ẟ Γ φ,
  (K; Γ |-- φ) ->
  (K; ẟ ++ Γ |-- φ).
Proof.
  intros.
  apply derive_weak with Γ.
  - unfold subset. intros.
    induction ẟ.
    + simpl; assumption.
    + simpl in *; right; assumption.
  - assumption.
Qed.

(* I don't know *)
Lemma derive_modus_ponens:
  forall Γ φ ψ,
  (K; φ::Γ |-- ψ) ->
  (K; Γ |-- φ) ->
  (K; Γ |-- ψ).
Proof.
  intros; dependent induction H.
  - apply nth_error_In in H.
    destruct H.
    + destruct H.
      assumption.
    + apply derive_In.
      assumption.
  - apply Ax with (a:=a).
    + assumption.
    + reflexivity.
  - eapply Mp.
    + eapply IHdeduction1.
      * eauto.
      * assumption.
    + eapply IHdeduction2.
      * eauto.
      * assumption.
  - apply Nec.
    + eapply IHdeduction.
      * eauto.
      * assumption.
Qed.
