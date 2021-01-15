Require Import Modal_Library List Classical Logic.

(**** HILBERT SYSTEM (axiomatic method) ****)
Inductive axiom : Set :=
  | ax1   : modalFormula -> modalFormula -> axiom
  | ax2   : modalFormula -> modalFormula -> modalFormula -> axiom
  | ax3   : modalFormula -> modalFormula -> axiom
  | ax4   : modalFormula -> modalFormula -> axiom
  | ax5   : modalFormula -> modalFormula -> axiom
  | ax6   : modalFormula -> modalFormula -> axiom
  | ax7   : modalFormula -> modalFormula -> axiom
  | ax8   : modalFormula -> modalFormula -> axiom
  | ax9   : modalFormula -> modalFormula -> modalFormula -> axiom
  | ax10  : modalFormula -> modalFormula -> axiom
  | axK   : modalFormula -> modalFormula -> axiom
  | axPos : modalFormula -> modalFormula -> axiom
  | axT   : modalFormula -> axiom
  | axB   : modalFormula -> axiom
  | axK4  : modalFormula -> axiom
  | axD   : modalFormula -> axiom
  | axK5  : modalFormula -> axiom.

Definition instantiate (a: axiom): modalFormula :=
  match a with
  | ax1    p   q       => [! p -> (q -> p) !]
  | ax2    p   q   r   => [! (p -> (q -> r)) -> ((p -> q) -> (p -> r)) !]
  | ax3    p   q       => [! (~ q -> ~ p) -> (p -> q) !]
  | ax4    p   q       => [! p -> (q -> (p /\ q)) !]
  | ax5    p   q       => [! (p /\ q) -> p !]
  | ax6    p   q       => [! (p /\ q) -> q !]
  | ax7    p   q       => [! p -> (p \/ q) !]
  | ax8    p   q       => [! q -> (p \/ q) !]
  | ax9    p   q   r   => [! (p -> r) -> ((q -> r) -> ((p \/ q) -> r)) !]
  | ax10   p   q       => [! ~ ~ p -> p !]
  | axK    p   q       => [! [] (p -> q) -> ([] p -> [] q) !]
  | axPos  p   q       => [! <> (p \/ q) -> (<> p \/ <> q) !]
  | axT    p           => [! []p -> p !]
  | axB    p           => [! p -> [] <> p !]
  | axK4   p           => [! [] p -> [] [] p !]
  | axD    p           => [! [] p -> <> p !]
  | axK5   p           => [! <> p -> [] <> p  !]
  end.

Inductive deduction (A: axiom -> Prop): theory -> modalFormula -> Prop :=
  (* Premise. *)
  | Prem: forall (t: theory)
                 (f: modalFormula)
                 (i: nat),
          (nth_error t i = Some f) -> deduction A t f
  (* Axiom. *)
  | Ax: forall (t: theory)
               (a: axiom)
               (f: modalFormula),
        A a -> instantiate a = f -> deduction A t f
  (* Modus Ponens. *)
  | Mp: forall (t: theory)
               (f g: modalFormula)
               (d1: deduction A t ([! f -> g !]))
               (d2: deduction A t f),
        deduction A t g
  (* Generalization. *)
  | Nec: forall (t: theory)
                (f: modalFormula)
                (d1: deduction A t f),
         deduction A t ([! [] f !]).
(*
Inductive deduction' (A: axiom -> Prop): theory -> modalFormula -> Prop :=
  (* Premise. *)
  | Prem': forall (t: theory)
                 (f: modalFormula)
                 (i: nat),
          (nth_error t i = Some f) -> deduction' A t f
  (* Axiom. *)
  | Ax': forall (t: theory)
               (a: axiom)
               (f: modalFormula),
        A a -> instantiate a = f -> deduction' A t f
  (* Modus Ponens. *)
  | Mp': forall (t: theory)
                (f g: modalFormula),
        deduction' A t (f -> g) -> deduction' A t f -> deduction' A t g
  (* Generalization. *)
  | Nec': forall (t: theory)
                (f: modalFormula),
        deduction' A t f -> deduction' A t (.[] f).
*)
Inductive K: axiom -> Prop :=
  | K_ax1: forall p q, K (ax1 p q)
  | K_ax2: forall p q r, K (ax2 p q r)
  | K_ax3: forall p q, K (ax3 p q)
  | K_ax4: forall p q, K (ax4 p q)
  | K_ax5: forall p q, K (ax5 p q)
  | K_ax6: forall p q, K (ax6 p q)
  | K_ax7: forall p q, K (ax7 p q)
  | K_ax8: forall p q, K (ax8 p q)
  | K_ax9: forall p q r, K (ax9 p q r)
  | K_ax10: forall p q, K (ax10 p q)
  | K_axK: forall p q, K (axK p q)
  | K_axPos: forall p q, K (axPos p q).

(* Reflexive *)
Inductive T: axiom -> Prop :=
  | T_K: forall p, K p -> T p
  | T_axT: forall p , T (axT p).

(* Reflexive and Symmetry *)
Inductive B: axiom -> Prop :=
  | B_T: forall p, T p -> B p
  | B_axB: forall p , B (axB p).

(* Transitive *)
Inductive K4: axiom -> Prop :=
  | K4_K: forall p, K p -> K4 p
  | K4_axK4: forall p , K4 (axK4 p).

(* Serial *)
Inductive D: axiom -> Prop :=
  | D_K: forall p, K p -> D p
  | D_axD: forall p , D (axD p).

(* Euclidean *)
Inductive K5: axiom -> Prop :=
  | K5_K: forall p, K p -> K5 p
  | K5_axK5: forall p , K5 (axK5 p).

(* Reflexive and Transitive*)
Inductive S4: axiom -> Prop :=
  | S4_T: forall p, T p -> S4 p
  | S4_axK4: forall p , S4 (axK4 p).

(* Symmetry and S4 *)
Inductive S5: axiom -> Prop :=
  | S5_B: forall p, B p -> S5 p
  | S5_S4: forall p , S4 p -> S5 p.

(* Reflexive and Euclidean *)
Inductive S5_2: axiom -> Prop :=
  | S5_2_T: forall p, T p -> S5_2 p
  | S5_2_K5: forall p , K5 p -> S5_2 p.

Notation "A ; G |-- p" := (deduction A G p) 
    (at level 110, no associativity).


Lemma deduction_identity:
  forall Gamma phi, 
  K; Gamma |-- [! phi -> phi !].
Proof.
  intros.
  apply Mp with (f := [! phi -> phi -> phi !]).
  - apply Mp with (f := [! phi -> (phi -> phi) -> phi !]).
    + apply Ax with (a := (ax2 [! phi !] [! (phi -> phi) !] phi )).
      * constructor.
      * reflexivity.
    + apply Ax with (a := (ax1 [! phi !] [! (phi -> phi) !])).
      * constructor.
      * reflexivity.
  - apply Ax with (a := (ax1 [! phi !] [! phi !])).
    + constructor.
    + reflexivity.
Qed.

Lemma deduction_reflexivity : 
  forall A Gamma phi,
  A; phi :: Gamma |-- [! phi !].
Proof.
  intros.
  apply Prem with (i := 0).
  reflexivity.
Qed.


Definition subset (Gamma Delta : theory) : Prop :=
  forall phi, 
  In phi Gamma -> 
  In phi Delta.

Lemma deduction_in_theory:
  forall A Gamma phi ,
  In phi Gamma ->
  A; Gamma |-- [! phi !].
Proof.
  intros; eapply In_nth_error in H.
  destruct H.
  apply Prem with (i:=x).
  assumption.
Qed.

Lemma deduction_weak: 
  forall Gamma Delta,
  subset Gamma Delta ->
  forall A phi,
  (A; Gamma |-- [! phi !]) -> 
  (A; Delta |-- [! phi !]).
Proof.
  intros.
  induction H0.
  - eapply deduction_in_theory; apply H. 
    eapply nth_error_In. 
    exact H0.
  - apply Ax with (a:= a). 
    + assumption.
    + assumption.
  - eapply Mp;
     eauto.
  - apply Nec; 
    intuition.
Qed.

Lemma deduction_monotonicity :
  forall Delta Gamma phi, 
  (K; Gamma |-- [! phi !]) -> 
  (K; Delta ++ Gamma |-- [! phi !]).
Proof.
  intros.
  apply deduction_weak with Gamma.
  - unfold subset. intros. 
    induction Delta.
    + simpl; assumption.
    + simpl in *; right; assumption.
  - assumption.
Qed.

Require Import Equality.

Lemma deduction_modus_ponens:
  forall Gamma phi psi,
  (K; phi::Gamma |-- [! psi !]) ->
  (K; Gamma |-- [! phi !]) ->
  (K; Gamma |-- [! psi !]).
Proof.
  intros; dependent induction H.
  - apply nth_error_In in H. 
    destruct H.
    + destruct H.
      assumption.
    + apply deduction_in_theory.
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
