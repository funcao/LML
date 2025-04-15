Require Import Modal_Library Modal_Notations List Classical Logic Equality Sets.

Set Implicit Arguments.

Section Hilbert.

Context `{X: modal_index_set}.

(**** HILBERT SYSTEM (axiomatic method) ****)
Inductive axiom: Set :=
  | ax1: formula -> formula -> axiom
  | ax2: formula -> formula -> formula -> axiom
  | ax3: formula -> formula -> axiom
  | ax4: formula -> formula -> axiom
  | ax5: formula -> formula -> axiom
  | ax6: formula -> formula -> axiom
  | ax7: formula -> formula -> axiom
  | ax8: formula -> formula -> axiom
  | ax9: formula -> formula -> formula -> axiom
  | ax10: formula -> axiom
  | axK: modal_index -> formula -> formula -> axiom
  | axDual: modal_index -> formula -> axiom
  | axT: modal_index -> formula -> axiom
  | axB: modal_index -> formula -> axiom
  | axK4: modal_index -> formula -> axiom
  | axD: modal_index -> formula -> axiom
  | axK5: modal_index -> formula -> axiom
  | axGL: modal_index -> formula -> axiom.

Definition instantiate (a: axiom): formula :=
  match a with
  | ax1      φ ψ   => [! φ -> (ψ -> φ) !]
  | ax2      φ ψ γ => [! (φ -> (ψ -> γ)) -> ((φ -> ψ) -> (φ -> γ)) !]
  | ax3      φ ψ   => [! (~ψ -> ~φ) -> (φ -> ψ) !]
  | ax4      φ ψ   => [! φ -> (ψ -> (φ /\ ψ)) !]
  | ax5      φ ψ   => [! (φ /\ ψ) -> φ !]
  | ax6      φ ψ   => [! (φ /\ ψ) -> ψ !]
  | ax7      φ ψ   => [! φ -> (φ \/ ψ) !]
  | ax8      φ ψ   => [! ψ -> (φ \/ ψ) !]
  | ax9      φ ψ γ => [! (φ -> γ) -> ((ψ -> γ) -> ((φ \/ ψ) -> γ)) !]
  | ax10     φ     => [! ~~φ -> φ !]
  | axK    i φ ψ   => [! [i](φ -> ψ) -> ([i]φ -> [i]ψ) !]
  | axDual i φ     => [! <i>φ <-> ~[i]~φ !]
  | axT    i φ     => [! [i]φ -> φ !]
  | axB    i φ     => [! φ -> [i]<i>φ !]
  | axK4   i φ     => [! [i]φ -> [i][i]φ !]
  | axD    i φ     => [! [i]φ -> <i>φ !]
  | axK5   i φ     => [! <i>φ -> [i]<i>φ !]
  | axGL   i φ     => [! [i]([i]φ -> φ) -> [i]φ !]
  end.

Inductive deduction (A: axiom -> Prop): theory -> formula -> Prop :=
  (* Premise. *)
  | Prem: forall (t: theory) (f: formula),
    t f ->
    deduction A t f
  (* Axiom. *)
  | Ax: forall (t: theory) (a: axiom) (f: formula),
    A a ->
    instantiate a = f ->
    deduction A t f
  (* Modus Ponens. *)
  | Mp: forall (t: theory) (f g: formula),
    deduction A t [! f -> g !] ->
    deduction A t f ->
    deduction A t g
  (* Generalization. *)
  | Nec: forall (t: theory) (f: formula) (i: modal_index),
    deduction A Empty f ->
    deduction A t [! [i]f !].

End Hilbert.

Section Systems.

Context `{X: modal_index_set}.

Inductive P: axiom -> Prop :=
  | P_ax1: forall φ ψ, P (ax1 φ ψ)
  | P_ax2: forall φ ψ Ɣ, P (ax2 φ ψ Ɣ)
  | P_ax3: forall φ ψ, P (ax3 φ ψ)
  | P_ax4: forall φ ψ, P (ax4 φ ψ)
  | P_ax5: forall φ ψ, P (ax5 φ ψ)
  | P_ax6: forall φ ψ, P (ax6 φ ψ)
  | P_ax7: forall φ ψ, P (ax7 φ ψ)
  | P_ax8: forall φ ψ, P (ax8 φ ψ)
  | P_ax9: forall φ ψ Ɣ, P (ax9 φ ψ Ɣ)
  | P_ax10: forall φ, P (ax10 φ).

Variable idx: modal_index.

Inductive K: axiom -> Prop :=
  | K_P: forall φ, P φ -> K φ
  | K_axK: forall φ ψ, K (axK idx φ ψ)
  | K_axDual: forall φ, K (axDual idx φ).

(* Reflexive *)
Inductive T: axiom -> Prop :=
  | T_K: forall φ, K φ -> T φ
  | T_axT: forall φ , T (axT idx φ).

(* Reflexive and Symmetry *)
Inductive B: axiom -> Prop :=
  | B_T: forall φ, T φ -> B φ
  | B_axB: forall φ , B (axB idx φ).

(* Transitive *)
Inductive K4: axiom -> Prop :=
  | K4_K: forall φ, K φ -> K4 φ
  | K4_axK4: forall φ , K4 (axK4 idx φ).

(* Serial *)
Inductive D: axiom -> Prop :=
  | D_K: forall φ, K φ -> D φ
  | D_axD: forall φ , D (axD idx φ).

(* Euclidean *)
Inductive K5: axiom -> Prop :=
  | K5_K: forall φ, K φ -> K5 φ
  | K5_axK5: forall φ , K5 (axK5 idx φ).

(* Reflexive and Transitive *)
Inductive S4: axiom -> Prop :=
  | S4_T: forall φ, T φ -> S4 φ
  | S4_axK4: forall φ , S4 (axK4 idx φ).

(* Symmetry and S4 *)
Inductive S5: axiom -> Prop :=
  | S5_B: forall φ, B φ -> S5 φ
  | S5_S4: forall φ , S4 φ -> S5 φ.

(* Reflexive and Euclidean *)
Inductive S5_2: axiom -> Prop :=
  | S5_2_T: forall φ, T φ -> S5_2 φ
  | S5_2_K5: forall φ , K5 φ -> S5_2 φ.

Inductive GL: axiom -> Prop :=
  | GL_K4:   forall φ, K4 φ -> GL φ
  | GL_axGL: forall φ, GL (axGL idx φ).

End Systems.

(* Notations and Theorems *)

(* TODO: Move you to the notation file!!! *)
Notation "A ; G |-- p" := (deduction A G p)
    (at level 110, no associativity).

Section Helper.

Context `{X: modal_index_set}.

Lemma derive_weak:
  forall Γ ẟ,
  Subset Γ ẟ ->
  forall A φ,
  (A; Γ |-- φ) ->
  (A; ẟ |-- φ).
Proof.
  intros.
  induction H0.
  - apply Prem.
    apply H.
    assumption.
  - apply Ax with (a:= a); auto.
  - eapply Mp; eauto.
  - apply Nec; intuition.
Qed.

Lemma derive_monotonicity:
  forall A ẟ Γ φ,
  (A; Γ |-- φ) ->
  (A; Union ẟ Γ |-- φ).
Proof.
  intros.
  apply derive_weak with Γ.
  - intros p ?.
    right; auto.
  - assumption.
Qed.

End Helper.
