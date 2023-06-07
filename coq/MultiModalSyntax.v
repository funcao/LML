Require Import Arith List Notations MultiModalCore Modal_Library Modal_Notations Deductive_System.
Export ListNotations.

(*
  Some properties related to translations of theories which are relevant to this part
  (And do not fit in the core part of this extension)
*)

Lemma theory_to_MMtheory_preserves_In: forall Γ φ n,
  In φ Γ -> In (formula_to_MMformula φ n) (theory_to_MMtheory Γ n).
Proof.
  intros Γ φ n H0.
  induction Γ; [inversion H0 |].
  destruct H0 as [H0 | H0];
  [subst | apply IHΓ in H0 ];
  simpl; auto.
Qed.

Lemma theory_to_MMtheory_preserves_lenght: forall Γ n,
  length Γ = length (theory_to_MMtheory Γ n).
Proof.
  intros Γ n; induction Γ as [ | φ Γ IHΓ]; simpl; try rewrite IHΓ; reflexivity.
Qed.

Lemma theory_to_MMtheory_preserves_order: forall Γ n1 n2 φ,
  nth_error Γ n1 = Some φ <->
  nth_error (theory_to_MMtheory Γ n2) n1 = Some (formula_to_MMformula φ n2).
Proof.
  intros Γ n1 n2 φ; generalize dependent n1; generalize dependent n2.
  induction Γ as [ | Ɣ Γ IHΓ]; split; intros H0;
  [
    apply nth_error_In in H0; inversion H0 |
    apply nth_error_In in H0; inversion H0 |
    destruct n1; simpl in * |
    destruct n1; simpl in *
  ].
  - inversion H0; subst; auto.
  - rewrite <- IHΓ; assumption.
  - inversion H0 as [H1];
    apply formula_to_MMformula_injective in H1;
    subst; auto.
  - apply IHΓ in H0; assumption.
Qed.

Theorem MMdeduction_in_premise: forall modalities A Γ φ,
  In φ Γ -> deducible_theory modalities Γ -> MMdeduction modalities A Γ φ.
Proof.
  intros modalities A Γ φ H0 H1.
  eapply In_nth_error in H0; destruct H0 as [n H0];
  eapply MMPrem; eauto.
Qed.

Theorem MMdeduction_weakeaning: forall modalities A Γ1 Γ2 φ,
  subset Γ1 Γ2 -> deducible_theory modalities Γ1 -> deducible_theory modalities Γ2 ->
  MMdeduction modalities A Γ1 φ -> MMdeduction modalities A Γ2 φ.
Proof.
  intros modalities A Γ1 Γ2 φ H0 H1 H2 H3.
  induction H3 as [ | | Γ1 ψ1 | ].
  - (*Premise*)
    unfold subset in H0; eapply nth_error_In in H3.
    apply H0 in H3; apply MMdeduction_in_premise; auto.
  - (*Axiom*)
    apply MMAx with (a); auto.
  - (*Modus Ponens*)
    apply MMMp with (ψ1); auto.
  - (*Necessitation*)
    apply MMNec; auto.
Qed.

Theorem MMdeduction_monotone: forall modalities A Γ1 Γ2 φ,
  deducible_theory modalities Γ1 -> deducible_theory modalities Γ2 ->
  MMdeduction modalities A Γ1 φ -> MMdeduction modalities A (Γ1 ++ Γ2) φ.
Proof.
  intros modalities A Γ1 Γ2 φ H0 H1 H2.
  apply MMdeduction_weakeaning with (Γ1); try (apply deducible_theory_union); auto.
  unfold subset; intros; apply in_or_app; auto.
Qed.

(*
  Properties of translations are done, now onwards to some preservation proofs
*)

Require Import Equality. (*For depent induction*)

Theorem deducible_formula_condition: forall f modalities n,
  n < modalities ->
  deducible_formula modalities (formula_to_MMformula f n).
Proof.
  induction f; simpl; firstorder.
Qed.

Theorem deducible_theory_condition: forall t modalities n,
  n < modalities ->
  deducible_theory modalities (theory_to_MMtheory t n).
Proof.
  induction t; simpl; firstorder; apply deducible_formula_condition with (f:=a) in H; auto.
Qed.

Theorem MMdeduction_generalization_Kn: forall modalities indexes n Γ φ,
  let K_to_Kn := formula_to_MMformula in
  n < modalities ->
  In n indexes ->
  deduction K Γ φ ->
  MMdeduction modalities (Kn modalities indexes) (theory_to_MMtheory Γ n) (K_to_Kn φ n).
Proof.
  intros modalities indexes n Γ φ K_to_Kn H0 H1 H2.
  dependent induction H2;
  assert (H3: deducible_formula modalities (K_to_Kn f n)) by
    (apply deducible_formula_condition with(f:=f) in H0; assumption);
  assert (H4: deducible_theory modalities (theory_to_MMtheory t n)) by
    (apply deducible_theory_condition with(t:=t) in H0; assumption).
  - (*Premise*)
    apply MMPrem with (i); try apply theory_to_MMtheory_preserves_order; assumption.
  - (*Axioms*)
    destruct H; unfold K_to_Kn in *.
    + apply axiom_to_MMaxiom_sound with (a:=ax1 φ ψ) (b:= MMax1 (K_to_Kn φ n) (K_to_Kn ψ n)) (n:=n) in H2;
      try constructor.
      apply MMAx with (MMax1 (K_to_Kn φ n) (K_to_Kn ψ n)); try constructor; try rewrite H2; easy.
    + apply axiom_to_MMaxiom_sound with (a:=ax2 φ ψ Ɣ) (b:= MMax2 (K_to_Kn φ n) (K_to_Kn ψ n) (K_to_Kn Ɣ n)) (n:=n) in H2;
      try constructor.
      apply MMAx with (MMax2 (K_to_Kn φ n) (K_to_Kn ψ n) (K_to_Kn Ɣ n)); try constructor; try rewrite H2; easy.
    + apply axiom_to_MMaxiom_sound with (a:=ax3 φ ψ) (b:= MMax3 (K_to_Kn φ n) (K_to_Kn ψ n)) (n:=n) in H2;
      try constructor.
      apply MMAx with (MMax3 (K_to_Kn φ n) (K_to_Kn ψ n)); try constructor; try rewrite H2; easy.
    + apply axiom_to_MMaxiom_sound with (a:=ax4 φ ψ) (b:= MMax4 (K_to_Kn φ n) (K_to_Kn ψ n)) (n:=n) in H2;
      try constructor.
      apply MMAx with (MMax4 (K_to_Kn φ n) (K_to_Kn ψ n)); try constructor; try rewrite H2; easy.
    + apply axiom_to_MMaxiom_sound with (a:=ax5 φ ψ) (b:= MMax5 (K_to_Kn φ n) (K_to_Kn ψ n)) (n:=n) in H2;
      try constructor.
      apply MMAx with (MMax5 (K_to_Kn φ n) (K_to_Kn ψ n)); try constructor; try rewrite H2; easy.
    + apply axiom_to_MMaxiom_sound with (a:=ax6 φ ψ) (b:= MMax6 (K_to_Kn φ n) (K_to_Kn ψ n)) (n:=n) in H2;
      try constructor.
      apply MMAx with (MMax6 (K_to_Kn φ n) (K_to_Kn ψ n)); try constructor; try rewrite H2; easy.
    + apply axiom_to_MMaxiom_sound with (a:=ax7 φ ψ) (b:= MMax7 (K_to_Kn φ n) (K_to_Kn ψ n)) (n:=n) in H2;
      try constructor.
      apply MMAx with (MMax7 (K_to_Kn φ n) (K_to_Kn ψ n)); try constructor; try rewrite H2; easy.
    + apply axiom_to_MMaxiom_sound with (a:=ax8 φ ψ) (b:= MMax8 (K_to_Kn φ n) (K_to_Kn ψ n)) (n:=n) in H2;
      try constructor.
      apply MMAx with (MMax8 (K_to_Kn φ n) (K_to_Kn ψ n)); try constructor; try rewrite H2; easy.
    + apply axiom_to_MMaxiom_sound with (a:=ax9 φ ψ Ɣ) (b:= MMax9 (K_to_Kn φ n) (K_to_Kn ψ n) (K_to_Kn Ɣ n)) (n:=n) in H2;
      try constructor.
      apply MMAx with (MMax9 (K_to_Kn φ n) (K_to_Kn ψ n) (K_to_Kn Ɣ n)); try constructor; try rewrite H2; easy.
    + apply axiom_to_MMaxiom_sound with (a:=ax10 φ ψ) (b:= MMax10 (K_to_Kn φ n) (K_to_Kn ψ n)) (n:=n) in H2;
      try constructor.
      apply MMAx with (MMax10 (K_to_Kn φ n) (K_to_Kn ψ n)); try constructor; try rewrite H2; easy.
    + apply axiom_to_MMaxiom_sound with (a:=axK φ ψ) (b:= MMaxK n (K_to_Kn φ n) (K_to_Kn ψ n)) (n:=n) in H2;
      try constructor.
      apply MMAx with (MMaxK n (K_to_Kn φ n) (K_to_Kn ψ n)); try constructor; try rewrite H2; easy.
    + apply axiom_to_MMaxiom_sound with (a:=axPos φ ψ) (b:= MMaxPos n (K_to_Kn φ n) (K_to_Kn ψ n)) (n:=n) in H2;
      try constructor.
      apply MMAx with (MMaxPos n (K_to_Kn φ n) (K_to_Kn ψ n)); try constructor; try rewrite H2; easy.
  - (*Modus Ponens*)
    assert (H5: deducible_formula modalities (K_to_Kn g n)) by
      (apply deducible_formula_condition with(f:=g) in H0; assumption);
    apply MMMp with (K_to_Kn f n);
    try apply IHdeduction1; try assumption;
    try apply IHdeduction2; try assumption;
    simpl; try intuition.
  - (*Necessitation*)
    apply MMNec; try apply IHdeduction; assumption.
Qed.

Lemma join_simmetric: forall modalities S1 S2 n1 n2 b,
  join modalities S1 S2 n1 n2 (n1 :: n2 :: nil) b <-> join modalities S2 S1 n2 n1 (n2 :: n1 :: nil) b.
Proof.
  intros modalities S1 S2 n1 n2 b; split; induction 1;
  try (eapply derivable_S2; eassumption);
  eapply derivable_S1; eassumption.
Qed.

Lemma join_two_simmetric: forall S1 S2 l1 l2 b,
  join_two S1 S2 l1 l2 (l1 ++ l2) b <-> join_two S2 S1 l2 l1 (l2 ++ l1) b.
Proof.
  intros S1 S2 l1 l2 b; split; induction 1;
  try (eapply derivable_S2_two; eassumption);
  eapply derivable_S1_two; eassumption.
Qed.

Theorem join_preserves_deduction: forall modalities S1 n1 Γ φ,
  let K_to_Kn := formula_to_MMformula in
  n1 < modalities -> deduction S1 Γ φ ->
  forall S2 n2 b, (forall a, axiom_to_MMaxiom n1 a b) -> join modalities S1 S2 n1 n2 (n1 :: n2 :: nil) b ->
  MMdeduction modalities (join modalities S1 S2 n1 n2 (n1 :: n2 :: nil)) (theory_to_MMtheory Γ n1) (K_to_Kn φ n1).
Proof.
  intros modalities S1 n1 Γ φ K_to_Kn H0 H1 S2 n2 b H2 H3.
  dependent induction H1;
  assert (H4: deducible_formula modalities (K_to_Kn f n1)) by
    (apply deducible_formula_condition with(f:=f) in H0; assumption);
  assert (H5: deducible_theory modalities (theory_to_MMtheory t n1)) by
    (apply deducible_theory_condition with(t:=t) in H0; assumption).
  - (*Premise*)
    eapply MMPrem; try apply theory_to_MMtheory_preserves_order; eassumption.
  - (*Axiom*)
    eapply MMAx in H; try eassumption;
    (try eapply MMAx; try eassumption);
    eapply axiom_to_MMaxiom_sound; try eassumption;
    eauto.
  - (*Modus Ponens*)
    assert (H6: deducible_formula modalities (K_to_Kn g n1)) by
      (apply deducible_formula_condition with(f:=g) in H0; assumption).
    apply MMMp with (K_to_Kn f n1);
    try eapply IHdeduction1; try eassumption;
    try eapply IHdeduction2; try eassumption;
    simpl; try intuition.
  - (*Necessitation*)
    apply MMNec; try eapply IHdeduction; eassumption.
Qed.

Theorem join_one_preserves_deduction_left: forall modalities S1 n Γ φ,
  let K_to_Kn := formula_to_MMformula in
  n < modalities -> deduction S1 Γ φ ->
  forall S2 l b, (forall a, axiom_to_MMaxiom n a b) -> join_one modalities S1 S2 n l (n :: l) b ->
  MMdeduction modalities (join_one modalities S1 S2 n l (n :: l)) (theory_to_MMtheory Γ n) (K_to_Kn φ n).
Proof.
  intros modalities S1 n Γ φ K_to_Kn H0 H1 S2 l b H2 H3.
  dependent induction H1;
  assert (H4: deducible_formula modalities (K_to_Kn f n)) by
    (apply deducible_formula_condition with(f:=f) in H0; assumption);
  assert (H5: deducible_theory modalities (theory_to_MMtheory t n)) by
    (apply deducible_theory_condition with(t:=t) in H0; assumption).
  - (*Premise*)
    eapply MMPrem; try apply theory_to_MMtheory_preserves_order; eassumption.
  - (*Axiom*)
    eapply MMAx in H; try eassumption;
    (try eapply MMAx; try eassumption);
    eapply axiom_to_MMaxiom_sound; try eassumption;
    eauto.
  - (*Modus Ponens*)
    assert (H6: deducible_formula modalities (K_to_Kn g n)) by
      (apply deducible_formula_condition with(f:=g) in H0; assumption).
    apply MMMp with (K_to_Kn f n);
    try eapply IHdeduction1; try eassumption;
    try eapply IHdeduction2; try eassumption;
    simpl; try intuition.
  - (*Necessitation*)
    apply MMNec; try eapply IHdeduction; eassumption.
Qed.

Theorem join_one_preserves_deduction_right: forall modalities S2 l n Γ φ,
  let K_to_Kn := formula_to_MMformula in
  n < modalities -> MMdeduction modalities (S2 l) Γ φ ->
  forall S1 b, join_one modalities S1 S2 n l (n :: l) b ->
  MMdeduction modalities (join_one modalities S1 S2 n l (n :: l)) Γ φ.
Proof.
  intros modalities S2 l n Γ φ K_to_Kn H0 H1 S1 b H2.
  dependent induction H1.
  - (*Premise*)
    eapply MMPrem; eassumption.
  - (*Axiom*)
    pose H as H'; eapply MMAx in H'; try eassumption.
    eapply derivable_S2_one in H;
    eapply MMAx; try eassumption.
  - (*Modus Ponens*)
    apply MMMp with (φ); try assumption;
    try eapply IHMMdeduction1; try eassumption.
    try eapply IHMMdeduction2; eassumption.
  - (*Necessitation*)
    apply MMNec; try eapply IHMMdeduction; eassumption.
Qed.

Theorem join_two_preserves_deduction: forall modalities S1 S2 l1 l2 Γ φ a,
  MMdeduction modalities (S1 l1) Γ φ -> join_two S1 S2 l1 l2 (l1 ++ l2) a ->
  MMdeduction modalities (join_two S1 S2 l1 l2 (l1 ++ l2)) Γ φ.
Proof.
  intros modalities S1 S2 l1 l2 Γ φ a H0 H1.
  dependent induction H0.
  - (*Premise*)
    eapply MMPrem; eassumption.
  - (*Axiom*)
    pose H as H';
    eapply MMAx in H'; try eassumption.
    eapply derivable_S1_two in H;
    eapply MMAx; try eassumption.
  - (*Modus Ponens*)
    apply MMMp with (φ); try assumption;
    try eapply IHMMdeduction1;
    try eapply IHMMdeduction2;
    assumption.
  - (*Necessitation*)
    apply MMNec; try eapply IHMMdeduction; assumption.
Qed.