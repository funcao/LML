Require Import Modal_Library List.

Export ListNotations.

Declare Custom Entry modal.
Declare Scope modal_scope.

(* Bind Scope modal_scope with modalFormula. *)

Notation "x" := x
  (in custom modal at level 0, x ident).
Notation "( x )" := x
  (in custom modal, x at level 90).
Notation "[! m !]" := m
  (at level 0, m custom modal at level 99, format "[!  m  !]").
Notation " p -> q " :=
  (Implies p q) (in custom modal at level 13, right associativity).
Notation " p <-> q " :=
  (And (Implies p q) (Implies q p)) (in custom modal at level 13,
    right associativity).
Notation " p \/ q " :=
  (Or p q) (in custom modal at level 12, left associativity).
Notation " p /\ q " :=
  (And p q) (in custom modal at level 11, left associativity).
Notation " ~ p " := (Neg p)
  (in custom modal at level 9, right associativity, format "~ p").
Notation " [] p " := (Box p)
  (in custom modal at level 9, right associativity, format "[] p").
Notation " <> p " := (Dia p)
  (in custom modal at level 9, right associativity, format "<> p").
Notation " # p " := (Lit p)
  (in custom modal at level 2, no associativity, p constr at level 1,
    format "# p").

Notation "[ F -- V ]" := (Build_Model F V).

Notation "Γ ||= φ" := (entails_modal Γ φ)
  (at level 110, no associativity).

Notation "M |= φ" := (validate_model M φ)
  (at level 110, right associativity).

Notation "φ =|= ψ" := (equivalence φ ψ)
  (at level 110, no associativity).

Notation "M ' w ||- φ" := (fun_validation M w φ)
  (at level 110, right associativity).
