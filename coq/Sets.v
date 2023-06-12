Require Import List.

Inductive Singleton {T} (t: T): T -> Prop :=
  | Singleton_mk: Singleton t t.

Definition Union {T} (A B: T -> Prop): T -> Prop :=
  fun t => A t \/ B t.

Definition Subset {T} (A B: T -> Prop): Prop :=
  forall t: T,
  A t -> B t.
