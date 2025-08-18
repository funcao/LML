Require Import List.

Inductive Singleton {T} (t: T): T -> Prop :=
  | Singleton_mk: Singleton t t.

Definition Union {T} (A B: T -> Prop): T -> Prop :=
  fun t => A t \/ B t.

Definition UnionOf {I T} (A: I -> T -> Prop): T -> Prop :=
  fun t =>
    exists i, A i t.

Definition Subset {T} (A B: T -> Prop): Prop :=
  forall t: T,
  A t -> B t.

Definition Empty {T} (t: T): Prop :=
  False.

Notation Extend p D :=
  (Union (Singleton p) D).

Definition Fin {T} (ps: list T) (q: T): Prop :=
  In q ps.
