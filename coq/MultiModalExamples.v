Require Import Arith List Notations Classical MultiModalCore Modal_Library Modal_Notations.
Export ListNotations.

Section MultimodalExample.

  (*
    For this example, we will define the systems KT and K4 that were presented in
    the Proof of Concept by means of the multimodal library
  *)

  Variable Worlds: Set. (* World Set *)

  Variables KTindex K4index: nat.
  Variables KTRel K4Rel: Worlds -> Worlds -> Prop.
  (* Variable dummyRel: forall X:Set, X -> X -> Prop. *)

  Variable KTCond: reflexive_rel  Worlds KTRel.
  Variable K4Cond: transitive_rel Worlds K4Rel.

  (* Variable teste1: length [KTRel; K4Rel] = 2. *)
  (* Variable teste2: length [(reflexive_rel Worlds KTRel); (transitive_rel Worlds K4Rel)] = 2. *)

  (* Definition KTFrame: Frame := Build_Frame Worlds KTRel.
  Definition K4Frame: Frame := Build_Frame Worlds K4Rel.

  Definition KT4Frame: nFrame 2 := Build_nFrame 2 Worlds [KTRel; K4Rel]
    [(reflexive_rel Worlds KTRel); (transitive_rel Worlds K4Rel)] teste1 teste2.

  Definition KTFrame': Frame := nFrame_to_Frame 2 dummyRel KT4Frame KTindex.
  Definition K4Frame': Frame := nFrame_to_Frame 2 dummyRel KT4Frame K4index.

  Definition KTFormula (φ: formula): MMformula := formula_to_MMformula φ KTindex.
  Definition K4Formula (φ: formula): MMformula := formula_to_MMformula φ K4index. *)

End MultimodalExample.