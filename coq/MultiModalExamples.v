Require Import Arith List Notations Classical MultiModalCore.
Export ListNotations.

Section ThreeWiseManExample.

(*
  For this example, we will model the puzzle of the three wise man and the king
    (A common variant deals with three wise man, a king and several colored hats)

  We will base this example on the presentation by Benzmüller on his paper:
    "Universal (meta-)logical reasoning: Recent Successes"

  The puzzle statement, as adapted by Benzmüller is as follows:
    "Once upon a time, a king wanted to find the wisest out of his three wisest men.
    He arranged them in a circle and told them that he would put a white or a black spot on their foreheads
    and that one of the three spots would certainly be white.
    The three wise men could see and hear each other but, of course, they could not see their faces reflected anywhere.
    The king, then, asked to each of them to find out the colour of his own spot.
    After a while, the wisest correctly answered that his spot was white."

  In this puzzle, it is only needed to represent the knowledge of each philosopher and knowledge common to all
    philosophers, both of which can be done with S5 modalities
*)

  (** First for some Definitions **)

  (*
    The wise men are represented implicitly by 3 relations, and the knowledge of each agent is
      represented by a modality which is evaluated by that relation
    It is also defined an inductive type as a helper for the latter conclusions
    Their common knowledge is represented by the transitive closure of the union of all relations
  *)

  (* The wise man are represented by an inductive type indexed by natural numbers *)
  Inductive wise: nat -> Prop :=
  | WiseManA: wise 0
  | WiseManB: wise 1
  | WiseManC: wise 2.

  (* Next we define the components for the model in which we will derive the conclusions of the puzzle *)
  Variable Worlds: Set.
  Variable Valuation: nat -> Worlds -> Prop.
  Variables RelA RelB RelC: Worlds -> Worlds -> Prop.
  Definition Modalities := 4.

  Definition S5_rel (R: Worlds -> Worlds -> Prop) :=
            reflexive_rel Worlds R /\ transitive_rel Worlds R /\ euclidean_rel Worlds R.
  Definition rel_union (R1 R2: Worlds -> Worlds -> Prop) (x y: Worlds): Prop := (R1 x y) \/ (R2 x y).
  Definition sub_rel (R1 R2: Worlds -> Worlds -> Prop): Prop := forall x y, (R1 x y) -> (R2 x y).
  Definition trans_closure (R1: Worlds -> Worlds -> Prop) (x y: Worlds): Prop := forall R2,
              transitive_rel Worlds R2 -> (sub_rel R1 R2 -> R2 x y).

  Hypothesis KnowledgeAisS5: S5_rel RelA.
  Hypothesis KnowledgeBisS5: S5_rel RelB.
  Hypothesis KnowledgeCisS5: S5_rel RelC.
  Definition RelCK := trans_closure (rel_union (rel_union RelA RelB) RelC).

  Definition Rels := (RelA :: RelB :: RelC :: RelCK :: nil).

  Corollary frameCondition: length Rels = 4.
  Proof. auto. Qed.

  (* We now define both the frame and model *)
  Definition ExampleFrame := Build_nFrame 4 Worlds Rels frameCondition.
  Definition ExampleModel := Build_nModel 4 ExampleFrame Valuation.

  (* Knowldge of each wise man is represent by an S5 modality whose index is the same as it's relation *)
  Notation "[A] f" := (MMBox 0 f) (in custom multi_modal at level 10, no associativity).
  Notation "[B] f" := (MMBox 1 f) (in custom multi_modal at level 10, no associativity).
  Notation "[C] f" := (MMBox 2 f) (in custom multi_modal at level 10, no associativity).
  Notation "[K] f" := (MMBox 3 f) (in custom multi_modal at level 10, no associativity).
  (* Common knowledge is represent by knowledge shared by all agents,
    which is associated to the RelCK relation *)

  (* The WhiteSpot is simply an atom *)
  Definition white_spot' := fun i => MMLit i.

  (* Some notation to make the proof easier to read *)
  Notation "[WA]"   := (white_spot' 0) (in custom multi_modal at level 14, no associativity).
  Notation "[WB]"   := (white_spot' 1) (in custom multi_modal at level 14, no associativity).
  Notation "[WC]"   := (white_spot' 2) (in custom multi_modal at level 14, no associativity).
  Notation "[W i ]" := (white_spot' i) (in custom multi_modal at level 14, no associativity).

  Definition val := validity_in_model 4 ExampleModel.
  Notation "M |= f" := (val f) (at level 110, right associativity).

  (* Hypothesis 1: It is common knowledge that at least one wise man has a white spot*)
  Hypothesis OneWhiteSpot: M |= <! [K] ( [WA] \/ [WB] \/ [WC]) !>.

  (* Hypothesis 2: It is common knowledge that if x has a white spot, then y knows that*)
  Hypothesis EveryoneSeesWhiteSpots: forall x y, wise x -> wise y -> x <> y ->
              M |= <! [K] ([W x] -> [y]([W x]))!>.

  (* Hypothesis 3: It is common knowledge that if x does not have a white spot, then y knows that*)
  Hypothesis EveryoneSeesNoWhiteSpot: forall x y, wise x -> wise y -> x <> y ->
              M |= <! [K](~ [W x] -> [y](~ [W x])) !>.

  (* Hypothesis 4: It is common knowledge that wise man 0 does not wether he has a white spot*)
  Hypothesis WiseADoesNotKnow: M |= <! [K] ~([A] [WA]) !>.

  (* Hypothesis 5: It is common knowledge that wise man 1 does not wether he has a white spot*)
  Hypothesis WiseBDoesNotKnow: M |= <! [K] ~([B] [WB]) !>.

  (*
    Some additional facts about the relations and the knowledge of the agents
      - The common knowledge relation is transitive (it is the transitive closure of some relation)
      - If f is common knowledge amidst the agents, then each agent knows it
      - If an agent knows something, it is true (axiom T)
        + If something is common knowledge amidst the agents, then it is true
          (Joining the 2 previous facts)
      - If an agent knows something, then it knows it knows that (axiom 4)
      - If an agent knows that φ implies ψ, then if it know φ it will know ψ (axiom K)
  *)

  Hypothesis CommonKnowledgeImpliesKnowledgebyAll: forall x φ, wise x ->
              (M |= <! [K] φ !>) -> M |= <! [x] φ !>.

  Hypothesis CommonKnowledgeTrue: forall φ,
              (M |= <! [K] φ !>) -> M |= <! φ !>.

  Hypothesis AgentKnowledgeTrue: forall x φ, wise x ->
              (M |= <! [x] φ !>) -> M |= <! φ !>.

  Hypothesis AgentKnowledgeTrueContra: forall x φ, wise x ->
              ~ (M |= <! φ !>) -> ~(M |= <! [x] φ !>).

  Hypothesis AgentKnowledgeRepeats: forall x φ, wise x ->
              (M |= <! [x] φ !>) -> M |= <! [x][x] φ !>.

  Hypothesis AgentKnowledgeImplication: forall x φ ψ, wise x ->
              (M |= <! [x](φ -> ψ) !>) -> M |= <! ([x] φ -> [x] ψ) !>.

  Theorem WiseCDoesKnow: M |= <! [C] [WC] !>.
  Proof.
    (*Defining the agents inside the proof*)
    assert (WiseA: wise 0) by constructor;
    assert (WiseB: wise 1) by constructor;
    assert (WiseC: wise 2) by constructor.
  Abort.
End ThreeWiseManExample.
