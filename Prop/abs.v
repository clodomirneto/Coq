Section PropositionalLogic.

Variables A B : Prop.

Hypothesis P1 : A -> B.

Theorem abs : A -> (A /\ B).
Proof.
intro Ha.
split.
- 
exact Ha.
-
apply P1.
exact Ha.
Qed.

End PropositionalLogic.