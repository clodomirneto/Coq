Section PropositionalLogic.

Variables A B : Prop.

Hypothesis P : A -> B.

Theorem abs : A -> (A /\ B).
Proof.
intro Ha.
split.
-
exact Ha.
-
apply P.
exact Ha.
Qed.

End PropositionalLogic.