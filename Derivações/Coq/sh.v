Section PropositionalLogic.

Variables A B C: Prop.

Hypothesis P1 : A -> B.

Hypothesis P2 : B -> C.

Theorem sh : A -> C.
Proof.
intro Ha.
apply P2.
apply P1.
exact Ha.
Qed.

End PropositionalLogic.