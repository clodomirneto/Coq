Section PropositionalLogic.

Variables A B : Prop.

Hypothesis P1 : A -> B.

Hypothesis P2 : ~B.

Theorem mt : ~A.
Proof.
unfold not.
intro Ha.
unfold not in P2.
apply P2.
apply P1.
exact Ha.
Qed.

End PropositionalLogic.