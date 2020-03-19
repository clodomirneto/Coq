Section PropositionalLogic.

Variables A B C D : Prop.

Hypothesis P1 : A \/ B.

Hypothesis P2 : A -> C.

Hypothesis P3 : B -> D.

Theorem dc : C \/ D.
Proof.
destruct P1 as [Ha | Hb].
left.
apply P2.
exact Ha.
right.
apply P3.
exact Hb.
Qed.

End PropositionalLogic.