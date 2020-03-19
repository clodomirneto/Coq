Section PropositionalLogic.

Variables A B : Prop.

Hypothesis P1 : A \/ B.

Hypothesis P2 : ~A.

Theorem sd : B.
Proof.
destruct P1 as [Ha | Hb].
contradiction.
exact Hb.
Qed.

End PropositionalLogic.