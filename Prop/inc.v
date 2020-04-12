Section PL.

Variables A B : Prop.

Hypothesis P1 : A.
Hypothesis P2 : ~A.

Theorem inc : B.
Proof.
contradiction.
Qed.

End PL.