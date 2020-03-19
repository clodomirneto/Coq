Section PropositionalLogic.

Variables P Q : Prop.

Theorem dm : ~(P \/ Q) <-> (~P /\ ~Q).
Proof.
unfold iff.
split.
-
intro Hnpq.

-
Qed.

End PropositionalLogic.