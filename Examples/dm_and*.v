Section PropositionalLogic.

Variables A B : Prop.

Theorem dm : ~(A /\ B) <-> (~A \/ ~B).
Proof.
unfold iff.
split.
-
intro Hnpq.

-
Qed.

End PropositionalLogic.