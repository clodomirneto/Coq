Section PropositionalLogic.

Variables A B : Prop.

Theorem im : (A -> B) <-> (~A \/ B).
Proof.
unfold iff.
split.
-
intro Hpq.

-

Qed.

End PropositionalLogic.