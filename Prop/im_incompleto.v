Section PropositionalLogic.

Variables A B : Prop.

Theorem im : (A -> B) <-> (~A \/ B).
Proof.
unfold iff.
split.
-
unfold not.
intro Hab.
right.
apply Hab.



-

Qed.

End PropositionalLogic.