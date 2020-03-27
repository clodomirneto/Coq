Section PropositionalLogic.

Variables A B : Prop.

Theorem dm_and : ~(A /\ B) <-> (~A \/ ~B).
Proof.
unfold iff.
split.
-
intro Hnab.
unfold not in Hnab.
left.
unfold not.
intro Ha.
apply Hnab.
split.
*
exact Ha.
*



-
Qed.

End PropositionalLogic.