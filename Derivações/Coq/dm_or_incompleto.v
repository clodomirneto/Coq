Section PropositionalLogic.

Variables A B : Prop.

Theorem dm_or : ~(A \/ B) <-> (~A /\ ~B).
Proof.
unfold iff.
split.
-
intro Hnab.
split.
+
intro Hna.
unfold not in Hnab.
apply Hnab.
left.
exact Hna.
+
intro Hnb.
unfold not in Hnab.
apply Hnab.
right.
exact Hnb.
-
intro Hnanb.
unfold not.
intro Hab.


Qed.

End PropositionalLogic.