Section PropositionalLogic.

Variables A B : Prop.

Theorem trans : (A -> B) <-> (~B -> ~A).
Proof.
unfold iff.
split.
-
intro Hab.
intro Hnq.
unfold not.
intro Ha.
unfold not in Hnq.
apply Hnq.
apply Hab.
exact Ha.
-
intro Hnbna.
intro Ha.

Qed.

End PropositionalLogic.