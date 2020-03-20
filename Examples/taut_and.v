Section PropositionalLogic.

Variables A : Prop.

Theorem taut_and : A <-> (A /\ A).
Proof.
unfold iff.
split.
-
intro Ha.
split.
*
exact Ha.
*
exact Ha.
-
intro Haa.
destruct Haa as [Ha Ha1].
exact Ha.
Qed.

End PropositionalLogic.