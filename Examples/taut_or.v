Section PropositionalLogic.

Variables A : Prop.

Theorem taut_or : A <-> (A \/ A).
Proof.
unfold iff.
split.
-
intro Ha.
left.
exact Ha.
-
intro Haa.
destruct Haa as [Ha | Ha1].
exact Ha.
exact Ha1.
Qed.

End PropositionalLogic.