Section PropositionalLogic.

Variables A B : Prop.

Theorem com_or : (A \/ B) <-> (B \/ A).
Proof.
unfold iff.
split.
-
intro Hab.
destruct Hab as [Ha | Hb].
right.
exact Ha.
left.
exact Hb.
-
intro Hba.
destruct Hba as [Hb | Ha].
right.
exact Hb.
left.
exact Ha.
Qed.

End PropositionalLogic.