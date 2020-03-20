Section PropositionalLogic.

Variables A B : Prop.

Theorem com : (A /\ B) <-> (B /\ A).
Proof.
unfold iff.
split.
-
intro Hab.
split.
*
destruct Hab as [Ha Hb].
exact Hb.
*
destruct Hab as [Ha Hb].
exact Ha.
-
intro Hba.
split.
+
destruct Hba as [Hb Ha].
exact Ha.
+
destruct Hba as [Hb Ha].
exact Hb.
Qed.

End PropositionalLogic.