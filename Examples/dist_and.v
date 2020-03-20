Section PropositionalLogic.

Variables A B C : Prop.

Theorem dist_and : (A /\ (B \/ C)) <-> ((A /\ B) \/ (A /\ C)).
Proof.
unfold iff.
split.
-
intro Habc.
destruct Habc as [Ha Hbc].
destruct Hbc as [Hb | Hc].
left.
split.
*
exact Ha.
*
exact Hb.
*
right.
split.
+
exact Ha.
+
exact Hc.
-
intro Habc.
destruct Habc as [Hab | Hac].
split.
*
destruct Hab as [Ha Hb].
exact Ha.
*
left.
destruct Hab as [Ha Hb].
exact Hb.
*
split.
+
destruct Hac as [Ha Hc].
exact Ha.
+
right.
destruct Hac as [Ha Hc].
exact Hc.
Qed.

End PropositionalLogic.