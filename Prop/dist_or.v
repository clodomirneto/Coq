Section PropositionalLogic.

Variables A B C : Prop.

Theorem dist_or : (A \/ (B /\ C)) <-> ((A \/ B) /\ (A \/ C)).
Proof.
unfold iff.
split.
-
intro Habc.
destruct Habc as [Ha | [Hb Hc]].
split.
*
left.
exact Ha.
*
left.
exact Ha.
*
split.
+
right.
exact Hb.
+
right.
exact Hc.
-
intro Habc.
destruct Habc as [Hab Hac].
destruct Hab as [Ha | Hb].
left.
exact Ha.
destruct Hac as [Ha | Hc].
left.
exact Ha.
right.
split.
exact Hb.
exact Hc.
Qed.

End PropositionalLogic.