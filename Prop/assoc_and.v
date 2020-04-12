Section PL.

Variables A B C : Prop.

Theorem assoc_and : (A /\ (B /\ C)) <-> ((A /\ B) /\ C).
Proof.
unfold iff.
split.
-
intro Habc.
split.
*
destruct Habc as [Ha Hbc].
split.
+ exact Ha.
+
destruct Hbc as [Hb Hc].
exact Hb.
*
destruct Habc as [Ha Hbc].
destruct Hbc as [Hb Hc].
exact Hc.
-
intro Habc.
split.
*
destruct Habc as [Hab Hc].
destruct Hab as [Ha Hb].
exact Ha.
*
split.
+
destruct Habc as [Hab Hc].
destruct Hab as [Ha Hb].
exact Hb.
+
destruct Habc as [Hab Hc].
exact Hc.
Qed.

End PL.