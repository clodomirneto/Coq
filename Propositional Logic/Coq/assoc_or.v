Section PropositionalLogic.

Variables A B C : Prop.

Theorem assoc_or : (A \/ (B \/ C)) <-> ((A \/ B) \/ C).
Proof.
unfold iff.
split.
-
intro Habc.
destruct Habc as [Ha | [Hb | Hc]].
left.
left.
exact Ha.
left.
right.
exact Hb.
right.
exact Hc.
-
intro Habc.
destruct Habc as [[Ha | Hb] | Hc].
left.
exact Ha.
right.
left.
exact Hb.
right.
right.
exact Hc.
Qed.

End PropositionalLogic.