Section PropositionalLogic.

Variables A B C : Prop.

Theorem exp : ((A /\ B) -> C) <-> (A -> (B -> C)).
Proof.
unfold iff.
split.
-
intro Habc.
intro Ha.
intro Hb.
apply Habc.
split.
*
exact Ha.
*
exact Hb.
-
intro Habc.
intro Hab.
apply Habc.
destruct Hab as [Ha Hb].
exact Ha.
destruct Hab as [Ha Hb].
exact Hb.
Qed.

End PropositionalLogic.