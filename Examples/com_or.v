Section PropositionalLogic.

Variables P Q : Prop.

Theorem com : (P \/ Q) <-> (Q \/ P).
Proof.
unfold iff.
split.
-
intro Hpq.
destruct Hpq as [Hp | Hq].
right.
exact Hp.
left.
exact Hq.
-
intro Hqp.
destruct Hqp as [Hq | Hp].
right.
exact Hq.
left.
exact Hp.
Qed.

End PropositionalLogic.