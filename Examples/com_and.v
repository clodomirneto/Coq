Section PropositionalLogic.

Variables P Q : Prop.

Theorem com : (P /\ Q) <-> (Q /\ P).
Proof.
unfold iff.
split.
-
intro Hpq.
split.
*
destruct Hpq as [Hp Hq].
exact Hq.
*
destruct Hpq as [Hp Hq].
exact Hp.
-
intro Hqp.
split.
+
destruct Hqp as [Hq Hp].
exact Hp.
+
destruct Hqp as [Hq Hp].
exact Hq.
Qed.

End PropositionalLogic.