Section PropositionalLogic.

Variables P Q R : Prop.

Theorem assoc : (P /\ (Q /\ R)) <-> ((P /\ Q) /\ R).
Proof.
unfold iff.
split.
-
intro Hpqr.
split.
*
destruct Hpqr as [Hp Hqr].
split.
+
exact Hp.
+
destruct Hqr as [Hq Hr].
exact Hq.
*
destruct Hpqr as [Hp Hqr].
destruct Hqr as [Hq Hr].
exact Hr.
-
intro Hpqr.
split.
*
destruct Hpqr as [Hpq Hr].
destruct Hpq as [Hp Hq].
exact Hp.
*
split.
+
destruct Hpqr as [Hpq Hr].
destruct Hpq as [Hp Hq].
exact Hq.
+
destruct Hpqr as [Hpq Hr].
exact Hr.
Qed.

End PropositionalLogic.