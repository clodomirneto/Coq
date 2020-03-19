Section PropositionalLogic.

Variables P Q R : Prop.

Theorem dist : (P /\ (Q \/ R)) <-> ((P /\ Q) \/ (P /\ R)).
Proof.
unfold iff.
split.
-
intro Hpqr.
destruct Hpqr as [Hp Hqr].
destruct Hqr as [Hq | Hr].
left.
split.
*
exact Hp.
*
exact Hq.
*
right.
split.
+
exact Hp.
+
exact Hr.
-
intro Hpqr.
destruct Hpqr as [Hpq | Hpr].
split.
*
destruct Hpq as [Hp Hq].
exact Hp.
*
left.
destruct Hpq as [Hp Hq].
exact Hq.
*
split.
+
destruct Hpr as [Hp Hr].
exact Hp.
+
right.
destruct Hpr as [Hp Hr].
exact Hr.
Qed.

End PropositionalLogic.