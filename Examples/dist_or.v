Section PropositionalLogic.

Variables P Q R : Prop.

Theorem dist : (P \/ (Q /\ R)) <-> ((P \/ Q) /\ (P \/ R)).
Proof.
unfold iff.
split.
-
intro Hpqr.
destruct Hpqr as [Hp | [Hq Hr]].
split.
*
left.
exact Hp.
*
left.
exact Hp.
*
split.
+
right.
exact Hq.
+
right.
exact Hr.
-
intro Hpqr.
destruct Hpqr as [Hpq Hpr].
destruct Hpq as [Hp | Hq].
left.
exact Hp.
destruct Hpr as [Hp | Hr].
left.
exact Hp.
right.
split.
exact Hq.
exact Hr.
Qed.

End PropositionalLogic.