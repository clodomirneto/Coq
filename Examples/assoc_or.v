Section PropositionalLogic.

Variables P Q R : Prop.

Theorem assoc : (P \/ (Q \/ R)) <-> ((P \/ Q) \/ R).
Proof.
unfold iff.
split.
-
intro Hpqr.
destruct Hpqr as [Hp | [Hq | Hr]].
left.
left.
exact Hp.
left.
right.
exact Hq.
right.
exact Hr.
-
intro Hpqr.
destruct Hpqr as [[Hp | Hq] | Hr].
left.
exact Hp.
right.
left.
exact Hq.
right.
right.
exact Hr.
Qed.

End PropositionalLogic.