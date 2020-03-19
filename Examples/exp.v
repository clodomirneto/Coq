Section PropositionalLogic.

Variables P Q R : Prop.

Theorem exp : ((P /\ Q) -> R) <-> (P -> (Q -> R)).
Proof.
unfold iff.
split.
-
intro Hpqr.
intro Hp.
intro Hq.
apply Hpqr.
split.
*
exact Hp.
*
exact Hq.
-
intro Hpqr.
intro Hpq.
apply Hpqr.
destruct Hpq as [Hp Hq].
exact Hp.
destruct Hpq as [Hp Hq].
exact Hq.
Qed.

End PropositionalLogic.