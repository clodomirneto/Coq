Section PropositionalLogic.

Variables P Q : Prop.

Theorem trans : (P -> Q) <-> (~Q -> ~P).
Proof.
unfold iff.
split.
-
intro Hpq.
intro Hnq.
unfold not.
intro Hp.
unfold not in Hnq.
apply Hnq.
apply Hpq.
exact Hp.
-
intro Hnqnp.
intro Hp.


Qed.

End PropositionalLogic.