Section PropositionalLogic.

Variables P Q : Prop.

Theorem im : (P -> Q) <-> (~P \/ Q).
Proof.
unfold iff.
split.
-
intro Hpq.
left.
unfold not.
intro Hp.

-

Qed.

End PropositionalLogic.