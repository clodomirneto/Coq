Section PropositionalLogic.

Variables P : Prop.

Theorem taut : P <-> (P /\ P).
Proof.
unfold iff.
split.
-
intro Hp.
split.
*
exact Hp.
*
exact Hp.
-
intro Hpp.
destruct Hpp as [Hp Hp1].
exact Hp.
Qed.

End PropositionalLogic.