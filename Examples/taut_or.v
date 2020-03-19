Section PropositionalLogic.

Variables P : Prop.

Theorem taut : P <-> (P \/ P).
Proof.
unfold iff.
split.
-
intro Hp.
left.
exact Hp.
-
intro Hpp.
destruct Hpp as [Hp | Hp1].
exact Hp.
exact Hp1.
Qed.

End PropositionalLogic.