Section PropositionalLogic.

Variables A B : Prop.

Theorem trans : (A -> B) <-> (~B -> ~A).
Proof.
unfold iff.
split.
-
intro Hab.
unfold not.
intro Hbf.
intro Ha.
apply Hbf.
apply Hab.
exact Ha.
-
intro Hnbna.
intro Ha.

Qed.

End PropositionalLogic.