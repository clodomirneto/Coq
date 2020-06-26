Section PropositionalLogic.

Variables A B C D : Prop.

Hypothesis P1 : ~C \/ ~D.

Hypothesis P2 : A -> C.

Hypothesis P3 : B -> D.

Theorem dd : ~A \/ ~B.
Proof.
destruct P1 as [Hnc | Hnd].
left.
unfold not.
intro Ha.
unfold not in Hnc.
apply Hnc.
apply P2.
exact Ha.
right.
unfold not.
unfold not in Hnd.
intro Hb.
apply Hnd.
apply P3.
exact Hb.
Qed.

End PropositionalLogic.