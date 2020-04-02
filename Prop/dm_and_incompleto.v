Require Import Coq.Logic.Classical_Prop.

Section PropositionalLogic.

Variables A B : Prop.

Theorem dm_and : ~(A /\ B) <-> (~A \/ ~B).
Proof.
unfold iff.
split.
-
intro Hnab.
unfold not in Hnab.
left.
unfold not.
intro Ha.
apply Hnab.
split.
*
exact Ha.
*
generalize(classic B); intro.
destruct H.
exact H.
unfold not in H.
apply H.
contradiction.

-
Qed.

End PropositionalLogic.