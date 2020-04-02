Require Import Coq.Logic.Classical_Prop.

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
generalize(classic B); intro.
destruct H.
exact H.
apply Hnbna in H.
contradiction.
Qed.

End PropositionalLogic.