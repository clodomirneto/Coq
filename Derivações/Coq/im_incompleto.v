Require Import Coq.Logic.Classical_Prop.

Section PropositionalLogic.

Variables A B : Prop.

Theorem im : (A -> B) <-> (~A \/ B).
Proof.
unfold iff.
split.
-
unfold not.
intro Hab.
right.
apply Hab.
generalize(classic B); intro.
destruct H.

-

Qed.

End PropositionalLogic.