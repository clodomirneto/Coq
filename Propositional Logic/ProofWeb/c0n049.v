Require Import ProofWeb.

Parameter A : Prop.

Hypothesis P1: ~~~A.

Theorem c0n049 : ~A.
Proof.
PBC H1.
neg_e (~~A).
exact P1.
exact H1.
Qed.