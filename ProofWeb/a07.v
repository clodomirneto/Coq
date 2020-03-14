Require Import ProofWeb.

Parameter P Q : Prop.

Theorem a07 : (P /\ Q) \/ (~P \/ ~Q).

Proof.
PBC H1.
neg_e ((P /\ Q) \/ (~P \/ ~Q)).
exact H1.

Qed.