Require Import ProofWeb.

Parameter P Q: Prop.

Theorem a04: P->(Q->(P /\ Q)).

Proof.
imp_i H1.
imp_i H2.
con_i.
exact H1.
exact H2.
Qed.