Require Import ProofWeb.

Parameter P Q R : Prop.

Hypothesis P1 : (P /\ Q) -> R.

Hypothesis P2 : P.

Theorem b12 : Q -> R.

Proof.
imp_i H1.
imp_e (P /\ Q).
exact P1.
con_i.
exact P2.
exact H1.
Qed.
