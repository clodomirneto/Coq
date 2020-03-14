Require Import ProofWeb.

Parameter A B C : Prop.

Hypothesis P1: (A -> (B /\ C)).

Theorem c0n024 : ((A -> B) /\ (A -> C)).
Proof.
con_i.
imp_i H1.
con_e1 C.
imp_e A.
exact P1.
exact H1.
imp_i H2.
con_e2 B.
imp_e A.
exact P1.
exact H2.
Qed.