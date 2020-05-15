Require Import ProofWeb.

Parameter A B C : Prop.

Hypothesis P1: (A -> B).

Theorem c0n018 : ((C /\ A) -> (B /\ C)).
Proof.
imp_i H1.
con_i.
imp_e A.
exact P1.
con_e2 C.
exact H1.
con_e1 A.
exact H1.
Qed.