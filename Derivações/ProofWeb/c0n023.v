Require Import ProofWeb.

Parameter A B C : Prop.

Hypothesis P1: ((A -> B) /\ (A -> C)).

Theorem c0n023 : (A -> (B /\ C)).
Proof.
imp_i H1.
con_i.
imp_e A.
con_e1 (A -> C).
exact P1.
exact H1.
imp_e A.
con_e2 (A -> B).
exact P1.
exact H1.
Qed.