Require Import ProofWeb.

Parameter A B C : Prop.

Hypothesis P1: (A -> (B -> C)).

Theorem c0n006 : (B -> (A -> C)).
Proof.
imp_i H1.
imp_i H2.
imp_e B.
imp_e A.
exact P1.
exact H2.
exact H1.
Qed.