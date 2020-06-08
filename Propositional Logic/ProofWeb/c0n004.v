Require Import ProofWeb.

Parameter A B C : Prop.

Hypothesis P1: ((A -> B) -> (A -> C)).

Theorem c0n004 : (A -> (B -> C)).
Proof.
imp_i H1.
imp_i H2.
imp_e A.
imp_e (A -> B).
exact P1.
imp_i H3.
exact H2.
exact H1.
Qed.