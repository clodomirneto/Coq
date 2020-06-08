Require Import ProofWeb.

Parameter A B : Prop.

Hypothesis P1: (A -> (A -> B)).

Theorem c0n005 : (A -> B).
Proof.
imp_i H1.
imp_e A.
imp_e A.
exact P1.
exact H1.
exact H1.
Qed.