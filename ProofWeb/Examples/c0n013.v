Require Import ProofWeb.

Parameter A B C D : Prop.

Theorem c0n013 : (A  ->  B  ->  C  ->  D)  ->  A  ->  ((A  ->  B  ->  C  ->  D)  ->  B)  ->  ((A  ->  B  ->  C  ->  D)  -> C)  ->  D.
Proof.
imp_i H1.
imp_i H2.
imp_i H3.
imp_i H4.
imp_e C.
imp_e B.
imp_e A.
exact H1.
exact H2.
imp_e (A -> B -> C -> D).
exact H3.
exact H1.
imp_e (A -> B -> C -> D).
exact H4.
exact H1.
Qed.