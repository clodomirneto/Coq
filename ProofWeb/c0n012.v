Require Import ProofWeb.

Parameter A B C D : Prop.

Theorem c0n012 : (A  ->  B)  ->  A  ->  ((A  ->  B)  ->  C  ->  B  ->  D)  ->  ((A  ->  B)  ->  C)  ->  D.
Proof.
imp_i H1.
imp_i H2.
imp_i H3.
imp_i H4.
imp_e B.
imp_e C.
imp_e (A -> B).
exact H3.
exact H1.
imp_e (A -> B).
exact H4.
exact H1.
imp_e A.
exact H1.
exact H2.
Qed.