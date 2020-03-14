Require Import ProofWeb.

Parameter A B C : Prop.

Theorem c0n009 : (A  ->  B)  ->  A  ->  (B  ->  C)  ->  C.
Proof.
imp_i H1.
imp_i H2.
imp_i H3.
imp_e B.
exact H3.
imp_e A.
exact H1.
exact H2.
Qed.