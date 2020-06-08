Require Import ProofWeb.

Parameter A B C : Prop.

Theorem c0n010 : (A  ->  B  ->  C)  ->  A  ->  (A  ->  B)  ->  C.
Proof.
imp_i H1.
imp_i H2.
imp_i H3.
imp_e B.
imp_e A.
exact H1.
exact H2.
imp_e A.
exact H3.
exact H2.
Qed.