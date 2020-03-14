Require Import ProofWeb.

Variables P Q : Prop.
Variable R : D -> Prop.

Hypothesis P1 : exi x,R(x). 

Theorem c1n025 : exi y,(P \/ R(y) \/ Q).
Proof.
exi_e (exi x, R(x)) a H1.
exact P1.
exi_i a.
dis_i2.
dis_i1.
exact H1.
Qed.