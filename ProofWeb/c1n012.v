Require Import ProofWeb.

Variable P: Prop.
Variable R: D -> Prop.

Hypothesis P1 : exi x,(R(x) \/ P).

Theorem c1n012 : (exi x,R(x)) \/ P.
Proof.
exi_e (exi x, (R(x) \/ P)) a H1.
exact P1.
dis_e (R(a) \/ P) H2 H3.
exact H1.
dis_i1.
exi_i a.
exact H2.
dis_i2.
exact H3.
Qed.