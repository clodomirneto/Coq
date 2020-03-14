Require Import ProofWeb.

Variables R S: D -> Prop.

Hypothesis P1 : exi x,(R(x) \/ S(x)). 

Theorem c1n026 : exi y,R(y) \/ exi z,S(z).
Proof.
exi_e (exi x, (R(x) \/ S(x))) a H1.
exact P1.
dis_e (R(a) \/ S(a)) H2 H3.
exact H1.
dis_i1.
exi_i a.
exact H2.
dis_i2.
exi_i a.
exact H3.
Qed.