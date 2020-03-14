Require Import ProofWeb.

Variables R S: D -> Prop.

Hypothesis P1 : exi x,R(x) \/ exi y,S(y). 

Theorem c1n027 : exi z,(R(z) \/ S(z)).
Proof.
dis_e (exi x, R(x) \/ exi y, S(y)) H1 H2.
exact P1.
exi_e (exi x, R(x)) a H3.
exact H1.
exi_i a.
dis_i1.
exact H3.
exi_e (exi y, S(y)) a H4.
exact H2.
exi_i a.
dis_i2.
exact H4.
Qed.