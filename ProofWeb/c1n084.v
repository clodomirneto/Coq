Require Import ProofWeb.

Variables F G : D -> Prop.

Hypothesis P1 : exi x,F(x) \/ exi x,G(x).
Hypothesis P2 : all x,(F(x) -> G(x)).

Theorem c1n084 : exi x,G(x).
Proof.
dis_e (exi x, F(x) \/ exi x, G(x)) H1 H2.
exact P1.
exi_e (exi x, F(x)) a H3.
exact H1.
exi_i a.
imp_e (F(a)).
all_e (all x, (F(x) -> G(x))).
exact P2.
exact H3.
exact H2.
Qed.