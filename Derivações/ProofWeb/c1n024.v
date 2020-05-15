Require Import ProofWeb.

Variables R S: D -> Prop.

Hypothesis P1 : exi x,(R(x) /\ S(x)).

Theorem c1n024 : exi y,R(y) /\ exi z,S(z).
Proof.
exi_e (exi x, (R(x) /\ S(x))) a H1.
exact P1.
con_i.
exi_i a.
con_e1 (S(a)).
exact H1.
exi_i a.
con_e2 (R(a)).
exact H1.
Qed.