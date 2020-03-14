Require Import ProofWeb.

Variable P: Prop.
Variable R: D -> Prop.

Hypothesis P1 : all x,(R(x)->P).

Theorem c1n009 : (exi x,R(x))->P.
Proof.
imp_i H1.
exi_e (exi x, R(x)) a H2.
exact H1.
imp_e (R(a)).
all_e (all x, (R(x) -> P)).
exact P1.
exact H2.
Qed.