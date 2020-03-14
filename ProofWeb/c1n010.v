Require Import ProofWeb.

Variable P: Prop.
Variable R: D -> Prop.

Hypothesis P1 : exi x,(R(x)->P).

Theorem c1n010 : (all x,R(x))->P.
Proof.
imp_i H1.
exi_e (exi x, (R(x) -> P)) a H2.
exact P1.
imp_e (R(a)).
exact H2.
all_e (all x, R(x)).
exact H1.
Qed.