Require Import ProofWeb.

Parameter P Q : Prop.

Hypothesis P1 : P.

Hypothesis P2 : ~~(P -> Q).

Theorem b05 : Q \/ ~Q.

Proof.
dis_i1.
imp_e (P).
PBC H1.
neg_e (~(P -> Q)).
exact P2.
exact H1.
exact P1.
Qed.
