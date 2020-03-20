Require Import ProofWeb.

Parameter P Q R S : Prop.

Hypothesis P1 : (P /\ Q) -> (R /\ S).

Hypothesis P2 : ~~P.

Hypothesis P3 : Q.

Theorem b03 : S.

Proof.
con_e2 (R).
imp_e (P /\ Q).
exact P1.
con_i.
PBC H1.
neg_e (~P).
exact P2.
exact H1.
exact P3.
Qed.
