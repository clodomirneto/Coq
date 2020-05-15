Require Import ProofWeb.

Parameter P Q : Prop.

Theorem a08 : Q -> (P \/ ~P).

Proof.
imp_i H1.
PBC H2.
neg_e (P \/ ~P).
exact H2.
dis_i2.
neg_i H3.
neg_e P.
neg_i H4.
neg_e (P \/ ~P).
exact H2.
dis_i1.
exact H4.
exact H3.
Qed.