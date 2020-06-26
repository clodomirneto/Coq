From LF Require Export ml1_soundness.
Require Export Decidable.
Set Implicit Arguments.
Export ListNotations.

Module Type mod_complete (B: mod_base) (S: mod_sound B).
Import B S.

Inductive NNF : Set :=
| NPos : VProp -> NNF
| NNeg : VProp -> NNF
| NBot : NNF
| NTop : NNF
| NConj : NNF -> NNF -> NNF
| NDisj : NNF -> NNF -> NNF.

Fixpoint MakeNNF (A : FProp) : NNF := match A with
| # P => NPos P
| ⊥ => NBot
| B ∨ C => NDisj (MakeNNF B) (MakeNNF C)
| B ∧ C => NConj (MakeNNF B) (MakeNNF C)
| B → C => NDisj (MakeNNFN B) (MakeNNF C)
end
with MakeNNFN (A : FProp) : NNF := match A with
| # P => NNeg P
| ⊥ => NTop
| B ∨ C => NConj (MakeNNFN B) (MakeNNFN C)
| B ∧ C => NDisj (MakeNNFN B) (MakeNNFN C)
| B → C => NConj (MakeNNF B) (MakeNNFN C)
end.

Fixpoint NNFtoFProp (A : NNF) : FProp := match A with
| NPos P => # P
| NNeg P => ¬ # P
| NBot => ⊥
| NTop => ¬ ⊥
| NConj B C => NNFtoFProp B ∧ NNFtoFProp C
| NDisj B C => NNFtoFProp B ∨ NNFtoFProp C
end.

Inductive Literal :=
| LPos : VProp -> Literal
| LNeg : VProp -> Literal
| LBot : Literal
| LTop : Literal.

Fixpoint Bar P := match P with
| LPos Q => LNeg Q
| LNeg Q => LPos Q
| LBot => LTop
| LTop => LBot
end.

Fixpoint LiteraltoFProp (P : Literal) : FProp :=
match P with
| LPos Q => # Q
| LNeg Q => ¬ # Q
| LBot => ⊥
| LTop => ¬ ⊥
end.

Definition Clause := list Literal.

Definition ClausetoFProp := map_fold_right LiteraltoFProp Disj ⊥.

Definition CNF := list Clause.

Definition CNFtoFProp := map_fold_right ClausetoFProp Conj ⊤.

Definition AddClause (l : Clause) (ll : CNF) : CNF := map (fun l2 => l ++ l2) ll.

Definition Disjunct (ll ll2 : CNF) : CNF := flat_map (fun l => AddClause l ll2) ll.

Fixpoint MakeCNF (A : NNF) : CNF := match A with
| NPos P => [[LPos P]]
| NNeg P => [[LNeg P]]
| NBot => [[LBot]]
| NTop => [[LTop]]
| NConj B C => MakeCNF B ++ MakeCNF C
| NDisj B C => Disjunct (MakeCNF B) (MakeCNF C)
end.

Definition Valid_Clause (l : Clause) := In LTop l \/ exists A, (In (LPos A) l /\ In (LNeg A) l).

Definition Valid_CNF ll := forall l, In l ll -> Valid_Clause l.

Lemma Literal_eqdec : forall x y : Literal, {x = y} + {x <> y}.
intros; destruct x; destruct y; try (right; discriminate); try (left; reflexivity); destruct (VarSeq_dec v v0); (left; f_equal; assumption)||(right; intro HH; injection HH; contradiction).
Qed.

Lemma NNF_equiv_valid : forall v A, TrueQ v (NNFtoFProp (MakeNNF  A)) = TrueQ v A /\ TrueQ v (NNFtoFProp (MakeNNFN A)) = TrueQ v ¬ A.
intros v A; induction A; try destruct IHA; try destruct IHA1; try destruct IHA2; split; simpl in *; try trivial; try rewrite H; try rewrite H0; try rewrite H1; try rewrite H2; try trivial; repeat rewrite orb_false_r; repeat rewrite orb_false_l; try rewrite negb_andb; try rewrite negb_orb; try rewrite negb_involutive; reflexivity.
Qed.

Lemma CNF_and_valid : forall v ll1 ll2, TrueQ v (CNFtoFProp (ll1 ++ ll2)) = TrueQ v (CNFtoFProp ll1) && TrueQ v (CNFtoFProp ll2).
intros; induction ll1; simpl.
reflexivity.
unfold CNFtoFProp in IHll1 at 1; rewrite IHll1.
apply andb_assoc.
Qed.

Lemma CNF_or_clause_valid : forall v l1 l2, TrueQ v (ClausetoFProp (l1 ++ l2)) = TrueQ v (ClausetoFProp l1) || TrueQ v (ClausetoFProp l2).
intros; induction l1; simpl.
reflexivity.
unfold ClausetoFProp in IHl1 at 1; rewrite IHl1.
apply orb_assoc.
Qed.

Lemma CNF_add_clause_valid : forall v l ll, TrueQ v (CNFtoFProp (AddClause l ll)) = TrueQ v (ClausetoFProp l) || TrueQ v (CNFtoFProp ll).
intros; induction ll; simpl.
rewrite orb_true_r; reflexivity.
unfold CNFtoFProp in IHll at 1; rewrite IHll.
rewrite CNF_or_clause_valid.
rewrite orb_andb_distrib_r.
reflexivity.
Qed.

Lemma CNF_or_valid : forall v ll1 ll2, TrueQ v (CNFtoFProp (Disjunct ll1 ll2)) = TrueQ v (CNFtoFProp ll1) || TrueQ v (CNFtoFProp ll2).
intros; induction ll1; simpl.
reflexivity.
rewrite CNF_and_valid; rewrite IHll1; rewrite CNF_add_clause_valid.
rewrite orb_andb_distrib_l; reflexivity.
Qed.

Theorem CNF_equiv_valid : forall v A, TrueQ v (CNFtoFProp (MakeCNF A)) = TrueQ v (NNFtoFProp A).
intros; induction A; simpl; try reflexivity; try (destruct (v v0); simpl; reflexivity; fail); [rewrite CNF_and_valid|rewrite CNF_or_valid]; rewrite IHA1; rewrite IHA2; reflexivity.
Qed.

Definition Countervaluation l P := if (in_dec Literal_eqdec (LNeg P) l) then true else false.

Definition Validates v Δ := exists A, In A Δ /\ Is_true (TrueQ v A).

Lemma TrueQ_impl_Validates : forall v m, Is_true (TrueQ v (ClausetoFProp m)) -> Validates v (map LiteraltoFProp m).
intros; induction m.
contradiction.
simpl in H; case_bool v (LiteraltoFProp a).
exists (LiteraltoFProp a); split; [in_solve|rewrite H0; trivial].
destruct (IHm H) as (?&?&?); exists x; split; [in_solve|assumption].
Qed.

Lemma Validated_valid : forall l, Validates (Countervaluation l) (map LiteraltoFProp l) -> Valid_Clause l.
intros l (A&H&K).
apply in_map_iff in H as (p&?&H); subst; destruct p; unfold Countervaluation in K; simpl in K.
destruct (in_dec Literal_eqdec (LNeg v) l).
right; eauto.
contradiction.
destruct (in_dec Literal_eqdec (LNeg v) l); contradiction.
contradiction.
left; assumption.
Qed.

Theorem Clause_valid : forall l, Valid (ClausetoFProp l) -> Valid_Clause l.
intros; apply Validated_valid; apply TrueQ_impl_Validates; apply H; intros ? Q; destruct Q.
Qed.

Theorem CNF_valid : forall ll, Valid (CNFtoFProp ll) -> Valid_CNF ll.
induction ll; intros ? ? H0; destruct H0; subst.
apply Clause_valid; intros v K; remember (H v K) as i eqn:x; clear x; simpl in i; case_bool v (ClausetoFProp l).
apply IHll.
intros v K.
remember (H v K).
eapply proj2.
apply andb_prop_elim.
rewrite <- CNF_and_valid.
change (a :: ll) with ([a] ++ ll) in H.
eapply H; assumption.
assumption.
Qed.

Lemma Clause_provable_3 : forall a l1 l2 Γ, In (LiteraltoFProp a) Γ -> Γ ⊢ ClausetoFProp (l1 ++ a :: l2).
intros; induction l1.
apply OrI1; is_ass.
apply OrI2; assumption.
Qed.

Lemma Clause_provable_2 : forall a l1 l2 l3, Provable (ClausetoFProp (l1 ++ (Bar a) :: l2 ++ a :: l3)).
intros; induction l1.
apply BotC; mp; [is_ass|destruct a; simpl; apply OrI1]; try (apply ImpI; mp; [is_ass|apply OrI2; apply Clause_provable_3; in_solve]); (apply BotC; mp; [constructor; constructor 2; in_solve|apply OrI2; apply Clause_provable_3; in_solve]).
apply OrI2; assumption.
Qed.

Theorem Clause_provable : forall l, Valid_Clause l -> Provable (ClausetoFProp l).
intros ? [?|(?&?&?)]; apply in_split in H as (?&?&?); subst.
induction x; simpl.
apply OrI1; simpl; apply ImpI; is_ass.
apply OrI2; apply IHx.
apply in_app_or in H0 as [].
apply in_split in H as (?&?&?); subst.
rewrite app_ass; apply (Clause_provable_2 (LPos x)).
inversion H; [discriminate|].
apply in_split in H0 as (?&?&?); subst.
apply (Clause_provable_2 (LNeg x)).
Qed.

Theorem CNF_provable : forall ll, Valid_CNF ll -> Provable (CNFtoFProp ll).
intros; induction ll; unfold CNFtoFProp; simpl.
apply ImpI;is_ass.
eapply AndI.
apply Clause_provable; apply H; constructor; reflexivity.
apply IHll; intro; intro; apply H; constructor 2; assumption.
Qed.

Lemma prov_and : forall A1 A2 B1 B2 Γ, Provable (A1 → A2) -> Provable (B1 → B2) -> In (A1 ∧ B1) Γ -> Γ ⊢ A2 ∧ B2.
intros; prov_impl_in H; prov_impl_in H0.
apply AndI; [apply K;eapply AndE1|apply K0; eapply AndE2]; is_ass.
Qed.

Lemma CNF_and_prov : forall ll1 ll2, Provable (CNFtoFProp (ll1 ++ ll2) → CNFtoFProp ll1 ∧ CNFtoFProp ll2).
intros; induction ll1; simpl.
unfold CNFtoFProp at 2; unfold ClausetoFProp; simpl.
apply ImpI; apply AndI.
unfold Top; unfold Neg; apply ImpI; is_ass.
is_ass.
prov_impl_in IHll1; apply ImpI; apply AndI.
unfold CNFtoFProp; simpl; apply AndI.
eapply AndE1; is_ass.
eapply AndE1; apply K.
eapply AndE2; is_ass.
eapply AndE2; apply K; eapply AndE2; is_ass.
Qed.

Lemma prov_or : forall A1 A2 B1 B2 Γ, Provable (A1 → A2) -> Provable (B1 → B2) -> In (A1 ∨ B1) Γ -> Γ ⊢ A2 ∨ B2.
intros; prov_impl_in H; prov_impl_in H0.
eapply OrE.
is_ass.
apply OrI1; apply K; is_ass.
apply OrI2; apply K0; is_ass.
Qed.

Lemma CNF_or_clause_prov : forall l1 l2, Provable (ClausetoFProp (l1 ++ l2) → ClausetoFProp l1 ∨ ClausetoFProp l2).
intros; induction l1; simpl; unfold ClausetoFProp; simpl.
apply ImpI; eapply OrI2; is_ass.
prov_impl_in IHl1.
apply ImpI.
eapply OrE.
is_ass.
do 2 eapply OrI1; is_ass.
apply OrE with (ClausetoFProp l1) (ClausetoFProp l2).
apply K; is_ass.
apply OrI1; apply OrI2; is_ass.
apply OrI2; is_ass.
Qed.

Lemma CNF_add_clause_prov : forall l ll, Provable (CNFtoFProp (AddClause l ll) → ClausetoFProp l ∨ CNFtoFProp ll).
intros; induction ll; simpl; unfold CNFtoFProp; simpl.
apply ImpI; eapply OrI2; is_ass.
prov_impl_in IHll; apply ImpI; apply OrE with (ClausetoFProp l) (ClausetoFProp a).
eapply prov_impl.
apply CNF_or_clause_prov.
eapply AndE1; is_ass.
apply OrI1; is_ass.
apply OrE with (ClausetoFProp l) (CNFtoFProp ll).
apply K; eapply AndE2; is_ass.
apply OrI1; is_ass.
apply OrI2; apply AndI; is_ass.
Qed.

Lemma CNF_or_prov : forall ll1 ll2, Provable (CNFtoFProp (Disjunct ll1 ll2) → CNFtoFProp ll1 ∨ CNFtoFProp ll2).
intros; induction ll1; simpl; unfold CNFtoFProp; simpl.
apply ImpI; eapply OrI1; is_ass.
prov_impl_in IHll1; apply ImpI; apply OrE with (ClausetoFProp a) (CNFtoFProp ll2).
eapply prov_impl; [apply CNF_add_clause_prov|].
eapply AndE1; eapply prov_impl; [apply CNF_and_prov|is_ass].
apply OrE with (CNFtoFProp ll1) (CNFtoFProp ll2).
apply K; eapply AndE2; eapply prov_impl; [apply CNF_and_prov|is_ass].
apply OrI1; apply AndI; is_ass.
apply OrI2; is_ass.
apply OrI2; is_ass.
Qed.

Theorem CNF_impl_prov : forall A, Provable (CNFtoFProp (MakeCNF A) → NNFtoFProp A).
Proof.
intros.
induction A.
unfold CNFtoFProp.
unfold ClausetoFProp.
simpl.
apply ImpI.
eapply OrE.
eapply AndE1.
is_ass.
is_ass.
apply BotC.
is_ass.
unfold CNFtoFProp.
unfold ClausetoFProp.
simpl.
apply ImpI.
eapply OrE.
eapply AndE1.
is_ass.
is_ass.
apply BotC.
is_ass.
unfold CNFtoFProp.
unfold ClausetoFProp.
simpl.
apply ImpI.
eapply OrE.
eapply AndE1.
is_ass.
is_ass.
apply BotC.
is_ass.
unfold CNFtoFProp.
unfold ClausetoFProp.
simpl.
apply ImpI.
eapply OrE.
eapply AndE1.
is_ass.
is_ass.
apply BotC.
is_ass.
apply ImpI; apply AndI; (eapply prov_impl; [eassumption|]); [eapply AndE1|eapply AndE2]; 
(eapply prov_impl; [apply CNF_and_prov|is_ass]).
apply ImpI; eapply prov_impl.
apply ImpI; eapply prov_or; try eassumption; in_solve.
eapply prov_impl; [apply CNF_or_prov|is_ass].
Qed.

Lemma NNF_impl_prov : forall A, Provable (NNFtoFProp (MakeNNF A) → A) /\ Provable (NNFtoFProp (MakeNNFN A) → ¬ A).
Proof.
intros A.
induction A.
simpl.
split.
apply ImpI.
is_ass.
apply ImpI.
is_ass.
simpl.
split.
apply ImpI.
is_ass.
apply ImpI.
is_ass.
destruct IHA1.
destruct IHA2.
simpl.
split.
apply ImpI.
eapply prov_and; try eassumption; in_solve.
apply ImpI.
apply OrE with ¬ A1 ¬ A2.
eapply prov_or; try eassumption; in_solve.
apply ImpI.
mp; [|eapply AndE1]; is_ass.
apply ImpI.
mp; [|eapply AndE2]; is_ass.
destruct IHA1.
destruct IHA2.
simpl.
split.
apply ImpI.
eapply prov_or; try eassumption; in_solve.
apply ImpI.
Qed.

Lemma NNF_impl_prov : forall A, Provable (NNFtoFProp (MakeNNF  A) →  A) /\ Provable (NNFtoFProp (MakeNNFN A) → ¬ A).
induction A; simpl; split;
try destruct IHA; try destruct IHA1;
try destruct IHA2; apply ImpI; try (is_ass; fail).
eapply prov_and; try eassumption; in_solve.
apply ImpI.
apply OrE with ¬ A1 ¬ A2.
eapply prov_or; try eassumption; in_solve.
mp; [|eapply AndE1]; is_ass.
mp; [|eapply AndE2]; is_ass.
eapply prov_or; try eassumption; in_solve.
apply ImpI.
eapply OrE; [is_ass|mp; [|is_ass]; eapply prov_impl; try eassumption..].
eapply AndE1; is_ass.
eapply AndE2; is_ass.
apply ImpI.
apply OrE with ¬ A1 A2.
eapply prov_or; try eassumption; in_solve.
apply BotC.
eapply ImpE with A1; is_ass.
is_ass.
apply ImpI.
apply ImpE with A2.
eapply prov_impl; try eassumption.
eapply AndE2; is_ass.
mp.
is_ass.
eapply prov_impl; try eassumption.
eapply AndE1; is_ass.
Qed.

Theorem Completeness : Prop_Completeness.
do 2 intro.
mp.
apply NNF_impl_prov.
mp.
apply CNF_impl_prov.
apply CNF_provable.
apply CNF_valid.
intros ? ?.
rewrite CNF_equiv_valid.
rewrite ((and_ind (fun A _ => A)) (NNF_equiv_valid v A)).
apply H; assumption.
Qed.

Theorem prov_equiv_models : forall Γ A, Γ ⊢ A <-> Γ ⊨ A.
split; [apply Soundness_general|revert A; induction Γ].
apply Completeness.
intros.
apply deduction.
apply IHΓ.
intros ? ?.
case_bool v a; rewrite H1; simpl.
apply H.
intros ? ?.
destruct H2; subst.
rewrite H1; exact I.
apply H0; in_solve.
exact I.
Qed.

Print Assumptions prov_equiv_models.

End complete_mod.