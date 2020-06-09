From LF Require Export ml2_soundness.
Require Export Decidable.
Set Implicit Arguments.
Module Type mod_complete (X: mod_base) (Y: mod_sound X).
Import X Y.

Inductive NNF : Set :=
| NPos : VarProp -> NNF
| NNeg : VarProp -> NNF
| NBot : NNF
| NTop : NNF
| NConj : NNF -> NNF -> NNF
| NDisj : NNF -> NNF -> NNF.

Fixpoint MakeNNF (A : FormProp) : NNF := match A with
| # P => NPos P
| ⊥ => NBot
| B ∨ C => NDisj (MakeNNF B) (MakeNNF C)
| B ∧ C => NConj (MakeNNF B) (MakeNNF C)
| B → C => NDisj (MakeNNFN B) (MakeNNF C)
end
with MakeNNFN (A : FormProp) : NNF := match A with
| # P => NNeg P
| ⊥ => NTop
| B ∨ C => NConj (MakeNNFN B) (MakeNNFN C)
| B ∧ C => NDisj (MakeNNFN B) (MakeNNFN C)
| B → C => NConj (MakeNNF B) (MakeNNFN C)
end.

Fixpoint NNFtoFormProp (A : NNF) : FormProp := match A with
| NPos P => # P
| NNeg P => ¬ # P
| NBot => ⊥
| NTop => ¬ ⊥
| NConj B C => NNFtoFormProp B ∧ NNFtoFormProp C
| NDisj B C => NNFtoFormProp B ∨ NNFtoFormProp C
end.

Inductive Literal :=
| LPos : VarProp -> Literal
| LNeg : VarProp -> Literal
| LBot : Literal
| LTop : Literal.

Fixpoint Bar P := match P with
| LPos Q => LNeg Q
| LNeg Q => LPos Q
| LBot => LTop
| LTop => LBot
end.

Fixpoint LiteraltoFormProp (P : Literal) : FormProp :=
match P with
| LPos Q => # Q
| LNeg Q => ¬ # Q
| LBot => ⊥
| LTop => ¬ ⊥
end.

Definition Clause := list Literal.

Definition ClausetoFormProp := map_fold_right LiteraltoFormProp Disj ⊥.

Definition CNF := list Clause.

Definition CNFtoFormProp := map_fold_right ClausetoFormProp Conj ⊤.

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
intros; destruct x; destruct y; try (right; discriminate); try (left; reflexivity); destruct (VarSeq p p0);  (left; f_equal; assumption)||(right; intro HH; injection HH; contradiction).
Qed.

Lemma NNF_equiv_valid : forall v A, TrueQ v (NNFtoFormProp (MakeNNF  A)) = TrueQ v A /\ TrueQ v (NNFtoFormProp (MakeNNFN A)) = TrueQ v ¬ A.
intros v A; induction A; try destruct IHA; try destruct IHA1; try destruct IHA2; split; simpl in *; try trivial; try rewrite H; try rewrite H0; try rewrite H1; try rewrite H2; try trivial; repeat rewrite orb_false_r; repeat rewrite orb_false_l; try rewrite negb_andb; try rewrite negb_orb; try rewrite negb_involutive; reflexivity.
Qed.

Lemma CNF_and_valid : forall v ll1 ll2, TrueQ v (CNFtoFormProp (ll1 ++ ll2)) = TrueQ v (CNFtoFormProp ll1) && TrueQ v (CNFtoFormProp ll2).
intros; induction ll1; simpl.
reflexivity.
unfold CNFtoFormProp in IHll1 at 1; rewrite IHll1.
apply andb_assoc.
Qed.

Lemma CNF_or_clause_valid : forall v l1 l2, TrueQ v (ClausetoFormProp (l1 ++ l2)) = TrueQ v (ClausetoFormProp l1) || TrueQ v (ClausetoFormProp l2).
intros; induction l1; simpl.
reflexivity.
unfold ClausetoFormProp in IHl1 at 1; rewrite IHl1.
apply orb_assoc.
Qed.

Lemma CNF_add_clause_valid : forall v l ll, TrueQ v (CNFtoFormProp (AddClause l ll)) = TrueQ v (ClausetoFormProp l) || TrueQ v (CNFtoFormProp ll).
intros; induction ll; simpl.
rewrite orb_true_r; reflexivity.
unfold CNFtoFormProp in IHll at 1; rewrite IHll.
rewrite CNF_or_clause_valid.
rewrite orb_andb_distrib_r.
reflexivity.
Qed.

Lemma CNF_or_valid : forall v ll1 ll2, TrueQ v (CNFtoFormProp (Disjunct ll1 ll2)) = TrueQ v (CNFtoFormProp ll1) || TrueQ v (CNFtoFormProp ll2).
intros; induction ll1; simpl.
reflexivity.
rewrite CNF_and_valid; rewrite IHll1; rewrite CNF_add_clause_valid.
rewrite orb_andb_distrib_l; reflexivity.
Qed.

Theorem CNF_equiv_valid : forall v A, TrueQ v (CNFtoFormProp (MakeCNF A)) = TrueQ v (NNFtoFormProp A).
intros; induction A; simpl; try reflexivity; try (destruct (v p); simpl; reflexivity; fail); [rewrite CNF_and_valid|rewrite CNF_or_valid]; rewrite IHA1; rewrite IHA2; reflexivity.
Qed.

Definition Countervaluation l P := if (in_dec Literal_eqdec (LNeg P) l) then true else false.

Definition Validates v Δ := exists A, In A Δ /\ Is_true (TrueQ v A).

Lemma TrueQ_impl_Validates : forall v m, Is_true (TrueQ v (ClausetoFormProp m)) -> Validates v (map LiteraltoFormProp m).
intros; induction m.
contradiction.
simpl in H; case_bool v (LiteraltoFormProp a).
exists (LiteraltoFormProp a); split; [in_solve|rewrite H0; trivial].
destruct (IHm H) as (?&?&?); exists x; split; [in_solve|assumption].
Qed.

Lemma Validated_valid : forall l, Validates (Countervaluation l) (map LiteraltoFormProp l) -> Valid_Clause l.
intros l (A&H&K).
apply in_map_iff in H as (p&?&H); subst; destruct p; unfold Countervaluation in K; simpl in K.
destruct (in_dec Literal_eqdec (LNeg p) l).
right; eauto.
contradiction.
destruct (in_dec Literal_eqdec (LNeg p) l); contradiction.
contradiction.
left; assumption.
Qed.

Theorem Clause_valid : forall l, Valid (ClausetoFormProp l) -> Valid_Clause l.
intros; apply Validated_valid; apply TrueQ_impl_Validates; apply H; intros ? Q; destruct Q.
Qed.

Theorem CNF_valid : forall ll, Valid (CNFtoFormProp ll) -> Valid_CNF ll.
induction ll; intros ? ? H0; destruct H0; subst.
apply Clause_valid; intros v K; remember (H v K) as i eqn:x; clear x; simpl in i; case_bool v (ClausetoFormProp l).
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

Lemma Clause_provable_3 : forall a l1 l2 Γ, In (LiteraltoFormProp a) Γ -> Γ ⊢ ClausetoFormProp (l1 ++ a :: l2).
intros; induction l1.
apply OrI1; is_ass.
apply OrI2; assumption.
Qed.

Lemma Clause_provable_2 : forall a l1 l2 l3, Provable (ClausetoFormProp (l1 ++ (Bar a) :: l2 ++ a :: l3)).
intros; induction l1.
apply BotC; mp; [is_ass|destruct a; simpl; apply OrI1]; try (apply ImpI; mp; [is_ass|apply OrI2; apply Clause_provable_3; in_solve]); (apply BotC; mp; [constructor; constructor 2; in_solve|apply OrI2; apply Clause_provable_3; in_solve]).
apply OrI2; assumption.
Qed.

Theorem Clause_provable : forall l, Valid_Clause l -> Provable (ClausetoFormProp l).
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

Theorem CNF_provable : forall ll, Valid_CNF ll -> Provable (CNFtoFormProp ll).
intros; induction ll; unfold CNFtoFormProp; simpl.
apply ImpI;is_ass.
eapply AndI.
apply Clause_provable; apply H; constructor; reflexivity.
apply IHll; intro; intro; apply H; constructor 2; assumption.
Qed.

Lemma prov_or : forall A1 A2 B1 B2 Γ, Provable (A1 → A2) -> Provable (B1 → B2) -> In (A1 ∨ B1) Γ -> Γ ⊢ A2 ∨ B2.
intros; prov_impl_in H; prov_impl_in H0. eapply OrE.
is_ass.
apply OrI1; apply K; is_ass.
apply OrI2; apply K0; is_ass.
Qed.

Lemma CNF_and_prov : forall ll1 ll2, Provable (CNFtoFormProp (ll1 ++ ll2) → CNFtoFormProp ll1 ∧ CNFtoFormProp ll2).
intros; induction ll1; simpl.
unfold CNFtoFormProp at 2; unfold ClausetoFormProp; simpl.
apply ImpI; apply AndI.
unfold Top; unfold Neg; apply ImpI; is_ass.
is_ass.
prov_impl_in IHll1; apply ImpI; apply AndI.
unfold CNFtoFormProp; simpl; apply AndI.
eapply AndE1; is_ass.
eapply AndE1; apply K.
eapply AndE2; is_ass.
eapply AndE2; apply K; eapply AndE2; is_ass.
Qed.

Lemma CNF_or_clause_prov : forall l1 l2, Provable (ClausetoFormProp (l1 ++ l2) → ClausetoFormProp l1 ∨ ClausetoFormProp l2).
intros; induction l1; simpl; unfold ClausetoFormProp; simpl.
apply ImpI; eapply OrI2; is_ass.
prov_impl_in IHl1.
apply ImpI.
eapply OrE.
is_ass.
do 2 eapply OrI1; is_ass.
apply OrE with (ClausetoFormProp l1) (ClausetoFormProp l2).
apply K; is_ass.
apply OrI1; apply OrI2; is_ass.
apply OrI2; is_ass.
Qed.

Lemma CNF_add_clause_prov : forall l ll, Provable (CNFtoFormProp (AddClause l ll) → ClausetoFormProp l ∨ CNFtoFormProp ll).
intros; induction ll; simpl; unfold CNFtoFormProp; simpl.
apply ImpI; eapply OrI2; is_ass.
prov_impl_in IHll; apply ImpI; apply OrE with (ClausetoFormProp l) (ClausetoFormProp a).
eapply prov_impl.
apply CNF_or_clause_prov.
eapply AndE1; is_ass.
apply OrI1; is_ass.
apply OrE with (ClausetoFormProp l) (CNFtoFormProp ll).
apply K; eapply AndE2; is_ass.
apply OrI1; is_ass.
apply OrI2; apply AndI; is_ass.
Qed.

Lemma CNF_or_prov : forall ll1 ll2, Provable (CNFtoFormProp (Disjunct ll1 ll2) → CNFtoFormProp ll1 ∨ CNFtoFormProp ll2).
intros; induction ll1; simpl; unfold CNFtoFormProp; simpl.
apply ImpI; eapply OrI1; is_ass.
prov_impl_in IHll1; apply ImpI; apply OrE with (ClausetoFormProp a) (CNFtoFormProp ll2).
eapply prov_impl; [apply CNF_add_clause_prov|].
eapply AndE1; eapply prov_impl; [apply CNF_and_prov|is_ass].
apply OrE with (CNFtoFormProp ll1) (CNFtoFormProp ll2).
apply K; eapply AndE2; eapply prov_impl; [apply CNF_and_prov|is_ass].
apply OrI1; apply AndI; is_ass.
apply OrI2; is_ass.
apply OrI2; is_ass.
Qed.

Theorem CNF_impl_prov : forall A, Provable (CNFtoFormProp (MakeCNF A) → NNFtoFormProp A).
induction A; simpl; try (unfold CNFtoFormProp; unfold ClausetoFormProp; simpl; apply ImpI;eapply OrE; [eapply AndE1;is_ass|is_ass|apply BotC;is_ass]; fail).
apply ImpI; apply AndI; (eapply prov_impl; [eassumption|]); [eapply AndE1|eapply AndE2]; (eapply prov_impl; [apply CNF_and_prov|is_ass]).
apply ImpI; eapply prov_impl.
apply ImpI; eapply prov_or; try eassumption; in_solve.
eapply prov_impl; [apply CNF_or_prov|is_ass].
Qed.

Lemma prov_and : forall A1 A2 B1 B2 Γ, Provable (A1 → A2) -> Provable (B1 → B2) -> In (A1∧B1) Γ -> Γ ⊢ A2 ∧ B2.
intros; prov_impl_in H; prov_impl_in H0.
apply AndI; [apply K;eapply AndE1|apply K0; eapply AndE2]; is_ass.
Qed.

Lemma NNF_impl_prov : forall A, Provable (NNFtoFormProp (MakeNNF  A) →  A) /\ Provable (NNFtoFormProp (MakeNNFN A) → ¬A).
induction A; simpl; split; try destruct IHA; try destruct IHA1; try destruct IHA2; apply ImpI; try (is_ass; fail).
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