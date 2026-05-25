Require Import Map.
Require Import VarSets.
Require Import Language.Main.
Require Import Language.Analysis.
Require Import Language.Optimizations.Safe.DSE.
Require Import Proofs.SecLookup.
Require Import Proofs.Noninference.


Definition sec_env_sub (se1 se2 : sec_env) : Prop :=
  forall x, sec_lookup se1 x = Secret -> sec_lookup se2 x = Secret.


Lemma sec_env_sub_refl : forall se,
  sec_env_sub se se.
Proof.
  unfold sec_env_sub. auto.
Qed.

Lemma sec_env_sub_trans : forall se1 se2 se3,
  sec_env_sub se1 se2 ->
  sec_env_sub se2 se3 ->
  sec_env_sub se1 se3.
Proof.
  unfold sec_env_sub. intros se1 se2 se3 H12 H23 x Hx.
  apply H23, H12, Hx.
Qed.

Lemma sec_env_sub_join_left : forall se1 se2,
  sec_env_sub se1 (join_sec_env se1 se2).
Proof.
  unfold sec_env_sub. intros se1 se2 x Hsecret.
  rewrite lookup_join_env.
  rewrite Hsecret.
  destruct (sec_lookup se2 x); reflexivity.
Qed.

Lemma sec_env_sub_join_right : forall se1 se2,
  sec_env_sub se2 (join_sec_env se1 se2).
Proof.
  unfold sec_env_sub. intros se1 se2 x Hsecret.
  rewrite lookup_join_env.
  rewrite Hsecret.
  destruct (sec_lookup se1 x); reflexivity.
Qed.

Lemma sec_env_sub_join_compat : forall se1 se1' se2 se2',
  sec_env_sub se1 se1' ->
  sec_env_sub se2 se2' ->
  sec_env_sub (join_sec_env se1 se2) (join_sec_env se1' se2').
Proof.
  unfold sec_env_sub.
  intros se1 se1' se2 se2' Hleft Hright x Hsecret.
  rewrite !lookup_join_env in *.
  destruct (sec_lookup se1 x) eqn:H1;
    destruct (sec_lookup se2 x) eqn:H2;
    cbn in Hsecret; try discriminate.
  - rewrite (Hright x H2). destruct (sec_lookup se1' x); reflexivity.
  - rewrite (Hleft x H1). reflexivity.
  - rewrite (Hleft x H1). rewrite (Hright x H2). reflexivity.
Qed.

Lemma sec_env_sub_update : forall se1 se2 x level1 level2,
  sec_env_sub se1 se2 ->
  (level1 = Secret -> level2 = Secret) ->
  sec_env_sub (update_sec se1 x level1) (update_sec se2 x level2).
Proof.
  unfold sec_env_sub.
  intros se1 se2 x level1 level2 Hsub Hlevel y Hsecret.
  destruct (x ==v y) eqn:Heq.
  - subst.
    rewrite lookup_update_sec_eq in *.
    auto.
  - rewrite lookup_update_sec_ne in Hsecret by congruence.
    rewrite lookup_update_sec_ne by congruence.
    apply Hsub. exact Hsecret.
Qed.

Lemma interp_sec_secret_monotone : forall e se1 se2,
  sec_env_sub se1 se2 ->
  interp_sec e se1 = Secret ->
  interp_sec e se2 = Secret.
Proof.
  induction e; intros se1 se2 Hsub Hsecret; cbn in *.
  - discriminate.
  - apply Hsub. exact Hsecret.
  - destruct (interp_sec e1 se1) eqn:He1;
      destruct (interp_sec e2 se1) eqn:He2;
      cbn in Hsecret; try discriminate.
    + rewrite (IHe2 se1 se2 Hsub He2).
      destruct (interp_sec e1 se2); reflexivity.
    + rewrite (IHe1 se1 se2 Hsub He1). reflexivity.
    + rewrite (IHe1 se1 se2 Hsub He1). reflexivity.
Qed.

Lemma cmov_level_secret_monotone : forall cond e1 e2 se1 se2,
  sec_env_sub se1 se2 ->
  join_sec (interp_sec cond se1)
    (join_sec (interp_sec e1 se1) (interp_sec e2 se1)) = Secret ->
  join_sec (interp_sec cond se2)
    (join_sec (interp_sec e1 se2) (interp_sec e2 se2)) = Secret.
Proof.
  intros cond e1 e2 se1 se2 Hsub Hsecret.
  destruct (interp_sec cond se1) eqn:Hcond;
    destruct (interp_sec e1 se1) eqn:He1;
    destruct (interp_sec e2 se1) eqn:He2;
    cbn in Hsecret; try discriminate.
  - pose proof (interp_sec_secret_monotone e2 se1 se2 Hsub He2) as He2'.
    rewrite He2'. destruct (interp_sec cond se2), (interp_sec e1 se2); reflexivity.
  - pose proof (interp_sec_secret_monotone e1 se1 se2 Hsub He1) as He1'.
    rewrite He1'. destruct (interp_sec cond se2); reflexivity.
  - pose proof (interp_sec_secret_monotone e1 se1 se2 Hsub He1) as He1'.
    rewrite He1'. destruct (interp_sec cond se2); reflexivity.
  - pose proof (interp_sec_secret_monotone cond se1 se2 Hsub Hcond) as Hcond'.
    rewrite Hcond'. reflexivity.
  - pose proof (interp_sec_secret_monotone cond se1 se2 Hsub Hcond) as Hcond'.
    rewrite Hcond'. reflexivity.
  - pose proof (interp_sec_secret_monotone cond se1 se2 Hsub Hcond) as Hcond'.
    rewrite Hcond'. reflexivity.
  - pose proof (interp_sec_secret_monotone cond se1 se2 Hsub Hcond) as Hcond'.
    rewrite Hcond'. reflexivity.
Qed.

(* ================================================================= *)
(* Public-side duals: derive Public-in-actual from Public-in-static   *)
(* under sec_env_sub se_actual se_static.                             *)
(* ================================================================= *)

Lemma sec_env_sub_public : forall se_actual se_static x,
  sec_env_sub se_actual se_static ->
  sec_lookup se_static x = Public ->
  sec_lookup se_actual x = Public.
Proof.
  intros se_actual se_static x Hsub Hpub.
  destruct (sec_lookup se_actual x) eqn:Hactual; auto.
  pose proof (Hsub x Hactual).
  congruence.
Qed.

Lemma interp_sec_public_under_sub : forall e se_actual se_static,
  sec_env_sub se_actual se_static ->
  interp_sec e se_static = Public ->
  interp_sec e se_actual = Public.
Proof.
  intros e se_actual se_static Hsub Hpub.
  destruct (interp_sec e se_actual) eqn:Hactual; auto.
  pose proof (interp_sec_secret_monotone e se_actual se_static Hsub Hactual).
  congruence.
Qed.

Lemma cmov_level_public_under_sub : forall cond e1 e2 se_actual se_static,
  sec_env_sub se_actual se_static ->
  join_sec (interp_sec cond se_static)
    (join_sec (interp_sec e1 se_static) (interp_sec e2 se_static)) = Public ->
  join_sec (interp_sec cond se_actual)
    (join_sec (interp_sec e1 se_actual) (interp_sec e2 se_actual)) = Public.
Proof.
  intros cond e1 e2 se_actual se_static Hsub Hpub.
  destruct (join_sec (interp_sec cond se_actual)
    (join_sec (interp_sec e1 se_actual) (interp_sec e2 se_actual))) eqn:Hactual; auto.
  pose proof (cmov_level_secret_monotone cond e1 e2 se_actual se_static Hsub Hactual).
  congruence.
Qed.

Lemma sec_post_monotone : forall c se1 se2,
  sec_env_sub se1 se2 ->
  sec_env_sub (sec_post c se1) (sec_post c se2).
Proof.
  induction c; intros se1 se2 Hsub; simpl.
  - exact Hsub.
  - eapply sec_env_sub_update; [exact Hsub |].
    intro Hlevel.
    eapply interp_sec_secret_monotone; eauto.
  - change (sec_env_sub (update_sec se1 s Secret) (update_sec se2 s Secret)).
    eapply sec_env_sub_update; [exact Hsub |].
    intros _. reflexivity.
  - eapply sec_env_sub_update; [exact Hsub |].
    intro Hlevel.
    eapply cmov_level_secret_monotone; eauto.
  - apply IHc2. apply IHc1. exact Hsub.
  - apply sec_env_sub_join_compat; auto.
  - change (sec_env_sub (join_sec_env se1 (vars_in_cmd c))
              (join_sec_env se2 (vars_in_cmd c))).
    apply sec_env_sub_join_compat; auto using sec_env_sub_refl.
Qed.

Lemma sec_post_secret_bound : forall c se,
  sec_env_sub (sec_post c se) (VarSet.union se (vars_in_cmd c)).
Proof.
  induction c; intros se; simpl.
  - unfold sec_env_sub. intros x Hsecret.
    apply secret_in_lookup.
    apply VarSet.union_spec. left.
    apply secret_lookup_in. exact Hsecret.
  - unfold sec_env_sub. intros y Hsecret.
    destruct (s ==v y) eqn:Heq.
    + subst. apply secret_in_lookup.
      apply VarSet.union_spec. right.
      apply VarSet.add_spec. left. reflexivity.
    + rewrite lookup_update_sec_ne in Hsecret by congruence.
      apply secret_in_lookup.
      apply VarSet.union_spec. left.
      apply secret_lookup_in. exact Hsecret.
  - unfold sec_env_sub. intros y Hsecret.
    destruct (s ==v y) eqn:Heq.
    + subst. apply secret_in_lookup.
      apply VarSet.union_spec. right.
      apply VarSet.add_spec. left. reflexivity.
    + pose proof (secret_lookup_in (VarSet.add s se) y Hsecret) as Hin_add.
      rewrite VarSet.add_spec in Hin_add.
      destruct Hin_add as [Heq' | Hin].
      * congruence.
      * apply secret_in_lookup.
        apply VarSet.union_spec. left.
        exact Hin.
  - unfold sec_env_sub. intros y Hsecret.
    destruct (s ==v y) eqn:Heq.
    + subst. apply secret_in_lookup.
      apply VarSet.union_spec. right.
      apply VarSet.add_spec. left. reflexivity.
    + rewrite lookup_update_sec_ne in Hsecret by congruence.
      apply secret_in_lookup.
      apply VarSet.union_spec. left.
      apply secret_lookup_in. exact Hsecret.
  - unfold sec_env_sub in *.
    intros x Hsecret.
    pose proof (IHc2 (sec_post c1 se) x Hsecret) as Hstep2.
    apply secret_lookup_in in Hstep2.
    rewrite VarSet.union_spec in Hstep2.
    destruct Hstep2 as [Hin_c1 | Hin_c2].
    + pose proof (IHc1 se x (secret_in_lookup _ _ Hin_c1)) as Hstep1.
      apply secret_lookup_in in Hstep1.
      apply secret_in_lookup.
      rewrite !VarSet.union_spec in *.
      VarSetDecide.fsetdec.
    + apply secret_in_lookup.
      rewrite !VarSet.union_spec in *.
      VarSetDecide.fsetdec.
  - unfold sec_env_sub in *.
    intros x Hsecret.
    apply secret_lookup_in in Hsecret.
    rewrite VarSet.union_spec in Hsecret.
    destruct Hsecret as [Hin_thn | Hin_els].
    + pose proof (IHc1 se x (secret_in_lookup _ _ Hin_thn)) as Hbound.
      apply secret_lookup_in in Hbound.
      apply secret_in_lookup.
      rewrite !VarSet.union_spec in *.
      VarSetDecide.fsetdec.
    + pose proof (IHc2 se x (secret_in_lookup _ _ Hin_els)) as Hbound.
      apply secret_lookup_in in Hbound.
      apply secret_in_lookup.
      rewrite !VarSet.union_spec in *.
      VarSetDecide.fsetdec.
  - unfold sec_env_sub. intros x Hsecret.
    apply secret_lookup_in in Hsecret.
    apply secret_in_lookup.
    rewrite !VarSet.union_spec in *.
    VarSetDecide.fsetdec.
Qed.

Theorem sec_post_overapproximates_eval_sec_subset : forall phi ctx c ctx',
  eval_sec phi ctx c ctx' ->
  sec_env_sub (sec_of ctx') (sec_post c (sec_of ctx)).
Proof.
  intros phi ctx c ctx' Heval.
  induction Heval; simpl.
  - apply sec_env_sub_refl.
  - unfold sec_env_sub. intros y Hsecret.
    cbn in *.
    rewrite H0.
    exact Hsecret.
  - unfold sec_env_sub. intros y Hsecret.
    cbn in *.
    rewrite H3.
    exact Hsecret.
  - unfold sec_env_sub. intros y Hsecret.
    cbn in *.
    rewrite H2.
    exact Hsecret.
  - unfold sec_env_sub. intros z Hsecret.
    cbn in *.
    destruct (x ==v z) eqn:Heq.
    + subst. unfold sec_lookup. rewrite VarSetEqProps.add_mem_1. reflexivity.
    + rewrite lookup_update_sec_ne in Hsecret by congruence.
      unfold sec_lookup. rewrite VarSetEqProps.add_mem_2 by congruence.
      exact Hsecret.
  - eapply sec_env_sub_trans.
    + exact IHHeval2.
    + apply sec_post_monotone.
      exact IHHeval1.
  - cbn in IHHeval.
    eapply sec_env_sub_trans.
    + exact IHHeval.
    + apply sec_env_sub_join_left.
  - cbn in IHHeval.
    eapply sec_env_sub_trans.
    + exact IHHeval.
    + apply sec_env_sub_join_right.
  - cbn in IHHeval1, IHHeval2.
    eapply sec_env_sub_trans.
    + exact IHHeval2.
    + unfold sec_env_sub. intros x Hsecret.
      apply secret_lookup_in in Hsecret.
      rewrite VarSet.union_spec in Hsecret.
      destruct Hsecret as [Hctx' | Hbody].
      * pose proof (IHHeval1 x (secret_in_lookup _ _ Hctx')) as Hbody_post.
        exact (sec_post_secret_bound body (sec_of ctx) x Hbody_post).
      * apply secret_in_lookup.
        rewrite VarSet.union_spec. right. exact Hbody.
  - apply sec_env_sub_join_left.
Qed.

Corollary sec_post_overapproximates_eval_sec : forall phi ctx c ctx' x,
  eval_sec phi ctx c ctx' ->
  sec_lookup (sec_of ctx') x = Secret ->
  sec_lookup (sec_post c (sec_of ctx)) x = Secret.
Proof.
  intros phi ctx c ctx' x Heval Hsecret.
  eapply sec_post_overapproximates_eval_sec_subset; eauto.
Qed.
