Require Import Map.
Require Import VarSets.
Require Import Language.Main.
Require Import Language.Security.

Lemma lookup_join_env : forall se1 se2 x,
  sec_lookup (join_sec_env se1 se2) x = join_sec (sec_lookup se1 x) (sec_lookup se2 x).
Proof.
  intros se1 se2 x.
  unfold sec_lookup, join_sec_env.
  rewrite VarSetEqProps.union_mem.
  destruct (VarSet.mem x se1) eqn:H1;
  destruct (VarSet.mem x se2) eqn:H2;
  cbn; try reflexivity.
Qed.


Lemma join_sec_public:
  forall se1 se2 x,
  sec_lookup (join_sec_env se1 se2) x = Public ->
  sec_lookup se1 x = Public /\ sec_lookup se2 x = Public.
Proof.
  intros se1 se2 x Hjoin.
  rewrite lookup_join_env in Hjoin.
  destruct (sec_lookup se1 x) eqn:H1;
  destruct (sec_lookup se2 x) eqn:H2;
  cbn in Hjoin; try discriminate; split; reflexivity.
Qed.

Lemma join_sec_public_thn:
  forall se1 se2 x,
  sec_lookup (join_sec_env se1 se2) x = Public ->
  sec_lookup se1 x = Public.
Proof. intros. apply join_sec_public in H. destruct H. assumption. Qed.

Lemma join_sec_public_els:
  forall se1 se2 x,
  sec_lookup (join_sec_env se1 se2) x = Public ->
  sec_lookup se2 x = Public.
Proof. intros. apply join_sec_public in H. destruct H. assumption. Qed.

Lemma join_sec_env_idempotent : forall se,
  VarSet.Equal (join_sec_env se se) se.
Proof.
  VarSetDecide.fsetdec.
Qed.


Lemma join_sec_env_update_public_right : forall se x,
  VarSet.Equal (join_sec_env se (update_sec se x Public)) se.
Proof.
  unfold join_sec_env, update_sec.
  VarSetDecide.fsetdec.
Qed.

Lemma lookup_update_sec_eq : forall se x level,
  sec_lookup (update_sec se x level) x = level.
Proof.
  intros. unfold sec_lookup, update_sec.
  destruct level; simpl.
  - (* Public *) rewrite VarSetEqProps.remove_mem_1. reflexivity.
  - (* Secret *) rewrite VarSetEqProps.add_mem_1. reflexivity.
Qed.

Lemma lookup_update_sec_ne : forall se x y level,
  x <> y ->
  sec_lookup (update_sec se x level) y = sec_lookup se y.
Proof.
  intros. unfold sec_lookup, update_sec.
  destruct level; simpl.
  - (* Public *) rewrite VarSetEqProps.remove_mem_2; [reflexivity | assumption].
  - (* Secret *) rewrite VarSetEqProps.add_mem_2; [reflexivity | assumption].
Qed.

Lemma lookup_senv_mk2_eq1 : forall x1 x2 l1 l2,
  x1 <> x2 ->
  sec_lookup (senv_mk2 x1 x2 l1 l2) x1 = l1.
Proof.
  intros. unfold senv_mk2.
  rewrite lookup_update_sec_ne by congruence.
  rewrite lookup_update_sec_eq. reflexivity.
Qed.

Lemma lookup_senv_mk2_eq2 : forall x1 x2 l1 l2,
  sec_lookup (senv_mk2 x1 x2 l1 l2) x2 = l2.
Proof.
  intros. unfold senv_mk2.
  rewrite lookup_update_sec_eq. reflexivity.
Qed.

Lemma lookup_senv_mk2_ne : forall x1 x2 y l1 l2,
  y <> x1 -> y <> x2 ->
  sec_lookup (senv_mk2 x1 x2 l1 l2) y = Public.
Proof.
  intros. unfold senv_mk2.
  do 2 rewrite lookup_update_sec_ne by congruence.
  reflexivity.
Qed.

(* ================================================================= *)
(* sec_lookup <-> VarSet membership                                   *)
(* ================================================================= *)

Lemma mem_lookup_simpl_1 : forall se x,
  sec_lookup se x = Public
  <->
  VarSet.mem x se = false.
Proof.
  unfold sec_lookup.
  split; simpl; intros.
  - destruct (VarSet.mem x se); congruence.
  - rewrite H. reflexivity.
Qed.

Lemma mem_lookup_simpl_2 : forall se x,
  sec_lookup se x = Secret
  <->
  VarSet.mem x se = true.
Proof.
  unfold sec_lookup.
  split; simpl; intros.
  - destruct (VarSet.mem x se); congruence.
  - rewrite H. reflexivity.
Qed.

Lemma pub_not_sec : forall se s,
  sec_lookup se s = Public <-> ~ VarSets.VarSet.In s se.
Proof.
  intros.
  split.
  - intro.
    intro.
    unfold sec_lookup in H.
    rewrite <- VarSet.mem_spec in H0.
    rewrite H0 in H.
    discriminate.
  - intro.
    unfold sec_lookup.
    rewrite <- VarSet.mem_spec in H.
    apply Bool.not_true_is_false in H.
    rewrite H.
    reflexivity.
Qed.

Lemma secret_lookup_in : forall se x,
  sec_lookup se x = Secret ->
  VarSet.In x se.
Proof.
  intros se x Hsecret.
  apply mem_lookup_simpl_2 in Hsecret.
  apply VarSet.mem_spec.
  exact Hsecret.
Qed.

Lemma secret_in_lookup : forall se x,
  VarSet.In x se ->
  sec_lookup se x = Secret.
Proof.
  intros se x Hin.
  apply mem_lookup_simpl_2.
  apply VarSet.mem_spec.
  exact Hin.
Qed.

(* ================================================================= *)
(* update_sec membership                                              *)
(* ================================================================= *)

Lemma simplify_update_ne : forall x y se level,
  y <> x ->
  VarSet.mem y (update_sec se x level)
  = VarSet.mem y se.
Proof.
  intros.
  unfold update_sec. destruct level.
  - apply VarSetEqProps.remove_mem_2; congruence.
  - apply VarSetEqProps.add_mem_2; congruence.
Qed.

Lemma mem_update_ne : forall se x y level,
  y <> x ->
  sec_lookup (update_sec se y level) x = Public ->
  VarSet.mem x se = false.
Proof.
  unfold sec_lookup.
  intros.
  destruct level; simpl in H0.
  1: rewrite VarSetEqProps.remove_mem_2 in H0 by assumption.
  2: rewrite VarSetEqProps.add_mem_2 in H0 by assumption.
  all: destruct (VarSet.mem x se); congruence.
Qed.

Lemma mem_update_eq : forall se x level,
  sec_lookup (update_sec se x level) x = Public <->
  level = Public.
Proof.
  unfold sec_lookup.
  split;
  intros.
  destruct level; simpl in H.
  reflexivity.
  rewrite VarSetEqProps.add_mem_1 in H. discriminate.
  subst.
  simpl.
  rewrite VarSetEqProps.remove_mem_1. reflexivity.
Qed.

Lemma mem_lookup_eq: forall se1 se2 x level,
  sec_lookup (update_sec se1 x level) x = sec_lookup (update_sec se2 x level) x.
Proof.
  intros.
  unfold update_sec, sec_lookup. destruct level.
  - repeat rewrite VarSetEqProps.remove_mem_1; reflexivity.
  - repeat rewrite VarSetEqProps.add_mem_1; reflexivity.
Qed.

(* ================================================================= *)
(* interp_sec extensional/agreement lemmas                            *)
(* ================================================================= *)

Lemma interp_sec_lookup_agree : forall e se1 se2,
  (forall x, sec_lookup se1 x = sec_lookup se2 x) ->
  interp_sec e se1 = interp_sec e se2.
Proof.
  induction e; intros se1 se2 Hagree; cbn.
  - reflexivity.
  - apply Hagree.
  - rewrite (IHe1 se1 se2 Hagree), (IHe2 se1 se2 Hagree).
    reflexivity.
Qed.

Lemma sec_lookup_update_agree : forall se1 se2 x level1 level2,
  (forall y, sec_lookup se1 y = sec_lookup se2 y) ->
  level1 = level2 ->
  forall y, sec_lookup (update_sec se1 x level1) y = sec_lookup (update_sec se2 x level2) y.
Proof.
  intros se1 se2 x level1 level2 Hagree Hlevel y.
  subst level2.
  destruct (x ==v y).
  - subst. rewrite lookup_update_sec_eq. rewrite lookup_update_sec_eq. reflexivity.
  - repeat rewrite lookup_update_sec_ne by congruence.
    apply Hagree.
Qed.

Lemma sec_lookup_update_public_id : forall se x,
  sec_lookup se x = Public ->
  forall y, sec_lookup (update_sec se x Public) y = sec_lookup se y.
Proof.
  intros se x Hpub y.
  destruct (x ==v y).
  - subst. rewrite lookup_update_sec_eq. symmetry. exact Hpub.
  - rewrite lookup_update_sec_ne by congruence. reflexivity.
Qed.

Lemma interp_sec_dynamic_agree : forall e se se_dyn1 se_dyn2,
  (forall x, sec_lookup se x = Public -> sec_lookup se_dyn1 x = sec_lookup se_dyn2 x) ->
  interp_sec e se = Public ->
  interp_sec e se_dyn1 = interp_sec e se_dyn2.
Proof.
  induction e; intros se se_dyn1 se_dyn2 Hagree Hpub; cbn in *.
  - (* Const *) reflexivity.
  - (* Var *) apply Hagree. exact Hpub.
  - (* Binop *)
    destruct (interp_sec e1 se) eqn:He1;
    destruct (interp_sec e2 se) eqn:He2;
    cbn in Hpub; try discriminate.
    rewrite (IHe1 se se_dyn1 se_dyn2 Hagree He1).
    rewrite (IHe2 se se_dyn1 se_dyn2 Hagree He2).
    reflexivity.
Qed.
