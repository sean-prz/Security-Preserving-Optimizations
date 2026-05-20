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
