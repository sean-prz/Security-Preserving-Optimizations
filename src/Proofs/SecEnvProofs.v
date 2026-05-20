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
