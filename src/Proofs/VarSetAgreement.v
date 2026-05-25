Require Import Map.
Require Import VarSets.
Require Import Language.Main.

Module vsp := VarSetProps.

(* ================================================================= *)
(* agree_on: two valuations agree on all variables in a set          *)
(* ================================================================= *)

Definition agree_on (S: var_set) (v1 v2: valuation) : Prop :=
  forall x, VarSet.mem x S = true -> v1 $? x = v2 $? x.

(* ================================================================= *)
(* Basic agree_on lemmas                                              *)
(* ================================================================= *)

Lemma agree_on_refl: forall S v,
  agree_on S v v.
Proof.
  unfold agree_on.
  reflexivity.
Qed.


Lemma agree_on_sym: forall S v1 v2,
  agree_on S v1 v2 -> agree_on S v2 v1.
Proof.
  unfold agree_on.
  intros.
  apply eq_sym.
  firstorder.
Qed.

Lemma agree_on_trans: forall S v1 v2 v3,
  agree_on S v1 v2 -> agree_on S v2 v3 -> agree_on S v1 v3.
Proof.
  unfold agree_on.
  intros.
  specialize (H x H1).
  specialize (H0 x H1).
  congruence.
Qed.

Lemma agree_on_subset: forall S S' v1 v2,
  VarSet.Subset S' S ->
  agree_on S v1 v2 ->
  agree_on S' v1 v2.
Proof.
  unfold agree_on, VarSet.Subset.
  intros.
  apply H0.
  apply VarSet.mem_spec.
  apply VarSet.mem_spec in H1.
  apply H.
  apply H1.
Qed.

Lemma agree_on_union: forall S1 S2 v1 v2,
    agree_on (VarSet.union S1 S2) v1 v2 ->
    agree_on S1 v1 v2 /\
    agree_on S2 v1 v2.
Proof.
  unfold agree_on.
  intros.
  split; intros.
  - apply H.
    rewrite VarSetEqProps.union_mem.
    rewrite Bool.orb_true_intro.
    reflexivity.
    left.
    assumption.
  - apply H.
    rewrite VarSetEqProps.union_mem.
    rewrite Bool.orb_true_intro.
    reflexivity.
    right.
    assumption.
Qed.


(* x is not in S, so updating x doesn't affect agreement on S *)
Lemma agree_on_update_out: forall S v x a,
  VarSet.mem x S = false ->
  agree_on S v (v $+ (x, a)).
Proof.
  unfold agree_on.
  intros.
  destruct (vsp.FM.eq_dec x x0).
  - subst.
    rewrite H in H0.
    discriminate.
  - rewrite lookup_add_ne.
    + reflexivity.
    + auto.
Qed.

(* Updating the same key on both sides preserves agreement *)
Lemma agree_on_update_both: forall S v1 v2 x a,
  agree_on S v1 v2 ->
  agree_on S (v1 $+ (x, a)) (v2 $+ (x, a)).
Proof.
  unfold agree_on.
  intros.
  destruct (vsp.FM.eq_dec x x0).
  - repeat rewrite lookup_add_eq; [reflexivity | assumption | assumption].
  - repeat rewrite lookup_add_ne.
    1: apply H; exact H0.
    1,2 : auto.
Qed.


Lemma agree_on_remove_both: forall S v1 v2 x,
  agree_on S v1 v2 ->
  agree_on (VarSet.remove x S) v1 v2.
Proof.
  unfold agree_on.
  intros.
  destruct (vsp.FM.eq_dec x x0).
  - subst.
    exfalso.
    rewrite VarSet.mem_spec in H0.
    rewrite VarSet.remove_spec in H0.
    tauto.
  - apply H.
    rewrite VarSet.mem_spec in *.
    rewrite VarSet.remove_spec in H0.
    tauto.
Qed.

Lemma agree_on_written_update: forall out deps v1 v2 x a,
  agree_on (VarSet.union (VarSet.remove x out) deps) v1 v2 ->
  agree_on out (v1 $+ (x, a)) (v2 $+ (x, a)).
Proof.
  unfold agree_on. intros out deps v1 v2 x a Hagree y Hy.
  destruct (vsp.FM.eq_dec x y).
  - subst. repeat rewrite lookup_add_eq by reflexivity. reflexivity.
  - repeat rewrite lookup_add_ne by auto.
    apply Hagree. apply VarSet.mem_spec, VarSet.union_spec. left.
    apply VarSet.remove_spec. split; [apply VarSet.mem_spec; exact Hy | apply not_eq_sym; exact n].
Qed.

Lemma agree_on_dead_update_left: forall out v1 v2 x a,
  VarSet.mem x out = false ->
  agree_on out v1 v2 ->
  agree_on out (v1 $+ (x, a)) v2.
Proof.
  unfold agree_on. intros out v1 v2 x a Hdead Hagree y Hy.
  rewrite lookup_add_ne; [apply Hagree; exact Hy |].
  intro Heq. subst. rewrite Hy in Hdead. discriminate.
Qed.

Lemma agree_on_dead_update_both: forall out v1 v2 x a1 a2,
  VarSet.mem x out = false ->
  agree_on out v1 v2 ->
  agree_on out (v1 $+ (x, a1)) (v2 $+ (x, a2)).
Proof.
  unfold agree_on. intros out v1 v2 x a1 a2 Hdead Hagree y Hy.
  repeat rewrite lookup_add_ne by (intro Heq; subst; rewrite Hy in Hdead; discriminate).
  apply Hagree. exact Hy.
Qed.

Lemma agree_on_remove_add: forall out v1 v2 x a,
  agree_on (VarSet.remove x out) v1 v2 ->
  agree_on out (v1 $+ (x, a)) (v2 $+ (x, a)).
Proof.
  intros.
  unfold agree_on.
  intros.
  destruct (x ==v x0).
  - subst. repeat rewrite lookup_add_eq; reflexivity.
  - eapply agree_on_update_both; [apply H|].
    rewrite VarSetEqProps.remove_mem_2; eauto.
Qed.
