Require Import Map.
Require Import VarSets.
Require Import Language.Main.
Require Import Language.Analysis.
Require Import Language.Optimizations.Unsafe.DSE.

From Stdlib Require Import Lia.

Module vsp := VarSetProps.

(* ================================================================= *)
(* agree_on: two valuations agree on all variables in a set          *)
(* ================================================================= *)

(*notations dont perfectly make sense (uppercase or lowercase lib), but it applies well to this file*)
Notation "a [=] b" := (VarSet.equal a b) (at level 70).
Notation "a [<=] b" := (VarSet.Subset a b) (at level 70).
Notation "a [∪] b" := (VarSet.union a b) (at level 60).
Notation "a [/] b" := (VarSet.diff a b) (at level 60).

Definition agree_on (S: var_set) (v1 v2: valuation) : Prop :=
  forall x, VarSet.mem x S = true -> v1 $? x = v2 $? x.

(* ================================================================= *)
(* Basic agree_on lemmas                                      *)
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
    Search (orb _ _ = true).
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

(* ================================================================= *)
(* Step 2: interp_arith only depends on vars_in_expr                 *)
(* ================================================================= *)

Lemma interp_arith_agree: forall e v1 v2,
  agree_on (vars_in_expr e) v1 v2 ->
  interp_arith e v1 = interp_arith e v2.
Proof.
  unfold agree_on.
  induction e; simpl; intros.
  - reflexivity.
  - rewrite H.
    reflexivity.
    rewrite VarSet.mem_spec.
    rewrite VarSet.singleton_spec.
    reflexivity.
  - erewrite IHe1.
    erewrite IHe2.
    1: reflexivity.
    1,2: intros;
      apply H;
      rewrite VarSet.mem_spec in *;
      rewrite VarSet.union_spec.
    + right. assumption.
    + left. assumption.
Qed.

    (* ================================================================= *)
(* Liveness monotonicity and variable bound                  *)
(* ================================================================= *)


(* The result always contains the initial out — proved early because while_fixpoint_monotone needs it *)
Lemma while_fixpoint_contains_out: forall f cond_vars out fuel,
  VarSet.Subset out (while_fixpoint f cond_vars out fuel).
Proof.
  (* revert out so the IH is universally quantified over it,
     allowing IH to be applied to _in instead of out. *)
  intros f cond_vars out fuel.
  revert out.
  induction fuel; simpl; intros out.
  - apply vsp.subset_refl.
  - destruct (VarSet.equal out (VarSet.union (VarSet.union out cond_vars) (f out))) eqn:H.
    + apply vsp.subset_refl.
    + apply vsp.subset_trans with (VarSet.union (VarSet.union out cond_vars) (f out)).
      * eapply vsp.subset_trans; [apply vsp.union_subset_1|].
        apply vsp.union_subset_1.
      * apply IHfuel.
Qed.

(* If out is already stable under one iteration step, all further iterations keep it unchanged *)
Lemma while_fixpoint_at_fixpoint: forall f cond_vars out fuel,
  VarSet.equal out (VarSet.union (VarSet.union out cond_vars) (f out)) = true ->
  while_fixpoint f cond_vars out fuel = out.
Proof.
  induction fuel; simpl; intros H.
  - reflexivity.
  - rewrite H. reflexivity.
Qed.

Lemma while_fixpoint_monotone: forall f cond_vars out1 out2 fuel,
  (forall s1 s2, VarSet.Subset s1 s2 -> VarSet.Subset (f s1) (f s2)) ->
  VarSet.Subset out1 out2 ->
  VarSet.Subset (while_fixpoint f cond_vars out1 fuel) (while_fixpoint f cond_vars out2 fuel).
Proof.
  (* Introduce f, cond_vars, fuel, Hf first; revert out1/out2 so the IH
     is universally quantified over them — needed when applying IH to _in1/_in2. *)
  intros f cond_vars out1 out2 fuel Hf.
  revert out1 out2.
  induction fuel; simpl; intros out1 out2 H0.
  - assumption.
  - assert (H_in: VarSet.Subset
        (VarSet.union (VarSet.union out1 cond_vars) (f out1))
        (VarSet.union (VarSet.union out2 cond_vars) (f out2))).
    { apply vsp.union_subset_3.
      - apply vsp.union_subset_3.
        + eapply vsp.subset_trans; [exact H0|].
          eapply vsp.subset_trans; [apply vsp.union_subset_1|].
          apply vsp.union_subset_1.
        + eapply vsp.subset_trans; [apply vsp.union_subset_2|].
          apply vsp.union_subset_1.
      - eapply vsp.subset_trans; [apply Hf; exact H0|].
        apply vsp.union_subset_2.
    }
    destruct (VarSet.equal out1 (VarSet.union (VarSet.union out1 cond_vars) (f out1))) eqn:Hout1,
             (VarSet.equal out2 (VarSet.union (VarSet.union out2 cond_vars) (f out2))) eqn:Hout2.
    + assumption.
    + (* out1 converged, out2 not: out1 ⊆ out2 ⊆ _in2 ⊆ while_fixpoint ... _in2 *)
      apply vsp.subset_trans with out2; [assumption|].
      apply vsp.subset_trans with (VarSet.union (VarSet.union out2 cond_vars) (f out2)).
      * eapply vsp.subset_trans; [apply vsp.union_subset_1|].
        apply vsp.union_subset_1.
      * apply while_fixpoint_contains_out.
    + (* out2 already converged, out1 not: while_fixpoint ... _in1 ⊆ out2 *)
      assert (H_in2_out2: VarSet.Subset
          (VarSet.union (VarSet.union out2 cond_vars) (f out2)) out2).
      { apply vsp.subset_equal.
        apply vsp.equal_sym.
        apply VarSet.equal_spec.
        exact Hout2. }
      apply vsp.subset_trans with (while_fixpoint f cond_vars out2 fuel).
      * apply IHfuel.
        eapply vsp.subset_trans; [exact H_in | exact H_in2_out2].
      * rewrite while_fixpoint_at_fixpoint by exact Hout2.
        apply vsp.subset_refl.
    + (* neither converged: IH applies directly to _in1 ⊆ _in2 *)
      apply IHfuel. exact H_in.
Qed.


Lemma while_fixpoint_vars_bound: forall f cond_vars out fuel universe,
  VarSet.Subset out universe ->
  VarSet.Subset cond_vars universe ->
  (forall s, VarSet.Subset s universe -> VarSet.Subset (f s) universe) ->
  VarSet.Subset (while_fixpoint f cond_vars out fuel) universe.
Proof.
  intros f cond_vars out fuel universe H0 H1 H2.
  generalize  out H0.
  induction fuel; simpl; intros.
  - assumption.
  - destruct (VarSet.equal out0 (VarSet.union (VarSet.union out0 cond_vars) (f out0))).
    + assumption.
    + rewrite IHfuel.
      * VarSetDecide.fsetdec.
      * rewrite  H2.
        2: assumption.
        rewrite H3.
        rewrite H1.
        VarSetDecide.fsetdec.
Qed.

(* liveness can only introduce variables already in out or in vars_in_cmd c *)
Lemma liveness_vars_bound: forall c out,
  VarSet.Subset (liveness c out) (VarSet.union out (vars_in_cmd c)).
Proof.
  induction c; simpl; intros.
  - VarSetDecide.fsetdec.
  - destruct (VarSet.mem s out) eqn:Hs.
    all: VarSetDecide.fsetdec.
  - VarSetDecide.fsetdec.
  - destruct (VarSet.mem s out) eqn:Hs.
    all: VarSetDecide.fsetdec.
  - eapply vsp.subset_trans.
    apply IHc1.
    rewrite IHc2.
    VarSetDecide.fsetdec.
  - rewrite IHc1.
    rewrite IHc2.
    VarSetDecide.fsetdec.
  - apply while_fixpoint_vars_bound.
    + VarSetDecide.fsetdec.
    + VarSetDecide.fsetdec.
    + intros.
      rewrite IHc.
      VarSetDecide.fsetdec.
Qed.


(* ================================================================= *)
(* while_fixpoint properties                                  *)
(* ================================================================= *)

(* The result always contains cond_vars *)
Lemma while_fixpoint_contains_cond_vars: forall f cond_vars out fuel,
    fuel > 0 ->
  VarSet.Subset cond_vars (while_fixpoint f cond_vars out fuel).
Proof.
  intros f cond_vars out fuel.
  revert out.
  induction fuel; simpl; intros.
  - lia.
  - destruct (VarSet.equal out (VarSet.union (VarSet.union out cond_vars) (f out))) eqn:Hout.
    apply VarSet.equal_spec in Hout.
    rewrite Hout.
    VarSetDecide.fsetdec.
    destruct fuel as [|n].
    + simpl.
      VarSetDecide.fsetdec.
    + apply IHfuel.
      lia.
Qed.


(*helpers*)

Lemma liveness_while_cond_subset : forall body e out,
  VarSet.Subset (vars_in_expr e) (liveness (While e body) out).
Proof.
  intros body e out. simpl.
  destruct (VarSet.cardinal (VarSet.union (vars_in_expr e) (vars_in_cmd body))) eqn:Hfuel.
  - apply vsp.cardinal_Empty in Hfuel. VarSetDecide.fsetdec.
  - apply while_fixpoint_contains_cond_vars. lia.
Qed.

Lemma cardinal_diff_with_witness : forall universe out _in x,
  VarSet.In x universe ->
  VarSet.In x _in ->
  ~ VarSet.In x out ->
  VarSet.Subset out _in ->
  VarSet.cardinal (VarSet.diff universe _in) < VarSet.cardinal (VarSet.diff universe out).
Proof.
  intros. apply vsp.subset_cardinal_lt with x; VarSetDecide.fsetdec.
Qed.

(* FIXPOINT LEMMA: with enough fuel the result is a real fixpoint.
   Enough fuel = cardinal of variables that can ever be added
   = cardinal (vars_in_cmd (While e body)).
   The fixpoint fp satisfies: fp = f(fp)*)


Lemma while_fixpoint_is_fixpoint: forall body e out n,
  VarSet.cardinal (VarSet.diff (VarSet.union (vars_in_expr e) (vars_in_cmd body)) out) <= n ->
  let fp := while_fixpoint (liveness body) (vars_in_expr e) out n in
  VarSet.Equal (VarSet.union (VarSet.union fp (vars_in_expr e)) (liveness body fp)) fp.
Proof.
  intros body e out n. revert body e out.
  induction n; simpl; intros body e out H.
  - apply Nat.le_0_r, vsp.cardinal_Empty in H.
    pose proof (liveness_vars_bound body out). VarSetDecide.fsetdec.
  - set (universe := VarSet.union (vars_in_expr e) (vars_in_cmd body)).
    set (_in := VarSet.union (VarSet.union out (vars_in_expr e)) (liveness body out)).
    destruct (VarSet.equal out _in) eqn:Heq.
    + apply VarSet.equal_spec in Heq. VarSetDecide.fsetdec.
    + apply IHn. fold universe in H.
      destruct (VarSet.choose (VarSet.diff _in out)) as [x|] eqn:Hchoose.
      * apply VarSet.choose_spec1, VarSet.diff_spec in Hchoose as [Hxin Hxout].
        assert (Hxuniv: VarSet.In x universe).
        { unfold _in in Hxin. rewrite !VarSet.union_spec in Hxin.
          destruct Hxin as [[Hxo|Hxe]|Hxl].
          - contradiction.
          - unfold universe. VarSetDecide.fsetdec.
          - assert (VarSet.In x (VarSet.union out (vars_in_cmd body)))
              by (apply liveness_vars_bound; exact Hxl).
            unfold universe. VarSetDecide.fsetdec. }
        assert (VarSet.cardinal (VarSet.diff universe _in) <
                VarSet.cardinal (VarSet.diff universe out))
          by (apply cardinal_diff_with_witness with x;
              [exact Hxuniv | exact Hxin | exact Hxout | VarSetDecide.fsetdec]).
        fold universe.
        lia.
      * exfalso. apply VarSet.choose_spec2 in Hchoose.
        assert (VarSet.equal out _in = true)
          by (apply VarSet.equal_spec; VarSetDecide.fsetdec).
        congruence.
Qed.

Lemma liveness_while_body_closed : forall body e out,
  VarSet.Subset (liveness body (liveness (While e body) out)) (liveness (While e body) out).
Proof.
  intros body e out.
  assert (Hbound: VarSet.cardinal (VarSet.diff (VarSet.union (vars_in_expr e) (vars_in_cmd body)) out) <=
          VarSet.cardinal (VarSet.union (vars_in_expr e) (vars_in_cmd body)))
    by (apply vsp.subset_cardinal; VarSetDecide.fsetdec).
  pose proof while_fixpoint_is_fixpoint body e out _ Hbound as Heq.
  simpl in Heq. VarSetDecide.fsetdec.
Qed.

Lemma eval_trace_insensitive: forall phi v t1 t2 c ctx',
  eval phi (v, t1) c ctx' ->
  exists ctx'', eval phi (v, t2) c ctx'' /\ val_of ctx'' = val_of ctx'.
Proof.
  enough (H_gen : forall phi ctx c ctx',
    eval phi ctx c ctx' ->
    forall t2, exists ctx'', eval phi (val_of ctx, t2) c ctx'' /\ val_of ctx'' = val_of ctx')
    by (intros phi v t1 t2 c ctx' H; exact (H_gen phi (v, t1) c ctx' H t2)).
  intros phi ctx c ctx' Heval. induction Heval; intros t2.
  - exists (val_of ctx, t2). split; [constructor | reflexivity].
  - exists ((val_of ctx, t2) v$+ (x, a)).
    split; [apply EvalAssign; simpl; exact H | reflexivity].
  - exists ((val_of ctx, t2) v$+ (x, a1)).
    split; [eapply EvalCmovTrue; simpl; eassumption | reflexivity].
  - exists ((val_of ctx, t2) v$+ (x, a2)).
    split; [eapply EvalCmovFalse; simpl; eassumption | reflexivity].
  - destruct (IHHeval t2) as [ctx_inner'' [H_inner Hval_inner]].
    exists (val_of ctx $+ (x, a), trace_of ctx_inner''). split; [| reflexivity].
    eapply EvalAssignCall with (ctx:=(val_of ctx, t2)); [exact H | simpl; exact H0 | simpl; exact H1 | exact H_inner |].
    rewrite Hval_inner. exact H2.
  - destruct (IHHeval1 t2) as [[v_mid t_mid] [H_mid Hval_mid]].
    destruct (IHHeval2 t_mid) as [ctx_out'' [H_out Hval_out]].
    exists ctx_out''. split; [| exact Hval_out].
    eapply EvalSequence; [exact H_mid |].
    simpl in Hval_mid. rewrite  Hval_mid. exact H_out.
  - destruct (IHHeval (app t2 (Branch true::nil))) as [ctx'' [H_if Hval_if]].
    exists ctx''. split; [| exact Hval_if].
    eapply EvalIfTrue; [simpl; exact H | exact H0 | simpl in H_if; exact H_if].
  - destruct (IHHeval (app t2 (Branch false::nil))) as [ctx'' [H_if Hval_if]].
    exists ctx''. split; [| exact Hval_if].
    eapply EvalIfFalse; [simpl; exact H | simpl in H_if; exact H_if].
  - destruct (IHHeval1 (app t2 (Branch true::nil))) as [[v_body t_body] [H_body Hval_body]].
    destruct (IHHeval2 t_body) as [ctx_final'' [H_final Hval_final]].
    exists ctx_final''. split; [| exact Hval_final].
    eapply EvalWhileTrue; [simpl; exact H | exact H0 | simpl in H_body; exact H_body |].
    simpl in Hval_body. rewrite Hval_body. exact H_final.
  - exists (val_of ctx, (app t2 (Branch false::nil))).
    split; [apply EvalWhileFalse; simpl; exact H | reflexivity].
Qed.


    (* ================================================================= *)
(*  dse_helper soundness (main inductive lemma)               *)
(* ================================================================= *)


Lemma dse_helper_sound: forall phi c out ctx1 ctx1',
  eval phi ctx1 c ctx1' ->
  forall v2,
    agree_on (liveness c out) (val_of ctx1) v2 ->
    exists ctx2',
      eval phi (v2, trace_of ctx1) (dse_helper c out) ctx2' /\
      agree_on out (val_of ctx1') (val_of ctx2').
Proof.
Ltac solve_interp_agree :=
  match goal with
  | H_eval: interp_arith ?e ?v1 = ?val, H_agree: agree_on _ ?v1 ?v2 |- interp_arith ?e ?v2 = ?val =>
      rewrite <- H_eval;
      apply interp_arith_agree;
      eapply agree_on_subset; [| apply agree_on_sym; exact H_agree];
      VarSetDecide.fsetdec
  end.

(* Automates the map equality proof when a variable is LIVE (updated on both sides) *)
Ltac solve_agree_live H_agree :=
  unfold agree_on; intros y0 Hy0; simpl;
  match goal with
  | |- ?m1 $+ (?x, _) $? ?y = ?m2 $+ (?x, _) $? ?y =>
      destruct (vsp.FM.eq_dec x y) as [Heq | Hneq];
      [ subst; repeat (rewrite lookup_add_eq; [| reflexivity]); reflexivity
      | repeat (rewrite lookup_add_ne; [| auto]);
        apply H_agree; apply VarSet.mem_spec, VarSet.union_spec; left;
        apply VarSet.remove_spec; split; [apply VarSet.mem_spec; exact Hy0 | apply not_eq_sym; exact Hneq] ]
  end.

(* Automates the map equality proof when a variable is DEAD (skipped, updated on only one side) *)
Ltac solve_agree_dead H_agree Hx :=
  unfold agree_on; intros y0 Hy0; simpl;
  match goal with
  | |- ?m1 $+ (?x, _) $? ?y = ?m2 $? ?y =>
      rewrite lookup_add_ne; [apply H_agree; exact Hy0|];
      intro Heq; subst; rewrite Hy0 in Hx; discriminate
  end.

  intros phi c out ctx1 ctx1' H. revert out.
  induction H; intros out v2 H_agree.

  - (* EvalSkip *)
    exists (v2, trace_of ctx). split; [constructor | exact H_agree].
  - (* EvalAssign *)
    simpl in *.
    destruct (VarSet.mem x out) eqn:Hx.
    + assert (Ha: interp_arith e v2 = a) by solve_interp_agree.
      exists (v2 $+ (x, a), trace_of ctx). split.
      * apply EvalAssign with (ctx:=(v2, trace_of ctx)). simpl. exact Ha.
      * solve_agree_live H_agree.
    + exists (v2, trace_of ctx). split; [constructor|].
      solve_agree_dead H_agree Hx.

  - (* EvalCmovTrue *)
    simpl in *.
    destruct (VarSet.mem x out) eqn:Hx.
    + assert (Hcond: interp_arith cond v2 = c) by solve_interp_agree.
      assert (Ha1: interp_arith e1 v2 = a1) by solve_interp_agree.
      assert (Ha2: interp_arith e2 v2 = a2) by solve_interp_agree.
      exists (v2 $+ (x, a1), trace_of ctx). split.
      * eapply EvalCmovTrue with (ctx:=(v2, trace_of ctx)); simpl; eassumption.
      * solve_agree_live H_agree.
    + exists (v2, trace_of ctx). split; [constructor|].
        solve_agree_dead H_agree Hx.

  - (* EvalCmovFalse *)
    simpl in *.
    destruct (VarSet.mem x out) eqn:Hx.
    + assert (Hcond: interp_arith cond v2 = 0) by solve_interp_agree.
      assert (Ha1: interp_arith e1 v2 = a1) by solve_interp_agree.
      assert (Ha2: interp_arith e2 v2 = a2) by solve_interp_agree.
      exists (v2 $+ (x, a2), trace_of ctx). split.
      * eapply EvalCmovFalse with (ctx:=(v2, trace_of ctx)); simpl; eassumption.
      * solve_agree_live H_agree.
    + exists (v2, trace_of ctx). split; [constructor|].
      solve_agree_dead H_agree Hx.

  - (* EvalAssignCall *)
    simpl in *.
    assert (Ha1: interp_arith e1 v2 = a1) by solve_interp_agree.
    assert (Ha2: interp_arith e2 v2 = a2) by solve_interp_agree.
    exists (v2 $+ (x, a), trace_of ctx'). split.
    + eapply EvalAssignCall; simpl; eassumption.
    + solve_agree_live H_agree.

  - (* EvalSequence *)
    simpl in *.
    destruct (IHeval1 (liveness c2 out) v2 H_agree) as [ctx_mid2 [H_mid2 H_agree_mid]].
    destruct (IHeval2 out (val_of ctx_mid2) H_agree_mid) as [ctx_out2 [H_out2 H_agree_out]].
    destruct (eval_trace_insensitive phi (val_of ctx_mid2) (trace_of ctx1) (trace_of ctx_mid2)
                (dse_helper c2 out) ctx_out2 H_out2) as [ctx_out2' [H_out2' Hval_out2']].
    exists ctx_out2'. split; [| rewrite Hval_out2'; exact H_agree_out].
    eapply EvalSequence; [exact H_mid2|]. destruct ctx_mid2. assumption.

  - (* EvalIfTrue *)
    simpl in *.
    assert (Hcond: interp_arith e v2 = c).
    { rewrite <- H. apply interp_arith_agree.
      eapply agree_on_subset; [| apply agree_on_sym; exact H_agree]. VarSetDecide.fsetdec. }
    destruct (IHeval out v2) as [ctx2' [H2' H_agree2']].
    { eapply agree_on_subset; [| exact H_agree]. VarSetDecide.fsetdec. }
    exists ctx2'. split; [eapply EvalIfTrue; [simpl; exact Hcond | exact H0 | exact H2'] | exact H_agree2'].

  - (* EvalIfFalse *)
    simpl in H_agree |- *.
    assert (Hcond: interp_arith e v2 = 0).
    { rewrite <- H. apply interp_arith_agree.
      eapply agree_on_subset; [| apply agree_on_sym; exact H_agree]. VarSetDecide.fsetdec. }
    destruct (IHeval out v2) as [ctx2' [H2' H_agree2']].
    { eapply agree_on_subset; [| exact H_agree]. VarSetDecide.fsetdec. }
    exists ctx2'. split; [eapply EvalIfFalse; [simpl; exact Hcond | exact H2'] | exact H_agree2'].

  - (* EvalWhileTrue *)
    set (fp := liveness (While e body) out).
    assert (Hcond: interp_arith e v2 = c).
    { rewrite <- H. apply interp_arith_agree.
      eapply agree_on_subset; [apply liveness_while_cond_subset | apply agree_on_sym; exact H_agree]. }
    destruct (IHeval1 fp v2) as [ctx_body2 [H_body2 H_agree_body2]].
    { eapply agree_on_subset; [apply liveness_while_body_closed | exact H_agree]. }
    destruct (IHeval2 out (val_of ctx_body2) H_agree_body2) as [ctx_while2 [H_while2 H_agree_while2]].
    destruct (eval_trace_insensitive phi (val_of ctx_body2) (trace_of ctx') (trace_of ctx_body2)
                (While e (dse_helper body fp)) ctx_while2 H_while2) as [ctx_while2' [H_while2' Hval_while2']].
    exists ctx_while2'. split; [| rewrite Hval_while2'; exact H_agree_while2].
    eapply EvalWhileTrue; [simpl; exact Hcond | exact H0 | | exact H_while2'].
    simpl. destruct ctx_body2. exact H_body2.

  - (* EvalWhileFalse *)
    set (fp := liveness (While e body) out).
    assert (Hcond: interp_arith e v2 = 0).
    { rewrite <- H. apply interp_arith_agree.
      eapply agree_on_subset; [apply liveness_while_cond_subset | apply agree_on_sym; exact H_agree]. }
    exists ((v2, trace_of ctx) t++ Branch false). split.
    + apply EvalWhileFalse. simpl. exact Hcond.
    + simpl. eapply agree_on_subset; [| exact H_agree].
      apply while_fixpoint_contains_out.
Qed.

Lemma opt_unskip_sound: forall phi c ctx ctx',
  eval phi ctx c ctx' ->
  exists ctx_opt,
    eval phi ctx (opt_unskip c) ctx_opt /\
    val_of ctx' = val_of ctx_opt.
Proof.
  induction 1; simpl; intros.
  Admitted.



(* ================================================================= *)
(*  Final proof                                     *)
(* ================================================================= *)

Theorem opt_dse_sound: forall phi (pgm: program) ctx ctx',
  eval phi ctx (cmd_of pgm) ctx' ->
  exists ctx_opt,
    eval phi ctx (cmd_of (opt_dse pgm)) ctx_opt /\
    agree_on (output_of pgm) (val_of ctx') (val_of ctx_opt). (*all output vars are the same*)
Proof.
  intros phi pgm ctx ctx' Heval.
  unfold opt_dse.
  (* 1: apply dse_helper_sound with ctx1 = ctx2 = ctx *)
  assert (H_dse: exists ctx_dse,
    eval phi ctx (dse_helper (cmd_of pgm) (output_of pgm)) ctx_dse /\
    agree_on (output_of pgm) (val_of ctx') (val_of ctx_dse)).
  {
        destruct ctx.
    destruct pgm.
    simpl.
    specialize (dse_helper_sound phi c v0 _ _ Heval v). simpl.  intro.
    eapply H.
    - apply agree_on_refl.
  }
  destruct H_dse as [ctx_dse [Hdse_eval Hdse_agree]].
  (* 2: apply opt_unskip_sound to ctx_dse *)
  apply opt_unskip_sound in Hdse_eval.
  destruct Hdse_eval as [ctx_opt [Hunskip_eval Hunskip_val]].
  exists ctx_opt.
  split.
  - exact Hunskip_eval.
  - rewrite <- Hunskip_val. exact Hdse_agree.
Qed.
