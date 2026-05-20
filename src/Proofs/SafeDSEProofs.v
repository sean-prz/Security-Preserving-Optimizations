Require Import Map.
Require Import VarSets.
Require Import Language.Main.
Require Import Language.Analysis.
Require Import Language.Optimizations.Safe.DSE.
Require Import Proofs.UnsafeDSEProofs.



Lemma safe_dse_helper_sound: forall phi c out v1 v2 v1' secrets,
  agree_on (liveness c out) v1 v2 ->
  eval phi v1 c v1' ->
  exists v2',
    eval phi v2 (safe_dse_helper c out secrets) v2' /\
    agree_on out v1' v2'.
Proof.
  intros phi c out v1 v2 v1' secrets H_agree H. revert out secrets v2 H_agree.
  induction H; intros out secrets v_2 H_agree.

  - eexists. split; [econstructor | exact H_agree].

  - simpl in *.
    destruct (VarSet.mem x out) eqn:Hx.
    + assert (Ha: interp_arith e v_2 = a).
      { rewrite <- H. apply interp_arith_agree.
        eapply agree_on_subset; [| apply agree_on_sym; exact H_agree]. VarSetDecide.fsetdec. }
      exists (v_2 $+ (x, a)). split.
      * apply EvalAssign with (v:=v_2). simpl. exact Ha.
      * eapply agree_on_written_update; exact H_agree.
    + destruct (sec_lookup secrets x) eqn:Hsecret.
      * exists v_2. split; [constructor |].
        eapply agree_on_dead_update_left; eauto.
      * exists (v_2 $+ (x, interp_arith e v_2)). split.
        -- apply EvalAssign. reflexivity.
        -- eapply agree_on_dead_update_both; eauto.

  - simpl in *.
    destruct (VarSet.mem x out) eqn:Hx.
    + assert (Hcond: interp_arith cond v_2 = c) by solve_dse_cmov_interp H_agree.
      assert (Ha1: interp_arith e1 v_2 = a1) by solve_dse_cmov_interp H_agree.
      assert (Ha2: interp_arith e2 v_2 = a2) by solve_dse_cmov_interp H_agree.
      exists (v_2 $+ (x, a1)). split.
      * eapply EvalCmovTrue with (v:=v_2); eassumption.
      * eapply agree_on_written_update; exact H_agree.
    + destruct (sec_lookup secrets x) eqn:Hsecret.
      * exists v_2. split.
        -- apply EvalSkip.
        -- eapply agree_on_dead_update_left; eauto.
      * destruct (interp_arith cond v_2) eqn:Hcond2.
        -- exists (v_2 $+ (x, interp_arith e2 v_2)). split.
           ++ eapply EvalCmovFalse with (v:=v_2) (a1:=interp_arith e1 v_2); eauto.
           ++ eapply agree_on_dead_update_both; eauto.
        -- exists (v_2 $+ (x, interp_arith e1 v_2)). split.
           ++ eapply EvalCmovTrue with (v:=v_2) (c:=S n) (a2:=interp_arith e2 v_2); eauto; discriminate.
           ++ eapply agree_on_dead_update_both; eauto.

  - simpl in *.
    destruct (VarSet.mem x out) eqn:Hx.
    + assert (Hcond: interp_arith cond v_2 = 0) by solve_dse_cmov_interp H_agree.
      assert (Ha1: interp_arith e1 v_2 = a1) by solve_dse_cmov_interp H_agree.
      assert (Ha2: interp_arith e2 v_2 = a2) by solve_dse_cmov_interp H_agree.
      exists (v_2 $+ (x, a2)). split.
      * eapply EvalCmovFalse with (v:=v_2); eassumption.
      * eapply agree_on_written_update; exact H_agree.
    + destruct (sec_lookup secrets x) eqn:Hsecret.
      * exists v_2. split.
        -- apply EvalSkip.
        -- eapply agree_on_dead_update_left; eauto.
      * destruct (interp_arith cond v_2) eqn:Hcond2.
        -- exists (v_2 $+ (x, interp_arith e2 v_2)). split.
           ++ eapply EvalCmovFalse with (v:=v_2) (a1:=interp_arith e1 v_2); eauto.
           ++ eapply agree_on_dead_update_both; eauto.
        -- exists (v_2 $+ (x, interp_arith e1 v_2)). split.
           ++ eapply EvalCmovTrue with (v:=v_2) (c:=S n) (a2:=interp_arith e2 v_2); eauto; discriminate.
           ++ eapply agree_on_dead_update_both; eauto.

  - simpl in *.
    assert (Ha1: interp_arith e1 v_2 = a1).
    { rewrite <- H0. apply interp_arith_agree.
      eapply agree_on_subset; [| apply agree_on_sym; exact H_agree]. VarSetDecide.fsetdec. }
    assert (Ha2: interp_arith e2 v_2 = a2).
    { rewrite <- H1. apply interp_arith_agree.
      eapply agree_on_subset; [| apply agree_on_sym; exact H_agree]. VarSetDecide.fsetdec. }
    exists (v_2 $+ (x, a)). split.
    + eapply EvalAssignCall; [exact H | simpl; exact Ha1 | simpl; exact Ha2 | exact H2 | exact H3].
    + eapply agree_on_written_update; exact H_agree.

  - simpl in *.
    destruct (IHeval1 (liveness c2 out) secrets v_2 H_agree) as [v_mid2 [H_mid2 H_agree_mid]].
    destruct (IHeval2 out secrets v_mid2 H_agree_mid) as [v_out2 [H_out2 H_agree_out]].
    exists v_out2. split; [| exact H_agree_out].
    eapply EvalSequence; [exact H_mid2|assumption]. 

  - simpl in *.
    assert (Hcond: interp_arith e v_2 = c).
    { rewrite <- H. apply interp_arith_agree.
      eapply agree_on_subset; [| apply agree_on_sym; exact H_agree]. VarSetDecide.fsetdec. }
    destruct (IHeval out secrets v_2) as [v2' [H2' H_agree2']].
    { eapply agree_on_subset; [| exact H_agree]. VarSetDecide.fsetdec. }
    exists v2'. split; [eapply EvalIfTrue; [simpl; exact Hcond | exact H0 | exact H2'] | exact H_agree2'].

  - simpl in H_agree |- *.
    assert (Hcond: interp_arith e v_2 = 0).
    { rewrite <- H. apply interp_arith_agree.
      eapply agree_on_subset; [| apply agree_on_sym; exact H_agree]. VarSetDecide.fsetdec. }
    destruct (IHeval out secrets v_2) as [v2' [H2' H_agree2']].
    { eapply agree_on_subset; [| exact H_agree]. VarSetDecide.fsetdec. }
    exists v2'. split; [eapply EvalIfFalse; [simpl; exact Hcond | exact H2'] | exact H_agree2'].

  - set (fp := liveness (While e body) out).
    assert (Hcond: interp_arith e v_2 = c).
    { rewrite <- H. apply interp_arith_agree.
      eapply agree_on_subset; [apply liveness_while_cond_subset | apply agree_on_sym; exact H_agree]. }
    destruct (IHeval1 fp secrets v_2) as [v_body2 [H_body2 H_agree_body2]].
    { eapply agree_on_subset; [apply liveness_while_body_closed | exact H_agree]. }
    destruct (IHeval2 out secrets v_body2 H_agree_body2) as [v_while2 [H_while2 H_agree_while2]].
    exists v_while2. split; [|  exact H_agree_while2].
    eapply EvalWhileTrue; [simpl; exact Hcond | exact H0 | exact H_body2 | exact H_while2].

  - set (fp := liveness (While e body) out).
    assert (Hcond: interp_arith e v_2 = 0).
    { rewrite <- H. apply interp_arith_agree.
      eapply agree_on_subset; [apply liveness_while_cond_subset | apply agree_on_sym; exact H_agree]. }
    exists v_2. split.
    + apply EvalWhileFalse. simpl. exact Hcond.
    + simpl. eapply agree_on_subset; [| exact H_agree].
      apply while_fixpoint_contains_out.
Qed.


Lemma opt_safe_dse_sound : forall phi pgm secrets v v',
  eval phi v (cmd_of pgm) v' ->
  exists v_opt,
    eval phi v (cmd_of (opt_safe_dse pgm  secrets)) v_opt /\
    agree_on (output_of pgm) v' v_opt.
Proof.
  intros phi pgm secrets v v' Heval.
  unfold opt_safe_dse.

  assert (H_dse: exists v_dse,
    eval phi v (safe_dse_helper (cmd_of pgm) (output_of pgm) secrets) v_dse /\
    agree_on (output_of pgm) v' v_dse).
  {
    destruct pgm.
    simpl.
    specialize (safe_dse_helper_sound phi c v0 v v v' secrets).
    intro.
    eapply H.
    - apply agree_on_refl.
    - apply Heval.
  }
  destruct H_dse as [v_dse [Hdse_eval Hdse_agree]].

  apply opt_unskip_sound in Hdse_eval.
  eexists.
  split; [exact Hdse_eval | exact Hdse_agree].
Qed.
