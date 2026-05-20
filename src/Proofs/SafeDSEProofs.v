Require Import Map.
Require Import VarSets.
Require Import Language.Main.
Require Import Language.Analysis.
Require Import Language.Optimizations.Safe.DSE.
Require Import Proofs.UnsafeDSEProofs.


Lemma safe_dse_helper_sound: forall phi c out ctx1 ctx1' secrets,
  eval phi ctx1 c ctx1' ->
  forall v2,
    agree_on (liveness c out) (val_of ctx1) v2 ->
    exists ctx2',
      eval phi (v2, trace_of ctx1) (safe_dse_helper c out secrets) ctx2' /\
      agree_on out (val_of ctx1') (val_of ctx2').
Proof.
  intros phi c out ctx1 ctx1' secrets H. revert out secrets.
  induction H; intros out secrets  v2 H_agree.

  - eexists. split; [econstructor | exact H_agree].

  - simpl in *.
    destruct (VarSet.mem x out) eqn:Hx.
    + assert (Ha: interp_arith e v2 = a).
      { rewrite <- H. apply interp_arith_agree.
        eapply agree_on_subset; [| apply agree_on_sym; exact H_agree]. VarSetDecide.fsetdec. }
      exists (v2 $+ (x, a), trace_of ctx). split.
      * apply EvalAssign with (ctx:=(v2, trace_of ctx)). simpl. exact Ha.
      * unfold agree_on. intros y Hy.
        destruct (vsp.FM.eq_dec x y).
        -- subst. repeat (rewrite lookup_add_eq; [| reflexivity]). simpl. rewrite lookup_add_eq;  reflexivity.
        -- repeat (rewrite lookup_add_ne; [| auto]).
           simpl.
           rewrite lookup_add_ne by congruence.
           apply H_agree. apply VarSet.mem_spec, VarSet.union_spec. left.
           apply VarSet.remove_spec. split; [apply VarSet.mem_spec; exact Hy | apply not_eq_sym; exact n].
    + destruct (sec_lookup secrets x) eqn:Hsecret; eexists; split.
      1,3: constructor.
      reflexivity.
      simpl.
      eapply agree_on_update_out in Hx.
      eapply agree_on_trans.
      apply agree_on_sym.
      apply Hx.
      apply H_agree.

      unfold agree_on. intros y Hy.
      rewrite lookup_add_ne. 
      * simpl.
        eapply agree_on_update_out with (v:=v2)(a:=(interp_arith e v2)) in Hx.
        pose proof agree_on_trans as Htrans. 
        specialize (Htrans _ _ _ _ H_agree Hx).
        apply Htrans. exact Hy.
      * intro Heq. subst. rewrite Hy in Hx. discriminate.

  - simpl in *.
    assert (Ha1: interp_arith e1 v2 = a1).
    { rewrite <- H0. apply interp_arith_agree.
      eapply agree_on_subset; [| apply agree_on_sym; exact H_agree]. VarSetDecide.fsetdec. }
    assert (Ha2: interp_arith e2 v2 = a2).
    { rewrite <- H1. apply interp_arith_agree.
      eapply agree_on_subset; [| apply agree_on_sym; exact H_agree]. VarSetDecide.fsetdec. }
    exists (v2 $+ (x, a), trace_of ctx'). split.
    + eapply EvalAssignCall; [exact H | simpl; exact Ha1 | simpl; exact Ha2 | exact H2 | exact H3].
    + unfold agree_on. intros y0 Hy0.
      destruct (vsp.FM.eq_dec x y0).
      * subst. simpl. repeat (rewrite lookup_add_eq; [| reflexivity]).  reflexivity.
      * simpl. repeat (rewrite lookup_add_ne; [| auto]).
        apply H_agree. apply VarSet.mem_spec, VarSet.union_spec. left.
        apply VarSet.remove_spec. split; [apply VarSet.mem_spec; exact Hy0 | apply not_eq_sym; exact n].

  - simpl in *.
    destruct (IHeval1 (liveness c2 out) secrets v2 H_agree) as [ctx_mid2 [H_mid2 H_agree_mid]].
    destruct (IHeval2 out secrets (val_of ctx_mid2) H_agree_mid) as [ctx_out2 [H_out2 H_agree_out]].
    destruct (eval_trace_insensitive phi (val_of ctx_mid2) (trace_of ctx1) (trace_of ctx_mid2)
                (safe_dse_helper c2 out secrets) ctx_out2 H_out2) as [ctx_out2' [H_out2' Hval_out2']].
    exists ctx_out2'. split; [| rewrite Hval_out2'; exact H_agree_out].
    eapply EvalSequence; [exact H_mid2|]. destruct ctx_mid2. assumption.

  - simpl in *.
    assert (Hcond: interp_arith e v2 = c).
    { rewrite <- H. apply interp_arith_agree.
      eapply agree_on_subset; [| apply agree_on_sym; exact H_agree]. VarSetDecide.fsetdec. }
    destruct (IHeval out secrets v2) as [ctx2' [H2' H_agree2']].
    { eapply agree_on_subset; [| exact H_agree]. VarSetDecide.fsetdec. }
    exists ctx2'. split; [eapply EvalIfTrue; [simpl; exact Hcond | exact H0 | exact H2'] | exact H_agree2'].

  - simpl in H_agree |- *.
    assert (Hcond: interp_arith e v2 = 0).
    { rewrite <- H. apply interp_arith_agree.
      eapply agree_on_subset; [| apply agree_on_sym; exact H_agree]. VarSetDecide.fsetdec. }
    destruct (IHeval out secrets v2) as [ctx2' [H2' H_agree2']].
    { eapply agree_on_subset; [| exact H_agree]. VarSetDecide.fsetdec. }
    exists ctx2'. split; [eapply EvalIfFalse; [simpl; exact Hcond | exact H2'] | exact H_agree2'].

  - set (fp := liveness (While e body) out).
    assert (Hcond: interp_arith e v2 = c).
    { rewrite <- H. apply interp_arith_agree.
      eapply agree_on_subset; [apply liveness_while_cond_subset | apply agree_on_sym; exact H_agree]. }
    destruct (IHeval1 fp secrets v2) as [ctx_body2 [H_body2 H_agree_body2]].
    { eapply agree_on_subset; [apply liveness_while_body_closed | exact H_agree]. }
    destruct (IHeval2 out secrets (val_of ctx_body2) H_agree_body2) as [ctx_while2 [H_while2 H_agree_while2]].
    destruct (eval_trace_insensitive phi (val_of ctx_body2) (trace_of ctx') (trace_of ctx_body2)
                (While e (safe_dse_helper body fp secrets)) ctx_while2 H_while2) as [ctx_while2' [H_while2' Hval_while2']].
    exists ctx_while2'. split; [| rewrite Hval_while2'; exact H_agree_while2].
    eapply EvalWhileTrue; [simpl; exact Hcond | exact H0 | | exact H_while2'].
    simpl. destruct ctx_body2. exact H_body2.

  - set (fp := liveness (While e body) out).
    assert (Hcond: interp_arith e v2 = 0).
    { rewrite <- H. apply interp_arith_agree.
      eapply agree_on_subset; [apply liveness_while_cond_subset | apply agree_on_sym; exact H_agree]. }
    exists ((v2, trace_of ctx) t++ Branch false). split.
    + apply EvalWhileFalse. simpl. exact Hcond.
    + simpl. eapply agree_on_subset; [| exact H_agree].
      apply while_fixpoint_contains_out.
Qed.


Theorem opt_safe_dse_sound : forall phi pgm secrets ctx ctx',
  eval phi ctx (cmd_of pgm) ctx' ->
  exists ctx_opt,
    eval phi ctx (cmd_of (opt_safe_dse pgm secrets)) ctx_opt /\
    agree_on (output_of pgm) (val_of ctx') (val_of ctx_opt).
Proof.
  intros phi pgm secrets ctx ctx' Heval.
  unfold opt_safe_dse.

  assert (H_dse: exists ctx_dse,
    eval phi ctx (safe_dse_helper (cmd_of pgm) (output_of pgm) secrets) ctx_dse /\
    agree_on (output_of pgm) (val_of ctx') (val_of ctx_dse)).
  {
        destruct ctx.
    destruct pgm.
    simpl.
    specialize (safe_dse_helper_sound phi c v0 _ _ secrets Heval v). simpl.  intro.
    eapply H.
    - apply agree_on_refl.
  }
  destruct H_dse as [ctx_dse [Hdse_eval Hdse_agree]].

  apply opt_unskip_sound in Hdse_eval.
  destruct Hdse_eval as [ctx_opt [Hunskip_eval Hunskip_val]].
  exists ctx_opt.
  split.
  - exact Hunskip_eval.
  - rewrite <- Hunskip_val. exact Hdse_agree.
Qed.
