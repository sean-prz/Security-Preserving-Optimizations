Require Import Map.
Require Import VarSets.
Require Import Language.Main.
Require Import Language.Analysis.
Require Import Language.Optimizations.Unsafe.DSE.
Require Import Language.Optimizations.Safe.Unskip.
Require Import Proofs.Analysis.LivenessProofs.
Require Import Proofs.unskip.Soundness.
Require Import Proofs.VarSetAgreement.

(*
  Local soundness of dead-store elimination: if two states agree on the variables
  live before `c`, then evaluating `c` and `dse_helper c out` produces final
  states that still agree on `out`.

  The proof follows the structure of the original evaluation derivation. In each
  evaluation case, the liveness information tells us whether a write is relevant
  to the final observable variables or can be safely ignored.
*)

Local Ltac solve_while_cond H H_agree :=
  rewrite <- H; apply interp_arith_agree;
  eapply agree_on_subset;
    [apply liveness_while_cond_subset | apply agree_on_sym; exact H_agree].

Lemma dse_helper_sound: forall c out v1 v2 v1',
  agree_on (liveness c out) v1 v2 ->
  eval v1 c v1' ->
  exists v2',
    eval v2 (dse_helper c out) v2' /\
    agree_on out v1' v2'.
Proof.
  intros c out v1 v2 v1' H_agree H. revert out v2 H_agree.
  induction H; intros out v_2 H_agree.

  (* Skip: the optimized command is still `Skip`, so both states already agree on `out`. *)
  - exists v_2. split; [constructor | exact H_agree].

  (* Assignment, live target: keep the assignment and show both sides compute the same value. *)
  - simpl in *.
    destruct (VarSet.mem x out) eqn:Hx.
    + assert (Ha: interp_arith e v_2 = a).
      { rewrite <- H. apply interp_arith_agree.
        eapply agree_on_subset; [| apply agree_on_sym; exact H_agree]. VarSetDecide.fsetdec. }
      exists (v_2 $+ (x, a)). split.
      * apply EvalAssign with (v:=v_2). simpl. exact Ha.
      * eapply agree_on_written_update; exact H_agree.
    (* Assignment, dead target: DSE drops the write, and agreement on `out` is unchanged. *)
    + exists v_2. split; [constructor |].
      eapply agree_on_dead_update_left; eauto.

  (* Conditional move (true branch), live target: preserve the write after matching all expressions. *)
  - simpl in *.
    destruct (VarSet.mem x out) eqn:Hx.
    + assert (Hcond: interp_arith cond v_2 = c) by solve_dse_cmov_interp H_agree.
      assert (Ha1: interp_arith e1 v_2 = a1) by solve_dse_cmov_interp H_agree.
      assert (Ha2: interp_arith e2 v_2 = a2) by solve_dse_cmov_interp H_agree.
      exists (v_2 $+ (x, a1)). split.
       * eapply EvalCmovTrue with (v:=v_2); eassumption.
       * eapply agree_on_written_update; exact H_agree.
    (* Conditional move (true branch), dead target: optimized code skips the write entirely. *)
    + exists v_2. split; [constructor |].
      eapply agree_on_dead_update_left; eauto.

  (* Conditional move (false branch), live target: same idea, but the second expression is written. *)
  - simpl in *.
    destruct (VarSet.mem x out) eqn:Hx.
    + assert (Hcond: interp_arith cond v_2 = 0) by solve_dse_cmov_interp H_agree.
      assert (Ha1: interp_arith e1 v_2 = a1) by solve_dse_cmov_interp H_agree.
      assert (Ha2: interp_arith e2 v_2 = a2) by solve_dse_cmov_interp H_agree.
      exists (v_2 $+ (x, a2)). split.
       * eapply EvalCmovFalse with (v:=v_2); eassumption.
       * eapply agree_on_written_update; exact H_agree.
    (* Conditional move (false branch), dead target: removing the write does not affect `out`. *)
    + exists v_2. split; [constructor |].
      eapply agree_on_dead_update_left; eauto.

  (* Sequence: first relate the intermediate states for `c1`, then reuse that relation for `c2`. *)
  - simpl in *.
    destruct (IHeval1 (liveness c2 out) v_2 H_agree) as [v_mid2 [H_mid2 H_agree_mid]].
    destruct (IHeval2 out v_mid2 H_agree_mid) as [v_out2 [H_out2 H_agree_out]].
    exists v_out2. split; [| assumption].
    eapply EvalSequence; [exact H_mid2 | assumption].

  (* If-true: agreement on live variables is enough to replay the same guard outcome and then use the IH. *)
  - simpl in *.
    assert (Hcond: interp_arith e v_2 = c).
    { rewrite <- H. apply interp_arith_agree.
      eapply agree_on_subset; [| apply agree_on_sym; exact H_agree]. VarSetDecide.fsetdec. }
    destruct (IHeval out v_2) as [v2' [H2' H_agree2']].
     { eapply agree_on_subset; [| exact H_agree]. VarSetDecide.fsetdec. }
     exists v2'. split; [eapply EvalIfTrue; [simpl; exact Hcond | exact H0 | exact H2'] | exact H_agree2'].

  (* If-false: identical to the true case, but we replay the false branch instead. *)
  - simpl in H_agree |- *.
    assert (Hcond: interp_arith e v_2 = 0).
    { rewrite <- H. apply interp_arith_agree.
      eapply agree_on_subset; [| apply agree_on_sym; exact H_agree]. VarSetDecide.fsetdec. }
    destruct (IHeval out v_2) as [v_2' [H2' H_agree2']].
     { eapply agree_on_subset; [| exact H_agree]. VarSetDecide.fsetdec. }
     exists v_2'. split; [eapply EvalIfFalse; [simpl; exact Hcond | exact H2'] | exact H_agree2'].

  (* While-true: use the loop fixpoint to replay one body step, then apply the IH again to the recursive loop evaluation. *)
  - set (fp := liveness (While e body) out).
    assert (Hcond: interp_arith e v_2 = c) by solve_while_cond H H_agree.
    destruct (IHeval1 fp v_2) as [v_body2 [H_body2 H_agree_body2]].
    { eapply agree_on_subset; [apply liveness_while_body_closed | exact H_agree]. }
    destruct (IHeval2 out v_body2 H_agree_body2) as [v_while2 [H_while2 H_agree_while2]].
    exists v_while2. split; [| assumption].
    eapply EvalWhileTrue; [simpl; exact Hcond | exact H0 | simpl; exact H_body2 | exact H_while2].

  (* While-false: agreement on the loop guard is enough to stop immediately, and the fixpoint already contains `out`. *)
  - set (fp := liveness (While e body) out).
    assert (Hcond: interp_arith e v_2 = 0) by solve_while_cond H H_agree.
    exists v_2. split.
    + apply EvalWhileFalse. exact Hcond.
    + simpl. eapply agree_on_subset; [| exact H_agree].
      apply while_fixpoint_contains_out.
Qed.

Create HintDb eval_db.
Hint Constructors eval eval_trace eval_sec : eval_db.

(*
  This theorem lifts the command-level lemma to whole programs.
  First, `dse_helper_sound` shows that unsafe DSE preserves the program outputs.
  Then `opt_unskip_sound` removes any administrative `Skip`s introduced by the
  optimizer, without changing the resulting evaluation.
*)
Theorem opt_dse_sound: forall (pgm: program) v v',
  eval v (cmd_of pgm) v' ->
  exists v_opt,
    eval v (cmd_of (opt_dse pgm)) v_opt /\
    agree_on (output_of pgm) v' v_opt.
Proof.
  intros pgm v v' Heval.
  unfold opt_dse.
  (* Step 1: run the local DSE soundness lemma on the program command and outputs. *)
  assert (H_dse: exists v_dse,
    eval v (dse_helper (cmd_of pgm) (output_of pgm)) v_dse /\
    agree_on (output_of pgm) v' v_dse).
  {
    destruct pgm as [c out]. simpl.
    eapply dse_helper_sound; [apply agree_on_refl | exact Heval].
  }
  (* Step 2: eliminate the `Skip`s inserted by the optimization pipeline. *)
  destruct H_dse as [v_dse [Hdse_eval Hdse_agree]].
  apply opt_unskip_sound in Hdse_eval.
  (* Step 3: keep the same final state; output agreement was already established above. *)
  exists v_dse. split; [exact Hdse_eval | exact Hdse_agree].
Qed.
