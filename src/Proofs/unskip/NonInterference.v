Require Import Map.
Require Import Language.Main.
Require Import Language.Analysis.
Require Import Language.Optimizations.Secure.Unskip.
Require Import Proofs.unskip.UnskipHints.
From Stdlib Require Import List.
From Stdlib Require Import Lia.
Import ListNotations.


Ltac solve_simple_assigns Hmatch:=
    destruct Hmatch as [Hval Htrace];
    rewrite Hval in *;
    eexists; split; eauto with unskip_db.

(* Forward simulation: Executing the unoptimized program implies the optimized
    program can execute to a matching state. *)
Lemma opt_unskip_forward : forall c ctx_src ctx_src_final ctx_opt,
  eval_trace ctx_src c ctx_src_final ->
  match_ctx ctx_src ctx_opt ->
  exists ctx_opt_final,
    eval_trace ctx_opt (opt_unskip_cmd c) ctx_opt_final /\
    match_ctx ctx_src_final ctx_opt_final.
Proof.
  intros c ctx_src ctx_src_final ctx_opt Heval Hmatch.
  revert ctx_opt Hmatch;
  induction Heval; intros ctx_opt Hmatch; simpl;
  try solve [ solve_simple_assigns Hmatch].

  - (* Skip *)
    eexists; split; eauto with unskip_db.

  - (* Sequence *)
    apply IHHeval1 in Hmatch as [ctx1_opt [Hstep1 Hmatch1]].
    apply IHHeval2 in Hmatch1 as [ctx2_opt [Hstep2 Hmatch2]].
    destruct (opt_unskip_cmd c1) eqn:Hc1opt;
    destruct (opt_unskip_cmd c2) eqn:Hc2opt;
    repeat match goal with
      | H : eval_trace _ Skip _ |- _ => inversion H; subst; clear H
    end;
    eexists; split; eauto with unskip_db.

  - (* IfTrue *)
    destruct (opt_unskip_cmd thn) eqn:Hthn;
    destruct (opt_unskip_cmd els) eqn:Hels.
    (* Skip, Skip case, drop branch *)
    1: {
      unfold match_ctx in Hmatch; destruct Hmatch as [Hval Htrace].
      assert (Hmatch_branch : match_ctx (ctx t++ Branch true) ctx_opt)
        by (split; auto; apply trace_subseq_append_drop; auto).
      apply IHHeval in Hmatch_branch as [ctx_opt_final [Hstep Hmatch_final]].
      inversion Hstep; subst; clear Hstep.
      eexists; split; eauto with unskip_db.
    }
    (* Other cases: the branch is kept *)
    all: unfold match_ctx in Hmatch; destruct Hmatch as [Hval Htrace].
    all: assert (Hmatch_branch : match_ctx (ctx t++ Branch true) (ctx_opt t++ Branch true))
           by (split; auto; apply trace_subseq_append_keep; auto).
    all: apply IHHeval in Hmatch_branch as [ctx_opt_final [Hstep Hmatch_final]].
    all: rewrite Hval in *.
    all: eexists; split; eauto with unskip_db.

  - (* IfFalse, same as IfTrue but with 'Branch false' *)
    destruct (opt_unskip_cmd thn) eqn:Hthn;
    destruct (opt_unskip_cmd els) eqn:Hels.
    1: {
      unfold match_ctx in Hmatch; destruct Hmatch as [Hval Htrace].
      assert (Hmatch_branch : match_ctx (ctx t++ Branch false) ctx_opt)
        by (split; auto; apply trace_subseq_append_drop; auto).
      apply IHHeval in Hmatch_branch as [ctx_opt_final [Hstep Hmatch_final]].
      inversion Hstep; subst; clear Hstep.
      eexists; split; eauto with unskip_db.
    }
    all: unfold match_ctx in Hmatch; destruct Hmatch as [Hval Htrace].
    all: assert (Hmatch_branch : match_ctx (ctx t++ Branch false) (ctx_opt t++ Branch false))
           by (split; auto; apply trace_subseq_append_keep; auto).
    all: apply IHHeval in Hmatch_branch as [ctx_opt_final [Hstep Hmatch_final]].
    all: rewrite Hval in *.
    all: eexists; split; eauto with unskip_db.

  - (* WhileTrue *)
    unfold match_ctx in Hmatch; destruct Hmatch as [Hval Htrace].
    (* Keep the true branch *)
    assert (Hmatch_branch : match_ctx (ctx t++ Branch true) (ctx_opt t++ Branch true))
      by (split; auto; apply trace_subseq_append_keep; auto).
    (* Chain the body execution and the rest of the loop execution *)
    apply IHHeval1 in Hmatch_branch as [ctx_opt_mid [Hstep1 Hmatch_mid]].
    apply IHHeval2 in Hmatch_mid as [ctx_opt_final [Hstep2 Hmatch_final]].
    rewrite Hval in *.
    eexists; split; eauto with unskip_db.
Qed.


(* Helper for backward simulation handling the `While` loop induction. *)
Lemma opt_unskip_backward_while : forall e body ctx_opt ctx_opt_final ctx_src,
  eval_trace ctx_opt (While e (opt_unskip_cmd body)) ctx_opt_final ->
  (forall ctx_o ctx_o_f ctx_s, eval_trace ctx_o (opt_unskip_cmd body) ctx_o_f -> match_ctx
      ctx_s ctx_o -> exists ctx_s_f, eval_trace ctx_s body ctx_s_f /\ match_ctx ctx_s_f
      ctx_o_f) ->
  match_ctx ctx_src ctx_opt ->
  exists ctx_src_final, eval_trace ctx_src (While e body) ctx_src_final /\ match_ctx ctx_src_final ctx_opt_final.
Proof.
  intros e body ctx_opt ctx_opt_final ctx_src Hopt Hbody_ih Hmatch.
  revert ctx_src Hmatch.
  remember (While e (opt_unskip_cmd body)) as loop_cmd.
  induction Hopt; intros ctx_src Hmatch; try discriminate.

  - (* EvalTraceWhileTrue *)
    inversion Heqloop_cmd; subst; clear Heqloop_cmd.
    unfold match_ctx in Hmatch; destruct Hmatch as [Hval Htrace].
    assert (Hmatch_branch : match_ctx (ctx_src t++ Branch true) (ctx t++ Branch true))
      by (split; simpl; [exact Hval | apply trace_subseq_append_keep; exact Htrace]).
    edestruct Hbody_ih as [ctx_src_mid [Hstep_body Hmatch_mid]]; [exact Hopt1 | exact Hmatch_branch |].
    edestruct IHHopt2 as [ctx_src_final [Hstep_loop Hmatch_final]]; [reflexivity | exact Hmatch_mid |].
    exists ctx_src_final; split.
    + eapply EvalTraceWhileTrue with (c := interp_arith e (val_of ctx)); eauto.
      rewrite Hval. reflexivity.
    + exact Hmatch_final.

  - (* EvalTraceWhileFalse *)
    inversion Heqloop_cmd; subst; clear Heqloop_cmd.
    unfold match_ctx in Hmatch; destruct Hmatch as [Hval Htrace].
    assert (Hmatch_branch : match_ctx (ctx_src t++ Branch false) (ctx t++ Branch false))
      by (split; simpl; [exact Hval | apply trace_subseq_append_keep; exact Htrace]).
    exists (ctx_src t++ Branch false); split.
    + eapply EvalTraceWhileFalse. rewrite Hval. eassumption.
    + exact Hmatch_branch.
Qed.

(* If the optimizer reduces a command to `Skip`, then the command has no
      effects on the valuation, but it might drop trace events. *)
Lemma opt_unskip_skip_trace_complete : forall c ctx,
  opt_unskip_cmd c = Skip ->
  exists ctx_src,
    eval_trace ctx c ctx_src /\
    match_ctx ctx_src ctx.
Proof.
  induction c; simpl; intros ctx Hskip; try discriminate.
  - (* Skip *) eauto with unskip_db.
  - (* Sequence*)
    destruct (opt_unskip_cmd c1) eqn:Hc1;
    destruct (opt_unskip_cmd c2) eqn:Hc2;
    try discriminate. (* solve all cases that don't optimize to skip *)

    destruct (IHc1 ctx eq_refl) as [ctx1_src [Hsrc1 Hmatch1]].
    destruct (IHc2 ctx1_src eq_refl) as [ctx2_src [Hsrc2 Hmatch2]].
    eauto with unskip_db.

  - (* If *)
    destruct (opt_unskip_cmd c1) eqn:Hc1;
    destruct (opt_unskip_cmd c2) eqn:Hc2;
    try discriminate. (* solve all cases that don't optimize to skip *)
    destruct (interp_arith e (val_of ctx)) eqn:Hcond.
    + (* If false *)
      destruct (IHc2 (ctx t++ Branch false) eq_refl) as [ctx2_src [Hsrc2 Hmatch2]].
      assert (Hbranch_match : match_ctx (ctx t++ Branch false) ctx);
      eauto with unskip_db.
    + (* If true *)
      destruct (IHc1 (ctx t++ Branch true) eq_refl) as [ctx1_src [Hsrc1 Hmatch1]].
      assert (Hbranch_match : match_ctx (ctx t++ Branch true) ctx);
      eauto with unskip_db.
Qed.

  Ltac solve_sim_step Hmatch ctx_src:=
  unfold match_ctx in Hmatch |- *;
  destruct Hmatch as [Hval Htrace];
  destruct ctx_src as [v_src t_src]; simpl in *;
  eexists; split;
  [ rewrite Hval; eauto with unskip_db
  | split; simpl; [ reflexivity | exact Htrace ] ].

(* Backward simulation: Executing the optimized program implies the source
      program could have executed to a matching state.  *)
Lemma opt_unskip_backward : forall c ctx_opt ctx_opt_final ctx_src,
  eval_trace ctx_opt (opt_unskip_cmd c) ctx_opt_final ->
  match_ctx ctx_src ctx_opt ->
  exists ctx_src_final, eval_trace ctx_src c ctx_src_final /\ match_ctx ctx_src_final ctx_opt_final.
Proof.
  induction c; intros ctx_opt ctx_opt_final ctx_src Hopt Hmatch; simpl in *.

  - (* Skip *) inversion Hopt; subst; eauto with unskip_db.
  - (* Assign *) inversion Hopt; subst. solve_sim_step Hmatch ctx_src.
  - (* Cmov *) inversion Hopt; subst; solve_sim_step Hmatch ctx_src.

  - (* Sequence *)
    (* We need 4 cases here because each subcommand may either optimize to Skip
      or not. The proof splits on the optimized forms of [c1] and [c2]:
      1. [Skip, Skip]: both commands disappear, so we use the completeness lemma
         for each side and build the source run directly.
      2. [Skip, non-Skip]: optimized is c2, so we first recover a matching
         source state after c1, then apply the IH to c2.
      3. [non-Skip, Skip]: symmetric to the previous case.
      4. [non-Skip, non-Skip]: both commands stay, the result is is the full
         sequence, so we invert the optimized sequence trace into two steps and
         apply the IH twice, once for each command. *)
    destruct (opt_unskip_cmd c1) eqn:Hc1;
    destruct (opt_unskip_cmd c2) eqn:Hc2;
    match goal with
    | Hc1 : opt_unskip_cmd c1 = Skip,
      Hc2 : opt_unskip_cmd c2 = Skip |- _ =>
        inversion Hopt; subst;
        destruct (opt_unskip_skip_trace_complete c1 ctx_src Hc1)
          as [ctx1_src [Hsrc1 Hmatch1]];
        destruct (opt_unskip_skip_trace_complete c2 ctx1_src Hc2)
          as [ctx2_src [Hsrc2 Hmatch2]];
        exists ctx2_src; eauto with unskip_db
    | Hc1 : opt_unskip_cmd c1 = Skip |- _ =>
        destruct (opt_unskip_skip_trace_complete c1 ctx_src Hc1)
          as [ctx1_src [Hsrc1 Hmatch1]];
        edestruct (IHc2 ctx_opt ctx_opt_final ctx1_src)
          as [ctx2_src [Hsrc2 Hmatch2]];
        [exact Hopt | eapply match_ctx_trans; eauto |];
        exists ctx2_src; eauto with unskip_db
    | Hc2 : opt_unskip_cmd c2 = Skip |- _ =>
        edestruct (IHc1 ctx_opt ctx_opt_final ctx_src)
          as [ctx1_src [Hsrc1 Hmatch1]];
        [exact Hopt | exact Hmatch |];
        destruct (opt_unskip_skip_trace_complete c2 ctx1_src Hc2)
          as [ctx2_src [Hsrc2 Hmatch2]];
        exists ctx2_src; split; eauto with unskip_db
    | _ =>
        inversion Hopt; subst; clear Hopt;
        match goal with
        | Hstep1 : eval_trace ctx_opt _ ?ctx1_opt,
          Hstep2 : eval_trace ?ctx1_opt _ ctx_opt_final |- _ =>
            edestruct (IHc1 ctx_opt ctx1_opt ctx_src)
              as [ctx1_src [Hsrc1 Hmatch1]];
            [exact Hstep1 | exact Hmatch |];
            edestruct (IHc2 ctx1_opt ctx_opt_final ctx1_src)
              as [ctx2_src [Hsrc2 Hmatch2]];
            [exact Hstep2 | exact Hmatch1 |];
            exists ctx2_src; split; eauto with unskip_db
        end
    end.

  - (* If *)
    (* We really have 2 cases:
      1. The conditional is preserved (48 cases) If the optimized command
         evaluated as an If statement (meaning at least one branch wasn't
         optimized down to a Skip), the optimized trace will contain a [Branch
         true] or [Branch false] event. The branch event is present in both the
         optimized and source traces: We determine which branch was taken,
         append it to the matching contexts, and call the IH.

      2. The conditional is dropped completely (1 case: Skip, Skip): the
         optimizer replaced the If cmd with a single Skip. Even though opt is
         just Skip, src still has an `If` statement, which means appends to the
         trace. To prove this is secure, we do two things:
        1. We use opt_unskip_skip_trace_complete to prove that running src's
           "useless" branch doesn't change the valuation.
        2. We use trace_subseq_append_drop as the traces don't match perfectly.
           The source trace has an extra branch event that opt dropped. *)

    unfold match_ctx in Hmatch; destruct Hmatch as [Hval Htrace].
    simpl in Hopt.
    destruct (opt_unskip_cmd c1) eqn:Hc1, (opt_unskip_cmd c2) eqn:Hc2;
    try (
      inversion Hopt; subst; clear Hopt;
      [ (* EvalTraceIfTrue *)
        assert (Hmatch_branch: match_ctx (ctx_src t++ Branch true) (ctx_opt t++ Branch true))
          by (split; simpl; [ exact Hval | apply trace_subseq_append_keep; exact Htrace ]);
        edestruct IHc1 as [ctx_fin [Hsrc1 Hmatch_fin]]; [ eassumption | exact Hmatch_branch | ];
        exists ctx_fin; split;
        [ eapply EvalTraceIfTrue with (c := interp_arith e (val_of ctx_opt));
          [ rewrite Hval; reflexivity | eassumption | exact Hsrc1 ]
        | exact Hmatch_fin ]
      | (* EvalTraceIfFalse *)
        assert (Hmatch_branch: match_ctx (ctx_src t++ Branch false) (ctx_opt t++ Branch false))
          by (split; simpl; [ exact Hval | apply trace_subseq_append_keep; exact Htrace ]);
        edestruct IHc2 as [ctx_fin [Hsrc2 Hmatch_fin]]; [ eassumption | exact Hmatch_branch | ];
        exists ctx_fin; split;
        [ eapply EvalTraceIfFalse;
          [ rewrite Hval; eassumption | exact Hsrc2 ]
        | exact Hmatch_fin ]
      ]
    ).

    (* Skip, Skip. *)
    inversion Hopt; subst; clear Hopt;
    destruct (interp_arith e (val_of ctx_src)) eqn:Heq;
    [ destruct (opt_unskip_skip_trace_complete c2 (ctx_src t++ Branch false) Hc2) as [ctx2_src [Hsrc2 Hmatch2]]
    | destruct (opt_unskip_skip_trace_complete c1 (ctx_src t++ Branch true) Hc1) as [ctx1_src [Hsrc1 Hmatch1]]];
    eexists; split; eauto with unskip_db.

  - (* While *)
    eapply opt_unskip_backward_while; eauto.
Qed.

Ltac kill_trace_contra Hstart Heq :=
  match goal with
  | H1 : eval_trace _ _ _, H2 : eval_trace _ _ _ |- _ =>
      destruct (eval_trace_prefix _ _ _ H1) as [diff1 Hdiff1];
      destruct (eval_trace_prefix _ _ _ H2) as [diff2 Hdiff2];
      simpl in *; rewrite Hdiff1, Hdiff2 in Heq;
      try rewrite Hstart in Heq;
      repeat rewrite <- app_assoc in Heq;
      apply branch_contradiction in Heq; discriminate Heq
  end.

(* Because traces only append, if two executions of `c` start with equal traces
   and end with traces that share a tail, their traces must have remained
   synchronized at every intermediate evaluation step. *)
Lemma eval_trace_sync : forall ctx1 c ctx1_out,
  eval_trace ctx1 c ctx1_out ->
  forall ctx2 ctx2_out tail1 tail2,
  eval_trace ctx2 c ctx2_out ->
  trace_of ctx1 = trace_of ctx2 ->
  trace_of ctx1_out ++ tail1 = trace_of ctx2_out ++ tail2 ->
  trace_of ctx1_out = trace_of ctx2_out.
Proof.
  intros ctx1 c ctx1_out Heval_1.
  induction Heval_1; intros ctxin_2 ctx2_out tail1 tail2 Heval_2 Hstart Heq;
  inversion Heval_2; subst; simpl in *;

  try solve [exact Hstart];
  try solve [kill_trace_contra Hstart Heq].

  - (* Sequence *)
    destruct (eval_trace_prefix _ _ _ Heval_1_2) as [diff1 Hdiff1].
    destruct (eval_trace_prefix _ _ _ H4) as [diff2 Hdiff2].
    assert (Hint_eq: trace_of ctx1 = trace_of ctx3).
    { eapply IHHeval_1_1; [exact H2 | exact Hstart | ].
      rewrite Hdiff1, Hdiff2 in Heq. do 2 rewrite <- app_assoc in Heq. exact Heq. }
    eapply IHHeval_1_2; [exact H4 | exact Hint_eq | exact Heq].

  - (* IfTrue / IfTrue *)
    eapply IHHeval_1; [exact H8 | rewrite Hstart; reflexivity | exact Heq].

  - (* IfFalse / IfFalse *)
    eapply IHHeval_1; [exact H6 | rewrite Hstart; reflexivity | exact Heq].

  - (* WhileTrue / WhileTrue *)
    destruct (eval_trace_prefix _ _ _ Heval_1_2) as [diff1 Hdiff1].
    destruct (eval_trace_prefix _ _ _ H8) as [diff2 Hdiff2].
    assert (Hint_eq: trace_of ctx' = trace_of ctx'0).
    { eapply IHHeval_1_1; [exact H6 | simpl; rewrite Hstart; reflexivity | ].
      rewrite Hdiff1, Hdiff2 in Heq. do 2 rewrite <- app_assoc in Heq. exact Heq. }
    eapply IHHeval_1_2; eauto.

  - (* WhileFalse / WhileFalse *)
    rewrite Hstart; reflexivity.
Qed.

Lemma eval_trace_sequence_inv : forall ctx c1 c2 ctx_out,
  eval_trace ctx (Sequence c1 c2) ctx_out ->
  exists ctx_mid,
    eval_trace ctx c1 ctx_mid /\
    eval_trace ctx_mid c2 ctx_out.
Proof.
  intros ctx c1 c2 ctx_out Heval.
  inversion Heval; subst; eauto.
Qed.

Ltac contradict_branch_traces Hstep1 Hstep2 Hstart Hout :=
  let tail1 := fresh "tail1" in let Htail1 := fresh "Htail1" in
  let tail2 := fresh "tail2" in let Htail2 := fresh "Htail2" in
  destruct (eval_trace_prefix _ _ _ Hstep1) as [tail1 Htail1];
  destruct (eval_trace_prefix _ _ _ Hstep2) as [tail2 Htail2];
  simpl in *; rewrite Htail1, Htail2 in Hout; rewrite Hstart in Hout;
  repeat rewrite <- app_assoc in Hout; apply branch_contradiction in Hout; discriminate Hout.

(** If both the source and optimized commands execute from matching contexts,
    their output contexts will also match. This essentially propagates the `match_ctx`
    invariant forward through execution steps. *)
Lemma opt_unskip_forward_match : forall c ctx ctx_out ctx_opt ctx_opt_out,
  eval_trace ctx c ctx_out ->
  eval_trace ctx_opt (opt_unskip_cmd c) ctx_opt_out ->
  match_ctx ctx ctx_opt ->
  match_ctx ctx_out ctx_opt_out.
Proof.
  intros c ctx ctx_out ctx_opt ctx_opt_out Hsrc Hopt Hmatch.
  destruct (opt_unskip_forward _ _ _ _ Hsrc Hmatch) as [ctx_fw [Hfw Hmatch_out]].
  replace ctx_opt_out with ctx_fw by (eapply eval_trace_deterministic; eauto).
  exact Hmatch_out.
Qed.

(* If two source executions agree on their output traces, then their optimized
   versions must also agree on their output traces. Proved by induction on the
   source trace execution, relying on `eval_trace_sync` to match intermediate
   traces *)
Lemma opt_traces_equal_gen : forall c ctx_src1 ctx_src2 ctx_opt1 ctx_opt2
    ctx_src1_out ctx_src2_out ctx_opt1_out ctx_opt2_out,
  eval_trace ctx_src1 c ctx_src1_out ->
  eval_trace ctx_src2 c ctx_src2_out ->
  eval_trace ctx_opt1 (opt_unskip_cmd c) ctx_opt1_out ->
  eval_trace ctx_opt2 (opt_unskip_cmd c) ctx_opt2_out ->
  match_ctx ctx_src1 ctx_opt1 ->
  match_ctx ctx_src2 ctx_opt2 ->
  trace_of ctx_src1 = trace_of ctx_src2 ->
  trace_of ctx_opt1 = trace_of ctx_opt2 ->
  trace_of ctx_src1_out = trace_of ctx_src2_out ->
  trace_of ctx_opt1_out = trace_of ctx_opt2_out.
Proof.
  intros c ctx_src1 ctx_src2 ctx_opt1 ctx_opt2
    ctx_src1_out ctx_src2_out ctx_opt1_out ctx_opt2_out Hsrc1.
  revert ctx_src2 ctx_opt1 ctx_opt2 ctx_src2_out ctx_opt1_out ctx_opt2_out.
  induction Hsrc1; intros ctx_src2 ctx_opt1 ctx_opt2
    ctx_src2_out ctx_opt1_out ctx_opt2_out
    Hsrc2 Hopt1 Hopt2 Hmatch1 Hmatch2 Hstart_src Hstart_opt Hout_src;
    simpl in Hopt1, Hopt2.
  (* No branching cmds: Starting traces matched trivially equal to final trace *)
  - (* Skip *) inversion Hopt1; inversion Hopt2; subst; auto.
  - (* Assign *) inversion Hopt1; inversion Hopt2; subst; auto.
  - (* CmovTrue *) inversion Hopt1; inversion Hopt2; subst; auto.
  - (* CmovFalse *) inversion Hopt1; inversion Hopt2; subst; auto.

  - (* Sequence *)

    (* src1 is c1 ;; c2. Force src2 into same c1 ;; c2 shape. Gives us
    intermediate ctx (`ctx2_mid`) to work with *)
    destruct (eval_trace_sequence_inv _ _ _ _ Hsrc2) as [ctx2_mid [Hsrc2_1 Hsrc2_2]].

    (* Prove that the intermediate traces are the same *)
    destruct (eval_trace_prefix _ _ _ Hsrc1_2) as [tail1 Htail1].
    destruct (eval_trace_prefix _ _ _ Hsrc2_2) as [tail2 Htail2].
    assert (Hsrc_mid : trace_of ctx1 = trace_of ctx2_mid).
    { eapply eval_trace_sync; eauto.
      rewrite Htail1, Htail2 in Hout_src; exact Hout_src. }

    (* Destruct optimized commands and solve all cases*)
    destruct (opt_unskip_cmd c1) eqn:Hc1; destruct (opt_unskip_cmd c2) eqn:Hc2;
    try (inversion Hopt1; subst; exact Hstart_opt);
    try (
      assert (Hmatch1_mid : match_ctx ctx1 ctx_opt1)
        by (eapply opt_unskip_forward_match; [exact Hsrc1_1 | rewrite Hc1; constructor | exact Hmatch1]);
      assert (Hmatch2_mid : match_ctx ctx2_mid ctx_opt2)
        by (eapply opt_unskip_forward_match; [exact Hsrc2_1 | rewrite Hc1; constructor | exact Hmatch2]);
      eapply IHHsrc1_2 with (ctx_src2 := ctx2_mid) (ctx_opt1 := ctx_opt1)(ctx_opt2 := ctx_opt2);
      eassumption );
    try (eapply IHHsrc1_1 with (ctx_src2 := ctx_src2) (ctx_opt1 := ctx_opt1) (ctx_opt2 := ctx_opt2);
      eassumption);
    try (
      destruct (eval_trace_sequence_inv _ _ _ _ Hopt1) as [ctx1_opt_mid [Hopt1_1 Hopt1_2]];
      destruct (eval_trace_sequence_inv _ _ _ _ Hopt2) as [ctx2_opt_mid [Hopt2_1 Hopt2_2]];
      assert (Hopt_mid : trace_of ctx1_opt_mid = trace_of ctx2_opt_mid)
        by (eapply IHHsrc1_1 with (ctx_src2 := ctx_src2) (ctx_opt1 := ctx_opt1) (ctx_opt2 := ctx_opt2);
      eassumption);
      assert (Hmatch1_mid : match_ctx ctx1 ctx1_opt_mid)
        by (eapply opt_unskip_forward_match; [exact Hsrc1_1 | rewrite Hc1; exact Hopt1_1 | exact Hmatch1]);
      assert (Hmatch2_mid : match_ctx ctx2_mid ctx2_opt_mid)
        by (eapply opt_unskip_forward_match; [exact Hsrc2_1 | rewrite Hc1; exact Hopt2_1 | exact Hmatch2]);
      eapply IHHsrc1_2 with (ctx_src2 := ctx2_mid) (ctx_opt1 := ctx1_opt_mid) (ctx_opt2 := ctx2_opt_mid);
      eassumption ).

  - (* IfTrue *)
    (* Append Branch true event to matching contexts *)
    assert (Hmatch1_branch : match_ctx (ctx t++ Branch true) (ctx_opt1 t++ Branch true)).
    { unfold match_ctx in *; destruct Hmatch1 as [Hval Htrace]; split; simpl;
      [exact Hval | apply trace_subseq_append_keep; exact Htrace]. }
    assert (Hmatch2_branch : match_ctx (ctx_src2 t++ Branch true) (ctx_opt2 t++ Branch true)).
    { unfold match_ctx in *; destruct Hmatch2 as [Hval Htrace]; split; simpl;
      [exact Hval | apply trace_subseq_append_keep; exact Htrace]. }
    assert (Hstart_src_branch : trace_of (ctx t++ Branch true) = trace_of (ctx_src2 t++ Branch
        true)).
    { simpl; rewrite Hstart_src; reflexivity. }
    assert (Hstart_opt_branch : trace_of (ctx_opt1 t++ Branch true) = trace_of (ctx_opt2 t++
        Branch true)).
    { simpl; rewrite Hstart_opt; reflexivity. }

    (* Contradict if src evaluated to Branch false *)
    dependent destruction Hsrc2; [| contradict_branch_traces Hsrc1 Hsrc2 Hstart_src Hout_src].

    (* Apply IH to the true branch *)
    destruct (opt_unskip_cmd thn) eqn:Hthn; destruct (opt_unskip_cmd els) eqn:Hels;
    unfold match_ctx in Hmatch1, Hmatch2; destruct Hmatch1 as [Hval1 _], Hmatch2 as [Hval2 _];
    inversion Hopt1; inversion Hopt2; subst;
    try (rewrite Hval1 in *; lia); try (rewrite Hval2 in *; lia);
    try exact Hstart_opt; eapply IHHsrc1; eauto.

  - (* IfFalse: similar to IfTrue but with 'Branch false' *)
    assert (Hmatch1_branch : match_ctx (ctx t++ Branch false) (ctx_opt1 t++ Branch false)).
    { unfold match_ctx in *; destruct Hmatch1 as [Hval Htrace]; split; simpl;
      [exact Hval | apply trace_subseq_append_keep; exact Htrace]. }
    assert (Hmatch2_branch : match_ctx (ctx_src2 t++ Branch false) (ctx_opt2 t++ Branch false)).
    { unfold match_ctx in *; destruct Hmatch2 as [Hval Htrace]; split; simpl;
      [exact Hval | apply trace_subseq_append_keep; exact Htrace]. }
    assert (Hstart_src_branch : trace_of (ctx t++ Branch false) = trace_of (ctx_src2 t++ Branch
        false)).
    { simpl; rewrite Hstart_src; reflexivity. }
    assert (Hstart_opt_branch : trace_of (ctx_opt1 t++ Branch false) = trace_of (ctx_opt2 t++
        Branch false)).
    { simpl; rewrite Hstart_opt; reflexivity. }
    dependent destruction Hsrc2; [contradict_branch_traces Hsrc1 Hsrc2 Hstart_src Hout_src |].
    destruct (opt_unskip_cmd thn) eqn:Hthn; destruct (opt_unskip_cmd els) eqn:Hels;
    unfold match_ctx in Hmatch1, Hmatch2; destruct Hmatch1 as [Hval1 _], Hmatch2 as [Hval2 _];
    inversion Hopt1; inversion Hopt2; subst;
    try (rewrite Hval1 in *; lia); try (rewrite Hval2 in *; lia);
    try exact Hstart_opt; eapply IHHsrc1; eauto.

  - (* WhileTrue *)
    (* Append Branch true event *)
    assert (Hmatch1_branch : match_ctx (ctx t++ Branch true) (ctx_opt1 t++ Branch true)).
    { unfold match_ctx in *; destruct Hmatch1 as [Hval Htrace]; split; simpl;
      [exact Hval | apply trace_subseq_append_keep; exact Htrace]. }
    assert (Hmatch2_branch : match_ctx (ctx_src2 t++ Branch true) (ctx_opt2 t++ Branch true)).
    { unfold match_ctx in *; destruct Hmatch2 as [Hval Htrace]; split; simpl;
      [exact Hval | apply trace_subseq_append_keep; exact Htrace]. }
    assert (Hstart_src_branch : trace_of (ctx t++ Branch true) = trace_of (ctx_src2 t++ Branch
        true)).
    { simpl; rewrite Hstart_src; reflexivity. }
    assert (Hstart_opt_branch : trace_of (ctx_opt1 t++ Branch true) = trace_of (ctx_opt2 t++
        Branch true)).
    { simpl; rewrite Hstart_opt; reflexivity. }

    (* Contradict if src evaluated to Branch false *)
    inversion Hsrc2; subst; clear Hsrc2;
    [| assert (Hsrc1_loop := EvalTraceSequence _ _ _ _ _ Hsrc1_1 Hsrc1_2);
       contradict_branch_traces Hsrc1_loop (EvalTraceSkip (ctx_src2 t++ Branch false))
                                Hstart_src Hout_src].
    unfold match_ctx in Hmatch1, Hmatch2; destruct Hmatch1 as [Hval1 _], Hmatch2 as [Hval2 _];
    inversion Hopt1; inversion Hopt2; subst;
    try (rewrite <- Hval1 in *; lia); try (rewrite <- Hval2 in *; lia).

    (* While true is a sequence of body + loop. Prove traces are same after body *)
    match goal with
    | Hsrc2_1 : eval_trace _ body ?ctx2_mid,
      Hsrc2_2 : eval_trace ?ctx2_mid _ _,
      Hopt1_1 : eval_trace _ _ ?ctxopt1_mid,
      Hopt1_2 : eval_trace ?ctxopt1_mid _ _,
      Hopt2_1 : eval_trace _ _ ?ctxopt2_mid,
      Hopt2_2 : eval_trace ?ctxopt2_mid _ _ |- _ =>
        destruct (eval_trace_prefix _ _ _ Hsrc1_2) as [tail1 Htail1];
        destruct (eval_trace_prefix _ _ _ Hsrc2_2) as [tail2 Htail2];
        assert (Hsrc_mid : trace_of ctx' = trace_of ctx2_mid)
          by (eapply eval_trace_sync;
              [exact Hsrc1_1 | exact Hsrc2_1 | exact Hstart_src_branch | ];
              rewrite Htail1, Htail2 in Hout_src; exact Hout_src);
        assert (Hmatch1_mid : match_ctx ctx' ctxopt1_mid)
          by (eapply opt_unskip_forward_match; eauto);
        assert (Hmatch2_mid : match_ctx ctx2_mid ctxopt2_mid)
          by (eapply opt_unskip_forward_match; eauto);
        assert (Hopt_mid : trace_of ctxopt1_mid = trace_of ctxopt2_mid)
          by (eapply IHHsrc1_1;
              [exact Hsrc2_1 | exact Hopt1_1 | exact Hopt2_1 | exact Hmatch1_branch |
               exact Hmatch2_branch | exact Hstart_src_branch | exact Hstart_opt_branch |
               exact Hsrc_mid]);
        eapply IHHsrc1_2;
        [exact Hsrc2_2 | exact Hopt1_2 | exact Hopt2_2 | exact Hmatch1_mid |
         exact Hmatch2_mid | exact Hsrc_mid | exact Hopt_mid | exact Hout_src]
    end.

  - (* WhileFalse *)
    inversion Hsrc2; subst; clear Hsrc2.
    + (* Contradiction if src2 stayed in the loop. *)
      match goal with
      | Hsrc2_1 : eval_trace (?ctx_src2 t++ Branch true) body ?ctx2_mid,
        Hsrc2_2 : eval_trace ?ctx2_mid (While e body) ctx_src2_out |- _ =>
          assert (Hsrc2_loop := EvalTraceSequence _ _ _ _ _ Hsrc2_1 Hsrc2_2);
          symmetry in Hstart_src, Hout_src;
          contradict_branch_traces Hsrc2_loop
            (EvalTraceSkip (ctx t++ Branch false)) Hstart_src Hout_src
      end.
    + (* Prove traces are equal, as they both appended Branch false *)
    unfold match_ctx in Hmatch1, Hmatch2;
      destruct Hmatch1 as [Hval1 _], Hmatch2 as [Hval2 _];
      inversion Hopt1; subst; clear Hopt1; try (rewrite <- Hval1 in *; lia);
      inversion Hopt2; subst; clear Hopt2; try (rewrite <- Hval2 in *; lia);
      simpl in *; rewrite Hstart_opt; reflexivity.
Qed.

(* Wrapper over `opt_traces_equal_gen` initializing the match contexts. *)
Lemma opt_traces_equal : forall c v1 v2 t_in final_v1 final_v2 trace1 trace2 src_final_v1
    src_final_v2 src_trace,
  eval_trace (v1, t_in) c (src_final_v1, src_trace) ->
  eval_trace (v2, t_in) c (src_final_v2, src_trace) ->
  eval_trace (v1, t_in) (opt_unskip_cmd c) (final_v1, trace1) ->
  eval_trace (v2, t_in) (opt_unskip_cmd c) (final_v2, trace2) ->
  trace1 = trace2.
Proof.
  intros c v1 v2 t_in final_v1 final_v2 trace1 trace2 src_final_v1 src_final_v2 src_trace
    Hsrc1 Hsrc2 Hopt1 Hopt2.
  pose proof (opt_traces_equal_gen c
    (v1, t_in) (v2, t_in)
    (v1, t_in) (v2, t_in)
    (src_final_v1, src_trace) (src_final_v2, src_trace)
    (final_v1, trace1) (final_v2, trace2)
    Hsrc1 Hsrc2 Hopt1 Hopt2) as Hgen.
  apply Hgen; clear Hgen.
  - unfold match_ctx. split; simpl; [reflexivity | apply trace_subseq_refl].
  - unfold match_ctx. split; simpl; [reflexivity | apply trace_subseq_refl].
  - reflexivity.
  - reflexivity.
  - reflexivity.
Qed.

(* Main theorem of non-interference preservation *)

(* [opt_unskip_preserves_secure_pgm] proves the non-interference half of
   [is_secure_opt]. [opt_unskip_backward] expands optimized executions into
   matching source executions; [opt_traces_equal] then transfers source trace
   equality to the optimized runs. *)
Lemma opt_unskip_preserves_secure_pgm : forall p secrets,
  is_secure_pgm p secrets ->
  is_secure_pgm (opt_unskip p secrets) secrets.
Proof.
  unfold is_secure_pgm, opt_unskip, opt_unskip_cmd.
  intros [c out] secrets [secrets' Hni].
  simpl in *.
  exists secrets'.
  unfold non_interference in *.
  intros v1 v2 t_in final_v1 final_v2 trace1 trace2 Hagree Hopt_eval1 Hopt_eval2.

  pose proof Hopt_eval1 as Hopt_eval1_copy.
  pose proof Hopt_eval2 as Hopt_eval2_copy.

  (* Apply opt_unskip_backward on Hopt_eval1 Hopt_eval2 tp prove that the
     original source program succesfully evaluates, giving us src_final_v1,
     src_trace1 src_final_v2 and src_trace2) *)
  apply opt_unskip_backward with (ctx_src := (v1, t_in)) in Hopt_eval1_copy; auto with unskip_db.
  destruct Hopt_eval1_copy as [[src_final_v1 src_trace1] [Hsrc_eval1 Hmatch_final1]].
  apply opt_unskip_backward with (ctx_src := (v2, t_in)) in Hopt_eval2_copy; auto with unskip_db.
  destruct Hopt_eval2_copy as [[src_final_v2 src_trace2] [Hsrc_eval2 Hmatch_final2]].

  (* v1 and v2 agree on public (Hagree). By the non-interference of the source
     program (Hni), we get that the traces are equal and that the public values
     are also equal *)
  pose proof (Hni v1 v2 t_in src_final_v1 src_final_v2 src_trace1 src_trace2 Hagree Hsrc_eval1
      Hsrc_eval2) as [Htrace_eq Hval_agree].
  split.
  - (* Optimized traces are equal: Feed all 4 executions to
       opt_traces_equal to get trace equality *)
  rewrite Htrace_eq in Hsrc_eval1.
    eapply opt_traces_equal with (src_trace := src_trace2)
                                 (src_final_v1 := src_final_v1)
                                 (src_final_v2 := src_final_v2); eauto.
  - (* Optimized final valuations agree on public variables: source final
       valuations agree. Backward simulation gives us that optimized final
       valuations are the same as final source valuations. *)
  unfold match_ctx in *.
    destruct Hmatch_final1 as [Hval1 Htrace1].
    destruct Hmatch_final2 as [Hval2 Htrace2].
    simpl in *.
    rewrite <- Hval1. rewrite <- Hval2. exact Hval_agree.
Qed.
