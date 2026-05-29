Require Import Map.
Require Import VarSets.
Require Import Language.Main.
Require Import Language.Analysis.
Require Import Language.Optimizations.Safe.DSE.
Require Import Proofs.safe_DSE.SecretPreservation.
Require Import Proofs.VarSetAgreement.
Require Import Proofs.EvalEquivalence.
Require Import Proofs.SecEnvSubtyping.


(* Two context coincide if they have the same trace and they agree on the output variables. *)
Record trace_coincide (out : var_set) (ctx_src ctx_opt : context) : Prop := {
  trace_coincide_trace : trace_of ctx_src = trace_of ctx_opt;
  trace_coincide_vals : agree_on out (val_of ctx_src) (val_of ctx_opt)
}.

(* eval_trace only updated var that occur in the command. *)
(* Variables not mentioned in the optimized command are unchanged,
   so public agreement for them follows from initial agreement. *)
Lemma eval_trace_frame : forall ctx c ctx',
    eval_trace ctx c ctx' ->
    forall x,  ~ VarSet.In x (vars_in_cmd c) -> (val_of ctx') $? x = (val_of ctx) $? x.
Proof.
    induction 1; simpl in *; intros.
    all: try (destruct (x ==v x0); [VarSetDecide.fsetdec | apply lookup_add_ne; congruence]).
    all: try (apply IHeval_trace; VarSetDecide.fsetdec).
    all: try (rewrite IHeval_trace2 by VarSetDecide.fsetdec;
      apply IHeval_trace1; VarSetDecide.fsetdec).
    all: reflexivity.
Qed.

(* Every traced execution of safe_dse_helper can be matched to an evaluation of the source program with
   the same trace and the same out *)
Lemma opt_safe_dse_helper_trace_complete : forall c out ctx ctx_opt secrets,
  eval_trace ctx (safe_dse_helper c out secrets) ctx_opt ->
  exists ctx_src,
    eval_trace ctx c ctx_src /\
    trace_coincide out ctx_src ctx_opt.
Proof.
  intros c out [v t] [v_opt t_opt] secrets Hopt.
  destruct (Eval_lift_sec v t (safe_dse_helper c out secrets) v_opt t_opt Hopt secrets)
    as [se_opt Hopt_sec].
  pose proof (safe_dse_helper_sec_complete c out secrets
    (v, secrets, t) (v_opt, se_opt, t_opt)
    (sec_env_sub_refl secrets) Hopt_sec) as Hcomplete.
  destruct Hcomplete as [ctx_src_sec [Hsrc_sec Hcoin_sec]].
  exists (sec_val_of ctx_src_sec, sec_trace_of ctx_src_sec).
  split.
  - exact (Eval_proj_sec (v, secrets, t) c ctx_src_sec Hsrc_sec).
  - destruct Hcoin_sec as [_ Htrace Hagree].
    constructor; simpl; exact Htrace || exact Hagree.
Qed.

Lemma opt_safe_dse_core_preserves_safe_pgm : forall p secrets,
    is_safe_pgm p secrets ->
    is_safe_pgm (opt_safe_dse_core p secrets) secrets.
Proof.
  unfold is_safe_pgm, opt_safe_dse_core in *.
  intros [c out] secrets [secrets' Hni].
  simpl in *.
  exists (VarSet.union secrets
    (vars_in_cmd (safe_dse_helper c (VarSet.union out (sec_post c secrets)) secrets))).
  unfold non_inference in *.
  intros v1 v2 t_in final_v1 final_v2 trace1 trace2 Hagree Hopt_eval1 Hopt_eval2.

  pose proof (opt_safe_dse_helper_trace_complete _ _ _ _ _ Hopt_eval1)
    as Htrace_complete1.
  pose proof (opt_safe_dse_helper_trace_complete _ _ _ _ _ Hopt_eval2)
    as Htrace_complete2.
  destruct Htrace_complete1 as [[v1_out trace1_out] [Heval1 Hcoin1]].
  destruct Hcoin1 as [Htrace1 Hagree1].
  destruct Htrace_complete2 as [[v2_out trace2_out] [Heval2 Hcoin2]].
  destruct Hcoin2 as [Htrace2 Hagree2].
  simpl in *.

  specialize (Hni v1 v2 t_in v1_out v2_out trace1_out trace2_out).
  specialize (Hni Hagree Heval1 Heval2).
  split.
  - destruct Hni as [Htrace_equal _].
    congruence.
  - unfold agree_on_public.
    intros x Hx.
    pose proof (eval_trace_frame _ _ _ Hopt_eval1 x) as Hframe1.
    pose proof (eval_trace_frame _ _ _ Hopt_eval2 x) as Hframe2.
    simpl in *.
    rewrite Hframe1.
    rewrite Hframe2.
    + apply Hagree.
      VarSetDecide.fsetdec.
    + VarSetDecide.fsetdec.
    + VarSetDecide.fsetdec.
Qed.
