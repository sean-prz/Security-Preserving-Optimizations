Require Import Map.
Require Import VarSets.
Require Import Language.Syntax.
Require Import Language.Security.
Require Import Language.EvalContext.
Require Import Language.Semantics.
Require Import Language.Analysis.
From Stdlib Require Import List.
Import ListNotations.

(*2 programs agree on public variables, with potentially different secrets *)
Definition agree_on_public (secrets : var_set) (v1 v2 : valuation) : Prop :=
  forall x, not (VarSet.In x secrets) -> v1 $? x = v2 $? x.

(* All secrets in sec_env have the same value *)
Definition agree_on_secret (se : sec_env) (v1 v2 : valuation) : Prop :=
  forall x, sec_lookup se x = Secret -> v1 $? x = v2 $? x.

Lemma agree_on_secret_trans : forall se v1 v2 v3,
  agree_on_secret se v1 v2 ->
  agree_on_secret se v2 v3 ->
  agree_on_secret se v1 v3.
Proof.
  unfold agree_on_secret.
  intros se v1 v2 v3 Hagree12 Hagree23 x Hsecret.
  rewrite (Hagree12 x Hsecret).
  apply Hagree23.
  exact Hsecret.
Qed.

(* Constant-time semantics.

   Unlike [eval], [eval_trace] and [eval_sec], this relation does not execute a command to a
   final valuation.  Instead, it checks statically whether the command is well-labeled with
   respect to constant-time discipline, carrying only a security environment.

   ct_cmd propagates security levels of each variable, and ensure that no branching is done on secrets (except using cmov). Otherwise, side channel attacks could be performed, by comparing the execution time between different secrets.

  CtWhile: security levels under a while loop could take time to stabilize. We must make sure that secrecy is propagated correctly, no matter the amount of loop iterations.
 *)
Inductive ct_cmd : sec_env -> cmd -> sec_env -> Prop :=
  | CtSkip : forall se,
      ct_cmd se Skip se
  | CtAssign : forall se x e level,
      interp_sec e se = level ->
      ct_cmd se (Assign x e) (update_sec se x level)
  | CtCmov : forall se x cond e1 e2 level,
      (* We allow conditioning on secret values, because no *)
      join_sec (interp_sec cond se) (join_sec (interp_sec e1 se) (interp_sec e2 se)) = level ->
      ct_cmd se (Cmov x cond e1 e2) (update_sec se x level)
  | CtSequence : forall se c1 se1 c2 se2,
      ct_cmd se c1 se1 ->
      ct_cmd se1 c2 se2 ->
      ct_cmd se (Sequence c1 c2) se2
  | CtIf : forall se e thn els se_thn se_els se_join,
      interp_sec e se = Public ->
      ct_cmd se thn se_thn ->
      ct_cmd se els se_els ->
      VarSet.Equal (join_sec_env se_thn se_els) se_join ->
      ct_cmd se (If e thn els) (se_join)
  | CtWhile : forall se se_inv se_body e body,
      (* Ensures the invariant covers all starting secrets. *)
      VarSet.Equal (join_sec_env se se_inv) se_inv ->
      (* The loop condition must evaluate to Public under the invariant. *)
      interp_sec e se_inv = Public ->
      (* The body executes under the assumptions of the invariant. *)
      ct_cmd se_inv body se_body ->
      (* Guarantees the body cannot mutate a variable into a Secret if the
      invariant expected it to be Public. *)
      VarSet.Equal (join_sec_env se_inv se_body) se_inv ->
      ct_cmd se (While e body) se_inv.



(* If two valuations agree on public data, then running the same program on them
should produce the same trace.
 *)
Definition non_interference (se: sec_env) (c: cmd) (se_out: sec_env) : Prop :=
  forall v1 v2 t_in final_v1 final_v2 trace1 trace2,
    agree_on_public se v1 v2 ->
    eval_trace (v1, t_in) c (final_v1, trace1) ->
    eval_trace (v2, t_in) c (final_v2, trace2) ->
    trace1 = trace2 /\ agree_on_public se_out final_v1 final_v2.



(* A secure program is defined as a non-interferent program *)
Definition is_secure_pgm (pgm: program) (secrets: sec_env): Prop :=
  exists secrets',
    non_interference secrets (cmd_of pgm) secrets'.


(* A secure optimization does not change the values and sec_level of secrets*)

  (* if both programs start with the same context (valuation+secrets),
      1. the resulting set of secrets are the same (secrets propagated correctly)
      AND
      2. both valuation agree on the value of secrets (secure assigns are kept)
  *)
Definition opt_keeps_secrets_secret (opt : program -> sec_env -> program) : Prop :=
  forall sctx sctx' sctx'' pgm pgm',
    opt pgm (sec_of sctx) = pgm' ->
    eval_sec sctx (cmd_of pgm) sctx' ->
    eval_sec sctx (cmd_of pgm') sctx'' ->
    forall x, sec_lookup (sec_of sctx') x = sec_lookup (sec_of sctx'') x /\
    agree_on_secret (sec_of sctx') (sec_val_of sctx') (sec_val_of sctx'').

(* Optimized program can evaluate if original program can. *)
Definition opt_eval_sec_sound (opt : program -> sec_env -> program) : Prop :=
  forall sctx sctx' pgm,
    eval_sec sctx (cmd_of pgm) sctx' ->
    exists sctx_opt,
      eval_sec sctx (cmd_of (opt pgm (sec_of sctx))) sctx_opt.


(* Composing optimizations to create a new optimization *)
Definition compose_opt
    (opt2 opt1 : program -> sec_env -> program)
    (pgm : program)
    (secrets : sec_env) : program :=
  opt2 (opt1 pgm secrets) secrets.


(*We define a secure optimization as an opt. that:
  1. transforms a secure program into another secure program
  2. doesn't change the value or sec_level of secrets, compared to the source program.
*)
Definition is_secure_opt (opt: program -> sec_env -> program): Prop :=
  (forall (p: program) (secrets: sec_env) ,
    is_secure_pgm p secrets -> is_secure_pgm (opt p secrets) secrets) /\
    opt_keeps_secrets_secret opt.

(* A composition of secure optimization is a secure optimization.*)
Theorem is_secure_opt_compose : forall opt1 opt2,
  is_secure_opt opt1 ->
  is_secure_opt opt2 ->
  opt_eval_sec_sound opt1 ->
  is_secure_opt (compose_opt opt2 opt1).
Proof.
  intros opt1 opt2 [Hsecure_pgm1 Hkeep1] [Hsecure_pgm2 Hkeep2] Hsound1.
  unfold is_secure_opt.
  split.
  - intros p secrets Hsecure.
    apply Hsecure_pgm2.
    apply Hsecure_pgm1.
    exact Hsecure.
  - unfold opt_keeps_secrets_secret, compose_opt in *.
    intros sctx sctx' sctx'' pgm pgm'' Hopt Hsrc Hopt_eval x.
    destruct (Hsound1 sctx sctx' pgm Hsrc) as [sctx_mid Hmid_eval].
    pose proof (Hkeep1 sctx sctx' sctx_mid pgm (opt1 pgm (sec_of sctx))
      eq_refl Hsrc Hmid_eval x) as Hmid.
    pose proof (Hkeep2 sctx sctx_mid sctx'' (opt1 pgm (sec_of sctx)) pgm''
      Hopt Hmid_eval Hopt_eval x) as Hfinal.
    destruct Hmid as [Hsec_mid Hagree_mid].
    destruct Hfinal as [Hsec_final Hagree_final].
    split.
    + rewrite Hsec_mid.
      exact Hsec_final.
    + eapply agree_on_secret_trans.
      * exact Hagree_mid.
      * unfold agree_on_secret.
        intros y Hsecret.
        apply Hagree_final.
        pose proof (Hkeep1 sctx sctx' sctx_mid pgm (opt1 pgm (sec_of sctx))
          eq_refl Hsrc Hmid_eval y) as Hy_mid.
        destruct Hy_mid as [Hsec_mid_y _].
        rewrite <- Hsec_mid_y.
        exact Hsecret.
Qed.
