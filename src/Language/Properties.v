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

Definition agree_on_secret (se : sec_env) (v1 v2 : valuation) : Prop :=
  forall x, sec_lookup se x = Secret -> v1 $? x = v2 $? x.

(* Another way is to say that two valuations are low-equivalent, meaning they agree on all public variables *)
Definition low_equiv := agree_on_public.


(* Constant-time semantics.

   Unlike [eval] and [eval_sec], this relation does not execute a command to a
   final valuation.  Instead, it checks whether the command is well-labeled with
   respect to constant-time discipline, threading only a security environment.

   The structural rules [CtSkip] and [CtSequence] mirror the corresponding rules
   in the evaluation relations, but over [sec_env] instead of execution contexts.

   [CtAssign] updates the assigned variable with the label computed by
   [interp_sec], recording how information may flow through the assignment.

   [CtAssignCall] mirrors function-call structure, but initializes the callee
   with the argument labels rather than argument values, checks the callee body
   under those labels, and propagates the return variable's label back to the
   caller via [sec_lookup body_se y].

   The new constant-time condition appears in [CtIf]: the guard must satisfy
   [interp_sec e se = Public], ensuring that branching does not depend on secret
   data.  Both branches are checked, and their resulting environments are joined
   with [join_sec_env].

   [CtWhile] similarly requires the loop guard to be public, but also adds the
   invariant premise [join_sec_env se se_inv = se_inv].  This ensures that the
   loop body is checked in a security environment stable enough to soundly model
   any number of iterations.
 *)
Inductive ct_cmd (phi : function_env) : sec_env -> cmd -> sec_env -> Prop :=
  | CtSkip : forall se,
      ct_cmd phi se Skip se
  | CtAssign : forall se x e level,
      interp_sec e se = level ->
      ct_cmd phi se (Assign x e) (update_sec se x level)
  | CtCmov : forall se x cond e1 e2 level,
      (* We allow conditioning on secret values, because no *)
      join_sec (interp_sec cond se) (join_sec (interp_sec e1 se) (interp_sec e2 se)) = level ->
      ct_cmd phi se (Cmov x cond e1 e2) (update_sec se x level)
  | CtAssignCall : forall se x f e1 e2 x1 x2 y body body_se level1 level2 level,
      phi $? f = Some ((x1, x2), y, body) ->
      interp_sec e1 se = level1 ->
      interp_sec e2 se = level2 ->
      ct_cmd phi
        (senv_mk2 x1 x2 level1 level2)
        body
        body_se ->
      sec_lookup body_se y = level ->
      ct_cmd phi se (AssignCall x f e1 e2) (update_sec se x level)
  | CtSequence : forall se c1 se1 c2 se2,
      ct_cmd phi se c1 se1 ->
      ct_cmd phi se1 c2 se2 ->
      ct_cmd phi se (Sequence c1 c2) se2
  | CtIf : forall se e thn els se_thn se_els se_join,
      interp_sec e se = Public ->
      ct_cmd phi se thn se_thn ->
      ct_cmd phi se els se_els ->
      VarSet.Equal (join_sec_env se_thn se_els) se_join ->
      ct_cmd phi se (If e thn els) (se_join)
  | CtWhile : forall se se_inv se_body e body,
      (* Ensures the invariant covers all starting secrets. *)
      VarSet.Equal (join_sec_env se se_inv) se_inv ->
      (* The loop condition must evaluate to Public under the invariant. *)
      interp_sec e se_inv = Public ->
      (* The body executes under the assumptions of the invariant. *)
      ct_cmd phi se_inv body se_body ->
      (* Guarantees the body cannot mutate a variable into a Secret if the
      invariant expected it to be Public. *)
      VarSet.Equal (join_sec_env se_inv se_body) se_inv ->
      ct_cmd phi se (While e body) se_inv.



(* If two valuations agree on public data, then running the same program on them
should produce the same trace.
Note 1: The initial trace has to be nonempty. This is necessary to prove the
sequence case, as the second statement won't always start with an empty trace.
Note 2: Also for the sequence proof, we have to strengthen the definition by
saying that the resulting context agrees on public variables, as in the sequence
case, the second statement doesn't start with the same context.
In both cases, we only strengthen the definition, so it is not a problem.
 *)
Definition non_inference (phi: function_env) (se: sec_env) (c: cmd) (se_out: sec_env) : Prop :=
  forall v1 v2 t_in final_v1 final_v2 trace1 trace2,
    agree_on_public se v1 v2 ->
    eval_trace phi (v1, t_in) c (final_v1, trace1) ->
    eval_trace phi (v2, t_in) c (final_v2, trace2) ->
    trace1 = trace2 /\ agree_on_public se_out final_v1 final_v2.



(* trace is independent of secrets *)
Definition is_safe_pgm (phi: function_env) (pgm: program) (secrets: sec_env): Prop :=
  exists secrets',
    non_inference phi secrets (cmd_of pgm) secrets'.


(* A safe optimization does not change the values and sec_level of secrets*)

  (* if both programs start with the same context (valuation+secrets),
      1. the resulting set of secrets are the same (secrets propagated correctly)
      2. AND both valuation agree on the value of secrets (all secure assigns are kept)
  *)
Definition opt_keeps_secrets_secret (opt : program -> program) : Prop :=
  forall sctx sctx' sctx'' pgm pgm' phi,
    opt pgm = pgm' ->
    eval_sec phi sctx (cmd_of pgm) sctx' ->
    eval_sec phi sctx (cmd_of pgm') sctx'' ->
    forall x, sec_lookup (sec_of sctx') x = sec_lookup (sec_of sctx'') x /\
    agree_on_secret (sec_of sctx') (sec_val_of sctx') (sec_val_of sctx'').



    (*A safe optimization:
      1. transform a safe program into another safe program
      2. doesn't change the value or sec_level of secrets, compared to the source program.
    *)
  Definition is_safe_opt (phi: function_env) (opt: program -> program): Prop :=
    (forall (p: program) (secrets: sec_env) ,
      is_safe_pgm phi p secrets -> is_safe_pgm phi (opt p) secrets) /\
      opt_keeps_secrets_secret opt.
