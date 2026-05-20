Require Import Map.
Require Import VarSets.
Require Import Language.Syntax.
Require Import Language.Security.
Require Import Language.EvalContext.
From Stdlib Require Import Lia.
From Stdlib Require Import List.
Import ListNotations.

(** ** Semantics *)
(** For expressions, we'll use an interpreter to implement the following rules::

                 n1 = n2
              ------------
               ⟦n2⟧ᵥ = n1

       (x ↦ a) ∈ v         x ∉ v
      --------------     ----------
         ⟦x⟧ᵥ = a         ⟦x⟧ᵥ = 0

               ⟦e1⟧ᵥ = a1
               ⟦e2⟧ᵥ = a2
         a = interp_binop b a1 a2
      -----------------------------
          ⟦Binop b e1 e2⟧ᵥ = a
*)

Definition interp_binop (b: BinopName) (n1 n2: nat) :=
  match b with
  | LogAnd => Nat.land n1 n2
  | Eq => if (n1 =? n2) then 1 else 0
  | Plus => n1 + n2
  | Minus => n1 - n2
  | Times => n1 * n2
  | Divide => n1 / n2
  | ShiftLeft => Nat.shiftl n1 n2
  | ShiftRight => Nat.shiftr n1 n2
  | Modulo => Nat.modulo n1 n2
  end.

Fixpoint interp_arith (e: expr) (v: valuation) {struct e}: nat :=
  match e with
  | Const n => n
  | Var x => match v $? x with Some a => a | None => 0 end
  | Binop b e1 e2 => interp_binop b (interp_arith e1 v) (interp_arith e2 v)
  end.

(** For commands, we'll use an inductive [Prop] to define big-step semantics.
    This is an opportunity to show that compiler proofs can work with a variety
    of semantics styles, since we focused on small-step semantics in lecture.
    The rules for [Assign], [While], [If], and [Skip] are the same as usual; for
    example:

                    ⟦e⟧ᵥ = a
      ----------------------------------- EvalAssign
       (v, Assign x e) ↓ᵩ (v $+ (x, a))

       (c1, v) ↓ᵩ v'   (c2, v') ↓ᵩ v''
      ----------------------------------- EvalSequence
          (v, Sequence c1 c2) ↓ᵩ v''

    Notice the subscript φ: this indicates that we have an function_env of functions.
    This function_env of functions gives the body of each function, the names of its
    arguments, and the name of its return value.  For example, to say that the
    function "collatz" has body [CollatzBody], takes arguments "start" and "flight",
    and writes its result to "out", we would write::

        phi = $0 $+ ("collatz", (("start", "flight"), "out", CollatzBody))

    and to say that function "factorial" has body [FactBody], takes argument "n",
    and writes its result to "f", we might write the following (every function takes
    two parameters, so we use "" as the name of the second argument of "factorial").

        phi = $0 $+ ("factorial", (("n", ""), "f", FactBody))

    We need an additional rule [EvalAssignCall] for function calls:

               (f ↦ ((x1, x2), y, body)) ∈ φ
                  ⟦e1⟧ᵥ = a1    ⟦e2⟧ᵥ = a2
          (body, ($0 $+ (x1, a1) $+ (x2, a2))) ↓ᵩ v'
                        (y ↦ a) ∈ v'
       ------------------------------------------------
         (AssignCall x f e1 e2, v) ↓ᵩ (v $+ (x, a))

   A few notes:

   - This rule passes arguments by value: that is, the function's arguments are
     evaluated in the current valuation [v]: [⟦e⟧ᵥ = a].

   - The function function_env [phi] (represented as φ above) maps function names
     (strings) to function signatures and function bodies:
     [(f ↦ ((x1, x2), y, body)) ∈ φ].

   - Functions return their output in variables indicated by their signatures:
     [(y ↦ a) ∈ v1].

   - Functions do not have access to the contexts of their callers: [body] runs
     in a clean environment.

   Here is how it looks in Rocq: *)

Inductive eval (phi: function_env): context -> cmd -> context -> Prop :=
  | EvalSkip: forall ctx,
      eval phi ctx Skip ctx
  | EvalAssign: forall ctx x e a,
      interp_arith e (val_of ctx) = a ->
      eval phi ctx (Assign x e) (ctx v$+ (x, a))
  | EvalCmovTrue: forall ctx x cond e1 e2 c a1 a2,
      interp_arith cond (val_of ctx) = c ->
      c <> 0 ->
      interp_arith e1 (val_of ctx) = a1 ->
      (* We evaluate both branches of the Cmov, so that it takes the same time
      regardless of the condition.  The result is the same as the "then" branch,
      but the "else" branch is still evaluated to ensure constant-time. *)
      interp_arith e2 (val_of ctx) = a2 ->
      eval phi ctx (Cmov x cond e1 e2) (ctx v$+ (x, a1))
  | EvalCmovFalse: forall ctx x cond e1 e2 a1 a2,
      interp_arith cond (val_of ctx) = 0 ->
      (* Same as CmovTrue, but for the false branch *)
      interp_arith e1 (val_of ctx) = a1 ->
      interp_arith e2 (val_of ctx) = a2 ->
      eval phi ctx (Cmov x cond e1 e2) (ctx v$+ (x, a2))
  | EvalAssignCall: forall x f e1 e2 x1 x2 y body a1 a2 a ctx ctx',
    phi $? f = Some ((x1, x2), y, body) ->
    interp_arith e1 (val_of ctx) = a1 ->
    interp_arith e2 (val_of ctx) = a2 ->
    (*reset the environmnet, but keep the trace. we could also simply append it after*)
    eval phi (($0 $+ (x1, a1) $+ (x2, a2)), trace_of ctx) body ctx' ->
    val_of ctx' $? y = Some a ->
    eval phi ctx (AssignCall x f e1 e2) (val_of ctx $+ (x, a), trace_of ctx')
  | EvalSequence: forall ctx c1 ctx1 c2 ctx2,
      eval phi ctx c1 ctx1 ->
      eval phi ctx1 c2 ctx2 ->
      eval phi ctx (Sequence c1 c2) ctx2
  | EvalIfTrue: forall ctx e thn els ctx' c,
      interp_arith e (val_of ctx) = c ->
      c <> 0 ->
      eval phi (ctx t++ Branch true) thn ctx' ->
      eval phi ctx (If e thn els) ctx'
  | EvalIfFalse: forall ctx e thn els ctx',
      interp_arith e (val_of ctx) = 0 ->
      eval phi (ctx t++ Branch false) els ctx' ->
      eval phi ctx (If e thn els) ctx'
  | EvalWhileTrue: forall ctx e body ctx' ctx'' c,
      interp_arith e (val_of ctx) = c ->
      c <> 0 ->
      eval phi (ctx t++ Branch true) body ctx' ->
      eval phi ctx' (While e body) ctx'' ->
      eval phi ctx (While e body) ctx''
  | EvalWhileFalse: forall ctx e body,
      interp_arith e (val_of ctx) = 0 ->
      eval phi ctx (While e body) (ctx t++ Branch false).


(* The evaluation relation is deterministic: if a command can evaluate to two
different contexts, those contexts must be the same. *)
Theorem eval_deterministic : forall phi c ctx ctx1 ctx2,
  eval phi ctx c ctx1 ->
  eval phi ctx c ctx2 ->
  ctx1 = ctx2.
Proof.
    Ltac invert_eval :=
    match goal with
    | H : eval _ _ _ _ |- _ => inversion H; subst; clear H
    end.

  intros phi c ctx ctx1 ctx2 Heval1.
  revert ctx2.
  induction Heval1; intros ? Heval2.
  - (* Skip *)
    invert_eval. auto.
  - (* Assign *)
    invert_eval. auto.
  - (* CmovTrue *)
    invert_eval.
    + auto.
    + lia.
  - (* CmovFalse *)
    invert_eval.
    + lia.
    + auto.
  - (* AssignCall *)
    invert_eval.
    rewrite H in H7. inversion H7. subst.
    apply IHHeval1 in H12. subst.
    rewrite H2 in H13. inversion H13. auto.
  - (* Sequence *)
    invert_eval.
    apply IHHeval1_1 in H2. subst.
    apply IHHeval1_2 in H4. auto.
  - (* IfTrue *)
    invert_eval.
    + apply IHHeval1 in H8. assumption.
    + lia.
  - (* IfFalse *)
    invert_eval.
    + lia.
    + apply IHHeval1 in H6. assumption.
  - (* WhileTrue *)
    invert_eval.
    + apply IHHeval1_1 in H6. subst.
      apply IHHeval1_2 in H8. assumption.
    + lia.
  - (* WhileFalse *)
    invert_eval.
    + lia.
    + reflexivity.
Qed.


(*
   Augment the eval relation to also track security levels.
   The new rules are detailed below.


   [EvalSecAssign]
   adds the premise
    [interp_sec e (sec_of ctx) = level]
   and updates both the valuation and the security environment,
   so the assigned variable receives both its value and its computed security label.

   [EvalSecAssignCall]
   adds security-level evaluation premises for the two arguments,
    [interp_sec e1 (sec_of ctx) = level1] and
    [interp_sec e2 (sec_of ctx) = level2].
   The callee then runs in a fresh security environment initialized
   with those argument labels.
   The caller additionally requires
    [sec_lookup (sec_of ctx') y = level]
   so that the return variable's security label can
   be propagated back to the assignee.
 *)


Inductive eval_sec (phi : function_env) : sec_context -> cmd -> sec_context -> Prop :=
  | EvalSecSkip : forall ctx,
      eval_sec phi ctx Skip ctx
  | EvalSecAssign : forall ctx x e a level ,
      interp_arith e (sec_val_of ctx) = a ->
      interp_sec e (sec_of ctx) = level ->
      eval_sec phi ctx (Assign x e) ((ctx sv$+ (x, a)) s$+ (x, level))
  | EvalSecCmovTrue : forall ctx x cond e1 e2 c a1 a2 level,
      interp_arith cond (sec_val_of ctx) = c ->
      c <> 0 ->
      interp_arith e1 (sec_val_of ctx) = a1 ->
      interp_arith e2 (sec_val_of ctx) = a2 ->
      join_sec (interp_sec cond (sec_of ctx)) (join_sec (interp_sec e1 (sec_of ctx)) (interp_sec e2 (sec_of ctx))) = level ->
      eval_sec phi ctx (Cmov x cond e1 e2) ((ctx sv$+ (x, a1)) s$+ (x, level))
  | EvalSecCmovFalse : forall ctx x cond e1 e2 a1 a2 level,
      interp_arith cond (sec_val_of ctx) = 0 ->
      interp_arith e1 (sec_val_of ctx) = a1 ->
      interp_arith e2 (sec_val_of ctx) = a2 ->
      join_sec (interp_sec cond (sec_of ctx)) (join_sec (interp_sec e1 (sec_of ctx)) (interp_sec e2 (sec_of ctx))) = level ->
      eval_sec phi ctx (Cmov x cond e1 e2) ((ctx sv$+ (x, a2)) s$+ (x, level))
  | EvalSecAssignCall : forall x f e1 e2 x1 x2 y body a1 a2 level1 level2 ctx ctx' a level,
      phi $? f = Some ((x1, x2), y, body) ->
      interp_arith e1 (sec_val_of ctx) = a1 ->
      interp_arith e2 (sec_val_of ctx) = a2 ->
      interp_sec e1 (sec_of ctx) = level1 ->
      interp_sec e2 (sec_of ctx) = level2 ->
      eval_sec phi (($0 $+ (x1, a1) $+ (x2, a2)), senv_mk2 x1 x2 level1 level2, sec_trace_of ctx) body ctx' ->
      sec_val_of ctx' $? y = Some a ->
      sec_lookup (sec_of ctx') y = level ->
      eval_sec phi ctx (AssignCall x f e1 e2) ((sec_val_of ctx $+ (x, a)), update_sec (sec_of ctx) x level, sec_trace_of ctx')
  | EvalSecSequence : forall ctx c1 ctx1 c2 ctx2,
      eval_sec phi ctx c1 ctx1 ->
      eval_sec phi ctx1 c2 ctx2 ->
      eval_sec phi ctx (Sequence c1 c2) ctx2
  | EvalSecIfTrue : forall ctx e thn els ctx' c,
      interp_arith e (sec_val_of ctx) = c ->
      c <> 0 ->
      eval_sec phi (ctx st++ Branch true) thn ctx' ->
      eval_sec phi ctx (If e thn els) ctx'
  | EvalSecIfFalse : forall ctx e thn els ctx',
      interp_arith e (sec_val_of ctx) = 0 ->
      eval_sec phi (ctx st++ Branch false) els ctx' ->
      eval_sec phi ctx (If e thn els) ctx'
  | EvalSecWhileTrue : forall ctx e body ctx' ctx'' c,
      interp_arith e (sec_val_of ctx) = c ->
      c <> 0 ->
      eval_sec phi (ctx st++ Branch true) body ctx' ->
      eval_sec phi ctx' (While e body) ctx'' ->
      eval_sec phi ctx (While e body) ctx''
  | EvalSecWhileFalse : forall ctx e body,
      interp_arith e (sec_val_of ctx) = 0 ->
      eval_sec phi ctx (While e body) (ctx st++ Branch false).

(* The evaluation relation is deterministic: if a command can evaluate to two
different contexts, those contexts must be the same. *)

(* A small inversion helper: it looks at the command in the goal first, then
inverts the matching evaluation hypothesis.  That makes the proof script read
like a case split on the command, not like a search through generated names. *)

Theorem eval_sec_deterministic : forall phi c ctx ctx1 ctx2,
  eval_sec phi ctx c ctx1 ->
  eval_sec phi ctx c ctx2 ->
  ctx1 = ctx2.
Proof.
  Ltac invert_eval_sec :=
    match goal with
    | H : eval_sec _ _ _ _ |- _ => inversion H; subst; clear H
    end.

  intros phi c ctx ctx1 ctx2 Heval1.
  revert ctx2.
  induction Heval1; intros ? Heval2.
  - (* Skip *)
    invert_eval_sec. auto.
  - (* Assign *)
    invert_eval_sec. auto.
  - (* CmovTrue *)
    invert_eval_sec.
    + auto.
    + lia.
  - (* CmovFalse *)
    invert_eval_sec.
    + lia.
    + auto.
  - (* AssignCall *)
    invert_eval_sec.
    rewrite H in H10. inversion H10. subst.
    apply IHHeval1 in H17. subst.
    rewrite H4 in H18. inversion H18. subst. auto.
  - (* Sequence *)
    invert_eval_sec.
    apply IHHeval1_1 in H2. subst.
    apply IHHeval1_2 in H4. auto.
  - (* IfTrue *)
    invert_eval_sec.
    + apply IHHeval1 in H8. assumption.
    + lia.
  - (* IfFalse *)
    invert_eval_sec.
    + lia.
    + apply IHHeval1 in H6. assumption.
  - (* WhileTrue *)
    invert_eval_sec.
    + apply IHHeval1_1 in H6. subst.
      apply IHHeval1_2 in H8. assumption.
    + lia.
  - (* WhileFalse *)
    invert_eval_sec.
    + lia.
    + reflexivity.
Qed.
