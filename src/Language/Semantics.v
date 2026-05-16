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
      ----------------------------------- EvalTraceAssign
       (v, Assign x e) ↓ᵩ (v $+ (x, a))

       (c1, v) ↓ᵩ v'   (c2, v') ↓ᵩ v''
      ----------------------------------- EvalTraceSequence
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

    We need an additional rule [EvalTraceAssignCall] for function calls:

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



Inductive eval (phi: function_env): valuation -> cmd -> valuation -> Prop :=
  | EvalSkip: forall v,
      eval phi v Skip v
  | EvalAssign: forall v x e a,
      interp_arith e v = a ->
      eval phi v (Assign x e) (v $+ (x, a))
  | EvalAssignCall: forall x f e1 e2 x1 x2 y body a1 a2 a v v',
    phi $? f = Some ((x1, x2), y, body) ->
    interp_arith e1 v = a1 ->
    interp_arith e2 v = a2 ->
    eval phi ($0 $+ (x1, a1) $+ (x2, a2)) body v' ->
    v' $? y = Some a ->
    eval phi v (AssignCall x f e1 e2) (v $+ (x, a))
  | EvalSequence: forall v c1 v1 c2 v2,
      eval phi v c1 v1 ->
      eval phi v1 c2 v2 ->
      eval phi v (Sequence c1 c2) v2
  | EvalIfTrue: forall v e thn els v' c,
      interp_arith e v = c ->
      c <> 0 ->
      eval phi v thn v' ->
      eval phi v (If e thn els) v'
  | EvalIfFalse: forall v e thn els v',
      interp_arith e v = 0 ->
      eval phi v els v' ->
      eval phi v (If e thn els) v'
  | EvalWhileTrue: forall v e body v' v'' c,
      interp_arith e v = c ->
      c <> 0 ->
      eval phi v body v' ->
      eval phi v' (While e body) v'' ->
      eval phi v (While e body) v''
  | EvalWhileFalse: forall v e body,
      interp_arith e v = 0 ->
      eval phi v (While e body) v.


Theorem eval_deterministic :
    forall phi c v0 v1 v2,
      eval phi v0 c v1 ->
      eval phi v0 c v2 ->
      v1 = v2.
  Proof.
    intros phi c v0 v1 v2 H.
    revert v2.
    induction H; simpl; intros.
    - inversion H. reflexivity.
    - inversion H0; subst;
    reflexivity.
    - inversion H4; subst.
      rewrite H in H9. injection H9; intros; subst.
      apply IHeval in H14. subst.
      congruence.
    - inversion H1; subst.
      apply IHeval1 in H5.
      subst.
      firstorder.
    - inversion H2; subst; firstorder.
    - inversion H1; subst; firstorder.
    - inversion H3; subst.
      + apply IHeval1 in H9.
        subst.
        apply IHeval2 in H11.
        assumption.
      + congruence.
    - inversion H0; subst; firstorder.
Qed.



Inductive eval_trace (phi: function_env): context -> cmd -> context -> Prop :=
  | EvalTraceSkip: forall ctx,
      eval_trace phi ctx Skip ctx
  | EvalTraceAssign: forall ctx x e a,
      interp_arith e (val_of ctx) = a ->
      eval_trace phi ctx (Assign x e) (ctx v$+ (x, a))
  | EvalTraceAssignCall: forall x f e1 e2 x1 x2 y body a1 a2 a ctx ctx',
    phi $? f = Some ((x1, x2), y, body) ->
    interp_arith e1 (val_of ctx) = a1 ->
    interp_arith e2 (val_of ctx) = a2 ->
    (*reset the environmnet, but keep the trace. we could also simply append it after*)
    eval_trace phi (($0 $+ (x1, a1) $+ (x2, a2)), trace_of ctx) body ctx' ->
    val_of ctx' $? y = Some a ->
    eval_trace phi ctx (AssignCall x f e1 e2) (val_of ctx $+ (x, a), trace_of ctx')
  | EvalTraceSequence: forall ctx c1 ctx1 c2 ctx2,
      eval_trace phi ctx c1 ctx1 ->
      eval_trace phi ctx1 c2 ctx2 ->
      eval_trace phi ctx (Sequence c1 c2) ctx2
  | EvalTraceIfTrue: forall ctx e thn els ctx' c,
      interp_arith e (val_of ctx) = c ->
      c <> 0 ->
      eval_trace phi (ctx t++ Branch true) thn ctx' ->
      eval_trace phi ctx (If e thn els) ctx'
  | EvalTraceIfFalse: forall ctx e thn els ctx',
      interp_arith e (val_of ctx) = 0 ->
      eval_trace phi (ctx t++ Branch false) els ctx' ->
      eval_trace phi ctx (If e thn els) ctx'
  | EvalTraceWhileTrue: forall ctx e body ctx' ctx'' c,
      interp_arith e (val_of ctx) = c ->
      c <> 0 ->
      eval_trace phi (ctx t++ Branch true) body ctx' ->
      eval_trace phi ctx' (While e body) ctx'' ->
      eval_trace phi ctx (While e body) ctx''
  | EvalTraceWhileFalse: forall ctx e body,
      interp_arith e (val_of ctx) = 0 ->
      eval_trace phi ctx (While e body) (ctx t++ Branch false).


(* The evaluation relation is deterministic: if a command can evaluate to two
different contexts, those contexts must be the same. *)
Theorem eval_trace_deterministic : forall phi c ctx ctx1 ctx2,
  eval_trace phi ctx c ctx1 ->
  eval_trace phi ctx c ctx2 ->
  ctx1 = ctx2.
Proof.
    Ltac invert_eval :=
    match goal with
    | H : eval_trace _ _ _ _ |- _ => inversion H; subst; clear H
    end.

  intros phi c ctx ctx1 ctx2 Heval1.
  revert ctx2.
  induction Heval1; intros ? Heval2.
  - (* Skip *)
    invert_eval. auto.
  - (* Assign *)
    invert_eval. auto.
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
      eval_sec phi ctx (Assign x e) ((ctx sv$+ (x, a)) s$+ (x,level))
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
