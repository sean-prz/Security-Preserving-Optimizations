Require Import Map.
Require Import Language.Main.
Require Import Examples.Programs.
From Stdlib Require Import List.
Import ListNotations.
From Stdlib Require Import Lia.

Hint Constructors eval_trace : eval_trace.

Ltac crush_eval :=
  let rec crush_eval_step :=
    cbn [empty_context interp_arith interp_binop] in *;
    autorewrite with core in *;
    lazymatch goal with
    | |- _ <> 0 => discriminate || congruence || lia
    | |- _ = _ => cbn; autorewrite with core; reflexivity
    | |- exists _ : valuation, _ => eexists; crush_eval_step
    | |- eval_trace _ _ _ _ => econstructor; crush_eval_step
    end
  in crush_eval_step.

Print simple_assign.

  Example simple_assign_empty_trace :
    exists v,
    eval_trace $0
      empty_context
      simple_assign
      (v, nil).
  Proof. crush_eval. Qed.

  Print two_assigns.

  Example two_assigns_empty_trace :
    exists v,
    eval_trace $0
      empty_context
      two_assigns
      (v, nil).
  Proof. crush_eval. Qed.

  Print simple_if.

  Example simple_if_true_branch :
    exists v,
    eval_trace $0
      empty_context
      simple_if
      (v, Branch true :: nil).
  Proof. crush_eval. Qed.

  Print simple_sequence.

  Example simple_sequence_true_false_branch :
    exists v,
    eval_trace $0
      empty_context
      simple_sequence
      (v, Branch true :: Branch false :: nil).
  Proof. crush_eval. Qed.

  Print nested_if.

  Example nested_if_true_false_branch :
    exists v,
    eval_trace $0
      empty_context
      nested_if
      (v, Branch true :: Branch false :: nil).
  Proof. crush_eval. Qed.

  Print simple_while.

  Example simple_while_true_false_branch :
    exists v,
    eval_trace $0
      ($0 $+ ("x", 1), nil)
      simple_while
      (v, Branch true :: Branch false :: nil).
  Proof. crush_eval. Qed.

  (* Final Boss: Example from Lab05 *)
  Print the_answer_is_42.

  Example trace_with_zero :
    exists v,
    eval_trace $0
      ($0 $+ ("oops", 0), nil)
      the_answer_is_42
      (v, Branch false :: Branch true :: nil).
  Proof. crush_eval. Qed.

  Example trace_with_nonzero :
    exists v,
    eval_trace $0
      ($0 $+ ("oops", 1), nil)
      the_answer_is_42
      (v, Branch true :: Branch true :: nil).
  Proof. crush_eval. Qed.
