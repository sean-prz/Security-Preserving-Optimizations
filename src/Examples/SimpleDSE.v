Require Import Examples.Programs.
Require Import Language.Optimizations.Unsafe.DSE.
Require Import Language.Main.


Goal opt_dse simple_assign_p1 = simple_assign_p1.
Proof.
  reflexivity.
Qed.

Goal opt_dse simple_assign_p2 = single_out_pgm Skip "y".
Proof.
  reflexivity.
Qed.

Goal opt_dse dead_assign_p = single_out_pgm ("x" <- 10) "x".
  reflexivity.
Qed.

Goal opt_dse live_assign_p1 =
single_out_pgm 
  ("x" <- 5;;
   "y" <- Var "x")
   "y".
  reflexivity.
Qed.

Goal opt_dse live_assign_p2 =
       single_out_pgm Skip "z".
  reflexivity.
Qed.

Goal opt_dse live_assign_p3 =
   single_out_pgm ("x" <- 10) "x".
  reflexivity.
Qed.

Goal opt_dse live_in_condition_p =
  single_out_pgm ("x" <- 5;;
   when (Var "x") then
     "y" <- 1
   else
     "y" <- 0
   done) "y".
  reflexivity.
Qed.

Goal opt_dse dead_before_if_p =
  single_out_pgm (
   when (Var "cond") then
     "x" <- 1
   else
     "x" <- 2
   done) "x".
  reflexivity.
Qed.

Goal opt_dse dead_in_loop_p =
  single_out_pgm (
   while (Var "n") loop
     "n" <- Var "n" - 1
   done) "n".
  reflexivity.
Qed.

Goal opt_dse chained_dead_p =
  single_out_pgm (
   "x" <- 3;;
   "y" <- Var "x") "y".
  reflexivity.
Qed.


Goal opt_dse while_issue1_p = while_issue1_p.
  reflexivity.
Qed.

Goal opt_dse while_issue2_p = while_issue2_p.
  reflexivity.
Qed.

Goal opt_dse while_issue3_p = while_issue3_p.
  reflexivity.
Qed.

Goal opt_dse while_issue4_p = while_issue4_p.
  reflexivity.
Qed.

(*We could possibly make DSE stronger, by detecting non-infinite, useless loops.
but that seems a lot of work for not much result.
 *)
(* Compute opt_dse (single_out_pgm FactBody "smth_else"). *)
