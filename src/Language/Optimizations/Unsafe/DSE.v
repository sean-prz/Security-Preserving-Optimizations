Require Import Map.
Require Import Language.Syntax.
Require Import Language.Analysis.
Require Import VarSets.


Fixpoint dse_helper (c: cmd) (out: var_set) : cmd :=
  match c with
  | Skip => Skip
  | Assign x e =>
      match VarSet.mem x out with
      | false => Skip (*not live, remove this assignment*)
      | true => Assign x e (*used later. keep it*)
      end
  | Cmov x cond e1 e2 =>
      match VarSet.mem x out with
      | false => Skip
      | true => Cmov x cond e1 e2
      end
        (*keep assigncalls for now, but they could be removed as in simple Assign*)
  | AssignCall x f e1 e2 => AssignCall x f e1 e2
  | Sequence c1 c2 =>
      Sequence (dse_helper c1 (liveness c2 out)) (dse_helper c2 out)
  | If e thenC elseC =>
      If e (dse_helper thenC out) (dse_helper elseC out)
  | While e body =>
      While e (dse_helper body (liveness c out))
  end.

Definition opt_dse (pgm: program): program :=
  (opt_unskip (dse_helper (cmd_of pgm) (output_of pgm)), output_of pgm).
