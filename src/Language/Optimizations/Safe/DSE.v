Require Import Map.
Require Import Language.Syntax.
Require Import Language.Security.
Require Import Language.Analysis.
Require Import VarSets.


Fixpoint safe_dse_helper (c: cmd) (out: var_set) (secrets: sec_env): cmd :=
  match c with
  | Skip => Skip
  | Assign x e =>
      match (VarSet.mem x out), (sec_lookup secrets x) with
      | false, Public => Skip (*not live and not secret, remove this assignment*)
      | _, _ => Assign x e (*used later or secret. keep it*)
      end
        (*keep assigncalls for now, but they could be removed as in simple Assign*)
  | AssignCall x f e1 e2 => AssignCall x f e1 e2
  | Cmov x cond e1 e2 =>
      match (VarSet.mem x out), (sec_lookup secrets x) with
      | false, Public => Skip
      | _, _ => Cmov x cond e1 e2
      end
  | Sequence c1 c2 =>
      Sequence (safe_dse_helper c1 (liveness c2 out) secrets) (safe_dse_helper c2 out secrets)
  | If e thenC elseC =>
      If e (safe_dse_helper thenC out secrets) (safe_dse_helper elseC out secrets)
  | While e body =>
      While e (safe_dse_helper body (liveness c out) secrets)
  end.

Definition opt_safe_dse (pgm: program) (secrets: sec_env): program :=
  (opt_unskip (safe_dse_helper (cmd_of pgm) (output_of pgm) secrets), output_of pgm).
