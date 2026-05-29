Require Import Map.
Require Import Language.Syntax.
Require Import Language.Security.
Require Import Language.Analysis.
Require Import Language.Optimizations.Safe.Unskip.
Require Import VarSets.

(* computes security environment of variables after evaluating c*)

(* This matches the ct_cmd inductive except for the while case, which is too restrictive on purpose. 
Proving security DSE otherwise would be too timetaking *)
Fixpoint sec_post (c: cmd) (se: sec_env) : sec_env :=
  match c with
  | Skip => se
  | Assign x e =>
      update_sec se x (interp_sec e se)
  | Cmov x cond e1 e2 =>
      update_sec se x
        (join_sec (interp_sec cond se)
           (join_sec (interp_sec e1 se) (interp_sec e2 se)))
  | Sequence c1 c2 =>
      sec_post c2 (sec_post c1 se)
  | If _ thenC elseC =>
      join_sec_env (sec_post thenC se) (sec_post elseC se)
  | While _ body =>
      (* Conservative approximation: any variable mentioned in the
         loop may be secret after some iteration. *)
      VarSet.union se (vars_in_cmd body)
  end.

(* Variables that shouldn't be optimized away are secrets (after propagation) and the program's output variables*)
Definition protected_out (pgm: program) (secrets: sec_env) : var_set :=
  VarSet.union (output_of pgm) (sec_post (cmd_of pgm) secrets).


Fixpoint safe_dse_helper (c: cmd) (out: var_set) (secrets: sec_env): cmd :=
  match c with
  | Skip => Skip
  | Assign x e =>
      (* Drop the assignment only if [x] is dead, currently public, and [e] evaluates to public. *)
      match (VarSet.mem x out), (sec_lookup secrets x), (interp_sec e secrets) with
      | false, Public, Public => Skip
      | _, _, _ => Assign x e
      end
  | Cmov x cond e1 e2 =>
      match (VarSet.mem x out), (sec_lookup secrets x),
            (join_sec (interp_sec cond secrets)
               (join_sec (interp_sec e1 secrets) (interp_sec e2 secrets))) with
      | false, Public, Public => Skip
      | _, _, _ => Cmov x cond e1 e2
      end
  | Sequence c1 c2 =>
      let secrets_mid := sec_post c1 secrets in
      Sequence (safe_dse_helper c1 (liveness c2 out) secrets)
        (safe_dse_helper c2 out secrets_mid)
  | If e thenC elseC =>
      If e (safe_dse_helper thenC out secrets) (safe_dse_helper elseC out secrets)
  | While e body =>
      (* Conservative temporary checkpoint: keep loop bodies unchanged until the
         loop secret invariant is implemented and proved. *)
      While e body
  end.

(* Core secure DSE pass: eliminate only assignments that are dead and
   statically public, before a later cleanup pass removes any leftover skips. *)
Definition opt_safe_dse_core (pgm: program) (secrets: sec_env) : program :=
  (safe_dse_helper (cmd_of pgm) (protected_out pgm secrets) secrets,
   output_of pgm).

(* Full secure DSE optimization: run the core pass, then simplify the
   resulting command by removing skips introduced during elimination. *)
Definition opt_safe_dse (pgm: program) (secrets: sec_env): program :=
  (opt_unskip_cmd (cmd_of (opt_safe_dse_core pgm secrets)), output_of pgm).
