Require Import Map.
Require Import Language.Syntax.
Require Import Language.Semantics.
Require Import examples.Programs.
Require Import VarSets.


(* clean programs by removing skips after DSE *)
Fixpoint opt_unskip (c: cmd) :  cmd :=
  match c with
  | Sequence c1 c2 => match (opt_unskip c1), (opt_unskip c2) with
                       | Skip, c2' => c2'
                       | c1', Skip => c1'
                       | c1', c2' => c1' ;; c2'
                     end
  | If cond thenC elseC => match opt_unskip thenC, opt_unskip elseC with
                          | Skip, Skip => Skip
                          | thenC', elseC' => If cond thenC' elseC'
                          end
  (* We can't simplify the body because it might be non-terminating *)
  | While cond body => While cond (opt_unskip body)
  | _ => c
  end.

  (* All vars used in an expr *)
Fixpoint vars_in_expr (e: expr) : var_set :=
  match e with
  | Const n => VarSet.empty
  | Var x => VarSet.singleton x
  | Binop b e1 e2 => VarSet.union (vars_in_expr e1) (vars_in_expr e2)
  end.

  (* All vars used in a cmd *)
Fixpoint vars_in_cmd (c: cmd) : var_set :=
  match c with
  | Skip => VarSet.empty
  | Assign x e => VarSet.add x (vars_in_expr e)
  | Cmov x cond e1 e2 => VarSet.add x (VarSet.union (vars_in_expr cond) (VarSet.union (vars_in_expr e1) (vars_in_expr e2)))
  | AssignCall x f e1 e2 => VarSet.add x (VarSet.union (vars_in_expr e1) (vars_in_expr e2))
  | Sequence c1 c2 => VarSet.union (vars_in_cmd c1) (vars_in_cmd c2)
  | If e c1 c2 => VarSet.union (vars_in_expr e) (VarSet.union (vars_in_cmd c1) (vars_in_cmd c2))
  | While e body => VarSet.union (vars_in_expr e) (vars_in_cmd body)
  end.

  (* Fixpoint algorithm, perform f until no change (max: fuel iterations) *)
Fixpoint while_fixpoint  (f: var_set -> var_set) (cond_vars: var_set) (out: var_set) (fuel: nat): var_set :=
  match fuel with
  | 0 => out
  | S n =>
      let _in := VarSet.union (VarSet.union out cond_vars) (f out) in
      if VarSet.equal out _in
      then out
      else while_fixpoint f cond_vars _in n
  end.

(*note: n_vars is enough to iterate. because f is monotonous, and there are a bound number of variables.*)

(*Set of all vars stored by some program*) (*This is unused for now. We need it if we do While loop elimination *)
(* Fixpoint written_vars (c: cmd) : var_set := *)
(*   match c with *)
(*   | Skip => VarSet.empty *)
(*   | Assign x _ => VarSet.singleton x *)
(*   | AssignCall x _ _ _ => VarSet.singleton x *)
(*   | Sequence c1 c2 => VarSet.union (written_vars c1) (written_vars c2) *)
(*   | If _ thenC elseC => VarSet.union (written_vars thenC) (written_vars elseC) *)
(*   | While _ body => written_vars body *)
(*   end. *)


(* compute live variables, given live variables from after command *)
(* The analysis goes backwards. *)
(* formula: live_in = live_out + vars used in command - vars overwritten in command *)

(*More details about formula: https://cs420.epfl.ch/c/06_dataflow.html*)
Fixpoint liveness (c: cmd) (out: var_set) {struct c}: var_set :=
  match c with 
  | Skip => out
  | Assign x e =>
      (* if the assigned value is not live, the values used dont become live 
      -> propagates backwardsunuse of variables *)
      if VarSet.mem x out
      then VarSet.union (VarSet.remove x out) (vars_in_expr e)
      else out
  | Cmov x cond e1 e2 =>
      if VarSet.mem x out
      then VarSet.union (VarSet.remove x out) (VarSet.union (vars_in_expr cond) (VarSet.union (vars_in_expr e1) (vars_in_expr e2)))
      else out
  (*Body of functions cant access outer functions, no need to care about it*)
  | AssignCall x f e1 e2 =>
      VarSet.union (VarSet.remove x out) (VarSet.union (vars_in_expr e1) (vars_in_expr e2))
  | Sequence c1 c2 =>
      liveness c1 (liveness c2 out)
  | If e thenC elseC =>
       VarSet.union (vars_in_expr e) (VarSet.union (liveness thenC out) (liveness elseC out))
  | While e body =>
        while_fixpoint (liveness body) (vars_in_expr e) out (VarSet.cardinal (vars_in_cmd c))
  end.


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
  (*Keep assigncalls for now, but they could be removed as in simple Assign*)
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

