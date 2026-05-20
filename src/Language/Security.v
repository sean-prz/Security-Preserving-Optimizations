Require Import VarSets.
Require Import Map.
Require Import Language.Syntax.



(* Define security levels for variables as either Public or Secret *)
Inductive sec_level :=
| Public
| Secret.

(* A security environment maps variables to their security levels *)
Definition sec_env := var_set.  

(* 
   A simple OR operation for security levels, where Secret dominates Public.
  Usefull for joining sec_env; if one of the two environments has a variable marked as Secret,
  the joined environment should also mark it as Secret.
*)
Definition join_sec (s1 s2 : sec_level) : sec_level :=
  match s1, s2 with
  | Secret, _ | _, Secret => Secret
  | Public, Public => Public
  end.

(* 
   A function to look up the security level of a variable in the security environment,
  returning Public if the variable is not found 
*)
Definition sec_lookup (se : sec_env) (x : var) : sec_level :=
  match VarSet.mem x se with
  | true => Secret
  | false => Public
  end.

Definition update_sec (se : sec_env) (x: var) (level: sec_level) : sec_env :=
  match level with
  | Secret => VarSet.add x se
  | Public => VarSet.remove x se
  end.

Definition senv_mk0 := VarSet.empty.

Definition senv_mk1 (x: var) (l: sec_level) :=
  update_sec VarSet.empty x l.

Definition senv_mk2 (x1 x2: var) (l1 l2: sec_level) :=
  update_sec (update_sec VarSet.empty x1 l1) x2 l2.

Definition senv_mk3 (x1 x2 x3: var) (l1 l2 l3: sec_level) :=
  update_sec (update_sec (update_sec VarSet.empty x1 l1) x2 l2) x3 l3.

(* 
    Join two security environments, combining their mappings using the join_sec operation.
    If a variable is absent from both environments, it stays absent.
    If it is present in exactly one environment, we keep that label.
    If it is present in both environments, we join the labels with [join_sec].
 *)
Definition join_sec_env (se1 se2 : sec_env) : sec_env :=
  VarSet.union se1 se2.


Definition is_secret (se : sec_env) (x : var) : Prop :=
  sec_lookup se x = Secret.

(*
  Compute the security level of an expression, given a security environment.
   Using join_sec to combine the security levels of subexpressions.
 *)
Fixpoint interp_sec (e : expr) (se : sec_env) {struct e} : sec_level :=
  match e with
  | Const _ => Public
  | Var x => sec_lookup se x
  | Binop _ e1 e2 => join_sec (interp_sec e1 se) (interp_sec e2 se)
  end.

(* Could prove keys equivalence betweeen sec_env fmap and val fmap *)
