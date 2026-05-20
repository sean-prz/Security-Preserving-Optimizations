
(** Constant folding  - from lab08 *)
Definition opt_binop_fold (b: BinopName) (e1 e2: expr) : expr :=
  match b with
  | Plus =>
    match e1 with
    | Const 0 => e2
    | _ =>
      match e2 with
      | Const 0 => e1
      | _ => Binop b e1 e2
      end
    end
  | Times =>
    match e1 with
    | Const 0 => Const 0
    | _ =>
      match e2 with
      | Const 0 => Const 0
      | _ => Binop b e1 e2
      end
    end
  | Divide =>
    match e2 with
    | Const 1 => e1
    | _ => Binop b e1 e2
    end
  | _ => Binop b e1 e2
  end.
Arguments opt_binop_fold !_ !_ !_ /. (* Coq magic *)

(** Precomputation *)
Definition opt_binop_precompute (b: BinopName) (e1 e2: expr) : expr :=
  match e1, e2 with
  | Const n1, Const n2 => Const (interp_binop b n1 n2)
  | _, _ => Binop b e1 e2
  end.
Arguments opt_binop_precompute !_ !_ !_ /. (* Coq magic *)

(** The overall arithmetic optimizer *)
Fixpoint opt_arith (e: expr) : expr :=
  match e with
  | Binop b e1 e2 =>
    match opt_binop_precompute b (opt_arith e1) (opt_arith e2) with
    | Binop b' e1' e2' =>
      opt_binop_fold b (opt_arith e1) (opt_arith e2)
    | e' => e'
    end
  | _ => e
  end.
Arguments opt_arith !e /. (* Coq magic *)

Fixpoint opt_remove_branch (c : cmd) : cmd :=
match c with
| Skip => Skip
| Assign _ _ => c
| Sequence c1 c2 => Sequence (opt_remove_branch c1) (opt_remove_branch c2)
| AssignCall x f e1 e2 => AssignCall x f e1 e2
| If cond thn els => match (opt_arith cond) with
                    | Const n => match n with
                                | 0 => (opt_remove_branch els)
                                | _ => (opt_remove_branch thn)
                                end
                    | optim => If optim (opt_remove_branch thn) (opt_remove_branch els)
                    end
| While cond body => match (opt_arith cond) with
                    | Const n => match n with
                                | 0 => Skip
                                | _ => While 1 (opt_remove_branch body)
                                end
                    | optim => While optim (opt_remove_branch body)
                    end
end.

