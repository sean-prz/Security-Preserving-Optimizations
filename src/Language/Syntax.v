From Stdlib Require Export NArith Arith.
From Stdlib Require Export Program.Equality.
Require Import Map.
From Stdlib Require Import String.

Arguments N.add : simpl nomatch.
Arguments N.sub : simpl nomatch.
Arguments N.mul : simpl nomatch.
Arguments N.div : simpl nomatch.
Arguments N.shiftl : simpl nomatch.
Arguments N.shiftr : simpl nomatch.

Declare Scope var_scope.

Notation var := string.
Definition var_eq : forall x y : var, {x = y} + {x <> y} := string_dec.
Infix "==v" := var_eq (no associativity, at level 50).
String Notation var string_of_list_byte list_byte_of_string: var_scope.

Open Scope var_scope.

(** ** Language definition *)

(** We'll start with a variant of an usual imperative language, with a few
    twists: first, we'll generalize the [Plus] constructor, allowing a number of
    binary operators.  Second, we'll add function calls (for simplicity, all
    functions take two arguments, and they assign their results to variables). *)

Inductive BinopName :=
| LogAnd 
| Eq 
| ShiftLeft 
| ShiftRight 
| Times 
| Divide 
| Plus 
| Minus 
| Modulo.

Inductive expr :=
| Const : nat -> expr
| Var : var -> expr
| Binop : BinopName -> expr -> expr -> expr.

Inductive cmd :=
| Skip : cmd
| Assign : var -> expr -> cmd
| AssignCall : var -> var -> expr -> expr -> cmd
| Cmov : var -> expr -> expr -> expr -> cmd
| Sequence : cmd -> cmd -> cmd
| If : expr -> cmd -> cmd -> cmd
| While : expr -> cmd -> cmd.

Declare Scope expr.
Delimit Scope expr with expr.

Coercion Const : nat >-> expr.
Coercion Var : var >-> expr.

(** The coercions defined in the previous section make programs easier to write by
    allowing to write [x] for [Var x] and [n] for [Const n], but they can be
    confusing when reading programs or proving properties, so the following line
    turns them off: *)

Set Printing Coercions.

Infix "&" := (Binop LogAnd) (at level 80) : expr.
Infix "==" := (Binop Eq) (at level 70) : expr.
Infix ">>" := (Binop ShiftRight) (at level 60) : expr.
Infix "<<" := (Binop ShiftLeft) (at level 60) : expr.
Infix "+" := (Binop Plus) (at level 50, left associativity) : expr.
Infix "-" := (Binop Minus) (at level 50, left associativity) : expr.
Infix "*" := (Binop Times) (at level 40, left associativity) : expr.
Infix "/" := (Binop Divide) (at level 40, left associativity) : expr.
Infix "mod" := (Binop Modulo) (at level 40) : expr.

Notation "x <- e" :=
  (Assign x e%expr)
    (at level 75).
Notation "x <- 'call1' f e1" :=
  (AssignCall x f e1%expr (Const 0))
    (at level 75, f at level 0, e1 at level 0).
Notation "x <- 'call2' f e1 e2" :=
  (AssignCall x f e1%expr e2%expr)
    (at level 75, f at level 0, e1 at level 0, e2 at level 0).
Infix ";;" :=
  Sequence (at level 76).
Notation "'when' e 'then' then_ 'else' else_ 'done'" :=
  (If e%expr then_ else_)
    (at level 75, e at level 0).
Notation "'while' e 'loop' body 'done'" :=
  (While e%expr body)
    (at level 75).

Definition function_env := fmap string ((var * var) * var * cmd).
