Require Import Map.
Require Import VarSets.
Require Import Language.Syntax.
Require Import Language.Security.
From Stdlib Require Import List.
Import ListNotations.

Definition valuation := fmap var nat.

Inductive trace_event :=
| Branch: bool -> trace_event
| MemWrite: var -> trace_event.

(*
  We define two different context, one for standard execution (with valuation and trace) 
  and one that also carries secrets, used to check if a program is secure
 *)
Definition context := (valuation * list trace_event)%type.
Definition sec_context := (valuation * sec_env * list trace_event)%type.

(* Getters for contexts *)
Definition val_of (ctx: context) := fst ctx.
Definition trace_of (ctx: context) := snd ctx.

(* Getters for sec_context *)
Definition sec_val_of (ctx : sec_context) := fst (fst ctx).
Definition sec_of (ctx : sec_context) := snd (fst ctx).
Definition sec_trace_of (ctx : sec_context) := snd ctx.


(* Some custom notations to make writing contexts more convenient.  For example, we can write
   [($0, nil) t++ Branch true]
   instead of
   [($0, nil), trace_of ($0, nil) ++ (Branch true :: nil)].
*)


(* Prepending an event to the trace *)
Notation "ev 't::' ctx" :=
  (val_of ctx, ev :: trace_of ctx)
  (at level 60).

(* Appending an event to the trace *)
Notation "ctx 't++' ev" :=
  (val_of ctx, trace_of ctx ++ (ev :: nil))
  (at level 60).

(* Updating the valuation in the context *)
Notation "ctx 'v$+' ( k , v )" :=
  (val_of ctx $+ (k, v), trace_of ctx)
  (at level 50, left associativity).

(* Updating the valuation in a security context *)
Notation "ctx 'sv$+' ( k , v )" :=
  (sec_val_of ctx $+ (k, v), sec_of ctx, sec_trace_of ctx)
  (at level 50, left associativity).

(* Updating the security environment in a security context *)
Notation "ctx 's$+' ( k , level )" :=
  (sec_val_of ctx, update_sec (sec_of ctx) k level, sec_trace_of ctx)
  (at level 50, left associativity).

(* Appending an event to the trace in a security context *)
Notation "ctx 'st++' ev" :=
  (sec_val_of ctx, sec_of ctx, sec_trace_of ctx ++ (ev :: nil))
  (at level 60).

(* Define empty contexts to make writing examples easier *)
Definition empty_context : context := ($0, nil).
Definition empty_sec_context : sec_context := ($0, VarSet.empty, nil).
