Require Import Map.
Require Import VarSets.
Require Import Language.Main.
Require Import Proofs.SecLookup.
Require Import Proofs.NonInterference.
From Stdlib Require Import Program.Equality.


(* 
Here we define a stronger definition of non_interference, which also accounts for security levels.
An example at the end of the file shows where a file could satisfy non_interference, but fails to satisfy
this new property.

Only after defining this stronger version of non_interference, we realized that it didn't bring a lot more value.
We decided to keep it for potential future work, if it turns out it has more value than we thought.
*)


(* Two security contexts agree if they have the same values AND the same
   dynamic security labels for all statically public variables. *)
Definition agree_on_public_sec_ctx (se_static : sec_env) (ctx1 ctx2 : sec_context) : Prop :=
  (* 1. The valuations agree on public variables *)
  agree_on_public se_static (sec_val_of ctx1) (sec_val_of ctx2) /\
  (* 2. The dynamic security environments agree on public variables *)
  (forall x, sec_lookup se_static x = Public ->
             sec_lookup (sec_of ctx1) x = sec_lookup (sec_of ctx2) x).

Definition non_interference_sec (se_static: sec_env) (c: cmd) (se_static_out: sec_env) : Prop :=
  forall ctx1_in ctx2_in ctx1_out ctx2_out,
    (* If the initial contexts agree on public data and labels... *)
    agree_on_public_sec_ctx se_static ctx1_in ctx2_in ->
    (* ...and they start with identical traces... *)
    sec_trace_of ctx1_in = sec_trace_of ctx2_in ->
    (* ...and they both evaluate the command... *)
    eval_sec ctx1_in c ctx1_out ->
    eval_sec ctx2_in c ctx2_out ->
    (* ...then their output traces must be identical... *)
    sec_trace_of ctx1_out = sec_trace_of ctx2_out /\
    (* ...and their output contexts must still agree on public data and labels. *)
    agree_on_public_sec_ctx se_static_out ctx1_out ctx2_out.


(* Helper lemmas for If *)

Lemma agree_on_public_sec_ctx_join_thn : forall se_thn se_els se_join ctx1 ctx2,
  VarSet.Equal (join_sec_env se_thn se_els) se_join ->
  (* If two contexts agree on public data and labels for "then" branch env... *)
  agree_on_public_sec_ctx se_thn ctx1 ctx2 ->
  (* ...then they agree on public data and labels for the joined environment. *)
  agree_on_public_sec_ctx se_join ctx1 ctx2.
Proof.
  intros se_thn se_els se_join ctx1 ctx2 Hjoin [Hval Hdyn].
  split; intros x Hpub.
  - rewrite <- lookup_simpl_pub in Hpub.
    unfold sec_lookup in Hpub; rewrite <- Hjoin in Hpub.
    apply join_sec_public in Hpub. destruct Hpub as [Hthn Hels].
    apply Hval. rewrite <- lookup_simpl_pub. exact Hthn.
  - unfold sec_lookup in Hpub; rewrite <- Hjoin in Hpub.
    apply join_sec_public in Hpub. destruct Hpub as [Hthn Hels].
    apply Hdyn. exact Hthn.
Qed.

Lemma agree_on_public_sec_ctx_join_els : forall se_thn se_els se_join ctx1 ctx2,
  VarSet.Equal (join_sec_env se_thn se_els) se_join ->
  (* If two contexts agree on public data and labels for "else" branch env... *)
  agree_on_public_sec_ctx se_els ctx1 ctx2 ->
  (* ...then they agree on public data and labels for the joined environment. *)
  agree_on_public_sec_ctx se_join ctx1 ctx2.
Proof.
  intros.
  apply agree_on_public_sec_ctx_join_thn with (se_els := se_thn) (se_thn:=se_els); [|exact H0].
  unfold join_sec_env in *.
  VarSetDecide.fsetdec.
Qed.

(*  Helper lemmas for While  *)
Lemma agree_on_public_sec_ctx_inv : forall se se_inv ctx1 ctx2,
  VarSet.Equal (join_sec_env se se_inv) se_inv ->
  (* If two contexts agree on public data and labels for the original env... *)
  agree_on_public_sec_ctx se ctx1 ctx2 ->
  (* ...then they agree on public data and labels for the loop invariant env. *)
  agree_on_public_sec_ctx se_inv ctx1 ctx2.
Proof.
  intros se se_inv ctx1 ctx2 Hjoin [Hval Hdyn].
  split; intros x Hpub.
  - apply Hval. rewrite <- lookup_simpl_pub. rewrite <- lookup_simpl_pub in Hpub. eapply join_sec_public_thn. unfold sec_lookup. rewrite Hjoin. exact Hpub.
  - apply Hdyn. eapply join_sec_public_thn. unfold sec_lookup. rewrite Hjoin. exact Hpub.
Qed.

Lemma agree_on_public_sec_ctx_body_inv : forall se_inv se_body ctx1 ctx2,
  VarSet.Equal (join_sec_env se_inv se_body) se_inv ->
  (* If two contexts agree on public data and labels for the body env... *)
  agree_on_public_sec_ctx se_body ctx1 ctx2 ->
  (* ...then they agree on public data and labels for the loop invariant env. *)
  agree_on_public_sec_ctx se_inv ctx1 ctx2.
Proof.
  intros.
  eapply agree_on_public_sec_ctx_inv; [|exact H0].
  unfold join_sec_env in *. VarSetDecide.fsetdec.
Qed.

(* proves the ct_cmd soundness, specifically for the while case. *)
Lemma while_soundness_sec : forall se_inv e body se_body,
  interp_sec e se_inv = Public ->
  ct_cmd se_inv body se_body ->
  non_interference_sec se_inv body se_body ->
  VarSet.Equal (join_sec_env se_inv se_body) se_inv ->
  non_interference_sec se_inv (While e body) se_inv.
Proof.
  intros se_inv e body se_body Hguard Hct_body Hni_body Hjoin.
  unfold non_interference_sec.
  intros ctx1_in ctx2_in ctx1_out ctx2_out Hagree_inv Htrace_in Heval1.

  revert ctx2_in ctx2_out Htrace_in Hagree_inv.
  dependent induction Heval1; intros ctx2_in ctx2_out Htrace_in Hagree_inv Heval2.

  - (* EvalSecWhileTrue *)
    inversion Heval2; subst; clear Heval2.
    + (* Case 1: Both True *)
      assert (Htrace_branched: sec_trace_of (ctx st++ Branch true) = sec_trace_of (ctx2_in st++ Branch true))
        by (cbn; rewrite Htrace_in; reflexivity).

      (* Traces don't affect valuations/labels*)
      assert (Hagree_branched: agree_on_public_sec_ctx se_inv (ctx st++ Branch true) (ctx2_in st++ Branch true))
        by exact Hagree_inv.

      edestruct Hni_body as [Htrace_body Hagree_body]; eauto.

      assert (Hagree_inv_after: agree_on_public_sec_ctx se_inv ctx' ctx'0).
      { eapply agree_on_public_sec_ctx_body_inv; eauto. }

      edestruct IHHeval1_2 as [Htrace_loop Hagree_loop]; eauto.

    + (* Case 2: True = False (contradiction) *)
      cbn in *.
      assert (Hcond: interp_arith e (sec_val_of ctx) = interp_arith e (sec_val_of ctx2_in)).
      { destruct Hagree_inv as [Hval _]. eapply interp_sec_public_agree; eauto. }
      congruence.

  - (* EvalSecWhileFalse *)
    inversion Heval2; subst; clear Heval2.
    + (* Case 3: False = True (contradiction) *)
      cbn in *.
      assert (Hcond: interp_arith e (sec_val_of ctx) = interp_arith e (sec_val_of ctx2_in)).
      { destruct Hagree_inv as [Hval _]. eapply interp_sec_public_agree; eauto. }
      congruence.

    + (* Case 4: False = False *)
      split.
      * cbn. rewrite Htrace_in. reflexivity.
      * exact Hagree_inv.
Qed.

(* proves the ct_cmd soundness, specifically for the cmov case. *)
Lemma cmov_non_interference_sec : forall se x cond e1 e2 level,
  join_sec (interp_sec cond se) (join_sec (interp_sec e1 se) (interp_sec e2 se)) = level ->
  non_interference_sec se (Cmov x cond e1 e2) (update_sec se x level).
Proof.
  Ltac resolve_sec_update_main :=
    intros param Hparam; cbn in *.

  unfold non_interference_sec.
  intros se x cond e1 e2 level Hjoin ctx1_in ctx2_in ctx1_out ctx2_out Hagree Htrace Heval1 Heval2.
  inversion Heval1; inversion Heval2; subst;
    (split; [assumption |]);
    destruct Hagree as [Hval_agree Hdyn_agree];
    unfold agree_on_public_sec_ctx, agree_on_public in *;
    split; resolve_sec_update_main.
  all: destruct (x ==v param);
  [ subst;
    try rewrite lookup_add_eq in Hparam by reflexivity;
    repeat rewrite lookup_add_eq by reflexivity;
    try rewrite <- lookup_simpl_pub in *;
    repeat rewrite lookup_update_sec_eq in *;
    destruct (interp_sec cond se) eqn:Hcond_sec;
    destruct (interp_sec e1 se) eqn:He1_sec;
    destruct (interp_sec e2 se) eqn:He2_sec;
    cbn in *; try discriminate;
    try match goal with
    | |- Some _ = Some _ =>
        try (apply f_equal; eapply interp_sec_public_agree; eauto);
        try (assert (Hcond_val: interp_arith cond (sec_val_of ctx1_in) = interp_arith cond (sec_val_of ctx2_in))
             by (eapply interp_sec_public_agree; eauto); congruence)
    | |- join_sec _ _ = join_sec _ _ =>
        rewrite (interp_sec_dynamic_agree cond se (sec_of ctx1_in) (sec_of ctx2_in) Hdyn_agree Hcond_sec);
        rewrite (interp_sec_dynamic_agree e1 se (sec_of ctx1_in) (sec_of ctx2_in) Hdyn_agree He1_sec);
        rewrite (interp_sec_dynamic_agree e2 se (sec_of ctx1_in) (sec_of ctx2_in) Hdyn_agree He2_sec);
        reflexivity
    end
  | try rewrite lookup_add_ne in Hparam by congruence;
    repeat rewrite lookup_add_ne by congruence;
    try rewrite <- lookup_simpl_pub in *;
    repeat rewrite lookup_update_sec_ne in * by congruence;
    try match goal with
    | |- _ $? ?v = _ $? ?v =>
        apply Hval_agree; rewrite <- lookup_simpl_pub; exact Hparam
    | |- sec_lookup _ ?v = sec_lookup _ ?v =>
        apply Hdyn_agree; exact Hparam
    end ].
Qed.

(* A program that is constant time according to our definition should satisfy
non-interference_sec. *)
Theorem ct_cmd_soundness_sec : forall se c se_out,
  ct_cmd se c se_out ->
  non_interference_sec se c se_out.
Proof.
  Ltac invert_evals_sec :=
    inversion Heval1; inversion Heval2; subst.

  Ltac resolve_sec_update x :=
  intros param Hparam; cbn in *; destruct (x ==v param);
  [ subst;
    try rewrite lookup_add_eq in Hparam by reflexivity;
    repeat rewrite lookup_add_eq by reflexivity;
    try rewrite <- lookup_simpl_pub in *;
    repeat rewrite lookup_update_sec_eq in *
  | try rewrite lookup_add_ne in Hparam by congruence;
    repeat rewrite lookup_add_ne by congruence;
    try rewrite <- lookup_simpl_pub in *;
    repeat rewrite lookup_update_sec_ne in * by congruence
  ].

  Ltac resolve_senv_mk2 dest1 dest2 Hagree:=
  intros param Hparam; cbn in *; try rewrite <- lookup_simpl_pub in Hparam;
  destruct (param ==v dest2); [
    subst; repeat rewrite lookup_senv_mk2_eq2 in *
  | destruct (param ==v dest1); [
      subst; repeat rewrite lookup_senv_mk2_eq1 in * by congruence
    | repeat rewrite lookup_senv_mk2_ne in * by congruence;
      autorewrite with core in *;
      try reflexivity; try (apply Hagree; exact Hparam)
    ]
  ];
  autorewrite with core in *; try reflexivity.

  intros se c se_out Hct.
  unfold non_interference_sec.

  induction Hct;
    intros ctx1_in ctx2_in ctx1_out ctx2_out Hagree Htrace Heval1 Heval2.

  - (* CtSkip *)
    invert_evals_sec.
    split; assumption.

  - (* CtAssign *)
    invert_evals_sec.
    split; [assumption |].

    destruct Hagree as [Hval_agree Hdyn_agree].
    unfold agree_on_public_sec_ctx, agree_on_public in *.
    split.

    + (* Prove values agree *)
      resolve_sec_update x.
      * apply f_equal. eapply interp_sec_public_agree; eauto.
      * apply Hval_agree. rewrite <- lookup_simpl_pub. exact Hparam.
    + (* Prove dynamic labels agree *)
      resolve_sec_update x.
      * eapply interp_sec_dynamic_agree; eauto.
      * apply Hdyn_agree. exact Hparam.

  - (* CtCmov *)
    pose proof (cmov_non_interference_sec se x cond e1 e2 level H) as Hcmov.
    unfold non_interference_sec in Hcmov.
    eapply Hcmov; eauto.

  - (* CtSequence *)
    inversion Heval1; inversion Heval2; subst; clear Heval1 Heval2.
    (* IHHct1 tells us that after executing c1, the intermediate contexts
       (ctx1 and ctx0) will agree on se1 and have identical traces. *)
    edestruct IHHct1 as [Htrace_mid Hagree_mid]; eauto.
  - (* CtIf *)
    (* 1. Prove the guard evaluates equally in both contexts *)
    assert (Hcond: interp_arith e (sec_val_of ctx1_in) = interp_arith e (sec_val_of ctx2_in)).
    { destruct Hagree as [Hval _]. eapply interp_sec_public_agree; eauto. }

    invert_evals_sec.

    + (* Case 1: Both branches are True *)
      (* Traces append the branch decision *)
      assert (Htrace_branched: sec_trace_of (ctx1_in st++ Branch true) = sec_trace_of (ctx2_in st++ Branch true))
        by (cbn; rewrite Htrace; reflexivity).
      (* Explicitly prove branched agreement *)
      assert (Hagree_branched: agree_on_public_sec_ctx se (ctx1_in st++ Branch true) (ctx2_in st++ Branch true))
        by exact Hagree.

      (* Force Coq to use the branched contexts instead of guessing *)
      edestruct (IHHct1 (ctx1_in st++ Branch true) (ctx2_in st++ Branch true) ctx1_out ctx2_out) as [Htrace_thn Hagree_thn]; eauto.
      split; [exact Htrace_thn |].
      eapply agree_on_public_sec_ctx_join_thn; eauto.
    + (* Case 2 and 3: branches dont match *)
      cbn in *. congruence.
    +  cbn in *. congruence.
    + (* Case 4: Botht branches are False *)
      assert (Htrace_branched: sec_trace_of (ctx1_in st++ Branch false) = sec_trace_of (ctx2_in st++ Branch false))
        by (cbn; rewrite Htrace; reflexivity).

      (* Explicitly prove branched agreement *)
      assert (Hagree_branched: agree_on_public_sec_ctx se (ctx1_in st++ Branch false) (ctx2_in st++ Branch false))
        by exact Hagree.

      (* Force Coq to use the branched contexts instead of guessing *)
      edestruct (IHHct2 (ctx1_in st++ Branch false) (ctx2_in st++ Branch false) ctx1_out ctx2_out) as [Htrace_els Hagree_els]; eauto.

      split; [exact Htrace_els |].
      eapply agree_on_public_sec_ctx_join_els; eauto.

  - (* CtWhile *)
    (* Cast the starting agreement to the loop invariant *)
    assert (Hagree_inv: agree_on_public_sec_ctx se_inv ctx1_in ctx2_in).
    { eapply agree_on_public_sec_ctx_inv; eauto. }

    eapply while_soundness_sec with (se_body := se_body); eauto.
Qed.


(* The example below is a program that satisfies non_interference, but does not satisfy non_interference_sec.

However, it is a bit of an outlier. By assigning "x" <- ("y" - "y"). the value stored in x is always 0. Therefore, the value of "y" has no impact on the final valuation and trace, so the program is non_interferent.

In the stricter non_interference_sec case, we could imagine two scenarios: "y" is secret or "y" is not defined. 
In the first case, the secrecy of "y" propagates to "x". in the second case, "x" remains public. So we don't have the same set of secrets in the end.
The program doesn't satisfy non_interference_sec.

We can see that this program is not very interesting (x being always 0 should not matter), and it hints that non_interference_sec does not bring any valuable information about the security of the program
This program is even a bit tricking the system. By not defining "y" in the second sctx, we are tricking our system with a var that is neither public nor secret.

We didn't formalize further this notion of difference between non_interference and non_interference_sec, but we found interesting to display where it didn't match. This point could point to a flaw in our system, inducing that we might need to declare all variables that we used (= undeclared vars are illegal)
*)

Definition interferent_example : cmd := Assign "x" (Var "y" - Var "y")%expr.

Definition se_sample     : sec_env := senv_mk1 "y" Secret.
Definition se_out_sample : sec_env := senv_mk1 "y" Secret.

(* [interferent_example] satisfies [non_interference] under ([se_sample], [se_out_sample]):
   the value of [x] is always 0 in both runs, and [Assign] adds nothing to the
   trace, so output traces and public values trivially agree. *)
Lemma interferent_example_non_interference :
  non_interference se_sample interferent_example se_out_sample.
Proof.
  unfold non_interference, interferent_example, se_sample, se_out_sample.
  intros v1 v2 t_in final_v1 final_v2 trace1 trace2 Hagree Heval1 Heval2.
  inversion Heval1; subst; clear Heval1.
  inversion Heval2; subst; clear Heval2.
  split; [reflexivity |].
  unfold agree_on_public in *. intros param Hparam.
  simpl.
  destruct (param ==v "x") as [Heq | Hne].
  - subst param. do 2 rewrite lookup_add_eq by reflexivity.
    destruct (v1 $? "y"); destruct (v2 $? "y");
      simpl; rewrite ?Nat.sub_diag; reflexivity.
  - do 2 rewrite lookup_add_ne by congruence.
    apply Hagree. exact Hparam.
Qed.

(* non_interference_sec fails*)
Lemma interferent_example_not_non_interference_sec :
  ~ non_interference_sec se_sample interferent_example se_out_sample.
Proof.
  unfold non_interference_sec, interferent_example, se_sample, se_out_sample.
  intros H.

  (* 2 start context that agree on public vars, but it's a bit of a trick,
    since "y" is not declared: not public nor secret.
  *)
  pose (ctx1 := (($0 : valuation), senv_mk1 "y" Secret, @nil trace_event)).
  pose (ctx2 := (($0 : valuation), VarSet.empty,        @nil trace_event)).

  assert (Heval1 : eval_sec ctx1 interferent_example
                            ((ctx1 sv$+ ("x", 0)) s$+ ("x", Secret))).
  { apply EvalSecAssign with (a := 0) (level := Secret).
    - unfold ctx1, sec_val_of; simpl.
      autorewrite with core. reflexivity.
    - reflexivity.
  }

  assert (Heval2 : eval_sec ctx2 interferent_example
                            ((ctx2 sv$+ ("x", 0)) s$+ ("x", Public))).
  { apply EvalSecAssign with (a := 0) (level := Public).
    - unfold ctx2, sec_val_of; simpl.
      autorewrite with core. reflexivity.
    - reflexivity. 
  }

  assert (Hagree : agree_on_public_sec_ctx (senv_mk1 "y" Secret) ctx1 ctx2).
  { split.
    - intros z . reflexivity.
    - intros z Hpub.
      apply lookup_simpl_pub in Hpub.
      assert (Hzy : z <> "y").
      { intro Heq. subst z. apply Hpub.
        unfold senv_mk1, update_sec. cbn.
        apply VarSet.add_spec. left. reflexivity. }
      unfold ctx1, ctx2, sec_of; cbn [fst snd].
      unfold senv_mk1.
      rewrite lookup_update_sec_ne by (intro Heq; symmetry in Heq; contradiction).
      reflexivity. }

  assert (Htrace : sec_trace_of ctx1 = sec_trace_of ctx2) by reflexivity.

  destruct (H _ _ _ _ Hagree Htrace Heval1 Heval2) as [_ [_ Hdyn]].

  assert (Hxpub : sec_lookup (senv_mk1 "y" Secret) "x" = Public).
  { apply lookup_simpl_pub. intro Hin.
    unfold senv_mk1, update_sec in Hin.
    apply VarSet.add_spec in Hin. destruct Hin as [Heq | Hin].
    - discriminate.
    - apply VarSetFacts.empty_iff in Hin; exact Hin. }

  specialize (Hdyn "x" Hxpub).
  cbn [sec_of fst snd] in Hdyn.
  rewrite !lookup_update_sec_eq in Hdyn.
  discriminate.
Qed.
