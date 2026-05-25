Require Import Map.
Require Import VarSets.
Require Import Language.Main.
Require Import Language.Analysis.
Require Import Language.Optimizations.Safe.DSE.
Require Import Language.Optimizations.Safe.Unskip.
Require Import Proofs.VarSetAgreement.
Require Import Proofs.SafeDSEProofs.
Require Import Proofs.EvalEquivalence.
Require Import Proofs.SecLookup.
Require Import Proofs.UnskipProofs.
Require Import Proofs.UnsafeDSEProofs.
Require Import Proofs.SecEnvSubtyping.
Require Import Proofs.Noninference.



(* Helper tactics *)


Ltac destruct_agree_while H :=
  match type of H with
  | agree_on (while_fixpoint (liveness ?body) (vars_in_expr ?e) ?out ?fuel) _ _ =>
    pose proof (liveness_while_cond_subset body e out) as He;
    pose proof (agree_on_subset _ _ _ _ He H) as Hagree_vars; 
    pose proof (while_fixpoint_contains_out) as Hout;
    pose proof (agree_on_subset _ _ _ _ (Hout _ _ _ _) H)  as Hagree_out;
     clear He Hout
  end.

Ltac solve_interp_from_agree Heval Hagree :=
  rewrite <- Heval;
  apply interp_arith_agree;
  eapply agree_on_subset; [| apply agree_on_sym; exact Hagree];
  VarSetDecide.fsetdec.

Ltac finish_sec_same H :=
  eexists; split; [exact H | constructor; [intro y; reflexivity | reflexivity | apply agree_on_refl]].

(** * Records to define properties *) 
(* instead of using conjunctions, for better readability (avoid  repeated split) *)


(* Two context coincide if they have the same trace and they agree on the output variables. *) 
Record trace_coincide (out : var_set) (ctx_src ctx_opt : context) : Prop := {
  trace_coincide_trace : trace_of ctx_src = trace_of ctx_opt;
  trace_coincide_vals : agree_on out (val_of ctx_src) (val_of ctx_opt)
}.

(* Two sec_context coincide if : 1. their sec_env are the same, 2. their traces are the same, 3. they agree on the output variables. *)
Record sec_coincide (out : var_set) (ctx1 ctx2 : sec_context) : Prop := {
  sec_coincide_sec : forall x,
    sec_lookup (sec_of ctx1) x = sec_lookup (sec_of ctx2) x;
  sec_coincide_trace : sec_trace_of ctx1 = sec_trace_of ctx2;
  sec_coincide_vals : agree_on out (sec_val_of ctx1) (sec_val_of ctx2)
}.

Definition sec_liveness_hyp c out ctx1 ctx2 : Prop :=
  (forall x, sec_lookup (sec_of ctx1) x = sec_lookup (sec_of ctx2) x) /\
  sec_trace_of ctx1 = sec_trace_of ctx2 /\
  agree_on (liveness c out) (sec_val_of ctx1) (sec_val_of ctx2).

Lemma sec_coincide_as_sec_liveness_hyp : forall c out ctx1 ctx2,
  sec_coincide (liveness c out) ctx1 ctx2 ->
  sec_liveness_hyp c out ctx1 ctx2.
Proof.
  intros c out ctx1 ctx2 [Hsec Htrace Hagree].
  repeat split; assumption.
Qed.

Lemma sec_liveness_hyp_sequence_left : forall c1 c2 out ctx1 ctx2,
  sec_liveness_hyp (Sequence c1 c2) out ctx1 ctx2 ->
  sec_liveness_hyp c1 (liveness c2 out) ctx1 ctx2.
Proof.
  intros c1 c2 out ctx1 ctx2 [Hsec [Htrace Hagree]].
  repeat split; simpl in *; assumption.
Qed.

Lemma sec_liveness_hyp_if_true_branch : forall e thn els out ctx1 ctx2,
  sec_liveness_hyp (If e thn els) out ctx1 ctx2 ->
  sec_liveness_hyp thn out (ctx1 st++ Branch true) (ctx2 st++ Branch true).
Proof.
  intros e thn els out ctx1 ctx2 [Hsec [Htrace Hagree]].
  repeat split.
  - simpl. exact Hsec.
  - simpl. rewrite Htrace. reflexivity.
  - simpl. simpl in Hagree.
    eapply agree_on_subset; [| exact Hagree].
    VarSetDecide.fsetdec.
Qed.

Lemma sec_liveness_hyp_if_false_branch : forall e thn els out ctx1 ctx2,
  sec_liveness_hyp (If e thn els) out ctx1 ctx2 ->
  sec_liveness_hyp els out (ctx1 st++ Branch false) (ctx2 st++ Branch false).
Proof.
  intros e thn els out ctx1 ctx2 [Hsec [Htrace Hagree]].
  repeat split.
  - simpl. exact Hsec.
  - simpl. rewrite Htrace. reflexivity.
  - simpl. simpl in Hagree.
    eapply agree_on_subset; [| exact Hagree].
    VarSetDecide.fsetdec.
Qed.

Lemma sec_liveness_hyp_while_body : forall e body out ctx1 ctx2,
  sec_liveness_hyp (While e body) out ctx1 ctx2 ->
  sec_liveness_hyp body (liveness (While e body) out)
    (ctx1 st++ Branch true) (ctx2 st++ Branch true).
Proof.
  intros e body out ctx1 ctx2 [Hsec [Htrace Hagree]].
  repeat split.
  - simpl. exact Hsec.
  - simpl. rewrite Htrace. reflexivity.
  - simpl.
    pose proof (liveness_while_body_closed body e out) as Hliveness_body.
    unfold liveness in Hliveness_body. fold liveness in Hliveness_body.
    eapply agree_on_subset; [exact Hliveness_body | exact Hagree].
Qed.

Lemma sec_liveness_hyp_while_exit_coincide : forall e body out ctx1 ctx2,
  sec_liveness_hyp (While e body) out ctx1 ctx2 ->
  sec_coincide out (ctx1 st++ Branch false) (ctx2 st++ Branch false).
Proof.
  intros e body out ctx1 ctx2 [Hsec [Htrace Hagree]].
  constructor.
  - simpl. exact Hsec.
  - simpl. rewrite Htrace. reflexivity.
  - simpl. eapply agree_on_subset; [| exact Hagree].
    apply while_fixpoint_contains_out.
Qed.


Definition opt_safe_dse_core (pgm: program) (secrets: sec_env) : program :=
  (safe_dse_helper (cmd_of pgm) (protected_out pgm secrets) secrets,
   output_of pgm).

(** * 3. Secret preservation (eval_sec) *)


Lemma agree_on_protected_out_implies_agree_on_secret : forall phi ctx c out ctx' v_opt,
  eval_sec phi ctx c ctx' ->
  agree_on (VarSet.union out (sec_post c (sec_of ctx))) (sec_val_of ctx') v_opt ->
  agree_on_secret (sec_of ctx') (sec_val_of ctx') v_opt.
Proof.
  intros phi ctx c out ctx' v_opt Heval Hagree.
  unfold agree_on_secret.
  intros x Hsecret.
  apply Hagree.
  rewrite VarSetEqProps.union_mem.
  apply Bool.orb_true_intro.
  right.
  apply mem_lookup_simpl_2.
  eapply sec_post_overapproximates_eval_sec; eauto.
Qed.


Lemma eval_sec_liveness_coincidence_skip : forall phi out ctx1 ctx2,
  sec_liveness_hyp Skip out ctx1 ctx2 ->
  exists ctx2_out,
    eval_sec phi ctx2 Skip ctx2_out /\
    sec_coincide out ctx1 ctx2_out.
Proof.
  intros phi out ctx1 ctx2 [Hsec [Htrace Hagree]].
  exists ctx2.
  split; [constructor|].
  constructor; assumption.
Qed.

Lemma eval_sec_liveness_coincidence_assign : forall phi out ctx x e a level ctx2,
  interp_arith e (sec_val_of ctx) = a ->
  interp_sec e (sec_of ctx) = level ->
  sec_liveness_hyp (Assign x e) out ctx ctx2 ->
  exists ctx2_out,
    eval_sec phi ctx2 (Assign x e) ctx2_out /\
    sec_coincide out ((ctx sv$+ (x, a)) s$+ (x, level)) ctx2_out.
Proof.
  intros phi out ctx x e a level ctx2 Heval Hlevel [Hsec [Htrace Hagree]].
  simpl in Hagree.
  destruct (VarSet.mem x out) eqn:Hx.
  - assert (Ha : interp_arith e (sec_val_of ctx2) = a).
    { solve_interp_from_agree Heval Hagree. }
    exists (((ctx2 sv$+ (x, a)) s$+ (x, interp_sec e (sec_of ctx2)))).
    split.
    + econstructor; eauto.
    + constructor.
      * intro y. simpl.
        apply sec_lookup_update_agree; auto.
        rewrite <- Hlevel.
        apply interp_sec_lookup_agree.
        exact Hsec.
      * exact Htrace.
      * apply agree_on_remove_add.
        eapply agree_on_subset; [| exact Hagree].
        VarSetDecide.fsetdec.
  - exists (((ctx2 sv$+ (x, interp_arith e (sec_val_of ctx2))) s$+ (x, interp_sec e (sec_of ctx2)))).
    split.
    + econstructor; eauto.
    + constructor.
      * intro y. simpl.
        apply sec_lookup_update_agree; auto.
        rewrite <- Hlevel.
        apply interp_sec_lookup_agree.
        exact Hsec.
      * exact Htrace.
      * apply agree_on_dead_update_both; auto.
Qed.

Lemma eval_sec_liveness_coincidence_cmov_true :
  forall phi out ctx x cond e1 e2 c a1 a2 level ctx2,
  interp_arith cond (sec_val_of ctx) = c ->
  c <> 0 ->
  interp_arith e1 (sec_val_of ctx) = a1 ->
  interp_arith e2 (sec_val_of ctx) = a2 ->
  join_sec (interp_sec cond (sec_of ctx))
    (join_sec (interp_sec e1 (sec_of ctx)) (interp_sec e2 (sec_of ctx))) = level ->
  sec_liveness_hyp (Cmov x cond e1 e2) out ctx ctx2 ->
  exists ctx2_out,
    eval_sec phi ctx2 (Cmov x cond e1 e2) ctx2_out /\
    sec_coincide out ((ctx sv$+ (x, a1)) s$+ (x, level)) ctx2_out.
Proof.
  intros phi out ctx x cond e1 e2 c a1 a2 level ctx2
    Hcond_src Hnz He1 He2 Hlevel [Hsec [Htrace Hagree]].
  simpl in Hagree.
  destruct (VarSet.mem x out) eqn:Hx.
  - assert (Hcond : interp_arith cond (sec_val_of ctx2) = c).
    { solve_interp_from_agree Hcond_src Hagree. }
    assert (Ha1 : interp_arith e1 (sec_val_of ctx2) = a1).
    { solve_interp_from_agree He1 Hagree. }
    assert (Ha2 : interp_arith e2 (sec_val_of ctx2) = a2).
    { solve_interp_from_agree He2 Hagree. }
    exists (((ctx2 sv$+ (x, a1)) s$+ (x,
      join_sec (interp_sec cond (sec_of ctx2))
        (join_sec (interp_sec e1 (sec_of ctx2)) (interp_sec e2 (sec_of ctx2)))))).
    split.
    + eapply EvalSecCmovTrue; eauto.
    + constructor.
      * intro y. simpl.
        apply sec_lookup_update_agree; auto.
        rewrite <- Hlevel.
        repeat rewrite (interp_sec_lookup_agree _ _ _ Hsec).
        reflexivity.
      * exact Htrace.
      * apply agree_on_remove_add.
        eapply agree_on_subset; [| exact Hagree].
        VarSetDecide.fsetdec.
  - destruct (interp_arith cond (sec_val_of ctx2)) eqn:Hc2.
    + exists (((ctx2 sv$+ (x, interp_arith e2 (sec_val_of ctx2))) s$+ (x,
        join_sec (interp_sec cond (sec_of ctx2))
          (join_sec (interp_sec e1 (sec_of ctx2)) (interp_sec e2 (sec_of ctx2)))))).
      split.
      * eapply EvalSecCmovFalse; eauto.
      * constructor.
        -- intro y. simpl.
           apply sec_lookup_update_agree; auto.
           rewrite <- Hlevel.
           repeat rewrite (interp_sec_lookup_agree _ _ _ Hsec).
           reflexivity.
        -- exact Htrace.
        -- apply agree_on_dead_update_both; auto.
    + exists (((ctx2 sv$+ (x, interp_arith e1 (sec_val_of ctx2))) s$+ (x,
        join_sec (interp_sec cond (sec_of ctx2))
          (join_sec (interp_sec e1 (sec_of ctx2)) (interp_sec e2 (sec_of ctx2)))))).
      split.
      * eapply EvalSecCmovTrue; eauto.
      * constructor.
        -- intro y. simpl.
           apply sec_lookup_update_agree; auto.
           rewrite <- Hlevel.
           repeat rewrite (interp_sec_lookup_agree _ _ _ Hsec).
           reflexivity.
        -- exact Htrace.
        -- apply agree_on_dead_update_both; auto.
Qed.

Lemma eval_sec_liveness_coincidence_cmov_false :
  forall phi out ctx x cond e1 e2 a1 a2 level ctx2,
  interp_arith cond (sec_val_of ctx) = 0 ->
  interp_arith e1 (sec_val_of ctx) = a1 ->
  interp_arith e2 (sec_val_of ctx) = a2 ->
  join_sec (interp_sec cond (sec_of ctx))
    (join_sec (interp_sec e1 (sec_of ctx)) (interp_sec e2 (sec_of ctx))) = level ->
  sec_liveness_hyp (Cmov x cond e1 e2) out ctx ctx2 ->
  exists ctx2_out,
    eval_sec phi ctx2 (Cmov x cond e1 e2) ctx2_out /\
    sec_coincide out ((ctx sv$+ (x, a2)) s$+ (x, level)) ctx2_out.
Proof.
  intros phi out ctx x cond e1 e2 a1 a2 level ctx2
    Hcond_src He1 He2 Hlevel [Hsec [Htrace Hagree]].
  simpl in Hagree.
  destruct (VarSet.mem x out) eqn:Hx.
  - assert (Hcond : interp_arith cond (sec_val_of ctx2) = 0).
    { solve_interp_from_agree Hcond_src Hagree. }
    assert (Ha1 : interp_arith e1 (sec_val_of ctx2) = a1).
    { solve_interp_from_agree He1 Hagree. }
    assert (Ha2 : interp_arith e2 (sec_val_of ctx2) = a2).
    { solve_interp_from_agree He2 Hagree. }
    exists (((ctx2 sv$+ (x, a2)) s$+ (x,
      join_sec (interp_sec cond (sec_of ctx2))
        (join_sec (interp_sec e1 (sec_of ctx2)) (interp_sec e2 (sec_of ctx2)))))).
    split.
    + eapply EvalSecCmovFalse; eauto.
    + constructor.
      * intro y. simpl.
        apply sec_lookup_update_agree; auto.
        rewrite <- Hlevel.
        repeat rewrite (interp_sec_lookup_agree _ _ _ Hsec).
        reflexivity.
      * exact Htrace.
      * apply agree_on_remove_add.
        eapply agree_on_subset; [| exact Hagree].
        VarSetDecide.fsetdec.
  - destruct (interp_arith cond (sec_val_of ctx2)) eqn:Hc2.
    + exists (((ctx2 sv$+ (x, interp_arith e2 (sec_val_of ctx2))) s$+ (x,
        join_sec (interp_sec cond (sec_of ctx2))
          (join_sec (interp_sec e1 (sec_of ctx2)) (interp_sec e2 (sec_of ctx2)))))).
      split.
      * eapply EvalSecCmovFalse; eauto.
      * constructor.
        -- intro y. simpl.
           apply sec_lookup_update_agree; auto.
           rewrite <- Hlevel.
           repeat rewrite (interp_sec_lookup_agree _ _ _ Hsec).
           reflexivity.
        -- exact Htrace.
        -- apply agree_on_dead_update_both; auto.
    + exists (((ctx2 sv$+ (x, interp_arith e1 (sec_val_of ctx2))) s$+ (x,
        join_sec (interp_sec cond (sec_of ctx2))
          (join_sec (interp_sec e1 (sec_of ctx2)) (interp_sec e2 (sec_of ctx2)))))).
      split.
      * eapply EvalSecCmovTrue; eauto.
      * constructor.
        -- intro y. simpl.
           apply sec_lookup_update_agree; auto.
           rewrite <- Hlevel.
           repeat rewrite (interp_sec_lookup_agree _ _ _ Hsec).
           reflexivity.
        -- exact Htrace.
        -- apply agree_on_dead_update_both; auto.
Qed.

Lemma eval_sec_liveness_coincidence_assign_call :
  forall phi out x f e1 e2 x1 x2 y body a1 a2 level1 level2 ctx ctx' a level ctx2,
  phi $? f = Some ((x1, x2), y, body) ->
  interp_arith e1 (sec_val_of ctx) = a1 ->
  interp_arith e2 (sec_val_of ctx) = a2 ->
  interp_sec e1 (sec_of ctx) = level1 ->
  interp_sec e2 (sec_of ctx) = level2 ->
  eval_sec phi (($0 $+ (x1, a1) $+ (x2, a2)), senv_mk2 x1 x2 level1 level2, sec_trace_of ctx) body ctx' ->
  sec_val_of ctx' $? y = Some a ->
  sec_lookup (sec_of ctx') y = level ->
  sec_liveness_hyp (AssignCall x f e1 e2) out ctx ctx2 ->
  exists ctx2_out,
    eval_sec phi ctx2 (AssignCall x f e1 e2) ctx2_out /\
    sec_coincide out ((sec_val_of ctx $+ (x, a)), update_sec (sec_of ctx) x level, sec_trace_of ctx') ctx2_out.
Proof.
  intros phi out x f e1 e2 x1 x2 y body a1 a2 level1 level2 ctx ctx' a level ctx2
    Hfun He1 He2 Hl1_src Hl2_src Hbody Hy Hylevel [Hsec [Htrace Hagree]].
  simpl in Hagree.
  assert (Ha1 : interp_arith e1 (sec_val_of ctx2) = a1).
  { solve_interp_from_agree He1 Hagree. }
  assert (Ha2 : interp_arith e2 (sec_val_of ctx2) = a2).
  { solve_interp_from_agree He2 Hagree. }
  assert (Hl1 : interp_sec e1 (sec_of ctx2) = level1).
  {
    rewrite <- Hl1_src.
    symmetry.
    apply interp_sec_lookup_agree.
    exact Hsec.
  }
  assert (Hl2 : interp_sec e2 (sec_of ctx2) = level2).
  {
    rewrite <- Hl2_src.
    symmetry.
    apply interp_sec_lookup_agree.
    exact Hsec.
  }
  exists ((sec_val_of ctx2 $+ (x, a), update_sec (sec_of ctx2) x level, sec_trace_of ctx')).
  split.
  - eapply EvalSecAssignCall with (x1 := x1) (x2 := x2) (y := y) (body := body)
      (a1 := a1) (a2 := a2) (level1 := level1) (level2 := level2) (ctx' := ctx'); eauto.
    rewrite <- Htrace.
    exact Hbody.
  - constructor.
    + intro z. simpl.
      apply sec_lookup_update_agree; auto.
    + reflexivity.
    + apply agree_on_remove_add.
      eapply agree_on_subset; [| exact Hagree].
      VarSetDecide.fsetdec.
Qed.

Lemma eval_sec_liveness_coincidence_sequence :
  forall phi out ctx c1 ctx1 c2 ctx1_out ctx2,
  (forall out ctx2,
    sec_liveness_hyp c1 out ctx ctx2 ->
    exists ctx2_out,
      eval_sec phi ctx2 c1 ctx2_out /\
      sec_coincide out ctx1 ctx2_out) ->
  (forall out ctx2,
    sec_liveness_hyp c2 out ctx1 ctx2 ->
    exists ctx2_out,
      eval_sec phi ctx2 c2 ctx2_out /\
      sec_coincide out ctx1_out ctx2_out) ->
  sec_liveness_hyp (Sequence c1 c2) out ctx ctx2 ->
  exists ctx2_out,
    eval_sec phi ctx2 (Sequence c1 c2) ctx2_out /\
    sec_coincide out ctx1_out ctx2_out.
Proof.
  intros phi out ctx c1 ctx1 c2 ctx1_out ctx2 IHc1 IHc2 Hhyp.
  destruct (IHc1 (liveness c2 out) ctx2
    (sec_liveness_hyp_sequence_left c1 c2 out ctx ctx2 Hhyp))
    as [ctx2_mid [Heval1 Hcoin1]].
  destruct (IHc2 out ctx2_mid
    (sec_coincide_as_sec_liveness_hyp c2 out ctx1 ctx2_mid Hcoin1))
    as [ctx2_final [Heval2 Hcoin2]].
  exists ctx2_final. split; [econstructor|exact Hcoin2]; eauto.
Qed.

Lemma eval_sec_liveness_coincidence_if_true :
  forall phi out ctx e thn els ctx1_out c ctx2,
  interp_arith e (sec_val_of ctx) = c ->
  c <> 0 ->
  (forall out ctx2,
    sec_liveness_hyp thn out (ctx st++ Branch true) ctx2 ->
    exists ctx2_out,
      eval_sec phi ctx2 thn ctx2_out /\
      sec_coincide out ctx1_out ctx2_out) ->
  sec_liveness_hyp (If e thn els) out ctx ctx2 ->
  exists ctx2_out,
    eval_sec phi ctx2 (If e thn els) ctx2_out /\
    sec_coincide out ctx1_out ctx2_out.
Proof.
  intros phi out ctx e thn els ctx1_out c ctx2 Hcond_src Hnz IHthn Hhyp.
  assert (Hhyp_copy := Hhyp).
  destruct Hhyp_copy as [Hsec [Htrace Hagree]].
  simpl in Hagree.
  assert (Hcond : interp_arith e (sec_val_of ctx2) = c).
  { solve_interp_from_agree Hcond_src Hagree. }
  destruct (IHthn out (ctx2 st++ Branch true)
    (sec_liveness_hyp_if_true_branch e thn els out ctx ctx2 Hhyp))
    as [ctx2' [Heval_thn Hcoin]].
  exists ctx2'. split; [eapply EvalSecIfTrue|exact Hcoin]; eauto.
Qed.

Lemma eval_sec_liveness_coincidence_if_false :
  forall phi out ctx e thn els ctx1_out ctx2,
  interp_arith e (sec_val_of ctx) = 0 ->
  (forall out ctx2,
    sec_liveness_hyp els out (ctx st++ Branch false) ctx2 ->
    exists ctx2_out,
      eval_sec phi ctx2 els ctx2_out /\
      sec_coincide out ctx1_out ctx2_out) ->
  sec_liveness_hyp (If e thn els) out ctx ctx2 ->
  exists ctx2_out,
    eval_sec phi ctx2 (If e thn els) ctx2_out /\
    sec_coincide out ctx1_out ctx2_out.
Proof.
  intros phi out ctx e thn els ctx1_out ctx2 Hcond_src IHels Hhyp.
  assert (Hhyp_copy := Hhyp).
  destruct Hhyp_copy as [Hsec [Htrace Hagree]].
  simpl in Hagree.
  assert (Hcond : interp_arith e (sec_val_of ctx2) = 0).
  { solve_interp_from_agree Hcond_src Hagree. }
  destruct (IHels out (ctx2 st++ Branch false)
    (sec_liveness_hyp_if_false_branch e thn els out ctx ctx2 Hhyp))
    as [ctx2' [Heval_els Hcoin]].
  exists ctx2'. split; [eapply EvalSecIfFalse|exact Hcoin]; eauto.
Qed.

Lemma eval_sec_liveness_coincidence_while_true :
  forall phi out ctx e body ctx' ctx1_out c ctx2,
  interp_arith e (sec_val_of ctx) = c ->
  c <> 0 ->
  (forall out ctx2,
    sec_liveness_hyp body out (ctx st++ Branch true) ctx2 ->
    exists ctx2_out,
      eval_sec phi ctx2 body ctx2_out /\
      sec_coincide out ctx' ctx2_out) ->
  (forall out ctx2,
    sec_liveness_hyp (While e body) out ctx' ctx2 ->
    exists ctx2_out,
      eval_sec phi ctx2 (While e body) ctx2_out /\
      sec_coincide out ctx1_out ctx2_out) ->
  sec_liveness_hyp (While e body) out ctx ctx2 ->
  exists ctx2_out,
    eval_sec phi ctx2 (While e body) ctx2_out /\
    sec_coincide out ctx1_out ctx2_out.
Proof.
  intros phi out ctx e body ctx' ctx1_out c ctx2 Hcond_src Hnz IHbody IHwhile Hhyp.
  assert (Hhyp_copy := Hhyp).
  destruct Hhyp_copy as [Hsec [Htrace Hagree]].
  simpl in Hagree.
  destruct (IHbody (liveness (While e body) out) (ctx2 st++ Branch true)
    (sec_liveness_hyp_while_body e body out ctx ctx2 Hhyp))
    as [ctx2_mid [Heval_body Hcoin1]].
  destruct (IHwhile out ctx2_mid
    (sec_coincide_as_sec_liveness_hyp (While e body) out ctx' ctx2_mid Hcoin1))
    as [ctx2_final [Heval_while Hcoin2]].
  exists ctx2_final. split.
  - destruct_agree_while Hagree.
    eapply EvalSecWhileTrue; eauto.
    simpl.
    assert (interp_arith e (sec_val_of ctx2) = c).
    { solve_interp_from_agree Hcond_src Hagree_vars. }
    congruence.
  - exact Hcoin2.
Qed.

Lemma eval_sec_liveness_coincidence_while_false :
  forall phi out ctx e body ctx2,
  interp_arith e (sec_val_of ctx) = 0 ->
  sec_liveness_hyp (While e body) out ctx ctx2 ->
  exists ctx2_out,
    eval_sec phi ctx2 (While e body) ctx2_out /\
    sec_coincide out (ctx st++ Branch false) ctx2_out.
Proof.
  intros phi out ctx e body ctx2 Hcond_src Hhyp.
  pose proof (sec_liveness_hyp_while_exit_coincide e body out ctx ctx2 Hhyp) as Hcoin.
  destruct Hhyp as [_ [_ Hagree]].
  simpl in Hagree.
  destruct_agree_while Hagree.
  exists (ctx2 st++ Branch false). split.
  - eapply EvalSecWhileFalse.
    simpl.
    assert (interp_arith e (sec_val_of ctx2) = 0).
    { solve_interp_from_agree Hcond_src Hagree_vars. }
    exact H.
  - exact Hcoin.
Qed.

Lemma eval_sec_liveness_coincidence : forall phi c out ctx1 ctx2 ctx1_out,
  eval_sec phi ctx1 c ctx1_out ->
  (forall x, sec_lookup (sec_of ctx1) x = sec_lookup (sec_of ctx2) x) ->
  sec_trace_of ctx1 = sec_trace_of ctx2 ->
  agree_on (liveness c out) (sec_val_of ctx1) (sec_val_of ctx2) ->
  exists ctx2_out,
    eval_sec phi ctx2 c ctx2_out /\
    sec_coincide out ctx1_out ctx2_out.
Proof.
  intros phi c out ctx1 ctx2 ctx1_out Heval Hsec Htrace Hagree.
  revert out ctx2 Hsec Htrace Hagree.
  dependent induction Heval; intros.
  - eapply eval_sec_liveness_coincidence_skip.
    repeat split; eauto.
  - eapply eval_sec_liveness_coincidence_assign; eauto.
    repeat split; eauto.
  - eapply eval_sec_liveness_coincidence_cmov_true; eauto.
    repeat split; eauto.
  - eapply eval_sec_liveness_coincidence_cmov_false; eauto.
    repeat split; eauto.
  - eapply eval_sec_liveness_coincidence_assign_call; eauto.
    repeat split; eauto.
  - eapply eval_sec_liveness_coincidence_sequence.
    + intros out' ctx2' [Hsec' [Htrace' Hagree']].
      eapply IHHeval1; eauto.
    + intros out' ctx2' [Hsec' [Htrace' Hagree']].
      eapply IHHeval2; eauto.
    + repeat split; eauto.
  - eapply eval_sec_liveness_coincidence_if_true; eauto.
    + intros out' ctx2' [Hsec' [Htrace' Hagree']].
      eapply IHHeval; eauto.
    + repeat split; eauto.
  - eapply eval_sec_liveness_coincidence_if_false; eauto.
    + intros out' ctx2' [Hsec' [Htrace' Hagree']].
      eapply IHHeval; eauto.
    + repeat split; eauto.
  - eapply eval_sec_liveness_coincidence_while_true; eauto.
    + intros out' ctx2' [Hsec' [Htrace' Hagree']].
      eapply IHHeval1; eauto.
    + intros out' ctx2' [Hsec' [Htrace' Hagree']].
      eapply IHHeval2; eauto.
    + repeat split; eauto.
  - eapply eval_sec_liveness_coincidence_while_false; eauto.
    repeat split; eauto.
Qed.

(* Any evaluation of the optimized program can be matched to an evaluation of the original program 
   that have : 1. same sec. labels, 2. same trace, 3. agree on the out variables. *)
Lemma safe_dse_helper_sec_complete : forall phi c out secrets ctx ctx_opt,
  sec_env_sub (sec_of ctx) secrets ->
  eval_sec phi ctx (safe_dse_helper c out secrets) ctx_opt ->
  exists ctx_src,
    eval_sec phi ctx c ctx_src /\
    sec_coincide out ctx_src ctx_opt.
Proof.
  intros phi c.
  induction c as
      [| x e
       | x f e1 e2
       | x cond e1 e2
       | c1 IHc1 c2 IHc2
       | e thn IHthn els IHels
       | e body IHbody];
    simpl; intros out secrets ctx ctx_opt Hsub Hopt.
  - finish_sec_same Hopt.
  - destruct (VarSet.mem x out) eqn:Hout.
    + finish_sec_same Hopt.
    + destruct (sec_lookup secrets x) eqn:Hsecret;
        destruct (interp_sec e secrets) eqn:Hlevel.
      * inversion Hopt; subst.
        pose proof (sec_env_sub_public _ _ _ Hsub Hsecret) as Hpub_actual.
        pose proof (interp_sec_public_under_sub e (sec_of ctx_opt) secrets Hsub Hlevel)
          as Hlevel_actual.
        exists ((ctx_opt sv$+ (x, interp_arith e (sec_val_of ctx_opt))) s$+ (x, Public)).
        split.
        -- econstructor; eauto.
        -- constructor.
           ++ intro y. simpl. apply sec_lookup_update_public_id. exact Hpub_actual.
           ++ reflexivity.
           ++ simpl. eapply agree_on_dead_update_left; eauto. apply agree_on_refl.
      * finish_sec_same Hopt.
      * finish_sec_same Hopt.
      * finish_sec_same Hopt.
  - finish_sec_same Hopt.
  - destruct (VarSet.mem x out) eqn:Hout.
    + finish_sec_same Hopt.
    + destruct (sec_lookup secrets x) eqn:Hsecret;
        destruct (join_sec (interp_sec cond secrets)
          (join_sec (interp_sec e1 secrets) (interp_sec e2 secrets))) eqn:Hlevel.
      * inversion Hopt; subst.
        pose proof (sec_env_sub_public _ _ _ Hsub Hsecret) as Hpub_actual.
        pose proof (cmov_level_public_under_sub cond e1 e2 (sec_of ctx_opt) secrets Hsub Hlevel)
          as Hlevel_actual.
        destruct (interp_arith cond (sec_val_of ctx_opt)) eqn:Hcond.
        -- exists ((ctx_opt sv$+ (x, interp_arith e2 (sec_val_of ctx_opt))) s$+ (x, Public)).
           split.
           ++ eapply EvalSecCmovFalse; eauto.
           ++ constructor.
              ** intro y. simpl. apply sec_lookup_update_public_id. exact Hpub_actual.
              ** reflexivity.
              ** simpl. eapply agree_on_dead_update_left; eauto. apply agree_on_refl.
        -- exists ((ctx_opt sv$+ (x, interp_arith e1 (sec_val_of ctx_opt))) s$+ (x, Public)).
           split.
           ++ eapply EvalSecCmovTrue; eauto.
           ++ constructor.
              ** intro y. simpl. apply sec_lookup_update_public_id. exact Hpub_actual.
              ** reflexivity.
              ** simpl. eapply agree_on_dead_update_left; eauto. apply agree_on_refl.
      * finish_sec_same Hopt.
      * finish_sec_same Hopt.
      * finish_sec_same Hopt.
  - inversion Hopt; subst.
    specialize (IHc1 (liveness c2 out) secrets ctx ctx1 Hsub H2).
    destruct IHc1 as [ctx1_src [Heval1_src Hcoin1]].
    destruct Hcoin1 as [Hsec_eq1 Htrace_eq1 Hagree1].
    assert (Hsub2 : sec_env_sub (sec_of ctx1) (sec_post c1 secrets)).
    {
      unfold sec_env_sub.
      intros y Hsecret_mid.
      pose proof (Hsec_eq1 y) as Hsec_eq1_y.
      rewrite <- Hsec_eq1_y in Hsecret_mid.
      eapply sec_env_sub_trans.
      - eapply sec_post_overapproximates_eval_sec_subset.
        exact Heval1_src.
      - eapply sec_post_monotone.
        exact Hsub.
      - exact Hsecret_mid.
    }
    specialize (IHc2 out (sec_post c1 secrets) ctx1 ctx_opt Hsub2 H4).
    destruct IHc2 as [ctx2_src_from_opt [Heval2_src_from_opt Hcoin2]].
    destruct Hcoin2 as [Hsec_eq2 Htrace_eq2 Hagree2].
    pose proof (eval_sec_liveness_coincidence phi c2 out ctx1 ctx1_src ctx2_src_from_opt
      Heval2_src_from_opt
      (fun y => eq_sym (Hsec_eq1 y))
      (eq_sym Htrace_eq1)
      (agree_on_sym _ _ _ Hagree1)) as Hcoincide.
    destruct Hcoincide as [ctx2_src [Heval2_src Hcoin]].
    destruct Hcoin as [Hsec_eq_coin Htrace_eq_coin Hagree_coin].
    exists ctx2_src.
    split.
    + econstructor; eauto.
    + constructor.
      * intro y. rewrite <- Hsec_eq_coin. apply Hsec_eq2.
      * rewrite <- Htrace_eq_coin. exact Htrace_eq2.
      * apply agree_on_sym in Hagree_coin.
        eapply agree_on_trans; eauto.
  - inversion Hopt; subst.
    + specialize (IHthn out secrets (ctx st++ Branch true) ctx_opt Hsub H6).
      destruct IHthn as [ctx_src [Heval_src Hcoin]].
      exists ctx_src.
      split; [eapply EvalSecIfTrue; eauto|exact Hcoin].
    + specialize (IHels out secrets (ctx st++ Branch false) ctx_opt Hsub H5).
      destruct IHels as [ctx_src [Heval_src Hcoin]].
      exists ctx_src.
      split; [eapply EvalSecIfFalse; eauto|exact Hcoin].
  - finish_sec_same Hopt.
Qed.

(* Main theorem for secret preservation on the helper*)
Lemma opt_safe_dse_core_keeps_secrets_secret :
  opt_keeps_secrets_secret opt_safe_dse_core.
Proof.
  unfold opt_keeps_secrets_secret, opt_safe_dse_core.
  intros sctx sctx' sctx'' pgm pgm' phi Hopt Hsrc Hopt_eval x.
  destruct pgm as [c out].
  destruct pgm' as [c' out'].
  simpl in Hopt.
  inversion Hopt; subst; clear Hopt.
  simpl in Hopt_eval.
  pose proof (safe_dse_helper_sec_complete phi c
    (VarSet.union out' (sec_post c (sec_of sctx)))
    (sec_of sctx) sctx sctx''
    (sec_env_sub_refl (sec_of sctx))
    Hopt_eval) as Hcomplete.
  destruct Hcomplete as [ctx_src [Hsrc_from_opt Hcoin_out]].
  destruct Hcoin_out as [Hsec_eq _ Hagree_out].
  pose proof (eval_sec_deterministic phi c sctx sctx' ctx_src Hsrc Hsrc_from_opt) as Hsame.
  subst ctx_src.
  split.
  - apply Hsec_eq.
  - eapply agree_on_protected_out_implies_agree_on_secret; eauto.
Qed.

(* Needed for composition *)
Lemma opt_safe_dse_core_eval_sec_sound :
  opt_eval_sec_sound opt_safe_dse_core.
Proof.
  unfold opt_eval_sec_sound, opt_safe_dse_core.
  intros phi sctx sctx' [c out] Hsrc.
  destruct sctx as [[v se] t].
  destruct sctx' as [[v' se'] t'].
  simpl in *.
  pose proof (Eval_proj_sec_trace phi (v, se, t) c (v', se', t') Hsrc) as Heval.
  pose proof (safe_dse_helper_sound phi c
    (VarSet.union out (sec_post c se))
    v v v' se (agree_on_refl _ _) Heval) as Hsound.
  destruct Hsound as [v_opt [Hopt _]].
  destruct (Eval_lift_trace_sec phi v
    (safe_dse_helper c (VarSet.union out (sec_post c se)) se)
    v_opt Hopt se t) as [sec_opt [trace_opt Hsec_opt]].
  exists (v_opt, sec_opt, trace_opt).
  exact Hsec_opt.
Qed.

(** * 4. Trace Preservation (eval_trace / is_safe_pgm) *)

(* eval_trace only updated var that occur in the command. *) 
(* Variables not mentioned in the optimized command are unchanged,
   so public agreement for them follows from initial agreement. *)
Lemma eval_trace_frame : forall phi ctx c ctx',
    eval_trace phi ctx c ctx' ->
    forall x,  ~ VarSet.In x (vars_in_cmd c) -> (val_of ctx') $? x = (val_of ctx) $? x.
Proof.
    induction 1; simpl in *; intros.
    all: try (destruct (x ==v x0); [VarSetDecide.fsetdec | apply lookup_add_ne; congruence]).
    all: try (apply IHeval_trace; VarSetDecide.fsetdec).
    all: try (rewrite IHeval_trace2 by VarSetDecide.fsetdec;
      apply IHeval_trace1; VarSetDecide.fsetdec).
    all: reflexivity.
Qed.

(* Every traced execution of safe_dse_helper can be matched to an evaluation of the source program with
   the same trace and the same out *)
Lemma opt_safe_dse_helper_trace_complete : forall phi c out ctx ctx_opt secrets,
  eval_trace phi ctx (safe_dse_helper c out secrets) ctx_opt ->
  exists ctx_src,
    eval_trace phi ctx c ctx_src /\
    trace_coincide out ctx_src ctx_opt.
Proof.
  intros phi c out [v t] [v_opt t_opt] secrets Hopt.
  destruct (Eval_lift_sec phi v t (safe_dse_helper c out secrets) v_opt t_opt Hopt secrets)
    as [se_opt Hopt_sec].
  pose proof (safe_dse_helper_sec_complete phi c out secrets
    (v, secrets, t) (v_opt, se_opt, t_opt)
    (sec_env_sub_refl secrets) Hopt_sec) as Hcomplete.
  destruct Hcomplete as [ctx_src_sec [Hsrc_sec Hcoin_sec]].
  exists (sec_val_of ctx_src_sec, sec_trace_of ctx_src_sec).
  split.
  - exact (Eval_proj_sec phi (v, secrets, t) c ctx_src_sec Hsrc_sec).
  - destruct Hcoin_sec as [_ Htrace Hagree].
    constructor; simpl; exact Htrace || exact Hagree.
Qed.

(** ** Main theorem for non inference preservation *)
Lemma opt_safe_dse_core_preserves_safe_pgm : forall phi p secrets,
    is_safe_pgm phi p secrets ->
    is_safe_pgm phi (opt_safe_dse_core p secrets) secrets.
Proof.
  unfold is_safe_pgm, opt_safe_dse_core in *.
  intros phi [c out] secrets [secrets' Hni].
  simpl in *.
  exists (VarSet.union secrets
    (vars_in_cmd (safe_dse_helper c (VarSet.union out (sec_post c secrets)) secrets))).
  unfold non_inference in *.
  intros v1 v2 t_in final_v1 final_v2 trace1 trace2 Hagree Hopt_eval1 Hopt_eval2.

  pose proof (opt_safe_dse_helper_trace_complete _ _ _ _ _ _ Hopt_eval1)
    as Htrace_complete1.
  pose proof (opt_safe_dse_helper_trace_complete _ _ _ _ _ _ Hopt_eval2)
    as Htrace_complete2.
  destruct Htrace_complete1 as [[v1_out trace1_out] [Heval1 Hcoin1]].
  destruct Hcoin1 as [Htrace1 Hagree1].
  destruct Htrace_complete2 as [[v2_out trace2_out] [Heval2 Hcoin2]].
  destruct Hcoin2 as [Htrace2 Hagree2].
  simpl in *.

  specialize (Hni v1 v2 t_in v1_out v2_out trace1_out trace2_out).
  specialize (Hni Hagree Heval1 Heval2).
  split.
  - destruct Hni as [Htrace_equal _].
    congruence.
  - unfold agree_on_public.
    intros x Hx.
    pose proof (eval_trace_frame _ _ _ _ Hopt_eval1 x) as Hframe1.
    pose proof (eval_trace_frame _ _ _ _ Hopt_eval2 x) as Hframe2.
    simpl in *.
    rewrite Hframe1.
    rewrite Hframe2.
    + apply Hagree.
      VarSetDecide.fsetdec.
    + VarSetDecide.fsetdec.
    + VarSetDecide.fsetdec.
Qed.

(** * 5. Putting the Core Proof Together *)

Theorem opt_safe_dse_core_secure : forall phi,
  is_safe_opt phi opt_safe_dse_core.
Proof.
  intros phi.
  unfold is_safe_opt.
  split.
  - apply opt_safe_dse_core_preserves_safe_pgm.
  - apply opt_safe_dse_core_keeps_secrets_secret.
Qed.


(** * 6. Putting it all together to prove dse is secure *)

Theorem opt_safe_dse_secure : forall phi,
  is_safe_opt phi opt_safe_dse.
Proof.
  intros phi.
  change (is_safe_opt phi (compose_opt opt_unskip opt_safe_dse_core)).
  eapply is_safe_opt_compose.
  - apply opt_safe_dse_core_secure.
  - apply opt_unskip_secure.
  - apply opt_safe_dse_core_eval_sec_sound.
Qed.
