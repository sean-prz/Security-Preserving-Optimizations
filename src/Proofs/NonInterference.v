Require Import Map.
Require Import VarSets.
Require Import Language.Main.
Require Import Proofs.SecLookup.
From Stdlib Require Import Program.Equality.


(* If two valuations agree on public data, then the interpretation of any public
expression should be the same. *)
Lemma interp_sec_public_agree : forall e se v1 v2,
  agree_on_public se v1 v2 ->
  interp_sec e se = Public ->
  interp_arith e v1 = interp_arith e v2.
Proof.
  induction e; cbn in *;
  intros se v1 v2 Hagree Hsec.
  - (* const *)
    reflexivity.
  - (* var *)
    apply lookup_simpl_pub in Hsec.
    specialize (Hagree s Hsec).
    rewrite Hagree. reflexivity.
  - (* binop *)
    unfold agree_on_public in Hagree.
    destruct (interp_sec e1 se) eqn:Hsec1;
    destruct (interp_sec e2 se) eqn:Hsec2;
    simpl in Hsec; try discriminate.
    rewrite (IHe1 se v1 v2 Hagree Hsec1).
    rewrite (IHe2 se v1 v2 Hagree Hsec2).
    reflexivity.
Qed.

(* Below are two helper lemmas to reason about loop invariants. 
the invariant represents all the reached variables after reaching fixpoint over a while cmd *)

(* If two valuations agree on public before executing an iteration of a
loop, then they agree on the loop invariant environment (se_inv) *)
Lemma agree_on_public_inv : forall se se_inv v1 v2,
(*se_inv is a subset of se*)
  VarSet.Equal (join_sec_env se se_inv) se_inv -> 
  agree_on_public se v1 v2 ->
  agree_on_public se_inv v1 v2.
Proof.
  intros se se_inv v1 v2 Hjoin Hagree.
  unfold agree_on_public in *. intros x Hpub.
  apply Hagree.
  apply lookup_simpl_pub.
  apply join_sec_public_thn with se_inv.
  unfold sec_lookup.
  rewrite Hjoin. 
  apply lookup_simpl_pub.
  exact Hpub.
Qed.

(* If two valuations agree on the output of the body of a loop, then they
agree on the loop invariant environment (se_inv) *)
Lemma agree_on_public_body_inv : forall se_inv se_body v1 v2,
(* se_inv is a subset of se_body*)
  VarSet.Equal (join_sec_env se_inv se_body) se_inv ->
  agree_on_public se_body v1 v2 ->
  agree_on_public se_inv v1 v2.
Proof.
  intros.
  eapply agree_on_public_inv; [|exact H0].
  unfold join_sec_env in *. VarSetDecide.fsetdec.
Qed.

(* Cmov doesn't create a trace event. We can prove its non_interference property*)
Lemma cmov_non_interference : forall se x cond e1 e2 level,
  join_sec (interp_sec cond se) (join_sec (interp_sec e1 se) (interp_sec e2 se)) = level ->
  non_interference se (Cmov x cond e1 e2) (update_sec se x level).
Proof.
  unfold non_interference.
  Ltac resolve_cmov_maps :=
    unfold agree_on_public, sec_lookup in *; intros param Hparam;
    autorewrite with core in *; cbn in *.
  intros se x cond e1 e2 level Hjoin
    v1 v2 t_in final_v1 final_v2 trace1 trace2 Hagree Heval1 Heval2.
  split.
  { inversion Heval1; inversion Heval2; subst; reflexivity. }
  inversion Heval1; inversion Heval2; subst; resolve_cmov_maps.
  all: destruct (param ==v x);
  [ subst; destruct (x ==v x); [ | congruence ];
    autorewrite with core in *;
    destruct (interp_sec cond se) eqn:Hcond_sec;
    destruct (interp_sec e1 se) eqn:He1_sec;
    destruct (interp_sec e2 se) eqn:He2_sec;
    cbn in Hparam; try VarSetDecide.fsetdec;
    try (apply f_equal; eapply interp_sec_public_agree; eauto);
    try (assert (Hcond_val: interp_arith cond v1 = interp_arith cond v2) by (eapply interp_sec_public_agree; eauto); congruence)
  | destruct (x ==v param); [ congruence | ];
    autorewrite with core in *; apply Hagree;
    rewrite <- VarSet.mem_spec in *; rewrite simplify_update_ne in Hparam; auto ].
Qed.

(* A program that is constant time according to our definition should satisfy
non-interference. *) 
Theorem ct_cmd_soundness : forall se c se_out,
  ct_cmd se c se_out ->
  non_interference se c se_out.
Proof.
  Ltac invert_evals :=
    inversion Heval1; inversion Heval2; subst.

  Ltac resolve_maps :=
    unfold agree_on_public, sec_lookup in *; intros param Hparam;
    autorewrite with core in *; cbn in *.


  intros se c se_out Hct.
  unfold non_interference.
  induction Hct;
  intros v1 v2 t_in final_v1 final_v2 trace1 trace2 Hagree Heval1 Heval2.
  - (* Skip*)
    split; invert_evals; [reflexivity | assumption].
  - (* Assign*)
    split; invert_evals; [reflexivity |].
      resolve_maps. destruct (param ==v x).
      + subst. destruct (x ==v x); [ | congruence ].
        autorewrite with core in *. apply f_equal.
        apply lookup_simpl_pub in Hparam.
        eapply interp_sec_public_agree; eauto.
        destruct (interp_sec e se).
        * reflexivity.
        * simpl in Hparam.
          unfold sec_lookup in Hparam.
          rewrite VarSetEqProps.add_mem_1 in Hparam.
          discriminate.
      + destruct (x ==v param); [ congruence | ].
        autorewrite with core in *. apply Hagree.
        destruct (interp_sec e se) eqn:Hinterp_e; simpl in Hparam.
        * rewrite VarSet.remove_spec in Hparam.
          auto.
        * rewrite VarSet.add_spec in Hparam.
          auto.
  - (* Cmov*)
    eapply cmov_non_interference; eauto.
  - (* Sequence *)
    (* Pipeline security properties directly from c1 into c2. *)
    invert_evals. destruct ctx1 as [v1' t1'], ctx3 as [v2' t2'].
    edestruct IHHct1 as [Htrace1 Hmem1]; eauto; subst.
    eapply IHHct2; eauto.
  - (* If*)
    (* Here, If destructs in 4 cases: boolean values interp_arith e v1|v2. 
    they must match, so half of the cases are impossible *)
    assert (Hcond: interp_arith e v1 = interp_arith e v2).
    { eapply interp_sec_public_agree; eauto. }
    invert_evals.
    + (* Case 1: True = True*)
      edestruct IHHct1 as [Htrace Hmem]; eauto.
      split; [exact Htrace |].
      unfold agree_on_public in *. intros x Hpub.
      apply Hmem. (* This Hmem comes from IHHct2, so it uses se_els*)
      apply lookup_simpl_pub. apply lookup_simpl_pub in Hpub.
      eapply join_sec_public_thn. 
      unfold sec_lookup.
      rewrite H0.
      apply Hpub.
    + (* Case 2: True = False (contradiction)*)
      cbn in *.
      rewrite H14 in Hcond.
      congruence.
    + (* Case 3: False = True (contradiction)*)
      cbn in *.
      rewrite H6 in Hcond.
      congruence.
    + (* Case 4: False = False*)
      edestruct IHHct2 as [Htrace Hmem]; eauto.
      split; [exact Htrace |].
      unfold agree_on_public in *. intros x Hpub.
      apply Hmem.
      apply lookup_simpl_pub. apply lookup_simpl_pub in Hpub.
      eapply join_sec_public_els. 
      unfold sec_lookup.
      rewrite H0.
      apply Hpub.
  - (* While*)
    (*Here again, While splits in 4 cases, WhileTrue and WhileFalse, and as in the If case, we must discard impossible cases*)
    (* The initial valuations agree on the loop invariant*)
    assert (Hagree_inv: agree_on_public se_inv v1 v2).
    { eapply agree_on_public_inv; eauto. }
    clear Hagree.

    revert v2 final_v2 trace2 Hagree_inv Heval2.
    dependent induction Heval1.

    + (* EvalTraceWhileTrue*)
      intros v2 final_v2 trace2 Hagree_inv Heval2.
      inversion Heval2; subst; clear Heval2.
      * (* Case 1: Both take True branch*)
        cbn in *.
        destruct ctx' as [v1' t1'].
        match goal with
        | H : eval_trace _ body ?ctx2' |- _ => destruct ctx2' as [v2' t2']
        end.

        edestruct IHHct as [Htrace_body Hmem_body]; eauto.
        subst t2'.

        assert (Hagree_inv_after: agree_on_public se_inv v1' v2').
        { eapply agree_on_public_body_inv; eauto. }
        eauto.

      * (* Case 2: Contradiction : v2 takes the wrong branch*)
        cbn in *.
        (* inversion unified v2 with final_v2 because EvalTraceWhileFalse doesn't change the valuation*)
        assert (Hcond: interp_arith e v1 = interp_arith e final_v2).
        {eapply interp_sec_public_agree; eauto. }
        congruence.

    + (* EvalTraceWhileFalse*)
      intros v2 final_v2 trace2 Hagree_inv Heval2.
      inversion Heval2; subst; clear Heval2.
      * (* Case 3: Contradiction - v1 takes the wrong branch *)
        cbn in *.
        (* inversion unified v1 with final_v1 because EvalTraceWhileFalse doesn't change the valuation*)
        assert (Hcond: interp_arith e final_v1 = interp_arith e v2) by (eapply interp_sec_public_agree; eauto).
        congruence.

      * (* Case 4: Both take False branch*)
        cbn in *.
        eauto.
Qed.


