Require Import Map.
Require Import Language.Main.
Require Import proofs.SecEnvProofs.
Require Import Coq.Program.Equality.


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
    unfold agree_on_public in Hagree.
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

(* Declare two helper lemmas to reason about loop invariants *)

(* If two valuations agree on public before executing an iteration of a
loop, then they agree on the loop invariant environment (se_inv) *)
Lemma agree_on_public_inv : forall se se_inv v1 v2,
  join_sec_env se se_inv = se_inv ->
  agree_on_public se v1 v2 ->
  agree_on_public se_inv v1 v2.
Proof.
  intros se se_inv v1 v2 Hjoin Hagree.
  unfold agree_on_public in *. intros x Hpub.
  apply Hagree.
  apply join_sec_public_thn with se_inv.
  rewrite Hjoin. exact Hpub.
Qed.
(* If two valuations agree on the output of the body of a loop, then they
agree on the loop invariant environment (se_inv) *)
Lemma agree_on_public_body_inv : forall se_inv se_body v1 v2,
  join_sec_env se_inv se_body = se_inv ->
  agree_on_public se_body v1 v2 ->
  agree_on_public se_inv v1 v2.
Proof.
  intros se_inv se_body v1 v2 Hjoin Hagree.
  unfold agree_on_public in *. intros x Hpub.
  apply Hagree.
  apply join_sec_public_els with se_inv.
  rewrite Hjoin. exact Hpub.
Qed.


(* A program that is constant time according to our definition should satisfy
non-inference. *)
Theorem ct_cmd_soundness : forall phi se c se_out,
  ct_cmd phi se c se_out ->
  non_inference phi se c se_out.
Proof.
  Ltac invert_evals :=
    inversion Heval1; inversion Heval2; subst.

  Ltac resolve_maps :=
    unfold agree_on_public, sec_lookup in *; intros param Hparam;
    autorewrite with core in *; cbn in *.


  intros phi se c se_out Hct.
  unfold non_inference.
  induction Hct;
  intros v1 v2 t_in final_v1 final_v2 trace1 trace2 Hagree Heval1 Heval2.
  - (* Skip *)
    split; invert_evals; [reflexivity | assumption].
  - (* Assign *)
    split; invert_evals; [reflexivity |].
      resolve_maps. destruct (param ==v x).
      + subst. destruct (x ==v x); [ | congruence ].
        autorewrite with core in *. apply f_equal.
        eapply interp_sec_public_agree; eauto.
      + destruct (x ==v param); [ congruence | ].
        autorewrite with core in *. apply Hagree. exact Hparam.
  - (* Cmov *)
    split.
    { invert_evals; reflexivity. }
    invert_evals; resolve_maps; destruct (param ==v x).
    + (* True / True, param = x *)
      subst. destruct (x ==v x); [ | congruence ].
      autorewrite with core in *.
      destruct (interp_sec cond se) eqn:Hcond_sec; destruct (interp_sec e1 se) eqn:He1_sec; destruct (interp_sec e2 se) eqn:He2_sec;
      cbn in Hparam; try discriminate.
      apply f_equal. eapply interp_sec_public_agree; eauto.
    + (* True / True, param <> x *)
      destruct (x ==v param); [ congruence | ].
      autorewrite with core in *. apply Hagree. exact Hparam.
    + (* True / False, param = x *)
      subst. destruct (x ==v x); [ | congruence ].
      autorewrite with core in *.
      destruct (interp_sec cond se) eqn:Hcond_sec; destruct (interp_sec e1 se) eqn:He1_sec; destruct (interp_sec e2 se) eqn:He2_sec;
      cbn in Hparam; try discriminate.
      assert (Hcond_val: interp_arith cond v1 = interp_arith cond v2) by (eapply interp_sec_public_agree; eauto).
      congruence.
    + (* True / False, param <> x *)
      destruct (x ==v param); [ congruence | ].
      autorewrite with core in *. apply Hagree. exact Hparam.
    + (* False / True, param = x *)
      subst. destruct (x ==v x); [ | congruence ].
      autorewrite with core in *.
      destruct (interp_sec cond se) eqn:Hcond_sec; destruct (interp_sec e1 se) eqn:He1_sec; destruct (interp_sec e2 se) eqn:He2_sec;
      cbn in Hparam; try discriminate.
      assert (Hcond_val: interp_arith cond v1 = interp_arith cond v2) by (eapply interp_sec_public_agree; eauto).
      congruence.
    + (* False / True, param <> x *)
      destruct (x ==v param); [ congruence | ].
      autorewrite with core in *. apply Hagree. exact Hparam.
    + (* False / False, param = x *)
      subst. destruct (x ==v x); [ | congruence ].
      autorewrite with core in *.
      destruct (interp_sec cond se) eqn:Hcond_sec; destruct (interp_sec e1 se) eqn:He1_sec; destruct (interp_sec e2 se) eqn:He2_sec;
      cbn in Hparam; try discriminate.
      apply f_equal. eapply interp_sec_public_agree; eauto.
    + (* False / False, param <> x *)
      destruct (x ==v param); [ congruence | ].
      autorewrite with core in *. apply Hagree. exact Hparam.
  - (* AssignCall*)
    (* Unify duplicated function environments and extract contexts. *)
    invert_evals. rewrite H in H10, H22; inversion H10; inversion H22; subst; clear H10 H22.
    destruct ctx' as [fv1 t1], ctx'0 as [fv2 t2]. cbn in *.
    (* Verify trace-independence of function arguments. *)
    assert (Hargs: agree_on_public ($0 $+ (x6, interp_sec e1 se) $+ (x7, interp_sec e2 se))
           ($0 $+ (x6, interp_arith e1 v1) $+ (x7, interp_arith e2 v1))
           ($0 $+ (x6, interp_arith e1 v2) $+ (x7, interp_arith e2 v2))).
    { resolve_maps. destruct (x7 ==v param); destruct (x6 ==v param);
      subst; autorewrite with core in *; try reflexivity;
      apply f_equal; eapply interp_sec_public_agree; eauto. }
    (* Extract caller trace/memory safety and verify return variable assignment. *)
    edestruct IHHct as [Htrace Hbody]; eauto.
    split; [exact Htrace |].
    resolve_maps. destruct (x ==v param).
    + subst. autorewrite with core in *.
      assert (Hpub: fv1 $? y1 = fv2 $? y1) by (apply Hbody; exact Hparam).
      rewrite H14, H26 in Hpub. inversion Hpub. reflexivity.
    + (* Any other variable *)
      autorewrite with core in *. apply Hagree. exact Hparam.
  - (* Sequence *)
    (* Pipeline safety properties directly from c1 into c2. *)
    invert_evals. destruct ctx1 as [v1' t1'], ctx3 as [v2' t2'].
    edestruct IHHct1 as [Htrace1 Hmem1]; eauto; subst.
    eapply IHHct2; eauto.
  - (* If *)
    assert (Hcond: interp_arith e v1 = interp_arith e v2).
    { eapply interp_sec_public_agree; eauto. }
    invert_evals.
    + (* Case 1: True / True *)
      edestruct IHHct1 as [Htrace Hmem]; eauto.
      split; [exact Htrace |].
      unfold agree_on_public in *. intros x Hpub.
      apply Hmem. (* This Hmem comes from IHHct2, so it uses se_els *)
      eapply join_sec_public_thn. exact Hpub.
    + (* Case 2: True / False (IMPOSSIBLE) *)
      cbn in *.
      rewrite H14 in Hcond.
      congruence.
    + (* Case 3: False / True (IMPOSSIBLE) *)
      cbn in *.
      rewrite H6 in Hcond.
      congruence.
    + (* Case 4: False / False *)
      edestruct IHHct2 as [Htrace Hmem]; eauto.
      split; [exact Htrace |].
      (* Memory safety for the joined environment *)
      unfold agree_on_public in *. intros x Hpub.
      apply Hmem.
      eapply join_sec_public_els. exact Hpub.
  - (* While *)
    (* The initial valuations agree on the loop invariant environment *)
    assert (Hagree_inv: agree_on_public se_inv v1 v2).
    { eapply agree_on_public_inv; eauto. }
    clear Hagree.

    revert v2 final_v2 trace2 Hagree_inv Heval2.
    dependent induction Heval1.

    + (* EvalWhileTrue *)
      intros v2 final_v2 trace2 Hagree_inv Heval2.
      inversion Heval2; subst; clear Heval2.
      * (* Case 1: Both take True branch *)
        cbn in *.
        destruct ctx' as [v1' t1'].
        match goal with
        | H : eval phi _ body ?ctx2' |- _ => destruct ctx2' as [v2' t2']
        end.

        edestruct IHHct as [Htrace_body Hmem_body]; eauto.
        subst t2'.

        assert (Hagree_inv_after: agree_on_public se_inv v1' v2').
        { eapply agree_on_public_body_inv; eauto. }
        eauto.

      * (* Case 2: Contradiction - v1 True, v2 False *)
        cbn in *.
        (* inversion unified v2 with final_v2 because EvalWhileFalse doesn't change the valuation *)
        assert (Hcond: interp_arith e v1 = interp_arith e final_v2).
        {eapply interp_sec_public_agree; eauto. }
        congruence.

    + (* EvalWhileFalse *)
      intros v2 final_v2 trace2 Hagree_inv Heval2.
      inversion Heval2; subst; clear Heval2.
      * (* Case 3: Contradiction - v1 False, v2 True *)
        cbn in *.
        (* inversion unified v1 with final_v1 because EvalWhileFalse doesn't change the valuation *)
        assert (Hcond: interp_arith e final_v1 = interp_arith e v2) by (eapply interp_sec_public_agree; eauto).
        congruence.

      * (* Case 4: Both take False branch and exit *)
        cbn in *.
        eauto.
Qed.
