Require Import Map.
Require Import VarSets.
Require Import Language.Main.
Require Import Language.Analysis.
Require Import Language.Optimizations.Safe.DSE.
Require Import Proofs.Analysis.LivenessProofs.
Require Import Proofs.safe_DSE.SecretPreservation.
Require Import Proofs.VarSetAgreement.
Require Import Proofs.unskip.Soundness.
Require Import Proofs.EvalEquivalence.

(* This file proves semantic soundness for the safe DSE optimization pipeline.
   The key local result is that `safe_dse_helper` can replay any source
   execution while preserving agreement on the requested outputs; the remaining
   lemmas package that result for whole programs and for the security-aware
   evaluator used by the top-level optimization theorems. *)

(* Plain evaluation inherits the liveness coincidence theorem by lifting a
   source run into the security-and-trace semantics, applying the stronger
   coincidence result there, then projecting back to ordinary evaluation. *)
Lemma eval_liveness_coincidence: forall c out v1 v2 v1',
  eval v1 c v1' ->
  agree_on (liveness c out) v1 v2 ->
  exists v2',
    eval v2 c v2' /\
    agree_on out v1' v2'.
Proof.
  intros c out v1 v2 v1' Heval Hagree.
  destruct (Eval_lift_trace_sec v1 c v1' Heval senv_mk0 nil)
    as [sec1' [trace1' Heval1_sec]].
  pose proof (eval_sec_liveness_coincidence
    c out
    (v1, senv_mk0, nil)
    (v2, senv_mk0, nil)
    (v1', sec1', trace1')
    Heval1_sec
    (fun x => eq_refl)
    eq_refl
    Hagree) as Hcoincide.
  destruct Hcoincide as [ctx2_out [Heval2_sec Hcoincide_out]].
  exists (sec_val_of ctx2_out).
  split.
   - exact (Eval_proj_sec_trace (v2, senv_mk0, nil) c ctx2_out Heval2_sec).
   - exact (sec_coincide_vals _ _ _ Hcoincide_out).
Qed.

(* Local soundness for safe DSE: starting from any valuation that agrees on the
   variables live for `out`, the optimized command can reproduce the source run
   and still agree on `out` at the end. The proof follows the source big-step
   derivation and uses the security side-condition to justify keeping writes to
   dead-but-secret-dependent destinations. *)
Lemma safe_dse_helper_sound: forall c out v1 v2 v1' secrets,
  agree_on (liveness c out) v1 v2 ->
  eval v1 c v1' ->
  exists v2',
    eval v2 (safe_dse_helper c out secrets) v2' /\
    agree_on out v1' v2'.
Proof.
  intros c out v1 v2 v1' secrets H_agree H.
  revert out secrets v2 H_agree.
  induction H; intros out secrets v_2 H_agree.
  - eexists. split; [econstructor | exact H_agree].
  - simpl in *.
    destruct (VarSet.mem x out) eqn:Hx.
    + assert (Ha: interp_arith e v_2 = a).
      { rewrite <- H. apply interp_arith_agree.
        eapply agree_on_subset; [| apply agree_on_sym; exact H_agree].
        VarSetDecide.fsetdec. }
      exists (v_2 $+ (x, a)). split.
      * apply EvalAssign with (v := v_2). simpl. exact Ha.
      * eapply agree_on_written_update; exact H_agree.
    + destruct (sec_lookup secrets x) eqn:Hsecret;
        destruct (interp_sec e secrets) eqn:Hlevel.
      * exists v_2. split; [constructor |].
        eapply agree_on_dead_update_left; eauto.
      * exists (v_2 $+ (x, interp_arith e v_2)). split.
        -- apply EvalAssign. reflexivity.
        -- eapply agree_on_dead_update_both; eauto.
      * exists (v_2 $+ (x, interp_arith e v_2)). split.
        -- apply EvalAssign. reflexivity.
        -- eapply agree_on_dead_update_both; eauto.
      * exists (v_2 $+ (x, interp_arith e v_2)). split.
        -- apply EvalAssign. reflexivity.
        -- eapply agree_on_dead_update_both; eauto.
  - simpl in *.
    destruct (VarSet.mem x out) eqn:Hx.
    + assert (Hcond: interp_arith cond v_2 = c) by solve_dse_cmov_interp H_agree.
      assert (Ha1: interp_arith e1 v_2 = a1) by solve_dse_cmov_interp H_agree.
      assert (Ha2: interp_arith e2 v_2 = a2) by solve_dse_cmov_interp H_agree.
      exists (v_2 $+ (x, a1)). split.
      * eapply EvalCmovTrue with (v := v_2); eassumption.
      * eapply agree_on_written_update; exact H_agree.
    + destruct (sec_lookup secrets x) eqn:Hsecret;
        destruct (join_sec (interp_sec cond secrets)
          (join_sec (interp_sec e1 secrets) (interp_sec e2 secrets))) eqn:Hlevel.
      { exists v_2. split.
        - apply EvalSkip.
        - eapply agree_on_dead_update_left; eauto. }
      all: destruct (interp_arith cond v_2) eqn:Hcond2;
        [ exists (v_2 $+ (x, interp_arith e2 v_2)); split;
          [ eapply EvalCmovFalse with (v := v_2) (a1 := interp_arith e1 v_2); eauto
          | eapply agree_on_dead_update_both; eauto ]
        | exists (v_2 $+ (x, interp_arith e1 v_2)); split;
          [ eapply EvalCmovTrue with (v := v_2) (c := S n)
              (a2 := interp_arith e2 v_2); eauto; discriminate
          | eapply agree_on_dead_update_both; eauto ] ].
  - simpl in *.
    destruct (VarSet.mem x out) eqn:Hx.
    + assert (Hcond: interp_arith cond v_2 = 0) by solve_dse_cmov_interp H_agree.
      assert (Ha1: interp_arith e1 v_2 = a1) by solve_dse_cmov_interp H_agree.
      assert (Ha2: interp_arith e2 v_2 = a2) by solve_dse_cmov_interp H_agree.
      exists (v_2 $+ (x, a2)). split.
      * eapply EvalCmovFalse with (v := v_2); eassumption.
      * eapply agree_on_written_update; exact H_agree.
    + destruct (sec_lookup secrets x) eqn:Hsecret;
        destruct (join_sec (interp_sec cond secrets)
          (join_sec (interp_sec e1 secrets) (interp_sec e2 secrets))) eqn:Hlevel.
      { exists v_2. split.
        - apply EvalSkip.
        - eapply agree_on_dead_update_left; eauto. }
      all: destruct (interp_arith cond v_2) eqn:Hcond2;
        [ exists (v_2 $+ (x, interp_arith e2 v_2)); split;
          [ eapply EvalCmovFalse with (v := v_2) (a1 := interp_arith e1 v_2); eauto
          | eapply agree_on_dead_update_both; eauto ]
        | exists (v_2 $+ (x, interp_arith e1 v_2)); split;
          [ eapply EvalCmovTrue with (v := v_2) (c := S n)
              (a2 := interp_arith e2 v_2); eauto; discriminate
          | eapply agree_on_dead_update_both; eauto ] ].
  - simpl in *.
    destruct (IHeval1 (liveness c2 out) secrets v_2 H_agree)
      as [v_mid2 [H_mid2 H_agree_mid]].
    destruct (IHeval2 out (sec_post c1 secrets) v_mid2 H_agree_mid)
      as [v_out2 [H_out2 H_agree_out]].
    exists v_out2. split; [| exact H_agree_out].
    eapply EvalSequence; [exact H_mid2 | exact H_out2].
  - simpl in *.
    assert (Hcond: interp_arith e v_2 = c).
    { rewrite <- H. apply interp_arith_agree.
      eapply agree_on_subset; [| apply agree_on_sym; exact H_agree].
      VarSetDecide.fsetdec. }
    destruct (IHeval out secrets v_2) as [v2' [H2' H_agree2']].
    { eapply agree_on_subset; [| exact H_agree]. VarSetDecide.fsetdec. }
    exists v2'. split.
    + eapply EvalIfTrue; [simpl; exact Hcond | exact H0 | exact H2'].
    + exact H_agree2'.
  - simpl in H_agree |- *.
    assert (Hcond: interp_arith e v_2 = 0).
    { rewrite <- H. apply interp_arith_agree.
      eapply agree_on_subset; [| apply agree_on_sym; exact H_agree].
      VarSetDecide.fsetdec. }
    destruct (IHeval out secrets v_2) as [v2' [H2' H_agree2']].
    { eapply agree_on_subset; [| exact H_agree]. VarSetDecide.fsetdec. }
    exists v2'. split.
    + eapply EvalIfFalse; [simpl; exact Hcond | exact H2'].
    + exact H_agree2'.
  - assert (Hwhile : eval v (While e body) v'').
    { eapply EvalWhileTrue; eauto. }
    destruct (eval_liveness_coincidence (While e body) out v v_2 v'' Hwhile H_agree)
      as [v_while2 [H_while2 H_agree_while2]].
    exists v_while2. split; assumption.
  - assert (Hwhile : eval v (While e body) v).
    { eapply EvalWhileFalse; eauto. }
     destruct (eval_liveness_coincidence (While e body) out v v_2 v Hwhile H_agree)
       as [v_while2 [H_while2 H_agree_while2]].
      exists v_while2. split; assumption.
Qed.

(* Plain soundness for the core pass follows immediately from the local helper
   theorem instantiated with identical source and target initial valuations. *)
Lemma opt_safe_dse_core_sound : forall pgm secrets v v',
  eval v (cmd_of pgm) v' ->
  exists v_opt,
    eval v (cmd_of (opt_safe_dse_core pgm secrets)) v_opt.
Proof.
  intros [c out] secrets v v' Heval.
  simpl.
  destruct (safe_dse_helper_sound
    c (VarSet.union out (sec_post c secrets)) v v v' secrets (agree_on_refl _ _) Heval)
    as [v_opt [Hopt _]].
  exists v_opt.
  exact Hopt.
Qed.

(* Program-level packaging of the local helper theorem for the core pass: the
   optimized core command both evaluates and preserves agreement on the
   protected outputs used by safe DSE. *)
Lemma opt_safe_dse_core_sound_agree : forall pgm secrets v v',
  eval v (cmd_of pgm) v' ->
  exists v_opt,
    eval v (cmd_of (opt_safe_dse_core pgm secrets)) v_opt /\
    agree_on (protected_out pgm secrets) v' v_opt.
Proof.
  intros [c out] secrets v v' Heval.
  simpl.
  exact (safe_dse_helper_sound c (VarSet.union out (sec_post c secrets)) v v v' secrets
    (agree_on_refl _ _) Heval).
Qed.

(* Program-level soundness for the full optimization: first run the safe DSE
   helper on the protected output set, then remove administrative `Skip`s via
   the `unskip` soundness theorem, and finally restrict the resulting agreement
   back to the original program outputs. *)
Lemma opt_safe_dse_sound : forall pgm secrets v v',
  eval v (cmd_of pgm) v' ->
  exists v_opt,
    eval v (cmd_of (opt_safe_dse pgm secrets)) v_opt /\
    agree_on (output_of pgm) v' v_opt.
Proof.
  intros pgm secrets v v' Heval.
  unfold opt_safe_dse.
  destruct (opt_safe_dse_core_sound_agree pgm secrets v v' Heval)
    as [v_dse [Hdse_eval Hdse_agree]].

  apply opt_unskip_sound in Hdse_eval.
  eexists.
  split; [exact Hdse_eval |].
  eapply agree_on_subset; [| exact Hdse_agree].
  simpl. unfold VarSet.Subset. intros x Hx.
  apply VarSet.union_spec. left. exact Hx.
Qed.

(* The core optimization also preserves the richer evaluation relation with
   dynamic security state and traces. Reuse the plain soundness lemma to obtain
   an optimized valuation, then lift that run back into the security semantics. *)
Lemma opt_safe_dse_core_eval_sec_sound :
  opt_eval_sec_sound opt_safe_dse_core.
Proof.
  unfold opt_eval_sec_sound, opt_safe_dse_core.
  intros sctx sctx' [c out] Hsrc.
  destruct sctx as [[v se] t].
  simpl in *.
  pose proof (Eval_proj_sec_trace (v, se, t) c sctx' Hsrc) as Heval.
  pose proof (opt_safe_dse_core_sound (c, out) se v (sec_val_of sctx') Heval) as Hsound.
  destruct Hsound as [v_opt Hopt].
  destruct (Eval_lift_trace_sec v
    (safe_dse_helper c (VarSet.union out (sec_post c se)) se)
    v_opt Hopt se t) as [sec_opt [trace_opt Hsec_opt]].
  exists (v_opt, sec_opt, trace_opt).
  exact Hsec_opt.
Qed.
