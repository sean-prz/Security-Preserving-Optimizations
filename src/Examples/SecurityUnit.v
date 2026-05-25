Require Import Map.
Require Import VarSets.
Require Import Language.Main.
Require Import Proofs.SecLookup.
Require Import Examples.Programs.
Require Import Language.Security.
From Stdlib Require Import List.
Import ListNotations.

Ltac crush_security :=
  unfold interp_sec, sec_lookup;
  cbn; autorewrite with core; reflexivity.

(* `eval_sec`: copying a secret value taints the destination as `Secret`. *)
Example eval_sec_secret_copy_taints_x :
  eval_sec $0
    (($0 $+ ("secret", 7)), senv_mk1 "secret" Secret, nil)
    secret_copy
    (($0 $+ ("secret", 7) $+ ("x", 7)), senv_mk2 "secret" "x" Secret Secret, nil).
Proof.
  econstructor; crush_security.
Qed.

(* `eval_sec`: when the source has no security label, the destination defaults to `Public`. *)
Example eval_sec_secret_copy_defaults_to_public :
  eval_sec $0
    (($0 $+ ("secret", 7)), senv_mk0, nil)
    secret_copy
    (($0 $+ ("secret", 7) $+ ("x", 7)), senv_mk1 "x" Public, nil).
Proof.
  econstructor; crush_security.
Qed.

(* `eval_sec`: overwriting a secret-labeled variable with a constant makes it Public. *)
Example eval_sec_secret_overwritten_with_const_is_public :
  eval_sec $0
    (($0 $+ ("x", 7)), senv_mk1 "x" Secret, nil)
    secret_overwritten_with_const
    (($0 $+ ("x", 7) $+ ("x", 0)), senv_mk2 "x" "x" Secret Public, nil).
Proof.
  econstructor; crush_security.
Qed.

(* `eval_sec`: overwriting a secret-labeled variable with a public variable makes it Public. *)
Example eval_sec_secret_overwritten_with_public_var_is_public :
  eval_sec $0
    (($0 $+ ("x", 7) $+ ("flag", 42)), senv_mk2 "x" "flag" Secret Public, nil)
    secret_overwritten_with_public_var
    (($0 $+ ("x", 7) $+ ("flag", 42) $+ ("x", 42)), senv_mk3 "x" "flag" "x" Secret Public Public, nil).
Proof.
  econstructor; crush_security.
Qed.

(* `ct_cmd`: branching on a public guard is accepted by the constant-time checker. *)
Example ct_public_guard_program_ok :
  exists se',
    ct_cmd $0
      (senv_mk1 "flag" Public)
      public_guard_program
      se'.
Proof.
  eexists.
  repeat econstructor; try crush_security; eauto.
Qed.

(* `ct_cmd`: branching on a secret guard is rejected by the constant-time checker. *)
Example ct_secret_guard_program_rejected :
  ~ exists se',
      ct_cmd $0
        (senv_mk1 "secret" Secret)
        secret_guard_program
        se'.
Proof.
  intros [se' Hct].
  inversion Hct; subst.
  unfold interp_sec, sec_lookup in H2.
  cbn in H2.
  autorewrite with core in H2.
  discriminate.
Qed.

(* `ct_cmd`: a public branch may be constant-time, but joining branch labels
still taints `x` as `Secret`. *)
Example ct_branch_join_marks_x_secret :
  exists se',
    ct_cmd $0
      (senv_mk2 "flag" "secret" Public Secret)
      branch_join_program
      se'
    /\ sec_lookup se' "x" = Secret
    /\ sec_lookup se' "flag" = Public.
Proof.
  eexists.
  split.
  - repeat (econstructor; try reflexivity).
  - split; rewrite lookup_join_env; crush_security.
Qed.

Example ct_simple_while_public_ok :
  exists se',
    ct_cmd $0
      (senv_mk1 "x" Public)
      simple_while
      se'.
Proof.
  eexists.
  eapply CtWhile.
  - apply join_sec_env_idempotent.
  - crush_security.
  - econstructor. crush_security.
  - apply (join_sec_env_update_public_right (senv_mk1 "x" Public) "x").
Qed.

Example ct_secret_downgrade_loop_ok :
  exists se',
    ct_cmd $0
      (senv_mk2 "flag" "secret" Public Secret)
      secret_downgrade_loop
      se'.
Proof.
  eexists.
  eapply CtWhile.
  - apply join_sec_env_idempotent.
  - crush_security.
  - econstructor; crush_security. (* Body makes 'secret' Public *)
  (* Preservation: join(Secret, Public) = Secret.
     The invariant perfectly absorbs the downgraded variable! *)
  - apply (join_sec_env_update_public_right (senv_mk2 "flag" "secret" Public Secret) "secret").
Qed.

Example ct_fact_body_public_ok :
  exists se',
    ct_cmd Fact_env
      (senv_mk2 "n" "f" Public Public)
      FactBody
      se'.
Proof.
  eexists.
  unfold FactBody.
  eapply CtSequence.
  - econstructor; crush_security. (* "f" <- 1 *)
  - eapply CtWhile with (se_inv := (senv_mk3 "n" "f" "f" Public Public Public)).
    + apply join_sec_env_idempotent.
    + crush_security.
    + (* The body is a Sequence of two assignments *)
      eapply CtSequence; econstructor; crush_security.
    + VarSetDecide.fsetdec.
Qed.

Example ct_secret_loop_rejected :
  ~ exists se',
    ct_cmd $0
      (senv_mk1 "secret" Secret)
      secret_loop_program
      se'.
Proof.
  (* Assume the checker somehow accepted this dangerous loop *)
  intros [se' Hct].
  inversion Hct; subst.
  (* Simplify the public guard requirement *)
  unfold interp_sec, sec_lookup in H2. cbn in H2.
  (* We need to prove se_inv knows "secret" is Secret. We extract this fact
  directly from the initial bound. *)
  assert (Hleak: sec_lookup (join_sec_env (senv_mk1 "secret" Secret) se') "secret" = sec_lookup se' "secret").
  { unfold sec_lookup. rewrite H1. reflexivity. }
  (* Evaluate the join on the left side using the helper lemma we just built! *)
  rewrite lookup_join_env in Hleak.
  unfold sec_lookup in Hleak at 1. autorewrite with core in *. cbn in *.
  (* H2 is exactly the definition of `sec_lookup se' "secret" = Public`! *)
  fold (sec_lookup se' "secret") in H2.
  rewrite H2 in Hleak.
  discriminate.
Qed.

Example ct_public_to_secret_loop_rejected :
  ~ exists se',
    ct_cmd $0
      (senv_mk2 "secret" "x" Secret Public)
      public_to_secret_loop
      se'.
Proof.
  (* Assume the checker accepted this mutating loop *)
  intros [se' Hct].
  (* Break open the While loop rule *)
  inversion Hct; subst.
  unfold interp_sec in H2; cbn in H2.
  (* Prove that se' knows 'secret' is Secret (extracted from H1) *)
  assert (Hsec: sec_lookup (join_sec_env (senv_mk2 "secret" "x" Secret Public) se') "secret" = sec_lookup se' "secret").
  { unfold sec_lookup. rewrite H1. reflexivity. }
  rewrite lookup_join_env in Hsec.
  unfold sec_lookup in Hsec at 1. cbn in Hsec. autorewrite with core in Hsec.
  (* Destruct forces Coq to realize se' "secret" MUST be Secret, otherwise the
  join would be invalid. *)
  destruct (sec_lookup se' "secret") eqn:Hsecret_val;
  cbn in Hsec; [ discriminate |  ].
  (* Break open the Assign rule inside the body *)
  inversion H4; subst.
  (* The preservation rule (H6) checks if the invariant survived. *)
  assert (Hpres: sec_lookup (join_sec_env se' (update_sec se' "x" (interp_sec "secret" se'))) "x" = sec_lookup se' "x").
  { unfold sec_lookup. rewrite H6. reflexivity. }
  rewrite lookup_join_env in Hpres.
  rewrite H2 in Hpres.
  unfold interp_sec in Hpres. cbn in Hpres.
  rewrite Hsecret_val in Hpres.
  unfold sec_lookup in Hpres at 1. autorewrite with core in Hpres.
  simpl in Hpres.
  rewrite VarSetEqProps.add_mem_1 in Hpres.
  discriminate.
Qed.

(* Prove the old approach is rejected because If guards must be Public *)
Example ct_old_secret_branch_rejected :
  ~ exists se',
      ct_cmd $0
        (senv_mk3 "secret_flag" "data1" "data2" Secret Public Public)
        old_secret_branch
        se'.
Proof.
  intros [se' Hct].
  inversion Hct; subst.
  unfold interp_sec, sec_lookup in H2. cbn in H2.
  autorewrite with core in H2.
  discriminate.
Qed.

(* Prove the new approach is accepted, gracefully propagating the Secret label to "out" *)
Example ct_new_cmov_branch_ok :
  exists se',
      ct_cmd $0
        (senv_mk3 "secret_flag" "data1" "data2" Secret Public Public)
        new_cmov_branch
        se'.
Proof.
  eexists.
  (* CtCmov allows secret conditions and uses join_sec to compute the output label *)
  repeat econstructor; crush_security.
Qed.
