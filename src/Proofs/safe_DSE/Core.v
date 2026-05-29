Require Import Language.Main.
Require Import Language.Optimizations.Safe.DSE.
Require Import Language.Optimizations.Safe.Unskip.
Require Import Proofs.safe_DSE.SecretPreservation.
Require Import Proofs.safe_DSE.Soundness.
Require Import Proofs.safe_DSE.Noninference.
Require Import Proofs.unskip.Core.

(* This file is the top-level proof packaging for the safe DSE pipeline.
   It combines the core DSE pass proofs, then lifts them through the
   final `unskip` cleanup pass used by `opt_safe_dse`. *)


(* The core safe DSE pass is secure because it preserves semantics and does not
   expose or reclassify secrets. *)
Theorem opt_safe_dse_core_secure :
  is_safe_opt opt_safe_dse_core.
Proof.
  unfold is_safe_opt.
  split.
  - apply opt_safe_dse_core_preserves_safe_pgm.
  - apply opt_safe_dse_core_keeps_secrets_secret.
Qed.

(* The full safe DSE pipeline is secure: compose the core pass with `unskip`,
   reuse security of each pass, and discharge the composition side-condition
   with the evaluation-level security soundness theorem for the core pass. *)
Theorem opt_safe_dse_secure :
  is_safe_opt opt_safe_dse.
Proof.
  change (is_safe_opt (compose_opt opt_unskip opt_safe_dse_core)).
  eapply is_safe_opt_compose.
  - apply opt_safe_dse_core_secure.
  - apply opt_unskip_secure.
  - apply opt_safe_dse_core_eval_sec_sound.
Qed.
