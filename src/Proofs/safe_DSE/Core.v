Require Import Language.Main.
Require Import Language.Optimizations.Safe.DSE.
Require Import Language.Optimizations.Safe.Unskip.
Require Import Proofs.safe_DSE.SecretPreservation.
Require Import Proofs.safe_DSE.Soundness.
Require Import Proofs.safe_DSE.Noninference.
Require Import Proofs.unskip.Core.


Theorem opt_safe_dse_core_secure :
  is_safe_opt opt_safe_dse_core.
Proof.
  unfold is_safe_opt.
  split.
  - apply opt_safe_dse_core_preserves_safe_pgm.
  - apply opt_safe_dse_core_keeps_secrets_secret.
Qed.

Theorem opt_safe_dse_secure :
  is_safe_opt opt_safe_dse.
Proof.
  change (is_safe_opt (compose_opt opt_unskip opt_safe_dse_core)).
  eapply is_safe_opt_compose.
  - apply opt_safe_dse_core_secure.
  - apply opt_unskip_secure.
  - apply opt_safe_dse_core_eval_sec_sound.
Qed.
