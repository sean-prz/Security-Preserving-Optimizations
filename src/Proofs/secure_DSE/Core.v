Require Import Language.Main.
Require Import Language.Optimizations.Secure.DSE.
Require Import Language.Optimizations.Secure.Unskip.
Require Import Proofs.secure_DSE.SecretPreservation.
Require Import Proofs.secure_DSE.Soundness.
Require Import Proofs.secure_DSE.NonInterference.
Require Import Proofs.unskip.Core.


(* This file is the top-level proof packaging for the secure DSE pipeline.
   It combines the core DSE pass proofs, then lifts them through the
   final `unskip` cleanup pass used by `opt_secure_DSE`. *)

(* The core secure DSE pass is secure because it preserves semantics and does not
   expose or reclassify secrets. *)
Theorem opt_secure_DSE_core_secure :
  is_secure_opt opt_secure_DSE_core.
Proof.
  unfold is_secure_opt.
  split.
  - apply opt_secure_DSE_core_preserves_secure_pgm.
  - apply opt_secure_DSE_core_keeps_secrets_secret.
Qed.

(* The full secure DSE pipeline is secure: compose the core pass with `unskip`,
   reuse security of each pass, and discharge the composition side-condition
   with the evaluation-level security soundness theorem for the core pass. *)
Theorem opt_secure_DSE_secure :
  is_secure_opt opt_secure_DSE.
Proof.
  change (is_secure_opt (compose_opt opt_unskip opt_secure_DSE_core)).
  eapply is_secure_opt_compose.
  - apply opt_secure_DSE_core_secure.
  - apply opt_unskip_secure.
  - apply opt_secure_DSE_core_eval_sec_sound.
Qed.
