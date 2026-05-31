Require Import Language.Main.
Require Import Language.Optimizations.Secure.Unskip.
Require Import Proofs.unskip.NonInterference.
Require Import Proofs.unskip.SecretPreservation.


Theorem opt_unskip_secure :
  is_secure_opt opt_unskip.
Proof.
  unfold is_secure_opt.
  split.
  - apply opt_unskip_preserves_secure_pgm.
  - apply opt_unskip_keeps_secrets_secret.
Qed.
