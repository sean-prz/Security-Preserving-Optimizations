Require Import Examples.Programs.
Require Import Map.
Require Import VarSets.
Require Import Language.Main.
Require Import Language.Optimizations.Insecure.DSE.


Example insecure2 := single_out_pgm secret_overwritten_with_const "y".

Example sctx:  sec_context := ($0 $+ ("x", 123), senv_mk1 "x" Secret, nil).
Example sctx': sec_context := ($0 $+ ("x", 123) $+ ("x", 0), senv_mk2 "x" "x" Secret Public, nil).

(* Counterexample outline:
   the source writes 0 into secret x, while insecure DSE drops that write and
   returns Skip. We evaluate both from the same secure input and show that the
   post-security contexts disagree on x, contradicting secret preservation. *)
Theorem insecureDSE_insecure : ~ is_secure_opt (fun p _ => opt_dse p).
Proof.
  unfold is_secure_opt.
  intros [_ H0].
  unfold opt_keeps_secrets_secret in H0.
  specialize (H0 sctx sctx' sctx insecure2 (single_out_pgm Skip "y")).
  unfold insecure2, secret_overwritten_with_const, opt_dse in H0.
  simpl in H0.
  assert (Hpre1 : eval_sec sctx ("x" <- 0) sctx') by (constructor; reflexivity).
  assert (Hpre2 : eval_sec sctx Skip sctx) by constructor.
  specialize (H0 eq_refl Hpre1 Hpre2 "x").
  destruct H0 as [Hcontra _].
  simpl in Hcontra. discriminate.
Qed.
