Require Import Examples.Programs.
Require Import Language.Semantics.
Require Import Map.
Require Import VarSets.
Require Import Language.Main.
Require Import Language.Optimizations.Insecure.DSE.
Require Import Proofs.NonInterference.


From Stdlib Require Import Lia.

Print secret_guard_program.

Example insecure1 := single_out_pgm secret_guard_program "x".

Example senv := senv_mk1 "secret" Secret.

Example v1 := $0 $+ ("secret", 1).
Example v2 := $0 $+ ("secret", 0).


Goal ~ (is_secure_pgm insecure1 senv).
Proof.  
    intros H.
    destruct H as [? Hct].
    unfold non_interference, insecure1 in Hct; simpl in Hct.
    specialize (Hct v1 v2 nil (v1 $+ ("x",1)) (v2 $+ ("x", 0)) (cons (Branch true)  nil) (cons (Branch false) nil)).
    assert (Hpre1 :  agree_on_public senv v1 v2).
    {
     unfold agree_on_public, v1, v2.
     intros.
     unfold sec_lookup, senv in H.
     destruct (var_eq x0 "secret") eqn:Hsecret; subst.
     + simpl in H.
        rewrite VarSet.add_spec in H.
        VarSetDecide.fsetdec.
     +  repeat rewrite lookup_add_ne by congruence.
        reflexivity.
    }
    assert (Hpre2 : eval_trace (v1, nil) secret_guard_program
            (v1 $+ ("x", 1), (Branch true :: nil)%list)).
    {
        eapply EvalTraceIfTrue.
        simpl.
        unfold v1.
        rewrite lookup_add_eq; reflexivity.
        lia.
        constructor.
        reflexivity.
    }
    assert (Hpre3 : eval_trace (v2, nil) secret_guard_program
            (v2 $+ ("x", 0), (Branch false :: nil)%list)).
    {
        eapply EvalTraceIfFalse.
        simpl.
        unfold v2.
        rewrite lookup_add_eq; reflexivity.
        constructor.
        reflexivity.
    }
    specialize (Hct Hpre1 Hpre2 Hpre3).
    easy.
Qed.

Example secure1 := single_out_pgm public_guard_program "x".

Goal is_secure_pgm secure1 VarSet.empty.
Proof.  
    unfold is_secure_pgm.
    eexists.
    eassert (Hct : ct_cmd VarSet.empty public_guard_program VarSet.empty).
    {
        unfold secure1, public_guard_program. simpl.
        econstructor.
        2,3: econstructor.
        all: unfold senv, interp_sec, sec_lookup in *. 
        VarSetDecide.fsetdec.
        1,2: reflexivity.
        unfold join_sec_env.
        simpl.
        assert (VarSet.Equal (VarSet.union (VarSet.remove "x" VarSet.empty) (VarSet.remove "x" VarSet.empty)) VarSet.empty) by VarSetDecide.fsetdec.
        VarSetDecide.fsetdec.
        Unshelve.
        apply VarSet.empty.
    }
    apply ct_cmd_soundness. auto.
Qed.

Example senv' := $0 $+ ("x", Secret).
