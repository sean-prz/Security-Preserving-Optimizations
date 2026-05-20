Require Import Language.Main.


(* eval_intro taken from lab6*)
Ltac simpl_maps := autorewrite with core in *.
Ltac eval_intro :=
let eval_intro_solve :=
    intros; simpl in *; simpl_maps;
    lazymatch goal with
    | [  |- eval _ _ _ _ ] => idtac
    | _ => intuition congruence
    end in
lazymatch goal with
| [  |- eval _ _ Skip _ ] =>
    apply EvalSkip
| [  |- eval _ _ (Assign _ _) _ ] =>
    eapply EvalAssign
| [  |- eval _ _ (Cmov _ _ _ _) _ ] =>
    (eapply EvalCmovFalse + eapply EvalCmovTrue); eval_intro_solve
| [  |- eval _ _ (AssignCall _ _ _ _) _ ] =>
    eapply EvalAssignCall
| [  |- eval _ _ (Sequence _ _) _ ] =>
    eapply EvalSequence
| [  |- eval _ _ (While _ _) _ ] =>
    (eapply EvalWhileTrue + eapply EvalWhileFalse); eval_intro_solve
| [  |- eval _ _ (If _ _ _) _ ] =>
    (eapply EvalIfTrue + eapply EvalIfFalse); eval_intro_solve
| [  |- eval _ _ ?cmd _ ] =>
    unfold cmd at -1 || unfold cmd
| [  |- interp_arith _ _ = _ _ ] => econstructor
| _ => progress (intros; simpl in *; simpl_maps) || (intuition congruence)
end.



Theorem Eval_proj_trace : forall phi ctx c ctx',
    eval_trace phi ctx c ctx' -> 
    eval phi (val_of ctx) c (val_of ctx').
Proof.
  induction 1; simpl; intros.
  - apply EvalSkip.
  - eapply EvalAssign; eauto.
  - eapply EvalCmovTrue; eauto.
  - eapply EvalCmovFalse; eauto.
  - eapply EvalAssignCall; eauto.
  - eapply EvalSequence; eauto.
  - eapply EvalIfTrue; eauto.
  - eapply EvalIfFalse; eauto.
  - eapply EvalWhileTrue; eauto.
  - eapply EvalWhileFalse; eauto.
Qed.


Theorem Eval_proj_sec : forall phi ctx c ctx',
    eval_sec phi ctx c ctx' ->
    eval_trace phi (sec_val_of ctx, sec_trace_of ctx) c (sec_val_of ctx', sec_trace_of ctx').
Proof.
  induction 1; simpl; intros.
  - apply EvalTraceSkip.
  - eapply EvalTraceAssign; eauto.
  - eapply EvalTraceCmovTrue; eauto.
  - eapply EvalTraceCmovFalse; eauto.
  - simpl in *.
    eapply EvalTraceAssignCall with (ctx':=(sec_val_of ctx', sec_trace_of ctx')); eauto.
  - eapply EvalTraceSequence; eauto.
  - eapply EvalTraceIfTrue; eauto.
  - eapply EvalTraceIfFalse; eauto.
  - eapply EvalTraceWhileTrue; eauto.
  - eapply EvalTraceWhileFalse; eauto.
Qed.

Theorem Eval_proj_sec_trace : forall phi ctx c ctx',
    eval_sec phi ctx c ctx' ->
    eval phi (sec_val_of ctx) c (sec_val_of ctx').
Proof.
    intros.
    apply Eval_proj_sec in H.
    apply Eval_proj_trace in H.
    easy.
Qed.
    
(* 
LIFTING THEOREMS
*)


Theorem Eval_lift_trace : forall phi v c v',
    eval phi v c v' ->
    forall t, exists t',
    eval_trace phi (v, t) c (v',t').
Proof.
  induction 1; simpl; intros.
  - eexists. apply EvalTraceSkip.
  - eexists. eapply EvalTraceAssign; eauto.
  - eexists. eapply EvalTraceCmovTrue; eauto.
  - eexists. eapply EvalTraceCmovFalse; eauto.
  - specialize (IHeval t). destruct IHeval as [t' Ht'].
    eexists. eapply EvalTraceAssignCall; eauto.
  - specialize (IHeval1 t). destruct IHeval1 as [t1 Ht1].
    specialize (IHeval2 t1). destruct IHeval2 as [t2 Ht2].
    eexists. eapply EvalTraceSequence; eauto.
  - specialize (IHeval (t ++ Branch true :: nil)%list).
    destruct IHeval as [t' Ht'].
    eexists. eapply EvalTraceIfTrue; eauto.
  - specialize (IHeval (t ++ Branch false :: nil)%list).
    destruct IHeval as [t' Ht'].
    eexists. eapply EvalTraceIfFalse; eauto.
  - specialize (IHeval1 (t ++ Branch true :: nil)%list).
    destruct IHeval1 as [t1 Ht1].
    specialize (IHeval2 t1). destruct IHeval2 as [t2 Ht2].
    eexists. eapply EvalTraceWhileTrue; eauto.
  - eexists. apply EvalTraceWhileFalse; eauto.
Qed.

Theorem Eval_lift_sec : forall phi v t c v' t',
    eval_trace phi (v, t) c (v', t') ->
    forall sec, exists sec',
    eval_sec phi (v, sec, t) c (v', sec', t').
Proof.
    intros phi v t c v' t' Heval.
    dependent induction Heval; simpl; intros.
    - do 2 econstructor.
    - do 2 econstructor; eauto.
    - eexists. eapply EvalSecCmovTrue; eauto.
    - eexists. eapply EvalSecCmovFalse; eauto.
    - destruct ctx'. simpl in *.
        specialize (IHHeval _ _ _ _ ltac:(reflexivity) ltac:(reflexivity) (senv_mk2 x1 x2 (interp_sec e1 sec) (interp_sec e2 sec))).
        destruct IHHeval as [sec' Hsec'].
        eexists.
        specialize (EvalSecAssignCall phi x f e1 e2); simpl; intros HevalAssignCall.
        specialize (HevalAssignCall x1 x2 y body (interp_arith e1 v) (interp_arith e2 v) (interp_sec e1 sec) (interp_sec e2 sec)). 
        specialize (HevalAssignCall (v, sec, t) (v0, sec', l) a (sec_lookup (sec_of (v0, sec', l)) y)).
        unfold sec_of, sec_val_of in HevalAssignCall.
        simpl in HevalAssignCall.
        eapply HevalAssignCall; eauto.
    - destruct ctx1.
        specialize (IHHeval1 _ _ _ _ ltac:(reflexivity) ltac:(reflexivity) sec).
        destruct IHHeval1 as [sec' Hsec'].
        specialize (IHHeval2 _ _ _ _ ltac:(reflexivity) ltac:(reflexivity) sec').
        destruct IHHeval2 as [sec'' Hsec''].
        eexists.
        econstructor.
        eapply Hsec'.
        eapply Hsec''.
    - specialize (IHHeval _ _ _ _ ltac:(reflexivity) ltac:(reflexivity) sec).
        destruct IHHeval as [sec' Hsec']. simpl in Hsec'.
        exists sec'.
        eapply EvalSecIfTrue; eauto.
    - specialize (IHHeval _ _ _ _ ltac:(reflexivity) ltac:(reflexivity) sec).
        destruct IHHeval as [sec' Hsec']. simpl in Hsec'.
        exists sec'.
        eapply EvalSecIfFalse; eauto.
    - destruct ctx'.
        specialize (IHHeval1 _ _ _ _ ltac:(reflexivity) ltac:(reflexivity) sec).
        destruct IHHeval1 as [sec' Hsec'].
        specialize (IHHeval2 _ _ _ _ ltac:(reflexivity) ltac:(reflexivity) sec').
        destruct IHHeval2 as [sec'' Hsec''].
        eexists.
        eapply EvalSecWhileTrue; eauto.
    - eexists.
        eapply EvalSecWhileFalse; eauto.
Qed.


Theorem Eval_lift_trace_sec : forall phi v c v',
    eval phi v c v'->
    forall sec t, exists sec' t',
    eval_sec phi (v, sec, t) c (v', sec', t').
Proof.
    intros.
    eapply Eval_lift_trace in H.
    destruct H as [t' H].
    eapply Eval_lift_sec in H.
    destruct H as [sec' H].
    eauto.
Qed.



    
    
    



    
