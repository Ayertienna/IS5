(* TODO: imports are messed up now that there's a module *) 
Require Import Syntax.
Require Import Substitution.
Print LoadPath.
Require Import Metatheory.
Require Import LibList.
Require Import LibListSorted.
Require Import Arith.

Open Scope label_free_is5_scope.

Global Reserved Notation " G '|=' Ctx '|-' M ':::' A " (at level 70).

(* Statics *)

Inductive types_LF: Background_LF -> Context_LF -> te_LF -> ty_LF -> Prop :=

| t_hyp_LF: forall A G w Gamma v_n
  (HT: Nth v_n Gamma A),
  G |= (w, Gamma) |- (hyp_LF v_n) ::: A

| t_lam_LF: forall A B G w Gamma M 
  (HT: G |= (w, A::Gamma) |- M ::: B),
  G |= (w, Gamma) |- (lam_LF A M) ::: A ---> B

| t_appl_LF: forall A B G Ctx M N
  (HT1: G |= Ctx |- M ::: A ---> B)
  (HT2: G |= Ctx |- N ::: A),
  G |= Ctx |- (appl_LF M N) ::: B

| t_box_LF: forall L A G Ctx M
  (HT: forall w', w' \notin L -> 
    G & Ctx |= (w', nil) |- M ^^ (fctx w') ::: A),
  G |= Ctx |- box_LF M ::: [*] A

| t_unbox_LF: forall A G Ctx M
  (HT: G |= Ctx |- M ::: [*] A),
  G |= Ctx |- unbox_LF M ::: A

| t_unbox_fetch_LF: forall A G w Gamma Ctx' M
  (HT: G & Ctx' |= (w, Gamma) |- M ::: [*] A),
  forall G', permut (G & (w, Gamma)) G' ->
    G' |= Ctx' |- unbox_fetch_LF (fctx w) M ::: A

| t_here_LF: forall A G Ctx M
  (HT: G |= Ctx |- M ::: A),
  G |= Ctx |- here_LF M ::: <*> A

| t_get_here_LF: forall A G w Gamma Ctx' M
  (HT: G & Ctx' |= (w, Gamma) |- M ::: A),
  forall G0, permut (G & (w, Gamma)) G0 -> 
    G0 |= Ctx' |- get_here_LF (fctx w) M ::: <*> A

| t_letdia_LF: forall L A B G Ctx M N
  (HT1: G |= Ctx |- M ::: <*> A)
  (HT2: forall w', w' \notin L ->
    (w', A :: nil) :: G |= Ctx |- N ^^ (fctx w') ::: B),
  G |= Ctx |- letdia_LF M N ::: B 

| t_letdia_get_LF: forall L A B G w Gamma Ctx' M N
  (HT1: G & Ctx' |= (w, Gamma) |- M ::: <*> A)
  (HT2: forall w', w' \notin L ->
    (w', (A :: nil)) :: G & (w, Gamma) |= Ctx' |- N ^^ (fctx w') ::: B),
  forall G0, permut (G & (w, Gamma)) G0 -> 
    G0 |= Ctx' |- letdia_get_LF (fctx w) M N ::: B

where " G '|=' Ctx '|-' M ':::' A " := (types_LF G Ctx M A) : label_free_is5_scope.

(* Dynamics *)

Inductive value_LF: te_LF -> Prop :=
| val_lam_LF: forall A M, value_LF (lam_LF A M)
| val_box_LF: forall M, value_LF (box_LF M)
| val_here_LF: forall M, value_LF M -> value_LF (here_LF M)
| val_get_here_LF: forall M Ctx, value_LF M -> value_LF (get_here_LF Ctx M)
.

Global Reserved Notation " M |-> N " (at level 70).

Inductive step_LF: (te_LF * ctx_LF) -> (te_LF * ctx_LF) -> Prop :=

| red_appl_lam_LF: forall ctx M A N,
  (appl_LF (lam_LF A M) N, ctx) |-> 
    ([N // 0] M, ctx)

| red_unbox_box_LF: forall ctx M,
  (unbox_LF (box_LF M), ctx) |-> 
    (M ^^ ctx, ctx)

| red_unbox_fetch_box_LF: forall ctx ctx' M,
  (unbox_fetch_LF ctx' (box_LF M), ctx) |-> 
    (M ^^ ctx, ctx) 

| red_letdia_here_LF: forall ctx M N,
  (letdia_LF (here_LF M) N, ctx) |-> 
    ([M // 0] N ^^ ctx , ctx)

| red_letdia__get_here_LF: forall ctx ctx' M N,
  (letdia_LF (get_here_LF ctx' M) N, ctx) |-> 
    ([M // 0] N ^^ ctx, ctx)

| red_letdia_get__here_LF: forall ctx ctx' M N,
  (letdia_get_LF ctx' (here_LF M) N, ctx) |-> 
    ([M // 0] N ^^ ctx , ctx)

| red_letdia_get_get_here_LF: forall ctx ctx' ctx'' M N,
  (letdia_get_LF ctx' (get_here_LF ctx'' M) N, ctx) |-> 
    ([M // 0] N ^^ ctx , ctx)

| red_appl_LF: forall ctx M N M'
  (HT: (M, ctx) |-> (M', ctx)), 
  (appl_LF M N, ctx) |-> (appl_LF M' N, ctx)

| red_unbox_LF: forall ctx M M'
  (HT: (M, ctx) |-> (M', ctx)), 
  (unbox_LF M, ctx) |-> (unbox_LF M', ctx)

| red_unbox_fetch_LF: forall ctx' M M' ctx
  (HT: (M, ctx') |-> (M', ctx')), 
  (unbox_fetch_LF ctx' M, ctx) |-> (unbox_fetch_LF ctx' M', ctx)

| red_here_LF: forall ctx M M' 
  (HT: (M, ctx) |-> (M', ctx)), 
  (here_LF M, ctx) |-> (here_LF M', ctx)

| red_get_here_LF: forall ctx ctx' M M' 
  (HT: (M, ctx) |-> (M', ctx)), 
  (get_here_LF ctx M, ctx') |-> (get_here_LF ctx M', ctx')

| red_letdia_LF: forall ctx M N M' 
  (HT: (M, ctx) |-> (M', ctx)),
  (letdia_LF M N, ctx) |-> (letdia_LF M' N, ctx)

| red_letdia_get_LF: forall ctx ctx' M N M'
  (HT: (M, ctx) |-> (M', ctx)), 
  (letdia_get_LF ctx M N, ctx') |-> (letdia_get_LF ctx M' N, ctx')

where " M |-> N " := (step_LF M N ) : label_free_is5_scope.

(* Extensions to Tlc library *)

Section PermutationAdd.
Variable A: Type.
Implicit Types l : list A.

Lemma permut_inv:
forall G0 G0' G1 G1' (elem: A),
  permut (G0 & elem ++ G0') (G1 & elem ++ G1') ->
  permut (G0 ++ G0') (G1 ++ G1').
Admitted.

Lemma permut_split_neq:
forall G G' H (elem:A) (elem':A)
  (HNeq: elem <> elem')
  (HT: permut (G & elem ++ G') (H & elem')),
  exists GH, exists GT, H = GH & elem ++ GT.
Admitted.

End PermutationAdd.

Section Lemmas.

Lemma BackgroundSubsetImpl:
forall G G' Ctx M A
  (HT: G |= Ctx |- M ::: A)
  (HSubst: exists GT, permut (G++GT) G'),
  G' |= Ctx |- M ::: A.
intros.
generalize dependent G'.
induction HT; intros; eauto using types_LF.
(* box *)
destruct HSubst as [GT];
apply t_box_LF with (L:=L); intros;
apply H; [ | exists GT; permut_simpl]; assumption.
(* unbox_fetch *)
destruct HSubst as [GT];
apply t_unbox_fetch_LF with (Gamma:=Gamma) (G:=G++GT).
apply IHHT;
  exists GT; permut_simpl.
apply permut_trans with (l2:= G' ++ GT); 
[ permut_simpl | ]; assumption.
(* get_here *)
destruct HSubst as [GT];
apply t_get_here_LF with (Gamma:=Gamma) (G:=G++GT).
apply IHHT;
  exists GT; permut_simpl.
apply permut_trans with (l2:= G0 ++ GT); 
[ permut_simpl | ]; assumption.
(* letdia *)
apply t_letdia_LF with (A:=A) (L:=L). 
apply IHHT; assumption.
intros; apply H. 
  assumption.
  destruct HSubst as [GT];
  exists GT; permut_simpl; assumption.
(* letdia_get *)
destruct HSubst as [GT];
apply t_letdia_get_LF with (A:=A) (Gamma:=Gamma) (G:=G++GT) (L:=L).
apply IHHT;
  exists GT; permut_simpl.
intros. apply H. 
  assumption.
  exists GT; permut_simpl.
apply permut_trans with (l2:= G0 ++ GT); 
[ permut_simpl | ]; assumption.
Qed.

Lemma GlobalWeakening:
forall G G' Ctx Ctx' M A
  (HT: G ++ G' |= Ctx |- M ::: A),
  G & Ctx' ++ G' |= Ctx |- M ::: A.
intros; rew_app;
apply BackgroundSubsetImpl with (G := G ++ G');
[assumption | exists (Ctx'::nil)];
permut_simpl.
Qed.

Lemma Weakening_general:
  forall G w Gamma M A
  (HT: G |= (w, Gamma) |- M ::: A),
  (forall G' w' Delta Delta',
    permut G (G' & (w', Delta)) ->
    G' & (w', Delta ++ Delta') |= (w, Gamma) |- M ::: A) /\ 
  (forall Gamma',
    G |= (w, Gamma ++ Gamma') |- M ::: A).
intros.
remember (w, Gamma) as Ctx.
generalize dependent Gamma.
generalize dependent w.
induction HT; split;
intros; subst; simpl;
try (inversion HeqCtx; subst).
(* hyp *)
eauto using types_LF.
constructor; generalize dependent v_n;
induction Gamma0; destruct v_n; intros;
try (apply Nth_nil_inv in HT; contradiction);
apply Nth_app_l; assumption.
(* lam *)
constructor; eapply IHHT; eauto.
constructor;
apply IHHT with (w:=w0) (Gamma:=A::Gamma0);
auto.
(* appl *)
econstructor; [eapply IHHT1| eapply IHHT2]; eauto.
econstructor; [eapply IHHT1| eapply IHHT2]; eauto.
(* box 1 *)
apply t_box_LF with (L:=L); intros.
apply BackgroundSubsetImpl with (G:=G' & (w, Gamma) & (w', Delta ++ Delta')).
  eapply H.
    assumption.
    eauto.
    apply permut_trans with (l2:=G' & (w', Delta) & (w, Gamma)).
      apply permut_app_lr. assumption.
      permut_simpl. 
      permut_simpl.
  exists (@nil Context_LF); permut_simpl; assumption.
(* box 2 *)
apply t_box_LF with (L:=L); intros.
eapply H. 
 assumption.
 eauto.
 permut_simpl.
(* unbox *)
constructor; eapply IHHT; eauto.
constructor; eapply IHHT; eauto.
(* unbox_fetch 1 *)
destruct (eq_context_LF_dec (w', Delta) (w, Gamma)).
(* = *)
inversion e; subst.
apply t_unbox_fetch_LF with (G:=G) (Gamma:=Gamma++Delta').
apply IHHT.
 reflexivity.
permut_simpl;
replace G with (G++nil) by (rew_app; reflexivity);
replace G'0 with (G'0++nil) by (rew_app; reflexivity);
apply permut_inv with (elem := (w, Gamma));
apply permut_trans with (l2:=G'); permut_simpl; assumption.
(* <> *)
assert (exists G0, exists G1, G'0 = G0 & (w, Gamma) ++ G1).
  apply permut_split_neq with (G:=G) (G':=nil) (elem':=(w',Delta)).
    intro e; symmetry in e; contradiction.
    rew_app; apply permut_trans with (l2:=G'); assumption.
destruct H1 as [GH]; destruct H1 as [GT]; subst G'0.
apply t_unbox_fetch_LF with (Gamma:=Gamma) (G:=GH ++ GT & (w', Delta ++ Delta')).
apply BackgroundSubsetImpl with (G:= (GH ++ GT & (w0, Gamma0)) & (w', Delta ++ Delta')).
  specialize IHHT with w Gamma.  
  destruct IHHT; try reflexivity.
  apply H1 with (G':= GH ++ GT & (w0, Gamma0)).
  permut_simpl.
  assert (permut (G++nil) (GH ++ GT & (w', Delta))).
    apply permut_inv with (elem := (w ,Gamma)).
    apply permut_trans with (l2:=G').
    rew_app; assumption.
    apply permut_trans with (l2:=(GH & (w, Gamma) ++ GT) & (w', Delta)).
      assumption.
      permut_simpl.
  rew_app in H3.
  apply permut_app_l with (l2:=(w0, Gamma0)::nil) in H3.
  apply permut_trans with (l2:=(GH ++ GT & (w', Delta) & (w0, Gamma0))).
    rew_app in *. assumption.
    permut_simpl.
  exists (@nil Context_LF); permut_simpl.
permut_simpl.
(* unbox_fetch 2 *)
apply t_unbox_fetch_LF with (G:=G) (Gamma:=Gamma).
  specialize IHHT with w Gamma.
destruct IHHT; try reflexivity.
apply H0.
permut_simpl.
assumption.
(* here *)
constructor; specialize IHHT with w Gamma; apply IHHT; auto. 
constructor; apply IHHT; auto.
(* get_here 1 *)
destruct (eq_context_LF_dec (w', Delta) (w, Gamma)).
(* = *)
inversion e;
subst;
apply t_get_here_LF with (Gamma:=Gamma++Delta') (G:=G).
  apply IHHT.
  reflexivity.
  apply permut_app_l.
  assert (permut (G & (w, Gamma)) (G' & (w, Gamma))).
  apply permut_trans with (l2:=G0); assumption.
  replace G with (G++nil) by (rew_app; reflexivity).
  replace G' with (G'++nil) by (rew_app; reflexivity).
  apply permut_inv with (elem:=(w, Gamma)).
  rew_app; assumption.
(* <> *)
assert (exists G0, exists G1, G' = G0 & (w, Gamma) ++ G1).
  apply permut_split_neq with (G:=G) (G':=nil) (elem':=(w', Delta)).
    intro e; symmetry in e; contradiction.
    rew_app; apply permut_trans with (l2:=G0); assumption.
destruct H1 as [GH]; destruct H1 as [GT]; subst G'.
apply t_get_here_LF with (Gamma:=Gamma) (G:=GH ++ GT & (w', Delta ++ Delta')).
apply BackgroundSubsetImpl with (G:= (GH ++ GT & (w0, Gamma0)) & (w', Delta ++ Delta')).
  specialize IHHT with w Gamma.
  apply IHHT. 
  reflexivity.
  assert (permut (G++nil) (GH++GT & (w', Delta))).
    apply permut_inv with (elem := (w ,Gamma)).
    apply permut_trans with (l2:=G0).
    rew_app; assumption.
    apply permut_trans with (l2:=(GH & (w, Gamma) ++ GT) & (w', Delta)).
      assumption.
      permut_simpl.
  rew_app in H1.
  apply permut_app_l with (l2:=(w0,Gamma0)::nil) in H1.
  apply permut_trans with (l2:=(GH ++ GT & (w', Delta)) & (w0, Gamma0)).
    assumption.
    permut_simpl.
  exists (@nil Context_LF); permut_simpl.
  permut_simpl.
(* get_here 2 *)
apply t_get_here_LF with (G:=G) (Gamma:=Gamma).
  specialize IHHT with w Gamma.
  apply IHHT. 
    reflexivity.
    permut_simpl.
  assumption.
(* letdia *)
apply t_letdia_LF with (A:=A) (L:=L).
specialize IHHT with w Gamma.
apply IHHT; auto.
intros. 
specialize H with (w':=w'0).
destruct H with (w0:=w) (Gamma0:=Gamma).
assumption.
reflexivity.
apply H2 with (G':=(w'0, A::nil)::G');
permut_simpl;
assumption.
apply t_letdia_LF with (A:=A) (L:=L).
apply IHHT; auto.
intros; apply H; auto.
(* letdia_get 1 *)
destruct (eq_context_LF_dec (w', Delta) (w, Gamma)).
(* = *)
inversion e;
subst;
apply t_letdia_get_LF with (Gamma:=Gamma++Delta') (G:=G) (A:=A) (L:=L).
  apply IHHT.
  reflexivity.
  intros.
  specialize H with (w':=w').
  destruct H with (w1:=w0)(Gamma1:=Gamma0).
    assumption.
    reflexivity.
  apply H3 with (G':= (w', A :: nil) :: G).
  permut_simpl.
  apply permut_app_l.
  assert (permut (G & (w, Gamma)) (G' & (w, Gamma))).
  apply permut_trans with (l2:=G0); assumption.
  replace G with (G++nil) by (rew_app; reflexivity).
  replace G' with (G'++nil) by (rew_app; reflexivity).
  apply permut_inv with (elem:=(w, Gamma)).
  rew_app; assumption.
(* <> *)
assert (exists G0, exists G1, G' = G0 & (w, Gamma) ++ G1).
  apply permut_split_neq with (G:=G) (G':=nil) (elem':=(w', Delta)).
    intro e; symmetry in e; contradiction.
    rew_app; apply permut_trans with (l2:=G0); assumption.
destruct H2 as [GH]; destruct H2 as [GT]; subst G'.
apply t_letdia_get_LF with (Gamma:=Gamma) (G:=GH ++ GT & (w', Delta ++ Delta')) (L:=L)(A:=A).
apply BackgroundSubsetImpl with (G:= (GH ++ GT & (w0, Gamma0)) & (w', Delta ++ Delta')).
  specialize IHHT with w Gamma.
  apply IHHT. 
  reflexivity.
  assert (permut (G++nil) (GH++GT & (w', Delta))).
    apply permut_inv with (elem := (w ,Gamma)).
    apply permut_trans with (l2:=G0).
    rew_app; assumption.
    apply permut_trans with (l2:=(GH & (w, Gamma) ++ GT) & (w', Delta)).
      assumption.
      permut_simpl.
  rew_app in H2.
  apply permut_app_l with (l2:=(w0,Gamma0)::nil) in H2.
  apply permut_trans with (l2:=(GH ++ GT & (w', Delta)) & (w0, Gamma0)).
    assumption.
    permut_simpl.
  exists (@nil Context_LF); permut_simpl.
  intros.
  specialize H with (w':=w'0).
  destruct H with (w1:=w0) (Gamma1:=Gamma0).
    assumption.
    reflexivity.
  apply BackgroundSubsetImpl with (G:=((w'0, A::nil) :: GH++GT &(w, Gamma)) & (w', Delta ++ Delta')).
  apply H3.
  permut_simpl.
  assert (permut (G & (w, Gamma)) (GH ++ GT & (w', Delta) & (w, Gamma) )).
    apply permut_trans with (l2:= (GH & (w,Gamma) ++ GT) & (w', Delta)).
      apply permut_trans with (l2:=G0); assumption.
    permut_simpl.
  replace G with (G++nil) by (rew_app; reflexivity).
  replace (GH++GT & (w',Delta)) with ((GH++GT & (w',Delta))++nil) by (rew_app; reflexivity).
  apply permut_inv with (elem := (w, Gamma)). 
  rew_app in *; assumption.
exists (@nil Context_LF); permut_simpl.
permut_simpl.
(* letdia_get 2 *)
apply t_letdia_get_LF with (G:=G) (Gamma:=Gamma) (A:=A) (L:=L).
  specialize IHHT with w Gamma.
  apply IHHT. 
    reflexivity.
    permut_simpl.
  intros.
  specialize H with (w':=w'); destruct H with (w1:=w0)(Gamma1:=Gamma0).
  assumption.
  reflexivity.
  apply H3.
  assumption.
Qed.

Lemma WeakeningBackgroundElem:
forall G G' w Delta Delta' Ctx M A
  (HT: G & (w, Delta) ++ G' |= Ctx |- M ::: A),
  G & (w, Delta ++ Delta') ++ G' |= Ctx |- M ::: A.
intros.
apply BackgroundSubsetImpl with (G:=(G++G') & (w, Delta ++ Delta')).
assert (permut (G & (w, Delta) ++ G') ((G++G') & (w, Delta))).
  permut_simpl.
destruct Ctx;
eapply Weakening_general; eassumption.
eexists nil; permut_simpl.
Qed.

Lemma Weakening:
forall G w Gamma Gamma' M A
  (HT: G |= (w, Gamma) |- M ::: A),
  G |= (w, Gamma ++ Gamma') |- M ::: A.
intros;
eapply Weakening_general; eassumption.
Qed.

(* Original formulations of modified typing rules can be reconstructed *)
Lemma test_box:
  forall L G G' Ctx M A,
    (forall w', w' \notin L -> 
      G & Ctx ++ G' |=  (w', nil) |- M^^(fctx w') ::: A) ->
      G ++ G' |= Ctx |- box_LF M ::: [*]A.
intros; apply t_box_LF with (L:=L); intros;
try assumption;
apply BackgroundSubsetImpl with (G:=G & Ctx ++ G');
[ apply H; assumption
|  exists (@nil Context_LF); permut_simpl].
Qed.

Lemma test_unbox_fetch:
  forall G G' Ctx w' Gamma' M A,
    G & Ctx ++ G' |= (w', Gamma') |- M ::: [*] A ->
      G & (w', Gamma') ++ G' |= Ctx |- unbox_fetch_LF (fctx w') M ::: A.
intros;
apply t_unbox_fetch_LF with (G:=G ++ G') (Gamma:=Gamma');
[apply BackgroundSubsetImpl with (G:=G & Ctx ++ G') | permut_simpl];
[ assumption | exists (@nil Context_LF); permut_simpl].
Qed.

Lemma test_get_here:
  forall G G' Ctx w' Gamma' M A,
    G & Ctx ++ G' |= (w', Gamma') |- M ::: A ->
      G & (w', Gamma') ++ G' |= Ctx |- get_here_LF (fctx w') M ::: <*> A.
intros;
apply t_get_here_LF with (G:=G ++ G') (Gamma:=Gamma');
[apply BackgroundSubsetImpl with (G:=G & Ctx ++ G') | permut_simpl];
[assumption | exists (@nil Context_LF); permut_simpl].
Qed.

Lemma test_letdia_get:
  forall L G G' w w' Gamma Gamma' M N A B,
    G & (w', Gamma') ++ G' |= (w, Gamma) |- M ::: <*>A ->
    (forall w'', w'' \notin L -> 
      (w'', (A::nil)) :: G & (w, Gamma) ++ G' |= (w', Gamma') |- N ^^ (fctx w'') ::: B) ->
    G & (w, Gamma) ++ G' |= (w', Gamma') |-  letdia_get_LF (fctx w) M N ::: B.
intros.
apply t_letdia_get_LF with (A:=A) (G:=G ++ G') (L:=L) (Gamma := Gamma); intros;
[ apply BackgroundSubsetImpl with (G:=G & (w', Gamma') ++ G') |
  apply BackgroundSubsetImpl with (G:=(w'0, A::nil) :: G & (w, Gamma) ++ G') |
  permut_simpl];
  [assumption | exists (@nil Context_LF); permut_simpl |
   apply H0; assumption | exists (@nil Context_LF); permut_simpl ].
Qed.

(* / *)

Fixpoint emptyEquiv (G: Background_LF) : Background_LF :=
match G with
| nil => nil
| (w, a)::G => (w, nil) :: emptyEquiv G
end.

Lemma emptyEquiv_nil:
forall G G' w Gamma,
  permut (emptyEquiv G) G' ->
  Mem (w, Gamma) G' -> Gamma = nil.
Admitted.

Lemma emptyEquiv_empty:
forall G G',
  permut (emptyEquiv G) G' ->
  emptyEquiv G' = G'.
Admitted.

Lemma emptyEquiv_inv:
forall G G' w,
  emptyEquiv (G & (w,nil)) = (G' & (w, nil)) ->
  emptyEquiv G = G'.
Admitted.

Lemma emptyEquiv_last:
forall G G' w,
  emptyEquiv G = G' ->
  emptyEquiv (G & (w, nil)) = G' & (w, nil).
Admitted.

Lemma Progress:
forall G w M A
  (HT: emptyEquiv G |= (w, nil) |- M ::: A),
  value_LF M \/ exists N, (M, fctx w) |-> (N, fctx w).
intros.
remember (w, (@nil ty_LF)) as Ctx.
generalize dependent Ctx.
generalize dependent A.
generalize dependent w.
generalize dependent G. 
induction M; intros; eauto using value_LF;
inversion HeqCtx; subst.
(* hyp *)
inversion HT; destruct n;
apply Nth_nil_inv in HT0; contradiction.
(* appl *)
right; inversion HT; subst.
destruct IHM1 with (Ctx := (w, (@nil ty_LF))) (G := G) (A := A0 ---> A) (w := w);
auto.
  inversion H0; subst; inversion HT1; subst; eexists; constructor.
  destruct H0; eexists; constructor; eapply H0.
(* unbox *)
right; inversion HT; subst;
destruct IHM with (Ctx := (w, (@nil ty_LF))) (G := G) (A := [*]A) (w := w);
auto.
  inversion H0; subst; inversion HT0; subst; eexists; constructor.
  destruct H0; eexists; constructor; eapply H0.
(* unbox_fetch *)
right; inversion HT; subst.
assert (Gamma = nil).
  apply emptyEquiv_nil with (G:=G) (G':=G0 & (w0, Gamma)) (w:=w0).
  apply permut_sym; assumption.
  rewrite Mem_app_or_eq; right; rewrite Mem_cons_eq; left; reflexivity.
subst. 
destruct IHM with (Ctx := (w0, (@nil ty_LF))) (G := G0 & (w, nil)) (A:=[*]A) (w:=w0).
reflexivity.
assert (emptyEquiv (G0 & (w, nil)) = G0 & (w, nil)).
apply emptyEquiv_last.
apply emptyEquiv_inv with (w:=w0).
apply emptyEquiv_empty with (G := G).
  apply permut_sym; assumption.
rewrite H0; assumption.
inversion H0; subst; inversion HT0; subst. 
eexists; constructor.
destruct H0 as [M'].
eexists; constructor; eassumption.
(* here *)
inversion HT; subst.
destruct (IHM G w A0 (w,nil)); auto.
left; apply val_here_LF; assumption.
right; destruct H0; exists (here_LF x); eauto using step_LF.
(* get_here *)
inversion HT; subst.
assert (Gamma = nil).
  apply emptyEquiv_nil with (G:=G) (G':=G0 & (w0, Gamma)) (w:=w0).
  apply permut_sym; assumption.
  rewrite Mem_app_or_eq; right; rewrite Mem_cons_eq; left; reflexivity.
subst; destruct (IHM (G0 & (w, nil)) w0 A0 (w0,nil)); auto.
assert (emptyEquiv (G0 & (w, nil)) = G0 & (w, nil)).
apply emptyEquiv_last.
apply emptyEquiv_inv with (w:=w0).
apply emptyEquiv_empty with (G := G).
  apply permut_sym; assumption.
rewrite H0; assumption.
left; econstructor; eassumption.
right; destruct H0; eexists; constructor; eassumption. 
(* letdia *)
right; inversion HT; subst.
destruct (IHM1 G w (<*>A0) (w, nil)); auto.
inversion H0; subst; inversion HT1; subst.
  eexists; econstructor; eassumption.
  eexists; econstructor; eassumption.
destruct H0; exists (letdia_LF x M2); eauto using step_LF.
(* letdia_get *)
right; inversion HT; subst.
assert (Gamma = nil).
  apply emptyEquiv_nil with (G:=G) (G':=G0 & (w0, Gamma)) (w:=w0).
  apply permut_sym; assumption.
  rewrite Mem_app_or_eq; right; rewrite Mem_cons_eq; left; reflexivity.
subst; destruct (IHM1 (G0 & (w, nil)) w0 (<*>A0) (w0,nil)); auto.
assert (emptyEquiv (G0 & (w, nil)) = G0 & (w, nil)).
apply emptyEquiv_last.
apply emptyEquiv_inv with (w:=w0).
apply emptyEquiv_empty with (G := G).
  apply permut_sym; assumption.
rewrite H0; assumption.
inversion H0; subst; inversion HT1; subst.
  eexists; econstructor; eauto.
  eexists; econstructor; eauto.
destruct H0; eexists; econstructor; eassumption.
Qed.

Lemma Preservation:
forall G w M N A
  (HT: emptyEquiv G |= (w, nil) |- M ::: A)
  (HS: (M, fctx w) |-> (N, fctx w)),
  emptyEquiv G |= (w, nil) |- N ::: A.
Admitted.

End Lemmas.

Close Scope label_free_is5_scope.
