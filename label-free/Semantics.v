(* TODO: imports are messed up now that there's a module *) 
Require Import Syntax.
Require Import Substitution.
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
    G & Ctx |= (w', nil) |- M ^^ [fctx w' | fctx w'] ::: A),
  G |= Ctx |- box_LF M ::: [*] A

| t_unbox_LF: forall A G w Gamma M
  (HT: G |= (w, Gamma) |- M ::: [*] A),
  G |= (w, Gamma) |- unbox_fetch_LF (fctx w) M ::: A

| t_unbox_fetch_LF: forall A G w Gamma Ctx' M
  (HT: G & Ctx' |= (w, Gamma) |- M ::: [*] A),
  forall G', permut (G & (w, Gamma)) G' ->
    G' |= Ctx' |- unbox_fetch_LF (fctx w) M ::: A

| t_here_LF: forall A G w Gamma M
  (HT: G |= (w, Gamma) |- M ::: A),
  G |= (w, Gamma) |- get_here_LF (fctx w) M ::: <*> A

| t_get_here_LF: forall A G w Gamma Ctx' M
  (HT: G & Ctx' |= (w, Gamma) |- M ::: A),
  forall G0, permut (G & (w, Gamma)) G0 -> 
    G0 |= Ctx' |- get_here_LF (fctx w) M ::: <*> A

| t_letdia_LF: forall L A B G w Gamma M N
  (HT1: G |= (w, Gamma) |- M ::: <*> A)
  (HT2: forall w', w' \notin L ->
    (w', A :: nil) :: G |= (w, Gamma) |- N ^^ [fctx w' | fctx w] ::: B),
  G |= (w, Gamma) |- letdia_get_LF (fctx w) M N ::: B 

| t_letdia_get_LF: forall L A B G w Gamma Ctx' M N
  (HT1: G & Ctx' |= (w, Gamma) |- M ::: <*> A)
  (HT2: forall w', w' \notin L ->
    (w', (A :: nil)) :: G & (w, Gamma) |= Ctx' |- N ^^ [fctx w' | fctx (fst Ctx')] ::: B),
  forall G0, permut (G & (w, Gamma)) G0 -> 
    G0 |= Ctx' |- letdia_get_LF (fctx w) M N ::: B

where " G '|=' Ctx '|-' M ':::' A " := (types_LF G Ctx M A) : label_free_is5_scope.

(* Dynamics *)

Inductive value_LF: te_LF -> Prop :=
| val_lam_LF: forall A M, value_LF (lam_LF A M)
| val_box_LF: forall M, value_LF (box_LF M)
| val_get_here_LF: forall M Ctx, value_LF M -> value_LF (get_here_LF Ctx M)
.

Global Reserved Notation " M |-> N " (at level 70).

Inductive step_LF: (te_LF * ctx_LF) -> (te_LF * ctx_LF) -> Prop :=
| red_appl_lam_LF: forall ctx M A N,
  lc_w_LF M -> lc_w_LF N ->
  (appl_LF (lam_LF A M) N, ctx) |-> 
    ([N // 0 | ctx ] [M | ctx], ctx)

| red_unbox_fetch_box_LF: forall ctx ctx' M,
  lc_w_n_LF M 1 ->
  (unbox_fetch_LF ctx' (box_LF M), ctx) |-> 
    (M ^^ [ctx | ctx], ctx) 

| red_letdia_get_get_here_LF: forall ctx ctx' ctx'' M N,
  lc_w_LF M ->
  lc_w_n_LF N 1 ->
  (letdia_get_LF ctx' (get_here_LF ctx'' M) N, ctx) |-> 
    ([M // 0 | ctx'' ] [N ^^ [ctx'' | ctx] | ctx] , ctx)

| red_appl_LF: forall ctx M N M'
  (HT: (M, ctx) |-> (M', ctx)), 
  lc_w_LF M ->
  lc_w_LF N ->
  (appl_LF M N, ctx) |-> (appl_LF M' N, ctx)

| red_unbox_fetch_LF: forall ctx' M M' ctx
  (HT: (M, ctx') |-> (M', ctx')), 
  lc_w_n_LF M 1 ->
  (unbox_fetch_LF ctx' M, ctx) |-> (unbox_fetch_LF ctx' M', ctx)

| red_get_here_LF: forall ctx ctx' M M' 
  (HT: (M, ctx) |-> (M', ctx)), 
  lc_w_LF M ->
  (get_here_LF ctx M, ctx') |-> (get_here_LF ctx M', ctx')

| red_letdia_get_LF: forall ctx ctx' M N M'
  (HT: (M, ctx) |-> (M', ctx)), 
  lc_w_LF M ->
  lc_w_n_LF N 1->
  (letdia_get_LF ctx M N, ctx') |-> (letdia_get_LF ctx M' N, ctx')

where " M |-> N " := (step_LF M N ) : label_free_is5_scope.

(* Extensions to tlc library *)

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
intros;
generalize dependent G';
induction HT; intros; eauto using types_LF.
(* box *)
destruct HSubst as [GT];
apply t_box_LF with (L:=L); intros;
apply H; [ | exists GT; permut_simpl]; assumption.
(* unbox_fetch *)
destruct HSubst as [GT];
apply t_unbox_fetch_LF with (Gamma:=Gamma) (G:=G++GT);
[ apply IHHT; exists GT; permut_simpl | 
  apply permut_trans with (l2:= G' ++ GT)]; 
[ permut_simpl | ]; assumption.
(* get_here *)
destruct HSubst as [GT];
apply t_get_here_LF with (Gamma:=Gamma) (G:=G++GT);
[ apply IHHT; exists GT; permut_simpl |
  apply permut_trans with (l2:= G0 ++ GT)]; 
[ permut_simpl | ]; assumption.
(* letdia *)
apply t_letdia_LF with (A:=A) (L:=L);
[ apply IHHT; assumption | 
  intros; apply H]; 
auto;
destruct HSubst as [GT];
exists GT; permut_simpl; assumption.
(* letdia_get *)
destruct HSubst as [GT];
apply t_letdia_get_LF with (A:=A) (Gamma:=Gamma) (G:=G++GT) (L:=L);
[ apply IHHT; exists GT; permut_simpl | 
  intros; apply H | 
  apply permut_trans with (l2:= G0 ++ GT) ];
auto;
[ exists GT |
  apply permut_trans with (l2:= G0 ++ GT)];
permut_simpl; auto.
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
intros;
remember (w, Gamma) as Ctx;
generalize dependent Gamma;
generalize dependent w;
induction HT; split;
intros; subst; simpl;
try (inversion HeqCtx; subst);
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
apply t_box_LF with (L:=L); intros;
apply BackgroundSubsetImpl with (G:=G' & (w, Gamma) & (w', Delta ++ Delta')).
  eapply H; eauto.
    apply permut_trans with (l2:=G' & (w', Delta) & (w, Gamma)).
      apply permut_app_lr; auto.
      permut_simpl. 
  exists (@nil Context_LF); permut_simpl; assumption.
(* box 2 *)
apply t_box_LF with (L:=L); intros;
eapply H; eauto; permut_simpl.
(* unbox *)
constructor; eapply IHHT; eauto.
constructor; eapply IHHT; eauto.
(* unbox_fetch 1 *)
destruct (eq_context_LF_dec (w', Delta) (w, Gamma)).
(* = *)
inversion e; subst;
apply t_unbox_fetch_LF with (G:=G) (Gamma:=Gamma++Delta');
[ apply IHHT; reflexivity | 
  permut_simpl];
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
constructor; specialize IHHT with w0 Gamma0; apply IHHT; auto. 
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
specialize IHHT with w0 Gamma0.
apply IHHT; auto.
intros. 
specialize H with (w':=w'0).
destruct H with (w:=w0) (Gamma:=Gamma0).
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
intros;
apply BackgroundSubsetImpl with (G:=(G++G') & (w, Delta ++ Delta')).
assert (permut (G & (w, Delta) ++ G') ((G++G') & (w, Delta))) by  permut_simpl;
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
      G & Ctx ++ G' |=  (w', nil) |- M^^[fctx w' | fctx w'] ::: A) ->
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
      (w'', (A::nil)) :: G & (w, Gamma) ++ G' |= (w', Gamma') |- N ^^ [fctx w'' | fctx w'] ::: B) ->
    G & (w, Gamma) ++ G' |= (w', Gamma') |-  letdia_get_LF (fctx w) M N ::: B.
intros;
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

Lemma emptyEquiv_stable:
forall G,
  emptyEquiv (emptyEquiv G) = emptyEquiv G.
Admitted.

Lemma emptyEquiv_permut:
forall G G',
  permut (emptyEquiv G) G' ->
  emptyEquiv G' = G'.
Admitted.

Fixpoint subst_typing G L D w : Prop :=
match L, D with
| nil, nil => True
| M::L', A :: D' => emptyEquiv G |= (w, nil) |- M ::: A /\ (subst_typing G L' D' w)
| _, _ => False
end.

Lemma subst_t_preserv_types_inner:
forall L G Gamma w Delta N B
  (HT_L: subst_typing G L Delta w)
  (HT_lc: forall M, Mem M L -> lc_w_LF M)
  (HT_N: G |= (w, Gamma ++ Delta) |- N ::: B),
  G |= (w, Gamma) |- subst_list L (length Gamma) N (fctx w) (fctx w) ::: B.
Admitted.

Lemma subst_t_preserv_types_outer:
forall L G0 G G' G'' Gamma Gamma' w w' Delta N B
  (HT_G0: permut G (G0 & (w', Gamma')))
  (HT_G': permut G' (G0 & (w, Gamma))) 
  (HT_G'': permut G'' (G0 & (w', Gamma' ++ Delta)))
  (HT_L: subst_typing G' L Delta w')
  (HT_lc: forall M, Mem M L -> lc_w_LF M)
  (HT_N: G'' & (w', Gamma' ++ Delta) |= (w, Gamma) |- N ::: B),
  G |= (w, Gamma) |- subst_list L (length Gamma) N (fctx w') (fctx w)  ::: B.
Admitted.

Lemma inv_subst_ctx_preserv_types_new:
forall G w w' Gamma Gamma' M A k
  (Fresh: w' \notin free_worlds_LF M)
  (HT: G |= (w, Gamma' ++ Gamma) |- {{fctx w // fctx w'}} 
    [ {{ fctx w' // bctx k }} [M | fctx w, 0] | fctx w, length Gamma'] ::: A),
  G |= (w, Gamma'++Gamma) |- {{fctx w // bctx 0 }}[ M | fctx w, 0] ::: A.
Admitted.

Lemma inv_subst_ctx_preserv_types_new':
forall G w w' Gamma Gamma' M A k
  (Fresh: w' \notin free_worlds_LF M)
  (HT: G |= (w, Gamma'++Gamma) |- {{fctx w // fctx w'}} 
    [ {{ fctx w' // bctx k }} [M | fctx w', 0] | fctx w', length Gamma'] ::: A),
  G |= (w, Gamma'++Gamma) |- {{fctx w // bctx 0 }}[ M | fctx w, 0] ::: A.
Admitted.

Lemma inv_subst_ctx_preserv_types_outer:
forall G0 G w w' w0 Gamma Gamma' Gamma0 M A k
  (Fresh: w' \notin free_worlds_LF M)
  (HT_G: permut G (G0 & (w, Gamma' ++ Gamma)))
  (HT: G |= (w0, Gamma0) |- {{ fctx w // fctx w'}} 
    [ {{fctx w' // bctx k}} [M | fctx w0, 0] | fctx w0, (length Gamma')] ::: A),
  G |= (w0, Gamma0) |- {{fctx w // bctx k}}[M | fctx w0, 0] ::: A.
Admitted.

Lemma rename_ctx_preserv_types_outer:
forall G G' G'' w w' w0 Gamma Gamma' Gamma0 M A
  (HT_G': permut G' (G & (w, Gamma) & (w', Gamma')))
  (HT_G'': permut G'' (G & (w, Gamma' ++ Gamma)))
  (HT: G' |= (w0, Gamma0) |- M ::: A),
  G'' |= (w0, Gamma0) |- {{fctx w // fctx w'}} [M | fctx w0, length (Gamma')] ::: A.
Admitted.

Lemma rename_ctx_preserv_types_old:
forall G G' w0 w1 Gamma0 Gamma1 M A
  (HT_G': permut G' (G & (w0, Gamma0)))
  (HT: G' |= (w1, Gamma1) |- M ::: A),
  G |= (w0, Gamma1++Gamma0) |- {{fctx w0 // fctx w1}} [M | fctx w1, length (Gamma1)] ::: A.
Admitted.

Lemma rename_ctx_preserv_types_new:
forall G G' w0 w1 Gamma0 Gamma1 M A
  (HT_G': permut G' (G & (w1, Gamma1)))
  (HT: G' |= (w0, Gamma0) |- M ::: A),
  G |= (w0, Gamma1++Gamma0) |- {{fctx w0 // fctx w1}} [M | fctx w0, length (Gamma1)] ::: A.
Admitted.

Lemma Progress:
forall G w M A
  (H_lc: lc_w_LF M)
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
inversion H_lc; subst.
destruct IHM1 with (Ctx := (w, (@nil ty_LF))) (G := G) (A := A0 ---> A) (w := w);
auto.
  inversion H0; subst; inversion HT1; subst; eexists; constructor.
  inversion H2; subst; assumption.
  assumption.
  destruct H0; eexists; constructor. 
  eapply H0.
  assumption.
  assumption.
(* unbox & unbox_fetch *)
right; inversion HT; subst.
(* unbox *)
inversion H_lc; subst.
destruct IHM with (Ctx := (w, (@nil ty_LF))) (G := G) (A := [*]A) (w := w);
auto.
  inversion H0; subst; inversion HT0; subst; eexists; constructor. 
  inversion H3; subst; assumption.
  destruct H0; eexists; constructor.
  eapply H0.
  apply closed_w_succ; assumption.
(* unbox_fetch *)
assert (Gamma = nil).
  apply emptyEquiv_nil with (G:=G) (G':=G0 & (w0, Gamma)) (w:=w0).
  apply permut_sym; assumption.
  rewrite Mem_app_or_eq; right; rewrite Mem_cons_eq; left; reflexivity.
subst. 
inversion H_lc; subst;
destruct IHM with (Ctx := (w0, (@nil ty_LF))) (G := G0 & (w, nil)) (A:=[*]A) (w:=w0).
assumption.
reflexivity.
assert (emptyEquiv (G0 & (w, nil)) = G0 & (w, nil)).
apply emptyEquiv_last.
apply emptyEquiv_inv with (w:=w0).
apply emptyEquiv_empty with (G := G).
  apply permut_sym; assumption.
rewrite H0; assumption.
inversion H0; subst; inversion HT0; subst. 
eexists; constructor.
inversion H3; subst; assumption.
destruct H0 as [M'].
eexists; constructor. eassumption. apply closed_w_succ; assumption.
(* here & get_here *)
inversion HT; subst.
(* here *)
inversion H_lc; subst.
destruct IHM with (G:=G) (w:=w) (A:=A0) (Ctx:=(w, (@nil ty_LF))); auto.
left; apply val_get_here_LF; assumption.
right; destruct H0; exists (get_here_LF (fctx w) x); eauto using step_LF.
(* get_here *)
inversion H_lc; subst;
assert (Gamma = nil).
  apply emptyEquiv_nil with (G:=G) (G':=G0 & (w0, Gamma)) (w:=w0).
  apply permut_sym; assumption.
  rewrite Mem_app_or_eq; right; rewrite Mem_cons_eq; left; reflexivity.
subst; destruct (IHM H3 (G0 & (w, nil)) w0 A0 (w0,nil)); auto.
assert (emptyEquiv (G0 & (w, nil)) = G0 & (w, nil)).
apply emptyEquiv_last.
apply emptyEquiv_inv with (w:=w0).
apply emptyEquiv_empty with (G := G).
  apply permut_sym; assumption.
rewrite H0; assumption.
left; econstructor; eassumption.
right; destruct H0; eexists; constructor; eassumption. 
(* letdia & letdia_get *)
inversion HT; subst;
inversion H_lc; subst.
(* letdia *)
right;
destruct IHM1 with  (G:=G) (w:=w) (A:=<*>A0) (Ctx:=(w, (@nil ty_LF))); auto.
inversion H0; subst; inversion HT1; subst.
  eexists; econstructor. 
  inversion H5; subst; assumption.
  eassumption.
  eexists; econstructor. inversion H5; subst; assumption. eassumption.
destruct H0; exists (letdia_get_LF (fctx w) x M2); eauto using step_LF.
(* letdia_get *)
right;
assert (Gamma = nil).
  apply emptyEquiv_nil with (G:=G) (G':=G0 & (w0, Gamma)) (w:=w0).
  apply permut_sym; assumption.
  rewrite Mem_app_or_eq; right; rewrite Mem_cons_eq; left; reflexivity.
subst; destruct (IHM1 H5 (G0 & (w, nil)) w0 (<*>A0) (w0,nil)); auto.
assert (emptyEquiv (G0 & (w, nil)) = G0 & (w, nil)).
apply emptyEquiv_last.
apply emptyEquiv_inv with (w:=w0).
apply emptyEquiv_empty with (G := G).
  apply permut_sym; assumption.
rewrite H0; assumption.
inversion H0; subst; inversion HT1; subst.
  eexists; econstructor; eauto.
  inversion H5; subst; assumption.
  eexists; econstructor; eauto.
  inversion H5; subst; eassumption.
  destruct H0; eexists; econstructor; eassumption.
Qed.

Lemma Fresh: 
  forall (L:fset var), exists w0, w0 \notin L.
intro;
exists (var_gen L);
apply var_gen_spec.
Qed.

Lemma Preservation:
forall G M N A w
  (HT: emptyEquiv G |= (w, nil) |- M ::: A)
  (HS: (M, fctx w) |-> (N, fctx w)),
  emptyEquiv G |= (w, nil) |- N ::: A.
intros;
remember (emptyEquiv G) as G';
remember (w, (@nil ty_LF)) as Ctx;
generalize dependent w;
generalize dependent N;
generalize dependent G;
induction HT; intros;
inversion HS; subst;
try (inversion HeqCtx; subst);
eauto using types_LF.
(* appl_lam *)
inversion HT1; subst.
replace ([N//0 | fctx w ] [M0 | fctx w]) with 
        (subst_list (N::nil) (length (@nil te_LF)) M0 (fctx w) (fctx w)) by auto.
apply subst_t_preserv_types_inner with (Delta := A::nil).
  simpl; split; auto.
  rewrite emptyEquiv_stable.
  assumption.
  intros; rewrite Mem_cons_eq in H; destruct H.
    subst; assumption.
    rewrite Mem_nil_eq in H; contradiction.
  assumption.
(* unbox_box *)
inversion HT; subst.
assert (exists w0, w0 \notin L \u free_worlds_LF M0).
  apply Fresh.
destruct H as [w1].
rewrite notin_union in H; destruct H.
unfold open_ctx in *.
apply inv_subst_ctx_preserv_types_new' with (w':=w1) (Gamma':=nil) (k:=0).
assumption.
apply rename_ctx_preserv_types_old with (G':=(emptyEquiv G0 & (w0, nil))).
permut_simpl.
apply HT0; auto.
(* unbox_fetch_box *)
inversion HT; subst.
assert (exists w0, w0 \notin L \u free_worlds_LF M0).
  apply Fresh.
destruct H0 as [w1].
rewrite notin_union in H0; destruct H0.
unfold open_ctx in *.
apply inv_subst_ctx_preserv_types_new' with (w':=w1) (Gamma':=nil) (k:=0).
assumption.
apply rename_ctx_preserv_types_old with (G':=(emptyEquiv G0 & (w0, nil))).
permut_simpl.
apply BackgroundSubsetImpl with (G:= G & (w0,nil) & (w,Gamma)).
  rew_app in *; apply HT0; auto.
  exists (@nil Context_LF); permut_simpl; assumption.
  auto.
(* unbox_fetch *)
apply t_unbox_fetch_LF with (G:=G) (Gamma:=Gamma).
assert (Gamma = nil).
apply emptyEquiv_nil with (G:=G0) (G':=G & (w, Gamma)) (w:=w).
  apply permut_sym; assumption.
  apply Mem_last.
subst.
apply IHHT with (G0:=G & (w0, nil)) (w1 := w).
rewrite emptyEquiv_last with (G':=G).
reflexivity.
apply emptyEquiv_inv with (w:=w).
apply emptyEquiv_permut with (G:=G0).
  apply permut_sym; assumption.
reflexivity.
assumption.
assumption.
(* get_here *)
apply t_get_here_LF with (G:=G) (Gamma:=Gamma); auto.
assert (Gamma = nil).
apply emptyEquiv_nil with (G:=G1) (G':=G & (w, Gamma)) (w:=w).
  apply permut_sym; assumption.
  apply Mem_last.
subst.
apply IHHT with (G0:=G & (w0,nil)) (w1:=w); auto.
rewrite emptyEquiv_last with (G':=G).
reflexivity.
apply emptyEquiv_inv with (w:=w).
apply emptyEquiv_permut with (G:=G1).
  apply permut_sym; assumption.
(* letdia + (here | get_here ) *)
inversion HT; subst.
(* letdia_here *)
assert (exists w1, w1 \notin L \u free_worlds_LF N) by apply Fresh.
destruct H0 as [w1];
apply notin_union in H0;
destruct H0.
replace ([M0 // 0 | fctx w0] [N ^^ [fctx w0 | fctx w0] | fctx w0])
   with (subst_list (M0::nil) (length (@nil te_LF)) (N ^^ [fctx w0 | fctx w0]) (fctx w0) (fctx w0)) by auto.
apply subst_t_preserv_types_inner with (Delta:=A::nil).
  simpl; split; auto;
  rewrite emptyEquiv_stable;
  assumption.
intros. rewrite Mem_cons_eq in H3; destruct H3.
  subst; assumption.
  rewrite Mem_nil_eq in H3; contradiction.
unfold open_ctx in *.
  replace (w0, (nil & A)) with (w0, (A::nil) ++ (@nil ty_LF)).
  apply inv_subst_ctx_preserv_types_new with (w':=w1) (Gamma':=A::nil) (k:=0).
  assumption.
  apply rename_ctx_preserv_types_new with (G':=(emptyEquiv G0 & (w1, A::nil))).
  permut_simpl.
  apply BackgroundSubsetImpl with (G:= (w1, A::nil) :: emptyEquiv G0).
  apply HT2; auto.
  eexists; permut_simpl.
  rew_app; reflexivity.
(* letdia__get_here *)
assert (exists w1, w1 \notin L \u free_worlds_LF N) by apply Fresh.
destruct H0 as [w1];
apply notin_union in H0;
destruct H0.
assert (Gamma = nil).
apply emptyEquiv_nil with (G:=G0) (G':=G & (w, Gamma)) (w:=w).
  apply permut_sym; assumption.
  apply Mem_last.
subst.
replace ([M0 // 0 | fctx w] [N ^^ [fctx w | fctx w0] | fctx w0])
   with (subst_list (M0::nil) (length (@nil te_LF)) (N ^^ [fctx w | fctx w0]) (fctx w) (fctx w0)) by auto.
apply subst_t_preserv_types_outer with (G0:=G) (Delta:=A::nil) (G':= G & (w0, nil)) (G'':= G & (w, nil & A)) (Gamma':= nil) .
  apply permut_sym; assumption.
  permut_simpl.
  permut_simpl.
  simpl; split; auto.
  rewrite emptyEquiv_last with (G':=G).
    assumption.
  apply emptyEquiv_inv with (w:=w).
  rewrite emptyEquiv_empty with (G:= emptyEquiv G0).
    reflexivity.
    rewrite emptyEquiv_stable.
    apply permut_sym; assumption.
intros. rewrite Mem_cons_eq in H3; destruct H3.
  subst; assumption.
  rewrite Mem_nil_eq in H3; contradiction.
  apply GlobalWeakening. (* sth is wrong with the conclusion of subst_t_.._outer *) 
  unfold open_ctx in *.
  apply inv_subst_ctx_preserv_types_outer with (G0:=G) (G:=G & (w, A::nil)) (w':=w1) (Gamma:=nil) (Gamma':=A::nil) (k:=0).
  assumption.
  permut_simpl.
  apply rename_ctx_preserv_types_outer with (G':=(emptyEquiv G0 & (w1, A::nil)))
    (G := G) (Gamma := nil).
  permut_simpl; apply permut_sym; assumption.
  permut_simpl.
  apply BackgroundSubsetImpl with (G:= (w1, A :: nil) :: emptyEquiv G0).
  apply HT2; auto.
  exists (@nil Context_LF); permut_simpl; assumption.
(* letdia_get + ( here | get_here) *)
inversion HT; subst.
(* letdia_get__here *)
assert (exists w1, w1 \notin L \u free_worlds_LF N).
  apply Fresh.
destruct H1 as [w2].
apply notin_union in H1;
destruct H1.
assert (Gamma = nil).
apply emptyEquiv_nil with (G:=G1) (G':=G & (w, Gamma)) (w:=w).
  apply permut_sym; assumption.
  apply Mem_last.
subst.
replace ([M0 // 0 | fctx w] [N ^^ [fctx w | fctx w0] | fctx w0])
   with (subst_list (M0::nil) (length (@nil te_LF)) (N ^^ [fctx w | fctx w0]) (fctx w) (fctx w0)) by auto.
apply subst_t_preserv_types_outer with (G0:=G) (Delta:=A::nil) (G':= G & (w0, nil)) (G'':= G & (w, nil & A)) (Gamma':= nil) .
  apply permut_sym; assumption.
  permut_simpl.
  permut_simpl.
  simpl; split; auto.
  rewrite emptyEquiv_last with (G':=G).
    assumption.
  apply emptyEquiv_inv with (w:=w).
  rewrite emptyEquiv_empty with (G:= emptyEquiv G1).
    reflexivity.
    rewrite emptyEquiv_stable.
    apply permut_sym; assumption.
intros. rewrite Mem_cons_eq in H4; destruct H4.
  subst; assumption.
  rewrite Mem_nil_eq in H4; contradiction.
  apply GlobalWeakening. (* sth is wrong with the conclusion of subst_t_.._outer *) 
  unfold open_ctx in *.
  apply inv_subst_ctx_preserv_types_outer with (G0:=G) (G:=G & (w, A::nil)) (w':=w2) (Gamma:=nil) (Gamma':=A::nil) (k:=0).
  assumption.
  permut_simpl.
  apply rename_ctx_preserv_types_outer with (G':=(emptyEquiv G1 & (w2, A::nil)))
    (G := G) (Gamma := nil).
  permut_simpl; apply permut_sym; assumption.
  permut_simpl.
  apply BackgroundSubsetImpl with (G:= (w2, A :: nil) :: G & (w,nil)).
  replace (fctx w0) with (fctx (fst (w0, (@nil ty_LF)))).
  apply HT2; auto.
  simpl; reflexivity.
  exists (@nil Context_LF); permut_simpl; assumption.
(* letdia_get_get_here *)
assert (Gamma = nil).
apply emptyEquiv_nil with (G:=G1) (G':=G & (w, Gamma)) (w:=w).
  apply permut_sym; assumption.
  apply Mem_last.
subst.
assert (Gamma0 = nil).
apply emptyEquiv_nil with (G:=G & (w0, nil)) (G':=G0 & (w1, Gamma0)) (w:=w1).
  rewrite emptyEquiv_last with (G':=G).
  apply permut_sym; assumption.
  apply emptyEquiv_inv with (w:=w).
  apply emptyEquiv_permut with (G:=G1).
  apply permut_sym; assumption.
  apply Mem_last.
subst.
assert (exists w1, w1 \notin L \u free_worlds_LF N).
  apply Fresh.
destruct H1 as [w2].
apply notin_union in H1;
destruct H1.
replace ([M0 // 0 | fctx w1] [N ^^ [fctx w1 | fctx w0] | fctx w0])
   with (subst_list (M0::nil) (length (@nil te_LF)) (N ^^ [fctx w1 | fctx w0]) (fctx w1) (fctx w0)) by auto.
(* ! *)
destruct (eq_var_LF_dec w0 w1).
(* = *)
subst.
assert (permut (G0 & (w1, nil) ++ nil) (G & (w1, nil) ++ nil)).
rew_app; assumption.
apply permut_inv in H4; rew_app in H4.
apply subst_t_preserv_types_inner with (Delta:=A::nil).
simpl; split; auto.
rewrite emptyEquiv_stable.
apply BackgroundSubsetImpl with (G:=G0 & (w,nil)).
assumption.
exists (@nil Context_LF).
rew_app.
apply permut_trans with (l2:=G&(w,nil));
permut_simpl; assumption.
intros. rewrite Mem_cons_eq in H6; destruct H6.
  subst; assumption.
  rewrite Mem_nil_eq in H6; contradiction.
unfold open_ctx in *.
replace (w1, (nil & A)) with (w1, (A::nil) ++ (@nil ty_LF)).
  apply inv_subst_ctx_preserv_types_new with (w':=w2) (k:=0). 
  assumption.
apply rename_ctx_preserv_types_new with (G':=(emptyEquiv G1 & (w2, A::nil))).
permut_simpl.
  apply BackgroundSubsetImpl with (G:= (w2, A :: nil) :: G & (w, nil)).
  apply HT2.
  assumption.
  exists (@nil Context_LF); permut_simpl; assumption.
  auto.
(* <> *)
assert (exists GH, exists GT, G = GH & (w1, nil) ++ GT). 
apply permut_split_neq with (G := G0) (G' := nil) (elem' := (w0, nil)).
intro; inversion H4; subst; elim n; reflexivity.
rew_app; assumption.
destruct H4 as (GH).
destruct H4 as (GT).
subst G.
assert (permut (G0++nil) (GH ++ GT & (w0,nil)++nil )).
  apply permut_inv with (elem:=(w1,nil)); rew_app.
  apply permut_trans with (l2:=(GH & (w1, nil) ++ GT) & (w0, nil)).
    assumption.
    permut_simpl.
rew_app in H4.
destruct (eq_var_LF_dec w w0).
(* = *)
apply subst_t_preserv_types_outer with (G0 := GH++GT & (w,nil)) 
  (Delta:=A::nil) (G':= G0 & (w, nil)) (G'':= G0 & (w1, nil & A)) (Gamma':= nil).
  apply permut_trans with (l2:=(GH & (w1, nil) ++ GT) & (w, nil)).
    apply permut_sym; assumption.
    permut_simpl. 
  permut_simpl; assumption.
  permut_simpl; subst; assumption.
  simpl; split; auto.
  rewrite emptyEquiv_last with (G':=G0).
    assumption.
  apply emptyEquiv_inv with (w:=w1).
  rewrite emptyEquiv_empty with (G:= G1).
    reflexivity.
    apply permut_trans with (l2:= (GH & (w1, nil) ++ GT) & (w, nil)).
    apply permut_sym; assumption.
    permut_simpl; apply permut_sym; subst; assumption.
intros. rewrite Mem_cons_eq in H6; destruct H6.
  subst; assumption.
  rewrite Mem_nil_eq in H6; contradiction.
apply GlobalWeakening. (* sth is wrong with the conclusion of subst_t_.._outer *) 
unfold open_ctx in *.
subst.
  apply inv_subst_ctx_preserv_types_outer with (w':=w2) (Gamma':=A::nil) (Gamma:=nil) (G0:=G0). 
  assumption.
  permut_simpl.
  apply rename_ctx_preserv_types_outer with (G':=(emptyEquiv G1 & (w2, A::nil)))
    (G := G0) (Gamma := nil).
  permut_simpl. 
  apply permut_trans with (l2:=(GH & (w1, nil) ++ GT) & (w0, nil)).
    apply permut_sym; assumption.
    permut_simpl; apply permut_sym; assumption.
  permut_simpl.
  apply BackgroundSubsetImpl with (G:= (w2, A :: nil) :: (GH & (w1, nil) ++ GT) & (w0,nil)).
  replace (fctx w0) with (fctx (fst (w0, (@nil ty_LF)))).
  apply HT2; auto.
  simpl; reflexivity.
  exists (@nil Context_LF). permut_simpl. rew_app in *; assumption.
(* <> *)
clear H5.
assert (permut (emptyEquiv G1 & (w0, nil)) (G0 & (w1,nil) &(w,nil))).
  apply permut_trans with (l2:=GH & (w1, nil) ++ GT & (w,nil)  & (w0, nil) ).
  permut_simpl. rew_app in H0. rew_app. apply permut_sym; assumption.
  permut_simpl; apply permut_sym; assumption.
assert (exists GH', exists GT', G0 & (w1,nil) = GH' & (w0,nil) ++ GT').
apply permut_split_neq with (G := emptyEquiv G1) (G' := nil) (elem' := (w, nil)).
intro; inversion H6; subst; elim n0; reflexivity.
rew_app in *; assumption.
destruct H6 as (GH').
destruct H6 as (GT').
assert (exists GH'', exists GT'', G0 = GH'' & (w0, nil) ++ GT'').
apply permut_split_neq with (G := GH') (G' := GT') (elem' := (w1, nil)).
intro; inversion H8; subst; elim n; reflexivity.
rewrite <- H6; permut_simpl.
destruct H8 as (GH'').
destruct H8 as (GT'').
subst G0.
assert (permut (emptyEquiv G1 ++ nil) ((GH'' ++ GT'') & (w, nil) & (w1, nil))).
apply permut_inv with (elem := (w0,nil)).
rew_app in *.
apply permut_trans with (l2:=(GH'' ++ (w0, nil) :: GT'' ++ (w1, nil) :: (w, nil) :: nil)).
assumption. permut_simpl.
apply subst_t_preserv_types_outer with (G0 := GH''++GT'' & (w, nil)) 
  (Delta:=A::nil) (G':= GH'' ++ GT'' & (w, nil) & (w0, nil)) (G'':= (GH'' ++ GT'' & (w, nil)) & (w1, nil & A)) (Gamma':= nil).
  permut_simpl; rew_app in *; assumption.
  permut_simpl.
  permut_simpl. 
  simpl; split; auto.
  rewrite emptyEquiv_inv with (w:=w1) (G':=(GH'' ++ GT'' & (w, nil) & (w0, nil))).
  apply BackgroundSubsetImpl with (G:=(GH'' & (w0, nil) ++ GT'') & (w, nil)).
  apply HT0.
  exists (@nil Context_LF); permut_simpl.
  apply emptyEquiv_last.
  replace ( GH'' ++ GT'' & (w, nil) & (w0, nil) ) with (( GH'' ++ GT'' & (w, nil)) & (w0, nil)).
  apply emptyEquiv_last.
  apply emptyEquiv_inv with (w:=w1).
  apply emptyEquiv_permut with (G:=G1). 
  rew_app in *. assumption.
  rew_app; reflexivity.
intros. rewrite Mem_cons_eq in H9; destruct H9.
  subst; assumption.
  rewrite Mem_nil_eq in H9; contradiction.
apply GlobalWeakening. (* sth is wrong with the conclusion of subst_t_.._outer *) 
unfold open_ctx in *.
  apply inv_subst_ctx_preserv_types_outer with (w':=w2) (Gamma':=A::nil) (Gamma:=nil) (G0:=(GH'' ++ GT'' & (w, nil))).
  assumption.
  permut_simpl.
  replace (fctx w0) with (fctx (fst (w0, (@nil ty_LF)))).
  apply rename_ctx_preserv_types_outer with (G':=(emptyEquiv G1 & (w2, A::nil))) (Gamma:=nil) (G:=GH''++GT'' & (w,nil)).
  permut_simpl; rew_app in H8.
  apply permut_trans with (l2:=GH'' ++ GT'' ++ (w, nil) :: (w1, nil) :: nil).
    assumption.
    permut_simpl.
  permut_simpl.
  apply BackgroundSubsetImpl with (G:=(w2, A :: nil) :: (GH & (w1, nil) ++ GT) & (w, nil)).
  apply HT2 with (w':=w2); auto.
  exists (@nil Context_LF). permut_simpl.
  rew_app in *; assumption.
  simpl; reflexivity.
(* letdia_get *)
apply t_letdia_get_LF with (L:=L)(A:=A) (G:=G) (Gamma:=Gamma); auto.
assert (Gamma = nil).
apply emptyEquiv_nil with (G:=G1) (G':=G & (w, Gamma)) (w:=w).
  apply permut_sym; assumption.
  apply Mem_last.
subst.
apply IHHT with (G0:=G & (w0,nil)) (w1:=w); auto.
rewrite emptyEquiv_last with (G':=G).
reflexivity.
apply emptyEquiv_inv with (w:=w).
apply emptyEquiv_permut with (G:=G1).
  apply permut_sym; assumption.
Qed.

End Lemmas.

Close Scope label_free_is5_scope.
