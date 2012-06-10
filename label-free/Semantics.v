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

Fixpoint ok_Bg (G: Background_LF) (Used: list var) : Prop :=
match G with
| nil => True
| (w, Gamma) :: G' => 
    If (Mem w Used) then False 
    else ok_Bg G' (w::Used)
end.

Inductive types_LF: Background_LF -> Context_LF -> te_LF -> ty_LF -> Prop :=

| t_hyp_LF: forall A G w Gamma v_n
  (HT: Nth v_n Gamma A),
  G |= (w, Gamma) |- hyp_LF v_n ::: A

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
  forall G', permut (G & (w, Gamma)) G' -> 
    G' |= Ctx' |- get_here_LF (fctx w) M ::: <*> A

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
Implicit Type l : list A.

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

(* TODO: Reconsider Permutation from standard library and / or make permut a Setoid *)
(* TODO: Move the extended permutation lib to a separate file *)

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
  apply permut_trans with (l2:= G' ++ GT)]; 
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
  assert (permut (G & (w, Gamma)) (G'0 & (w, Gamma))).
  apply permut_trans with (l2:=G'); assumption.
  replace G with (G++nil) by (rew_app; reflexivity).
  replace G'0 with (G'0++nil) by (rew_app; reflexivity).
  apply permut_inv with (elem:=(w, Gamma)).
  rew_app; assumption.
(* <> *)
assert (exists G0, exists G1, G'0 = G0 & (w, Gamma) ++ G1).
  apply permut_split_neq with (G:=G) (G':=nil) (elem':=(w', Delta)).
    intro e; symmetry in e; contradiction.
    rew_app; apply permut_trans with (l2:=G'); assumption.
destruct H1 as [GH]; destruct H1 as [GT]; subst G'0.
apply t_get_here_LF with (Gamma:=Gamma) (G:=GH ++ GT & (w', Delta ++ Delta')).
apply BackgroundSubsetImpl with (G:= (GH ++ GT & (w0, Gamma0)) & (w', Delta ++ Delta')).
  specialize IHHT with w Gamma.
  apply IHHT. 
  reflexivity.
  assert (permut (G++nil) (GH++GT & (w', Delta))).
    apply permut_inv with (elem := (w ,Gamma)).
    apply permut_trans with (l2:=G').
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
      (w'', (A::nil)) :: G & (w, Gamma) ++ G' |= (w', Gamma') 
        |- N ^^ [fctx w'' | fctx w'] ::: B) ->
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

(* emptyEquiv = map (fun x => (x, nil)) (map fst G) *)
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
forall G G' Gamma w,
  emptyEquiv G = G' ->
  emptyEquiv (G & (w, Gamma)) = G' & (w, nil).
Admitted.

Lemma emptyEquiv_stable:
forall G,
  emptyEquiv (emptyEquiv G) = emptyEquiv G.
Admitted.

Lemma emptyEquiv_permut:
forall G G',
  permut G G' ->
  permut (emptyEquiv G) (emptyEquiv G').
Admitted.

Lemma emptyEquiv_typing:
forall G w Gamma M A
  (HT: emptyEquiv G |= (w, Gamma) |- M ::: A),
  G |= (w, Gamma) |- M ::: A.
Admitted.

Lemma emptyEquiv_dom:
forall G,
  map fst G = map fst (emptyEquiv G).
Admitted.

(* TODO: get rid of this, using ok_Bg instead should work! *)
Lemma unique_worlds:
forall G G' w w' Gamma Gamma' M A
  (HPermut: permut G' (G & (w', Gamma')))
  (HT: G' |= (w, Gamma) |- M ::: A),
  w <> w'.
Admitted.

Lemma Nth_last:
forall Gamma (A: ty_LF) A',
  Nth (length Gamma) (Gamma & A) A' -> A = A'.
Admitted.

Lemma Nth_not_last:
forall Gamma (A: ty_LF) A' n,
  Nth n (Gamma & A) A' ->
  n <> length Gamma ->
  Nth n Gamma A'.
Admitted.

(* TODO: It's not really smart yet.. *)
(* Goal of smart destruct is to destruct chains of assumptions without loosing
   any of them; it should also work when the chain is conditional, but the
   condition is easily checked to be true (e.g. provable by reflexivity) *)
Ltac smart_destruct :=
match goal with
| [H: ?w = ?w -> _ |- _] => destruct H; [reflexivity | try smart_destruct]
| [H: ?w = ?w -> ?w' = ?w' -> _ |- _] => 
  destruct H; [reflexivity | reflexivity | try smart_destruct]
| [H: ?t1 = ?t2 /\ _ |- _] => destruct H; try smart_destruct 
end.

Lemma ok_Bg_permut:
forall G G' L,
  permut  G G' ->
  ok_Bg G L -> ok_Bg G' L.
Admitted.

Lemma ok_Bg_change_last:
forall G w Gamma Gamma' L,
  ok_Bg (G & (w, Gamma)) L ->
  ok_Bg (G & (w, Gamma')) L.
Admitted.

Lemma ok_Bg_emptyEquiv:
forall G L,
  ok_Bg G L = ok_Bg (emptyEquiv G) L.
Admitted.

(* TODO: add_fresh and add_new are too specialized and should be 
         removed (or changed) *)
Lemma ok_Bg_add_fresh:
forall G w Gamma w' Gamma' L,
  w' \notin (\{w} \u from_list (map fst G) \u from_list L) ->
  ok_Bg ((w, Gamma)::G) L ->
  ok_Bg ((w', Gamma') :: (w, Gamma) :: G) L. 
Admitted.

Lemma ok_Bg_add_new:
forall G w Gamma L,
  w \notin from_list(map fst G) ->
  ok_Bg G L ->
  ok_Bg ((w, Gamma) :: G) L.
Admitted.

Lemma ok_Bg_unify:
forall G G0 G1 w Gamma Gamma',
  permut G (G0 & (w, Gamma)) ->
  permut G (G1 & (w, Gamma')) ->
  ok_Bg G nil ->
  Gamma = Gamma'.
Admitted.

Lemma ok_Bg_step:
forall G L w,
  ok_Bg G (w::L) ->
  ok_Bg G L.
Admitted.

Lemma ok_Bg_swap:
forall G w Gamma Gamma' L,
  ok_Bg (G & (w, Gamma)) L ->
  ok_Bg ((w, Gamma')::G) L.
Admitted.

Lemma emptyEquiv_mem:
forall G G' w,
  permut (emptyEquiv G) (emptyEquiv G') ->
  w \notin from_list (map fst G) -> 
  w \notin from_list (map fst G').
Admitted.

Fixpoint subst_typing G L D w : Prop :=
match L, D with
| nil, nil => True
| M::L', A :: D' => emptyEquiv G |= (w, nil) |- M ::: A /\ (subst_typing G L' D' w)
| _, _ => False
end.

Ltac try_rewrite_subst :=
try repeat rewrite subst_t__inner;
try repeat erewrite subst_t__outer;
try repeat rewrite subst_ctx__new;
try repeat rewrite subst_ctx__old;
try repeat rewrite subst_ctx__outer; 
eauto.

Lemma subst_t_preserv_types_end:
forall G_HT w Gamma_HT M N B
  (H_lc: lc_w_LF M)
  (H_G_ok: ok_Bg ((w, Gamma_HT) :: G_HT) nil)
  (HT: G_HT |= (w, Gamma_HT) |- N ::: B),
  forall A Gamma_TS w_subst G_min Gamma_subst G_TS G0,
  ( emptyEquiv G_HT |= (w, nil) |- M ::: A ->
    Gamma_HT = Gamma_TS & A ->
    G_HT |= (w, Gamma_TS) |- [ M // length Gamma_TS | fctx w] [ N | fctx w ] ::: B)
  /\
  ( permut G_min (G0 & (w, Gamma_HT)) ->
    permut G_HT (G0 & (w_subst, Gamma_subst & A)) ->
    permut G_TS (G0 & (w_subst, Gamma_subst)) -> 
    w_subst <> w ->
    ok_Bg ((w_subst, nil)::G_min) nil -> 
    ok_Bg ((w, Gamma_HT) :: G_TS) nil ->
    emptyEquiv G_min |= (w_subst, nil) |- M ::: A ->
    G_TS |= (w, Gamma_HT) |- [ M // length Gamma_subst | fctx w_subst] [ N | fctx w ] ::: B).
intros until A;
remember (w, Gamma_HT) as Ctx_HT;
generalize dependent Gamma_HT;
generalize dependent w;
generalize dependent A;
induction HT; intros; split; 
inversion HeqCtx_HT;
subst; unfold subst_t; intros;
case_if; simpl; subst.

(* hyp inner *)
case_if; subst.
(* v_n = length Gamma *)
apply Nth_last in HT; subst;
replace Gamma_TS with (nil ++ Gamma_TS) by auto;
apply Weakening;
apply emptyEquiv_typing in H; assumption.
(* v_n <> length Gamma *)
constructor;
generalize dependent v_n;
induction Gamma_TS; simpl in *; intros.
(* nil *)
rew_length in H0;
destruct v_n;
[ elim H0; reflexivity | 
  inversion HT; subst]; 
apply Nth_nil_inv in H6; contradiction.
(* step *)
destruct v_n; simpl in *;
inversion HT; subst;
eapply Nth_not_last;
eassumption.

(* hyp outer *)
constructor; assumption.

(* lam inner *)
constructor; subst;
replace (S (length Gamma_TS)) with (length (A0 :: Gamma_TS)) by (rew_length; omega);
rewrite subst_t__inner;
eapply IHHT with (Gamma_TS := A::Gamma_TS); eauto.

(* lam outer *)
constructor; subst;
rewrite subst_t__outer with (w':=fctx w0); auto;
eapply IHHT; eauto.
replace ((w_subst, nil) :: G0 & (w0, A :: Gamma_HT)) with 
        (((w_subst, nil) :: G0) & (w0, A :: Gamma_HT)) by (rew_app; reflexivity).
apply ok_Bg_change_last with (Gamma:= Gamma_HT).
apply ok_Bg_permut with (G := (w_subst, nil)::G_min); try permut_simpl; auto.
apply emptyEquiv_permut in H;
rewrite emptyEquiv_last with (G':=emptyEquiv G0) in H; auto.
rewrite emptyEquiv_last with (G':=emptyEquiv G0); auto;
apply BackgroundSubsetImpl with (G:=emptyEquiv G_min);
[ | exists (@nil Context_LF); permut_simpl]; auto;
erewrite <- emptyEquiv_last; eauto;
eapply emptyEquiv_permut; eauto.

(* appl inner *)
apply t_appl_LF with (A:=A);
rewrite subst_t__inner;
[edestruct IHHT1 | edestruct IHHT2];
eauto.

(* appl outer *)
apply t_appl_LF with (A:=A); subst;
rewrite subst_t__outer with (w':=fctx w); auto;
[ eapply IHHT1 | 
  eapply IHHT2 ]; 
eauto.

(* box inner *)
apply t_box_LF with (L:=L \u \{w} \u from_list(map fst G)); intros;
repeat rewrite notin_union in H2; destruct H2 as (H2a, H2b);
destruct H2b as (H2b, H2c);
assert (w' <> w) by
 (intro; subst; rewrite notin_singleton in H2b; elim H2b; reflexivity);
rewrite subst_t__outer with (w':=fctx w'); 
try (intro nn; inversion nn; subst; elim H2; reflexivity);
unfold open_ctx in *;
rewrite <- subst_order_irrelevant; eauto;
eapply H; eauto.

apply ok_Bg_permut with (G:=(w',nil)::(w, Gamma_TS & A0)::G); try permut_simpl.
apply ok_Bg_add_fresh;
[repeat rewrite notin_union; repeat split | ]; auto. apply notin_empty.

simpl. simpl in H_G_ok. case_if.
apply ok_Bg_permut with (G:=(w',nil)::G). 
permut_simpl.
apply ok_Bg_add_new. assumption.
assumption.

remember ((w',nil)::G) as G_w'.
assert (ok_Bg (G_w' & (w, Gamma_TS)) nil).
apply ok_Bg_change_last with (Gamma:=Gamma_TS & A0).
assert (ok_Bg ((w', nil) :: G & (w, Gamma_TS & A0)) nil).
apply ok_Bg_permut with (G:=(w',nil)::(w, Gamma_TS & A0)::G); try permut_simpl.
apply ok_Bg_add_fresh.
repeat rewrite notin_union; repeat split; try assumption.
apply notin_empty.

assumption.
subst; rew_app in *; assumption.
subst; rew_app in *; assumption.

rewrite emptyEquiv_last with (G':=emptyEquiv G); auto;
replace (emptyEquiv G & (w', nil)) with (emptyEquiv G & (w', nil) ++ nil) 
  by (rew_app; reflexivity);
apply GlobalWeakening; rew_app; assumption.

(* box outer *)
apply t_box_LF with (L:=L \u \{w_subst} \u \{w} \u from_list (map fst G)); intros;
apply notin_union in H9; destruct H9;
apply notin_union in H10; destruct H10;
apply notin_union in H11; destruct H11;
rewrite subst_t__outer with (w':=fctx w');
try (intro nn; inversion nn; subst; elim H8; reflexivity);
unfold open_ctx in *.
rewrite <- subst_order_irrelevant; auto;
assert (permut (G & (w, Gamma_HT)) (G0 & (w, Gamma_HT) & (w_subst, Gamma_subst & A0)))by
  (permut_simpl; assumption);
eapply H; eauto.

apply ok_Bg_permut with (G:=(w',nil)::(w, Gamma_HT)::G); try permut_simpl.
apply ok_Bg_add_fresh;
[repeat rewrite notin_union; repeat split | ]; try assumption;
apply notin_empty.

apply permut_trans with (l2:=G0 & (w_subst, Gamma_subst) & (w, Gamma_HT));
[ apply permut_app_l; assumption | permut_simpl].

rewrite ok_Bg_emptyEquiv.
apply ok_Bg_permut with (G:=emptyEquiv((w',nil)::(w, Gamma_HT)::G)).
apply emptyEquiv_permut in H2. 
simpl; simpl in H2.
rewrite emptyEquiv_last with (G':=emptyEquiv G0 & (w, nil)).
rewrite emptyEquiv_last with (G':=emptyEquiv G0) in H2. 
permut_simpl.
apply permut_trans with (l2:=emptyEquiv (G0 & (w_subst, Gamma_HT))).
  rewrite emptyEquiv_last with (G' := emptyEquiv G0).
  assumption.
reflexivity.
  rewrite emptyEquiv_last with (G' := emptyEquiv G0).
permut_simpl.
reflexivity.
reflexivity.
  rewrite emptyEquiv_last with (G' := emptyEquiv G0).
  reflexivity.
  reflexivity.
rewrite <- ok_Bg_emptyEquiv.
apply ok_Bg_add_fresh;
[repeat rewrite notin_union; repeat split | ]; auto.
apply notin_empty.

rewrite ok_Bg_emptyEquiv.
apply ok_Bg_permut with (G:=emptyEquiv((w',nil)::(w, Gamma_HT)::G)).
apply emptyEquiv_permut in H3. 
simpl; simpl in H3.
permut_simpl.
apply permut_trans with (l2:=emptyEquiv (G0 & (w_subst, Gamma_subst) & (w, Gamma_HT))).
rewrite emptyEquiv_last with (G':=emptyEquiv (G0 & (w_subst, nil))).
rewrite emptyEquiv_last with (G':=emptyEquiv G0).
permut_simpl.
apply emptyEquiv_permut in H2.
rewrite emptyEquiv_last with (G':=emptyEquiv G0) in H2. 
assumption.
reflexivity.
reflexivity.
rewrite emptyEquiv_last with (G':=emptyEquiv G0).
rewrite emptyEquiv_last with (G':=emptyEquiv G0).
reflexivity.
reflexivity.
reflexivity.
apply permut_sym.
rewrite emptyEquiv_last with (G':= emptyEquiv G_TS). 
rewrite emptyEquiv_last with (G':= emptyEquiv (G0 & (w_subst, Gamma_subst))). 
permut_simpl. assumption.
reflexivity.
reflexivity.
rewrite <- ok_Bg_emptyEquiv.
apply ok_Bg_add_fresh;
[repeat rewrite notin_union; repeat split | ]; auto;
apply notin_empty.

rewrite emptyEquiv_last with (G' := emptyEquiv (G0 & (w, Gamma_HT))); auto;
replace (emptyEquiv (G0 & (w, Gamma_HT)) & (w', nil)) with (emptyEquiv (G0 & (w, Gamma_HT)) & (w', nil) ++ nil) by (rew_app; auto).
apply GlobalWeakening; rew_app;
apply BackgroundSubsetImpl with (G:= emptyEquiv G_min);
[ assumption | exists (@nil Context_LF)]; 
permut_simpl; apply emptyEquiv_permut; assumption.
intro nn; inversion nn; subst. rewrite notin_singleton in H10. elim H10; reflexivity.

(* unbox inner *)
case_if; constructor; 
rewrite subst_t__inner;
eapply IHHT; eauto.

(* unbox outer *)
case_if;
constructor;
rewrite subst_t__outer with (w':=fctx w0); eauto;
eapply IHHT; eauto.

(* unbox_fetch inner *)
assert (w0 <> w) by
  (apply emptyEquiv_permut in H;
   apply BackgroundSubsetImpl with (G':=emptyEquiv (G & (w, Gamma))) in H1;
   try rewrite emptyEquiv_last with (G':=emptyEquiv G) in H1; auto;
   try eapply unique_worlds; eauto;
   exists (@nil Context_LF); permut_simpl; apply permut_sym; auto);
case_if;
apply t_unbox_fetch_LF with (G:=G) (Gamma:=Gamma); auto;
rewrite subst_t__outer with (w':=fctx w); eauto;
eapply IHHT; eauto.

apply ok_Bg_permut with (G:=(w0, Gamma_TS & A0) :: G').
apply permut_trans with (l2:=(w0, Gamma_TS & A0) :: (w,Gamma)::G).
permut_simpl. apply permut_sym; apply permut_trans with (l2:=G & (w, Gamma)).
permut_simpl. assumption.
permut_simpl.
assumption.

rewrite ok_Bg_emptyEquiv.
apply ok_Bg_permut with (G:= emptyEquiv ((w0, Gamma_TS & A0) :: G')).
simpl; permut_simpl; apply emptyEquiv_permut in H. 
apply permut_sym; assumption.
rewrite <- ok_Bg_emptyEquiv; assumption.

assert (permut ((w, Gamma)::G & (w0, Gamma_TS & A0)) ((w0, Gamma_TS & A0) :: G')).
apply permut_trans with (l2:=((w0, Gamma_TS & A0) :: G & (w, Gamma))).
permut_simpl. permut_simpl; assumption.
rewrite ok_Bg_emptyEquiv.
apply ok_Bg_permut with (G:=emptyEquiv ((w0, Gamma_TS & A0) :: G')).
apply emptyEquiv_permut in H5. apply permut_sym.
remember ((w, Gamma) :: G) as G_w. 
assert (permut (emptyEquiv (G_w & (w0, Gamma_TS))) (emptyEquiv ((w0, Gamma_TS & A0) :: G'))).
rewrite emptyEquiv_last with (G':=emptyEquiv G_w). 
replace ((w, Gamma) :: G & (w0, Gamma_TS & A0)) with (G_w & (w0, Gamma_TS & A0)) in H5.
rewrite emptyEquiv_last with (G':=emptyEquiv G_w) in H5. 
assumption.
reflexivity.
subst; rew_app; reflexivity.
reflexivity.
subst; rew_app in *; assumption.
rewrite ok_Bg_emptyEquiv in H_G_ok; assumption.

apply BackgroundSubsetImpl with (G:=emptyEquiv G');
[ assumption |
  exists (@nil Context_LF)];
rew_app; apply emptyEquiv_permut;
apply permut_sym; assumption.

(* unbox_fetch outer *)
case_if.
(* switch back to inner *)
inversion H9; subst.
assert (Gamma_subst & A0 = Gamma). 
apply ok_Bg_unify with (G:=G') (G0:=G0) (G1:= G) (w:=w).
assumption.
apply permut_sym; assumption.
simpl in H_G_ok. rewrite Mem_nil_eq in H_G_ok. case_if.
apply ok_Bg_step in H_G_ok; assumption.
subst Gamma.

assert (permut G G0).
assert (permut (G & (w, Gamma_subst & A0) ++ nil) (G0 & (w, Gamma_subst & A0) ++ nil)).
rew_app; apply permut_trans with (l2:=G'); assumption.
apply permut_inv in H10. rew_app in H10; assumption.

apply t_unbox_fetch_LF with (G:=G) (Gamma:=Gamma_subst).
rewrite subst_t__inner.
eapply IHHT with (Gamma_TS := Gamma_subst) (Gamma_HT0 := Gamma_subst & A0) (w1 := w) (A1:=A0); eauto.

apply ok_Bg_permut with (G:=(w0, Gamma_HT) :: G').
apply permut_trans with (l2:=((w0, Gamma_HT)::(w, Gamma_subst & A0) :: G)).
permut_simpl.
apply permut_trans with (l2:= (G0 & (w, Gamma_subst & A0))).
assumption.
permut_simpl. apply permut_sym; assumption.
permut_simpl.
assumption.

apply BackgroundSubsetImpl with (G:=emptyEquiv G_min); eauto.
exists (@nil Context_LF). 
apply permut_trans with (l2:=emptyEquiv (G0 & (w0, Gamma_HT))).
apply emptyEquiv_permut in H1; rew_app; assumption.
apply emptyEquiv_permut; apply permut_sym; apply permut_app_l; assumption.
apply permut_trans with (l2:=G0 & (w, Gamma_subst)).
apply permut_app_l; assumption.
apply permut_sym; assumption.
(* stay in outer *)
assert (exists GH, exists GT, G0 = GH & (w, Gamma) ++ GT).
apply permut_split_neq with (G:=G) (G':=nil) (elem':=(w_subst, Gamma_subst & A0)).
intro nn; inversion nn; subst; elim H9; reflexivity.
apply permut_trans with (l2:=G'). 
rew_app; assumption.
assumption.

destruct H10 as [GH]; destruct H10 as [GT].
apply t_unbox_fetch_LF with (G:=GH++GT & (w_subst, Gamma_subst)) (Gamma:=Gamma).
rewrite subst_t__outer with (w':= fctx w).
subst.
eapply IHHT with (Gamma_subst := Gamma_subst) (w_subst:=w_subst) (w1:=w) (G0:=GH ++ GT & (w0, Gamma_HT)) (G_TS:=(GH++GT & (w_subst, Gamma_subst)) & (w0, Gamma_HT)) (A0:=A0); eauto.

apply ok_Bg_permut with (G:=(w0, Gamma_HT) :: G').
apply permut_trans with (l2:= (w0, Gamma_HT) :: (G & (w, Gamma))).
permut_simpl. apply permut_sym; assumption.
permut_simpl.
assumption.

apply permut_trans with (l2:=((GH ++ GT & (w_subst, Gamma_subst & A0)) & (w0, Gamma_HT))).
apply permut_app_l.
assert (permut (G & (w, Gamma)) ((GH & (w, Gamma) ++ GT) & (w_subst, Gamma_subst & A0))). 
apply permut_trans with (l2:=G'); assumption.
replace G with (G++nil).
replace (GH ++ GT & (w_subst, Gamma_subst & A0)) with (GH ++ GT & (w_subst, Gamma_subst & A0) ++ nil).
apply permut_inv with (elem:=(w, Gamma)).
rew_app in *; assumption.
rew_app; reflexivity.
rew_app; reflexivity.
permut_simpl.

permut_simpl.
intro nn; subst; elim H9; reflexivity.

apply ok_Bg_permut with (G:= (w_subst, nil):: G_min).
permut_simpl.
apply permut_trans with (l2:=(GH & (w, Gamma) ++ GT) & (w0, Gamma_HT)).
assumption.
permut_simpl.
assumption.

apply ok_Bg_permut with (G:= (w_subst, Gamma_subst)::G_min).
permut_simpl.
apply permut_trans with (l2:=(GH & (w, Gamma) ++ GT) & (w0, Gamma_HT)).
assumption.
permut_simpl.
rewrite ok_Bg_emptyEquiv.
rewrite ok_Bg_emptyEquiv in H5.
simpl in *. rewrite Mem_nil_eq in *. case_if.
assumption.

apply BackgroundSubsetImpl with (G:=emptyEquiv G_min).
eassumption.
exists (@nil Context_LF).
apply permut_trans with (l2:=emptyEquiv ((GH & (w, Gamma) ++ GT) & (w0, Gamma_HT))).
apply emptyEquiv_permut in H1; rew_app in *; assumption.
apply emptyEquiv_permut; permut_simpl.
assumption.
apply permut_trans with (l2:=G0 & (w_subst, Gamma_subst)).
subst; permut_simpl.
apply permut_sym; assumption.

(* here inner *)
case_if; constructor; 
rewrite subst_t__inner;
eapply IHHT; eauto.

(* here outer *)
case_if; constructor;
rewrite subst_t__outer with (w':=fctx w0); auto;
eapply IHHT; eauto.

(* get_here inner *)
assert (w0 <> w) by
  (apply emptyEquiv_permut in H;
   apply BackgroundSubsetImpl with (G':=emptyEquiv (G & (w, Gamma))) in H1;
   try rewrite emptyEquiv_last with (G':=emptyEquiv G) in H1; auto;
   try eapply unique_worlds; eauto;
   exists (@nil Context_LF); permut_simpl; apply permut_sym; auto);
case_if.
apply t_get_here_LF with (G:=G) (Gamma:=Gamma); auto;
rewrite subst_t__outer with (w':=fctx w); eauto;
eapply IHHT; eauto.

apply ok_Bg_permut with (G:=(w0, Gamma_TS & A0) :: G').
apply permut_trans with (l2:=(w0, Gamma_TS & A0) :: (w,Gamma)::G).
permut_simpl. apply permut_sym; apply permut_trans with (l2:=G & (w, Gamma)).
permut_simpl. assumption.
permut_simpl.
assumption.

rewrite ok_Bg_emptyEquiv.
apply ok_Bg_permut with (G:= emptyEquiv ((w0, Gamma_TS & A0) :: G')).
simpl; permut_simpl; apply emptyEquiv_permut in H. 
apply permut_sym; assumption.
rewrite <- ok_Bg_emptyEquiv; assumption.

assert (permut ((w, Gamma)::G & (w0, Gamma_TS & A0)) ((w0, Gamma_TS & A0) :: G')).
apply permut_trans with (l2:=((w0, Gamma_TS & A0) :: G & (w, Gamma))).
permut_simpl. permut_simpl; assumption.
rewrite ok_Bg_emptyEquiv.
apply ok_Bg_permut with (G:=emptyEquiv ((w0, Gamma_TS & A0) :: G')).
apply emptyEquiv_permut in H5. apply permut_sym.
remember ((w, Gamma) :: G) as G_w. 
assert (permut (emptyEquiv (G_w & (w0, Gamma_TS))) (emptyEquiv ((w0, Gamma_TS & A0) :: G'))).
rewrite emptyEquiv_last with (G':=emptyEquiv G_w). 
replace ((w, Gamma) :: G & (w0, Gamma_TS & A0)) with (G_w & (w0, Gamma_TS & A0)) in H5.
rewrite emptyEquiv_last with (G':=emptyEquiv G_w) in H5. 
assumption.
reflexivity.
subst; rew_app; reflexivity.
reflexivity.
subst; rew_app in *; assumption.
rewrite ok_Bg_emptyEquiv in H_G_ok; assumption.

apply BackgroundSubsetImpl with (G:=emptyEquiv G');
[ assumption |
  exists (@nil Context_LF)];
rew_app; apply emptyEquiv_permut;
apply permut_sym; assumption.

(* get_here outer *)
case_if.
(* switch back to inner *)
inversion H9; subst.
assert (Gamma_subst & A0 = Gamma). 
apply ok_Bg_unify with (G:=G') (G0:=G0) (G1:= G) (w:=w).
assumption.
apply permut_sym; assumption.
simpl in H_G_ok. rewrite Mem_nil_eq in H_G_ok. case_if.
apply ok_Bg_step in H_G_ok; assumption.
subst Gamma.

assert (permut G G0).
assert (permut (G & (w, Gamma_subst & A0) ++ nil) (G0 & (w, Gamma_subst & A0) ++ nil)).
rew_app; apply permut_trans with (l2:=G'); assumption.
apply permut_inv in H10. rew_app in H10; assumption.

apply t_get_here_LF with (G:=G) (Gamma:=Gamma_subst).
rewrite subst_t__inner.
eapply IHHT with (Gamma_TS := Gamma_subst) (Gamma_HT0 := Gamma_subst & A0) (w1 := w) (A1:=A0); eauto.

apply ok_Bg_permut with (G:=(w0, Gamma_HT) :: G').
apply permut_trans with (l2:=((w0, Gamma_HT)::(w, Gamma_subst & A0) :: G)).
permut_simpl.
apply permut_trans with (l2:= (G0 & (w, Gamma_subst & A0))).
assumption.
permut_simpl. apply permut_sym; assumption.
permut_simpl.
assumption.

apply BackgroundSubsetImpl with (G:=emptyEquiv G_min); eauto.
exists (@nil Context_LF). 
apply permut_trans with (l2:=emptyEquiv (G0 & (w0, Gamma_HT))).
apply emptyEquiv_permut in H1; rew_app; assumption.
apply emptyEquiv_permut; apply permut_sym; apply permut_app_l; assumption.
apply permut_trans with (l2:=G0 & (w, Gamma_subst)).
apply permut_app_l; assumption.
apply permut_sym; assumption.
(* stay in outer *)
assert (exists GH, exists GT, G0 = GH & (w, Gamma) ++ GT).
apply permut_split_neq with (G:=G) (G':=nil) (elem':=(w_subst, Gamma_subst & A0)).
intro nn; inversion nn; subst; elim H9; reflexivity.
apply permut_trans with (l2:=G'). 
rew_app; assumption.
assumption.

destruct H10 as [GH]; destruct H10 as [GT].
apply t_get_here_LF with (G:=GH++GT & (w_subst, Gamma_subst)) (Gamma:=Gamma).
rewrite subst_t__outer with (w':= fctx w).
subst.
eapply IHHT with (Gamma_subst := Gamma_subst) (w_subst:=w_subst) (w1:=w) (G0:=GH ++ GT & (w0, Gamma_HT)) (G_TS:=(GH++GT & (w_subst, Gamma_subst)) & (w0, Gamma_HT)) (A0:=A0); eauto.

apply ok_Bg_permut with (G:=(w0, Gamma_HT) :: G').
apply permut_trans with (l2:= (w0, Gamma_HT) :: (G & (w, Gamma))).
permut_simpl. apply permut_sym; assumption.
permut_simpl.
assumption.

apply permut_trans with (l2:=((GH ++ GT & (w_subst, Gamma_subst & A0)) & (w0, Gamma_HT))).
apply permut_app_l.
assert (permut (G & (w, Gamma)) ((GH & (w, Gamma) ++ GT) & (w_subst, Gamma_subst & A0))). 
apply permut_trans with (l2:=G'); assumption.
replace G with (G++nil).
replace (GH ++ GT & (w_subst, Gamma_subst & A0)) with (GH ++ GT & (w_subst, Gamma_subst & A0) ++ nil).
apply permut_inv with (elem:=(w, Gamma)).
rew_app in *; assumption.
rew_app; reflexivity.
rew_app; reflexivity.
permut_simpl.

permut_simpl.
intro nn; subst; elim H9; reflexivity.

apply ok_Bg_permut with (G:= (w_subst, nil):: G_min).
permut_simpl.
apply permut_trans with (l2:=(GH & (w, Gamma) ++ GT) & (w0, Gamma_HT)).
assumption.
permut_simpl.
assumption.

apply ok_Bg_permut with (G:= (w_subst, Gamma_subst)::G_min).
permut_simpl.
apply permut_trans with (l2:=(GH & (w, Gamma) ++ GT) & (w0, Gamma_HT)).
assumption.
permut_simpl.
rewrite ok_Bg_emptyEquiv.
rewrite ok_Bg_emptyEquiv in H5.
simpl in *. rewrite Mem_nil_eq in *. case_if.
assumption.

apply BackgroundSubsetImpl with (G:=emptyEquiv G_min).
eassumption.
exists (@nil Context_LF).
apply permut_trans with (l2:=emptyEquiv ((GH & (w, Gamma) ++ GT) & (w0, Gamma_HT))).
apply emptyEquiv_permut in H1; rew_app in *; assumption.
apply emptyEquiv_permut; permut_simpl.
assumption.
apply permut_trans with (l2:=G0 & (w_subst, Gamma_subst)).
subst; permut_simpl.
apply permut_sym; assumption.

(* letdia inner *)
case_if; apply t_letdia_LF with (L:=L \u \{w0} \u from_list (map fst G)) (A:=A);
rewrite subst_t__inner.
eapply IHHT; eauto.
intros.
unfold open_ctx.
rewrite <- subst_order_irrelevant; eauto.
eapply H; eauto.
apply ok_Bg_permut with (G:= (w', A::nil) :: ((w0, Gamma_TS & A0)::G)).
permut_simpl.
apply ok_Bg_add_fresh.
repeat rewrite notin_union in *; destruct H3. destruct H4.
repeat split; auto; apply notin_empty.
assumption.

replace ( emptyEquiv ((w', A :: nil) :: G)) with (nil & (w', nil) ++ emptyEquiv G).
apply GlobalWeakening; rew_app; assumption.
simpl; rew_app; reflexivity. 

(* letdia outer *)
case_if; apply t_letdia_LF 
  with (L:=L \u \{w0} \u from_list (map fst G) \u \{w_subst}) (A:=A).

rewrite subst_t__outer with (w':=fctx w0); eauto;
eapply IHHT; eauto.

intros;
rewrite subst_t__outer with (w':=fctx w0); auto.
unfold open_ctx;
rewrite <- subst_order_irrelevant; eauto.
eapply H with (G_TS := (w', A::nil) :: G_TS) (G0:=(w', A::nil) :: G0) ; eauto.

apply ok_Bg_permut with (G:=(w', A::nil) :: ((w0,Gamma_HT) :: G)).
permut_simpl.
apply ok_Bg_add_fresh.
repeat rewrite notin_union in *;
destruct H9; destruct H10; destruct H11.
repeat split; try assumption. apply notin_empty.
assumption.

permut_simpl; eassumption.
permut_simpl; assumption.

rewrite ok_Bg_emptyEquiv.
apply ok_Bg_permut with (G := (w', nil):: (w0,nil) :: emptyEquiv G).
apply permut_trans with (l2:=emptyEquiv((w', nil) :: (w0, nil)::G0 & (w_subst, Gamma_subst & A0))).
permut_simpl.
simpl. permut_simpl. apply emptyEquiv_permut in H1; assumption.
permut_simpl. simpl. permut_simpl.
rewrite emptyEquiv_last with (G':=emptyEquiv G0).
rewrite emptyEquiv_last with (G':=emptyEquiv G0).
permut_simpl.
reflexivity. 
reflexivity.
apply ok_Bg_add_fresh.
repeat rewrite notin_union in *;
destruct H9; destruct H10; destruct H11.
repeat split. assumption.
rewrite <- emptyEquiv_dom. assumption.
apply notin_empty.
replace ((w0,nil)::emptyEquiv G) with (emptyEquiv ((w0,nil)::G)) by (simpl; reflexivity).
apply ok_Bg_permut with (G:=emptyEquiv ((w0, Gamma_HT)::G_TS)).
simpl. permut_simpl.
apply permut_trans with (l2:=emptyEquiv G0 & (w_subst, nil)).
replace (emptyEquiv G0 & (w_subst, nil)) with (emptyEquiv (G0 & (w_subst, Gamma_subst))).
apply emptyEquiv_permut. assumption.
replace (emptyEquiv G0 & (w_subst, nil)) with (emptyEquiv (G0 & (w_subst, Gamma_subst & A0))).
rewrite emptyEquiv_last with (G':=emptyEquiv G0).
rewrite emptyEquiv_last with (G':=emptyEquiv G0).
reflexivity.
reflexivity.
reflexivity.
rewrite emptyEquiv_last with (G':=emptyEquiv G0).
reflexivity.
reflexivity.
replace (emptyEquiv G0 & (w_subst, nil)) with (emptyEquiv (G0 & (w_subst, Gamma_subst & A0))).
apply emptyEquiv_permut in H1; apply permut_sym. assumption.
rewrite emptyEquiv_last with (G':=emptyEquiv G0).
reflexivity.
reflexivity.
rewrite <- ok_Bg_emptyEquiv. assumption.

apply ok_Bg_permut with (G:=(w', A::nil)::(w0, Gamma_HT)::G_TS).
permut_simpl.
apply ok_Bg_add_fresh.
repeat rewrite notin_union in *;
destruct H9; destruct H10; destruct H11.
repeat split. assumption.
apply emptyEquiv_mem with (G:=G).
apply permut_trans with (l2:=emptyEquiv (G0 & (w_subst, Gamma_subst))).
rewrite emptyEquiv_last with (G':=emptyEquiv G0).
apply emptyEquiv_permut in H1.
rewrite emptyEquiv_last with (G':=emptyEquiv G0) in H1.
assumption.
reflexivity.
reflexivity.
apply emptyEquiv_permut in H2. apply permut_sym; assumption.
assumption.
apply notin_empty.
assumption.

apply BackgroundSubsetImpl with (G:=emptyEquiv G_min).
assumption.
exists ((w',(@nil ty_LF))::nil); permut_simpl; simpl;
permut_simpl.
apply emptyEquiv_permut; assumption.

(* letdia_get inner *)
assert (w0 <> w) by
  (apply emptyEquiv_permut in H0;
   apply BackgroundSubsetImpl with (G':=emptyEquiv (G & (w, Gamma))) in H2;
   try rewrite emptyEquiv_last with (G':=emptyEquiv G) in H2; auto;
   try eapply unique_worlds; eauto;
   exists (@nil Context_LF); permut_simpl; apply permut_sym; auto);
case_if.
eapply t_letdia_get_LF with (L:=L \u \{w0} \u \{w} \u from_list(map fst G)); eauto.
rewrite subst_t__outer with (w':= fctx w).
eapply IHHT; eauto.

apply ok_Bg_permut with (G:=(w0, Gamma_TS & A0) :: G0).
apply permut_trans with (l2:= (w0, Gamma_TS & A0) :: G & (w, Gamma)).
permut_simpl.
apply permut_sym; assumption.
permut_simpl.
assumption.

apply ok_Bg_permut with ((w0, nil)::G0).
permut_simpl; apply permut_sym; assumption.
rewrite ok_Bg_emptyEquiv in H_G_ok; 
rewrite ok_Bg_emptyEquiv.
simpl in *; assumption. 

apply ok_Bg_permut with ((w0, Gamma_TS)::G0).
apply permut_trans with (l2:=(w0, Gamma_TS)::G & (w, Gamma)).
permut_simpl. apply permut_sym. assumption.
permut_simpl.
assumption.

apply BackgroundSubsetImpl with (G:=emptyEquiv G0).
assumption.
exists (@nil Context_LF); rew_app; apply emptyEquiv_permut. apply permut_sym; assumption.
assumption.

intros.
rewrite subst_t__inner.
unfold open_ctx; rewrite <- subst_order_irrelevant; auto.
eapply H; eauto.

apply ok_Bg_permut with (G:=(w', A::nil)::(w0, Gamma_TS & A0) :: (w, Gamma) :: G).
permut_simpl.
apply ok_Bg_add_fresh.
repeat rewrite notin_union in *.
destruct H6; destruct H7; destruct H8.
split. assumption.
rewrite map_cons. simpl.
rewrite from_list_cons.
repeat rewrite notin_union; repeat split; auto. apply notin_empty.
apply ok_Bg_permut with (G:=(w0, Gamma_TS & A0) :: G0).
permut_simpl.
apply permut_trans with (l2:=G & (w, Gamma)).
apply permut_sym; assumption.
permut_simpl.
assumption.

simpl.
replace ((w', nil) :: emptyEquiv (G & (w, Gamma))) with (nil & (w', nil) ++ emptyEquiv (G & (w, Gamma))).
apply GlobalWeakening; rew_app.
apply BackgroundSubsetImpl with (G:=emptyEquiv G0).
assumption.
exists (@nil Context_LF).
rew_app; apply emptyEquiv_permut.
apply permut_sym; assumption.
rew_app; reflexivity.

(* letdia_get outer *)
case_if.
(* switch back to inner *)
inversion H10; subst.
assert (Gamma_subst & A0 = Gamma). 
apply ok_Bg_unify with (G:=G0) (G0:=G1) (G1:= G) (w:=w).
assumption.
apply permut_sym; assumption.
simpl in H_G_ok. rewrite Mem_nil_eq in H_G_ok. case_if.
apply ok_Bg_step in H_G_ok; assumption.
subst Gamma.

assert (permut G G1).
assert (permut (G & (w, Gamma_subst & A0) ++ nil) (G1 & (w, Gamma_subst & A0) ++ nil)).
rew_app; apply permut_trans with (l2:=G0); assumption.
apply permut_inv in H11. rew_app in H11; assumption.

apply t_letdia_get_LF with (L:=L) (A:=A) (G:=G) (Gamma:=Gamma_subst).
rewrite subst_t__inner.
eapply IHHT with (Gamma_TS := Gamma_subst) (Gamma_HT0 := Gamma_subst & A0) (w1 := w) (A1:=A0); eauto.

apply ok_Bg_permut with (G:=(w0, Gamma_HT) :: G0).
apply permut_trans with (l2:=((w0, Gamma_HT)::(w, Gamma_subst & A0) :: G)).
permut_simpl.
apply permut_trans with (l2:= (G1 & (w, Gamma_subst & A0))).
assumption.
permut_simpl. apply permut_sym; assumption.
permut_simpl.
assumption.

apply BackgroundSubsetImpl with (G:=emptyEquiv G_min); eauto.
exists (@nil Context_LF). 
apply permut_trans with (l2:=emptyEquiv (G1 & (w0, Gamma_HT))).
apply emptyEquiv_permut in H2; rew_app; assumption.
apply emptyEquiv_permut; apply permut_sym; apply permut_app_l; assumption.

intros.
rewrite subst_t__outer with (w':=fctx w0).
unfold open_ctx;
rewrite <- subst_order_irrelevant; eauto.
eapply H with (G0:=(w',A::nil)::G1) (A1:=A0); eauto.

skip. (* ok_Bg *)
permut_simpl; assumption.
permut_simpl; assumption.
skip. (* ok_Bg *) 
skip. (* ok_Bg *)

apply BackgroundSubsetImpl with (G:= (nil & (w', nil) ++ emptyEquiv G_min)).
apply GlobalWeakening. rew_app. assumption.
exists (@nil Context_LF); permut_simpl. simpl. permut_simpl. 
apply emptyEquiv_permut. assumption.
assumption.
apply permut_trans with (l2:=G1 & (w, Gamma_subst)).
permut_simpl; assumption.
apply permut_sym; assumption.

(* stay in outer *)
assert (exists GH, exists GT, G1 = GH & (w, Gamma) ++ GT).
apply permut_split_neq with (G:=G) (G':=nil) (elem':=(w_subst, Gamma_subst & A0)).
intro nn; inversion nn; subst; elim H10; reflexivity.
apply permut_trans with (l2:=G0). 
rew_app; assumption.
assumption.

destruct H11 as [GH]; destruct H11 as [GT].
apply t_letdia_get_LF with (G:=GH++GT & (w_subst, Gamma_subst)) (Gamma:=Gamma) (L:=L)(A:=A).
rewrite subst_t__outer with (w':= fctx w).
subst.
eapply IHHT with (Gamma_subst := Gamma_subst) (w_subst:=w_subst) (w1:=w) (G0:=GH ++ GT & (w0, Gamma_HT)) (G_TS:=(GH++GT & (w_subst, Gamma_subst)) & (w0, Gamma_HT)) (A0:=A0); eauto.

apply ok_Bg_permut with (G:=(w0, Gamma_HT) :: G0).
apply permut_trans with (l2:= (w0, Gamma_HT) :: (G & (w, Gamma))).
permut_simpl. apply permut_sym; assumption.
permut_simpl.
assumption.

apply permut_trans with (l2:=((GH ++ GT & (w_subst, Gamma_subst & A0)) & (w0, Gamma_HT))).
apply permut_app_l.
assert (permut (G & (w, Gamma)) ((GH & (w, Gamma) ++ GT) & (w_subst, Gamma_subst & A0))). 
apply permut_trans with (l2:=G0); assumption.
replace G with (G++nil).
replace (GH ++ GT & (w_subst, Gamma_subst & A0)) with (GH ++ GT & (w_subst, Gamma_subst & A0) ++ nil).
apply permut_inv with (elem:=(w, Gamma)).
rew_app in *; assumption.
rew_app; reflexivity.
rew_app; reflexivity.
permut_simpl.

permut_simpl.
intro nn; subst; elim H10; reflexivity.

apply ok_Bg_permut with (G:= (w_subst, nil):: G_min).
permut_simpl.
apply permut_trans with (l2:=(GH & (w, Gamma) ++ GT) & (w0, Gamma_HT)).
assumption.
permut_simpl.
assumption.

skip. (* ok_Bg *)

apply BackgroundSubsetImpl with (G:=emptyEquiv G_min).
eassumption.
exists (@nil Context_LF).
apply permut_trans with (l2:=emptyEquiv ((GH & (w, Gamma) ++ GT) & (w0, Gamma_HT))).
apply emptyEquiv_permut in H2; rew_app in *; assumption.
apply emptyEquiv_permut; permut_simpl.
assumption.

intros.
rewrite subst_t__outer with (w':=fctx w0).
unfold open_ctx;
rewrite <- subst_order_irrelevant; eauto.
eapply H with (G0:=(w',A::nil)::G1) (A0:=A0); eauto.

skip. (* ok_Bg *)

permut_simpl.
apply permut_trans with (l2:=G0); assumption.

rewrite H11; 
permut_simpl.

skip. (* ok_Bg *)
skip. (* ok_Bg *)

apply BackgroundSubsetImpl with (G:=nil & (w', nil) ++ emptyEquiv G_min).
apply GlobalWeakening.
rew_app. assumption.
exists (@nil Context_LF).
permut_simpl; simpl. permut_simpl.
apply emptyEquiv_permut. assumption.
assumption.

apply permut_trans with (l2:=G1 & (w_subst, Gamma_subst)). 
subst; permut_simpl.
apply permut_sym; assumption.
Admitted. (* Existential variable non-instantiated *)

Lemma subst_t_preserv_types_end_inner:
forall Gamma G M N A B w
  (Ok: ok_Bg ((w, Gamma & A)::G) nil)
  (HM: emptyEquiv G |= (w, nil) |- M ::: A)
  (HT: G |= (w, Gamma & A) |- N ::: B)
  (H_lc: lc_w_LF M),
  G |= (w, Gamma) |- [ M // length Gamma | fctx w] [N | fctx w] ::: B.
intros;
eapply subst_t_preserv_types_end with (Gamma_HT := Gamma & A); eauto. 
Qed.

Lemma subst_t_preserv_types_end_outer:
forall G0 w w_subst Gamma_subst A G' G_HT G_TS Gamma M N B
  (Ok_G': ok_Bg ((w_subst, nil)::G') nil)
  (Ok_GHT: ok_Bg ((w,Gamma)::G_HT) nil)
  (H_G': permut G' (G0 & (w, Gamma)))
  (H_G'': permut G_HT (G0 & (w_subst, Gamma_subst & A)))
  (H_G''': permut G_TS (G0 & (w_subst, Gamma_subst)))
  (HM: emptyEquiv G' |= (w_subst, nil) |- M ::: A)
  (H_lc: lc_w_LF M)
  (HT: G_HT |= (w, Gamma) |- N ::: B),
  G_TS |= (w, Gamma) |- [ M // length Gamma_subst | fctx w_subst ] [N | fctx w] ::: B.
intros;
eapply subst_t_preserv_types_end; eauto.
intro; absurd (w_subst = w); auto.
apply emptyEquiv_permut in H_G';
eapply unique_worlds with (G:=emptyEquiv G0); eauto;
eapply BackgroundSubsetImpl with (G:=emptyEquiv G'); eauto.
exists (@nil Context_LF); rew_app.
rewrite emptyEquiv_last with (G':=emptyEquiv G0) in H_G'.
eassumption.
auto.
rewrite ok_Bg_emptyEquiv.
apply ok_Bg_permut with (G:=emptyEquiv ((w, Gamma)::G_HT)).
simpl; permut_simpl.
apply permut_trans with (l2:=emptyEquiv(G0 & (w_subst, Gamma_subst & A))).
apply emptyEquiv_permut in H_G''; assumption.
apply permut_trans with (l2:=emptyEquiv(G0 & (w_subst, Gamma_subst))).
rewrite emptyEquiv_last with (G':=emptyEquiv G0).
rewrite emptyEquiv_last with (G':=emptyEquiv G0).
permut_simpl.
reflexivity. reflexivity.
apply emptyEquiv_permut in H_G'''. apply permut_sym; assumption.
rewrite ok_Bg_emptyEquiv in Ok_GHT. simpl in Ok_GHT.
simpl. assumption.
Qed.

Lemma subst_t_preserv_types:
forall L Delta G0 G_min G_HT G_TS Gamma_HT Gamma_TS w_subst Gamma_subst w N A
  (H_L: subst_typing G_min L Delta w_subst)
  (H_lc: forall M, Mem M L -> lc_w_LF M)
  (H_inner: w_subst = w -> G_HT = G_min /\ G_HT = G_TS /\ Gamma_HT = Gamma_TS ++ Delta /\
            permut G0 G_HT /\ Gamma_subst = Gamma_TS)
  (H_outer: w_subst <> w -> Gamma_HT = Gamma_TS /\ permut G_min (G0 & (w, Gamma_HT)) /\
            permut G_HT (G0 & (w_subst, Gamma_subst ++ Delta)) /\ 
            permut G_TS (G0 & (w_subst, Gamma_subst)))
  (HOk: ok_Bg ((w, Gamma_HT) :: G_HT) nil)
  (HT: G_HT |= (w, Gamma_HT) |- N ::: A),
  G_TS |= (w, Gamma_TS) |- subst_list L (length Gamma_subst) N (fctx w_subst) (fctx w) ::: A.
induction L; destruct Delta; simpl in *; intros; try contradiction;
unfold subst_t;
destruct (eq_var_LF_dec w_subst w).
(* = - inner substitution, nil *)
apply H_inner in e; destruct e; destruct H0; destruct H1; destruct H2.
subst G_TS; subst Gamma_HT.
replace Gamma_TS with (Gamma_TS ++ nil) by (rew_app; reflexivity).
  assumption.
(* <> - outer substitution, nil *)
apply H_outer in n; destruct n; destruct H0; destruct H1.
rew_app in H1; apply BackgroundSubsetImpl with (G:=G_HT).
subst Gamma_TS; assumption.
exists (@nil Context_LF); permut_simpl;
apply permut_trans with (l2:=(G0 & (w_subst, Gamma_subst))).
  assumption.
  apply permut_sym; assumption.
(* = - inner substitution, step *)
case_if; try (inversion H; discriminate); clear H.
assert (w_subst = w) by assumption.
apply H_inner in H; destruct H; destruct H0; destruct H1; destruct H2;
clear H_inner H_outer;
destruct H_L;
rewrite subst_t__inner.
subst Gamma_subst. subst w_subst;
apply subst_t_preserv_types_end_inner with (A:=t);
subst G_min; subst G_TS;
case_if. simpl. case_if. assumption.
assumption.
replace (S(length Gamma_TS)) with (length (Gamma_TS & t) ).
eapply IHL; eauto. 
intros; apply H_lc; apply Mem_next; assumption.
intro n; elim n. reflexivity.
case_if; assumption.
subst Gamma_HT; rew_app in *; assumption.
rew_length; omega.
apply H_lc; apply Mem_here.
(* <> - outer substitution, step *)
case_if; clear H.
assert (w_subst <> w) by assumption.
apply H_outer in H. destruct H. destruct H0; destruct H1.
clear H_inner H_outer.
destruct H_L.
rewrite subst_t__outer with (w':=fctx w).
subst.
eapply subst_t_preserv_types_end_outer with (A:=t) (G_HT := (G0&(w_subst, Gamma_subst & t))); eauto.
apply ok_Bg_permut with (G:=(w, Gamma_TS) :: G0 & (w_subst, nil)).
permut_simpl.
apply permut_trans with (l2:=G0 & (w, Gamma_TS)).
permut_simpl; apply permut_sym; assumption.
apply permut_sym; assumption.
simpl.
case_if.
apply ok_Bg_permut with (G':=G0 & (w_subst, Gamma_subst ++ t::Delta)) in HOk. 
rewrite ok_Bg_emptyEquiv in HOk.
rewrite emptyEquiv_last with (G':=emptyEquiv G0) in HOk.
rewrite ok_Bg_emptyEquiv.
rewrite emptyEquiv_last with (G':=emptyEquiv G0).
assumption.
reflexivity.
reflexivity. 
assumption.
simpl; case_if.
rewrite ok_Bg_emptyEquiv in HOk.
apply ok_Bg_permut with (G':=emptyEquiv(G0 & (w_subst, Gamma_subst & t))) in HOk.
rewrite ok_Bg_emptyEquiv;
assumption.
apply permut_trans with (l2:=emptyEquiv (G0 & (w_subst, Gamma_subst ++ t :: Delta))).
apply emptyEquiv_permut; assumption.
rewrite emptyEquiv_last with (G':=emptyEquiv G0).
apply permut_sym;
rewrite emptyEquiv_last with (G':=emptyEquiv G0).
permut_simpl. reflexivity.
reflexivity.
apply H_lc; apply Mem_here.
replace (S(length Gamma_subst)) with (length (Gamma_subst & t) ).
eapply IHL; eauto.
intros; apply H_lc; apply Mem_next; assumption.
intro nn; elim n; subst w; reflexivity.
case_if. apply ok_Bg_permut with (G:=G_HT); rew_app in *; assumption.
apply BackgroundSubsetImpl with (G:=G_HT).
assumption.
exists (@nil Context_LF); permut_simpl; rew_app in *; assumption.
rew_length; omega.
intro nn; inversion nn; subst; elim n; reflexivity.
Qed.

Lemma subst_t_preserv_types_inner:
forall L G Gamma w Delta N B
  (HT_L: subst_typing G L Delta w)
  (HT_lc: forall M, Mem M L -> lc_w_LF M)
  (HOk: ok_Bg ((w, Gamma++Delta)::G) nil)
  (HT_N: G |= (w, Gamma ++ Delta) |- N ::: B),
  G |= (w, Gamma) |- subst_list L (length Gamma) N (fctx w) (fctx w) ::: B.
intros;
eapply subst_t_preserv_types; eauto.
intro n; elim n; reflexivity.
Qed.

Lemma subst_t_preserv_types_outer:
forall L G0 G G' G'' Gamma Gamma' w w' Delta N B
  (HT_G0: permut G (G0 & (w', Gamma')))
  (HT_G': permut G' (G0 & (w, Gamma))) 
  (HT_G'': permut G'' (G0 & (w', Gamma' ++ Delta)))
  (HT_L: subst_typing G' L Delta w')
  (HT_lc: forall M, Mem M L -> lc_w_LF M)
  (HOk: ok_Bg ((w, Gamma)::G'') nil)
  (HT_N: G'' |= (w, Gamma) |- N ::: B),
  G |= (w, Gamma) |- subst_list L (length Gamma') N (fctx w') (fctx w)  ::: B.
intros;
eapply subst_t_preserv_types; eauto.
intro n; absurd (w = w'); try symmetry; auto.
eapply unique_worlds; eauto.
Qed.

Lemma inv_subst_ctx_preserv_types:
forall G_HT G_TS G0 Gamma_HT Gamma_TS Gamma_fresh Gamma_subst w_TS w_HT 
       w_fresh w_subst w_step M A k
  (Fresh: w_fresh \notin free_worlds_LF M)
  (H_outer: w_subst <> w_TS -> w_fresh <> w_TS ->
            w_TS = w_HT /\ G_HT = G_TS /\ Gamma_HT = Gamma_TS /\
            permut G_HT (G0 & (w_subst, Gamma_fresh ++ Gamma_subst)))
  (H_old: w_subst = w_HT -> w_step = w_fresh -> 
            w_TS = w_HT /\ G_HT = G_TS /\ Gamma_TS = Gamma_HT /\
            G0 = G_HT /\ Gamma_HT = Gamma_fresh ++ Gamma_subst)
  (H_new: w_subst = w_fresh -> w_subst = w_HT ->
            w_TS = w_HT /\ w_HT = w_step /\
            w_TS = w_HT /\ w_HT = w_step /\
            Gamma_TS = Gamma_HT /\ Gamma_HT = Gamma_fresh ++ Gamma_subst)
  (HT: G_HT |= (w_HT, Gamma_HT) |- {{ fctx w_subst // fctx w_fresh }} 
                                   [ {{fctx w_fresh // bctx k }}  [ M | fctx w_step, 0] |
                                     fctx w_step, length Gamma_fresh] ::: A),
  G_TS |= (w_TS, Gamma_TS) |- {{ fctx w_subst // bctx k }} [ M | fctx w_TS, 0] ::: A.
Admitted.

Lemma inv_subst_ctx_preserv_types_outer:
forall G0 G w w' w0 Gamma Gamma' Gamma0 M A k
  (Fresh: w' \notin free_worlds_LF M)
  (HT_G: permut G (G0 & (w, Gamma' ++ Gamma)))
  (HT: G |= (w0, Gamma0) |- {{ fctx w // fctx w'}} 
    [ {{fctx w' // bctx k}} [M | fctx w0, 0] | fctx w0, (length Gamma')] ::: A),
  G |= (w0, Gamma0) |- {{fctx w // bctx k}}[M | fctx w0, 0] ::: A.
intros;
assert (w0 <> w) by (eapply unique_worlds; eauto);
eapply inv_subst_ctx_preserv_types 
  with (w_TS:=w0) (w_subst:=w) (w_fresh:=w') (w_step:=w0) (
G0:=G0);
eauto.
intro n; symmetry in n; contradiction.
intros m n; symmetry in n; contradiction.
Qed.

Lemma inv_subst_ctx_preserv_types_new:
forall G w w' Gamma Gamma' M A k
  (Fresh: w' \notin free_worlds_LF M)
  (HT: G |= (w, Gamma' ++ Gamma) |- {{fctx w // fctx w'}} 
    [ {{ fctx w' // bctx k }} [M | fctx w, 0] | fctx w, length Gamma'] ::: A),
  G |= (w, Gamma'++Gamma) |- {{fctx w // bctx k }}[ M | fctx w, 0] ::: A.
intros; 
eapply inv_subst_ctx_preserv_types with (w_HT:=w);
eauto.
intro n; elim n; reflexivity.
intros; repeat split; auto.
Qed.

Lemma inv_subst_ctx_preserv_types_old:
forall G w w' Gamma Gamma' M A k
  (Fresh: w' \notin free_worlds_LF M)
  (HT: G |= (w, Gamma'++Gamma) |- {{fctx w // fctx w'}} 
    [ {{ fctx w' // bctx k }} [M | fctx w', 0] | fctx w', length Gamma'] ::: A),
  G |= (w, Gamma'++Gamma) |- {{fctx w // bctx k }}[ M | fctx w, 0] ::: A.
intros; 
eapply inv_subst_ctx_preserv_types with (w_step:=w');
eauto.
intro n; elim n; reflexivity.
intros; repeat split; auto.
Qed.

Lemma rename_ctx_preserv_types:
forall G0 G_HT G_TS Gamma Gamma' Gamma_HT Gamma_TS w w' w_HT w_TS M A
  (H_outer: w_HT <> w -> w_HT <> w' ->
    permut G_HT (G0 & (w, Gamma) & (w', Gamma')) /\
    w_HT = w_TS /\ Gamma_HT = Gamma_TS)
  (H_old: w_HT = w' ->
    permut G_HT (G0 & (w, Gamma)) /\ w_TS = w /\
    Gamma_HT = Gamma' /\ Gamma_TS = Gamma' ++ Gamma /\ G_TS = G0)
  (H_new: w_HT = w ->
    permut G_HT (G0 & (w', Gamma')) /\ Gamma_HT = Gamma /\
    w_TS = w /\ Gamma_TS = Gamma' ++ Gamma /\ G_TS = G0)
  (HT: G_HT |= (w_HT, Gamma_HT) |- M ::: A),
  G_TS |= (w_TS, Gamma_TS) |- {{ fctx w // fctx w'}}[ M | fctx w_HT, length Gamma'] ::: A.
Admitted.

Lemma rename_ctx_preserv_types_outer:
forall G G' G'' w w' w0 Gamma Gamma' Gamma0 M A
  (HT_G': permut G' (G & (w, Gamma) & (w', Gamma')))
  (HT_G'': permut G'' (G & (w, Gamma' ++ Gamma)))
  (HT: G' |= (w0, Gamma0) |- M ::: A),
  G'' |= (w0, Gamma0) |- {{fctx w // fctx w'}} [M | fctx w0, length (Gamma')] ::: A.
intros;
eapply rename_ctx_preserv_types; eauto.
assert (w0 <> w') by (eapply unique_worlds; eauto);
intro n; subst; elim H; reflexivity.
assert (w0 <> w). 
eapply unique_worlds with (G':=G'); eauto.
  apply permut_trans with (l2:=(G & (w', Gamma') & (w, Gamma))); eauto.
  apply permut_trans with (l2:=(G & (w, Gamma) & (w', Gamma'))); auto; permut_simpl.
intro n; subst; elim H; reflexivity.
Qed.

Lemma rename_ctx_preserv_types_old:
forall G G' w0 w1 Gamma0 Gamma1 M A
  (HT_G': permut G' (G & (w0, Gamma0)))
  (HT: G' |= (w1, Gamma1) |- M ::: A),
  G |= (w0, Gamma1++Gamma0) |- {{fctx w0 // fctx w1}} [M | fctx w1, length (Gamma1)] ::: A.
intros;
eapply rename_ctx_preserv_types with (w_HT:=w1); eauto.
intros a b; elim b; reflexivity.
assert (w1 <> w0) by (eapply unique_worlds; eauto).
intro; subst; elim H; reflexivity.
Qed.

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
  (HOk: ok_Bg ((w,nil)::emptyEquiv G) nil)
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
  simpl; split. rewrite emptyEquiv_stable. eauto. auto.
  intros; rewrite Mem_cons_eq in H; destruct H.
    subst; assumption.
    rewrite Mem_nil_eq in H; contradiction.
  simpl in *; assumption.
  intros; repeat split; eauto.
(* unbox_box *)
inversion HT; subst.
assert (exists w0, w0 \notin L \u free_worlds_LF M0).
  apply Fresh.
destruct H as [w1].
rewrite notin_union in H; destruct H.
unfold open_ctx in *.
eapply inv_subst_ctx_preserv_types with (w_fresh:=w1) (Gamma_fresh:=nil) (k:=0) (w_step:=w1); eauto.
intros b; elim b; reflexivity.
intros; repeat split; eauto.
intros; repeat split; eauto. (* ?this should give contradiction? *)
replace (w0, (@nil ty_LF)) with (w0, nil ++ (@nil ty_LF)).
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
eapply inv_subst_ctx_preserv_types with (w_fresh:=w1) (w_step :=w1) (Gamma_fresh:=nil) (k:=0); eauto.
intros b; elim b; reflexivity.
intros; repeat split; eauto.
intros; repeat split; eauto.
replace (w0, (@nil ty_LF)) with (w0, nil ++ (@nil ty_LF)).
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
apply IHHT with (G0:=G & (w0, nil)) (w1 := w); auto.

apply ok_Bg_permut with (G:=(w0, nil)::emptyEquiv G0).
apply permut_trans with (l2:=(w0,nil) :: G & (w, nil)); permut_simpl.
apply permut_sym; assumption.
assumption.

rewrite emptyEquiv_last with (G':=G).
reflexivity.
apply emptyEquiv_inv with (w:=w).
apply emptyEquiv_empty with (G:=G0).
  apply permut_sym; assumption.
assumption.
(* get_here *)
apply t_get_here_LF with (G:=G) (Gamma:=Gamma); auto.
assert (Gamma = nil).
apply emptyEquiv_nil with (G:=G0) (G':=G & (w, Gamma)) (w:=w).
  apply permut_sym; assumption.
  apply Mem_last.
subst.
apply IHHT with (G0:=G & (w0,nil)) (w1:=w); auto.

apply ok_Bg_permut with (G:=(w0, nil)::emptyEquiv G0).
apply permut_trans with (l2:=(w0,nil) :: G & (w, nil)); permut_simpl.
apply permut_sym; assumption.
assumption.

rewrite emptyEquiv_last with (G':=G).
reflexivity.
apply emptyEquiv_inv with (w:=w).
apply emptyEquiv_empty with (G:=G0).
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
eapply subst_t_preserv_types_inner with (Delta:=A::nil). 
  simpl; split; auto;
  rewrite emptyEquiv_stable;
  assumption.
intros. rewrite Mem_cons_eq in H3; destruct H3.
  subst; assumption.
  rewrite Mem_nil_eq in H3; contradiction.
simpl in *; assumption.
unfold open_ctx in *.
  replace (w0, (nil & A)) with (w0, (A::nil) ++ (@nil ty_LF)).
  eapply inv_subst_ctx_preserv_types_new; eauto.
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
assert (w <> w0).
  eapply unique_worlds; eauto.
replace ([M0 // 0 | fctx w] [N ^^ [fctx w | fctx w0] | fctx w0])
   with (subst_list (M0::nil) (length (@nil te_LF)) (N ^^ [fctx w | fctx w0]) (fctx w) (fctx w0)) by auto.
apply subst_t_preserv_types with (G0:=G) (Delta:=A::nil) (G_min:= G & (w0, nil)) (G_HT:= G & (w, nil & A)) (Gamma_subst:= nil) (Gamma_HT := nil) .
  simpl; split; auto.
  rewrite emptyEquiv_last with (G':=G).
    assumption.
  apply emptyEquiv_inv with (w:=w).
  rewrite emptyEquiv_empty with (G:= emptyEquiv G0).
    reflexivity.
    rewrite emptyEquiv_stable.
    apply permut_sym; assumption.
intros. rewrite Mem_cons_eq in H5; destruct H5.
  subst; assumption.
  rewrite Mem_nil_eq in H5; contradiction.
  intro; contradiction.
  intro; repeat split; auto; apply permut_sym; auto.
  simpl in *. case_if. apply ok_Bg_permut with (G':=(w,nil)::G) in HOk.
  apply ok_Bg_permut with (G:=(w,nil & A)::G).
  permut_simpl.
  simpl in *; assumption.
  apply permut_trans with (l2:=G & (w, nil)); try apply permut_sym; permut_simpl; eauto.
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
apply subst_t_preserv_types with (G0:=G) (Delta:=A::nil) (G_min:= G & (w0, nil)) (G_HT:= G & (w, nil & A)) (Gamma_subst:= nil) (Gamma_HT:=nil).
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
  intro. absurd (w = w0). eapply unique_worlds; eauto.
  assumption.
  intro; repeat split; auto; apply permut_sym; auto.

  simpl in *. case_if. apply ok_Bg_permut with (G':=(w,nil)::G) in HOk.
  apply ok_Bg_permut with (G:=(w,nil & A)::G).
  permut_simpl.
  simpl in *; assumption.
  apply permut_trans with (l2:=G & (w, nil)); try apply permut_sym; permut_simpl; eauto.

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
  apply emptyEquiv_empty with (G:=G1).
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
destruct (eq_var_LF_dec w0 w1).
(* = *)
subst.
assert (permut (G0 & (w1, nil) ++ nil) (G & (w1, nil) ++ nil)).
rew_app; assumption.
apply permut_inv in H4; rew_app in H4.
eapply subst_t_preserv_types_inner with (Delta:=A::nil). 
simpl; split; auto.
rewrite emptyEquiv_stable; 
apply BackgroundSubsetImpl with (G:=G0 & (w,nil)).
assumption.
exists (@nil Context_LF).
rew_app.
apply permut_trans with (l2:=G&(w,nil));
permut_simpl; assumption.
intros. rewrite Mem_cons_eq in H6; destruct H6.
  subst; assumption.
  rewrite Mem_nil_eq in H6; contradiction.
assumption.
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
assert (w <> w0).
eapply unique_worlds with (G':=(GH & (w1, nil) ++ GT) & (w0, nil));
eauto.
assert (permut (emptyEquiv G1 & (w0, nil)) (G0 & (w1,nil) &(w,nil))).
  apply permut_trans with (l2:=GH & (w1, nil) ++ GT & (w,nil)  & (w0, nil) ).
  permut_simpl. rew_app in H0. rew_app. apply permut_sym; assumption.
  permut_simpl; apply permut_sym; assumption.
assert (exists GH', exists GT', G0 & (w1,nil) = GH' & (w0,nil) ++ GT').
apply permut_split_neq with (G := emptyEquiv G1) (G' := nil) (elem' := (w, nil)).
intro; inversion H9; subst; elim H6; reflexivity.
rew_app in *; assumption.
destruct H9 as (GH').
destruct H9 as (GT').
assert (exists GH'', exists GT'', G0 = GH'' & (w0, nil) ++ GT'').
apply permut_split_neq with (G := GH') (G' := GT') (elem' := (w1, nil)).
intro; inversion H10; subst; elim n; reflexivity.
rewrite <- H9; permut_simpl.
destruct H10 as (GH'').
destruct H10 as (GT'').
subst G0.
assert (permut (emptyEquiv G1 ++ nil) ((GH'' ++ GT'') & (w, nil) & (w1, nil))).
apply permut_inv with (elem := (w0,nil)).
rew_app in *.
apply permut_trans with (l2:=(GH'' ++ (w0, nil) :: GT'' ++ (w1, nil) :: (w, nil) :: nil)).
assumption. permut_simpl.
apply subst_t_preserv_types with (G0 := GH''++GT'' & (w, nil)) 
  (Delta:=A::nil) (G_min:= GH'' ++ GT'' & (w, nil) & (w0, nil)) (G_HT:= (GH'' ++ GT'' & (w, nil)) & (w1, nil & A)) (Gamma_subst:= nil) (Gamma_HT:=nil).
  simpl; split; auto.
  rewrite emptyEquiv_inv with (w:=w1) (G':=(GH'' ++ GT'' & (w, nil) & (w0, nil))).
  apply BackgroundSubsetImpl with (G:=(GH'' & (w0, nil) ++ GT'') & (w, nil)).
  apply HT0.
  exists (@nil Context_LF); permut_simpl.
  apply emptyEquiv_last.
  replace ( GH'' ++ GT'' & (w, nil) & (w0, nil) ) with (( GH'' ++ GT'' & (w, nil)) & (w0, nil)).
  apply emptyEquiv_last.
  apply emptyEquiv_inv with (w:=w1).
  apply emptyEquiv_empty with (G:=G1). 
  rew_app in *. assumption.
  rew_app; reflexivity.
intros. rewrite Mem_cons_eq in H11; destruct H11.
  subst; assumption.
  rewrite Mem_nil_eq in H11; contradiction.
intro neq; symmetry in neq. subst; elim n. reflexivity. 
intro; repeat split; eauto; permut_simpl. rew_app in *; assumption.

simpl in *. 
case_if.
rewrite ok_Bg_emptyEquiv.
apply ok_Bg_permut with (G:=emptyEquiv G1).
apply permut_trans with (l2:=(GH'' ++ GT'') & (w, nil) & (w1, nil)).
rew_app in *; assumption.
rewrite emptyEquiv_last with (G':= (GH'' ++ GT'') & (w, nil)).
permut_simpl.
assert ((GH'' ++ GT'') & (w, nil) & (w1, nil) = emptyEquiv ((GH'' ++ GT'') & (w, nil) & (w1, nil))).
symmetry; apply emptyEquiv_empty with (G:=G1).
rew_app in *; assumption.
assert (permut ((GH'' ++ GT'') & (w, nil) & (w1, nil)) (emptyEquiv ((GH'' ++ GT'') & (w, nil) & (w1, nil)))).
rewrite <- H12; permut_simpl.
assert (permut (emptyEquiv (GH'' ++ GT'' & (w, nil)) ++ nil) ((GH'' ++ GT'' & (w, nil))++nil)).
apply permut_inv with (elem := (w1, nil)).
apply permut_sym.
rewrite emptyEquiv_last with (G':=emptyEquiv ((GH'' ++ GT'') & (w, nil))) in H13.
rew_app in *; assumption.
reflexivity.
rew_app.
apply emptyEquiv_empty with (G:=GH'' ++ GT'' & (w, nil)).
rew_app in *; assumption.
assumption.

unfold open_ctx in *.
  apply inv_subst_ctx_preserv_types_outer with (w':=w2) (Gamma':=A::nil) (Gamma:=nil) (G0:=(GH'' ++ GT'' & (w, nil))).
  assumption.
  permut_simpl.
  replace (fctx w0) with (fctx (fst (w0, (@nil ty_LF)))).
  apply rename_ctx_preserv_types_outer with (G':=(emptyEquiv G1 & (w2, A::nil))) (Gamma:=nil) (G:=GH''++GT'' & (w,nil)).
  permut_simpl; rew_app in H10.
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

apply ok_Bg_permut with (G:=(w0, nil)::emptyEquiv G1).
apply permut_trans with (l2:=(w0,nil) :: G & (w, nil)); permut_simpl.
apply permut_sym; assumption.
assumption.

rewrite emptyEquiv_last with (G':=G).
reflexivity.
apply emptyEquiv_inv with (w:=w).
apply emptyEquiv_empty with (G:=G1).
apply permut_sym; assumption.
Qed.

End Lemmas.

Close Scope label_free_is5_scope.
