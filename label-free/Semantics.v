Require Export Syntax.
Require Export Substitution.
Require Import List.
Require Import LibList.
Require Import LibNat.
Require Import LibListSorted.

Open Scope is5_scope.

Global Reserved Notation " G '|=' Gamma '|-' M ':::' A " (at level 70).

Definition Context := list ty.

(* Statics *)

Inductive types: list Context -> Context -> te -> ty -> Prop :=
| t_hyp: forall A G Gamma v_n
  (HT: nth_error Gamma v_n = Some A),
  G |= Gamma |- (hyp v_n) ::: A
| t_lam: forall A B G Gamma M 
  (HT: G |= A::Gamma |- M ::: B),
  G |= Gamma |- (lam A M) ::: A ---> B
| t_appl: forall A B G Gamma M N
  (HT1: G |= Gamma |- M ::: A ---> B)
  (HT2: G |= Gamma |- N ::: A),
  G |= Gamma |- (appl M N) ::: B
| t_box: forall A G G' Gamma M
  (HT: G & Gamma ++ G' |= nil |- M ::: A),
  G ++ G' |= Gamma |- (box M) ::: [*] A
| t_unbox: forall A G Gamma M
  (HT: G |= Gamma |- M ::: [*] A),
  G |= Gamma |- unbox M ::: A
| t_unbox_fetch: forall A G G' Gamma Gamma' M
  (HT: G & Gamma' ++ G' |= Gamma |- M ::: [*] A),
  G & Gamma ++ G' |= Gamma' |- unbox_fetch M ::: A
| t_here: forall A G Gamma M
  (HT: G |= Gamma |- M ::: A),
  G |= Gamma |- here M ::: <*> A
| t_get_here: forall A G G' Gamma Gamma' M
  (HT: G & Gamma' ++ G' |= Gamma |- M ::: A),
  G & Gamma ++ G' |= Gamma' |- get_here M ::: <*> A
| t_letdia: forall A B G Gamma M N
  (HT1: G |= Gamma |- M ::: <*> A)
  (HT2: (A :: nil) :: G |= Gamma |- N ::: B),
  G |= Gamma |- letdia M N ::: B
| t_letdia_get: forall A B G G' Gamma Gamma' M N
  (HT1: G & Gamma' ++ G' |= Gamma |- M ::: <*> A)
  (HT2: (A :: nil) :: G ++ G' |= Gamma' |- N ::: B),
  G & Gamma ++ G' |= Gamma' |- letdia_get M N ::: B
where " G '|=' Gamma '|-' M ':::' A " := (types G Gamma M A).

(* Dynamics *)

Inductive value: te -> Prop :=
| val_lam: forall A M, value (lam A M)
| val_box: forall M, value (box M)
| val_here: forall M, value M -> value (here M)
| val_get_here: forall M, value M -> value (get_here M)
.

Global Reserved Notation " M |-> N " (at level 70).

Inductive step: te -> te -> Prop :=
| red_appl_lam: forall M A N, appl (lam A M) N |-> [N//0] M
| red_unbox_box: forall M, unbox (box M) |-> M
| red_unbox_fetch_box: forall M, unbox_fetch (box M) |-> M
| red_letdia_here: forall M N, letdia (here M) N |-> [M//0]N
| red_letdia__get_here: forall M N, letdia (get_here M) N |-> [M//0]N
| red_letdia_get__here: forall M N, letdia_get (here M) N |-> [M//0]N
| red_letdia_get_get_here: forall M N, letdia_get (get_here M) N |-> [M//0]N
| red_appl: forall M N M' (HT: M |-> M'), appl M N |-> appl M' N
| red_unbox: forall M M' (HT: M |-> M'), unbox M |-> unbox M'
| red_unbox_fetch: forall M M' (HT: M |-> M'), unbox_fetch M |-> unbox_fetch M'
| red_dia_here: forall M M' (HT: M |-> M'), here M |-> here M'
| red_dia_move: forall M M' (HT: M |-> M'), get_here M |-> get_here M'
| red_letdia: forall M N M' (HT: M |-> M'), letdia M N |-> letdia M' N
| red_letdia_move: forall M N M' (HT: M |-> M'), letdia_get M N |-> letdia_get M' N
where " M |-> N " := (step M N ) : is5_scope.


Section Lemmas.

Lemma eq_context_dec:
forall Gamma Gamma': Context, {Gamma = Gamma'} + {Gamma <> Gamma'}.
  intros; decide equality; decide equality.
Qed.

(* TODO: this may be moved to a separate file *)
Lemma PermutationElementSplit:
forall A G G' H (elem: A)
  (HT: permut (G & elem ++ G') H),
  exists GH, exists GT, H = GH & elem ++ GT.
Admitted.

Lemma PermutationElementSplit_Neq:
forall A G G' H (elem: A) (elem': A)
  (HNeq: elem <> elem')
  (HT: permut (G & elem ++ G') (H & elem')),
  exists GH, exists GT, H = GH & elem ++ GT.
Admitted.

Lemma PermutationElemInside:
forall A G G' H H' (elem: A)
  (HP: permut (G & elem ++ G') (H & elem ++ H')),
  permut (G++G') (H++H').
Admitted.

(* TODO: ugly.. *)
Lemma BackgroundSubsetImpl:
forall G G' Gamma M A
  (HSubst: exists GT, permut (G++GT) G')
  (HT: G |= Gamma |- M ::: A),
  G' |= Gamma |- M ::: A.
intros.
generalize dependent G'.
induction HT; intros; eauto using types.
(* box *)
replace G'0 with (G'0 ++ nil) by (rew_app; reflexivity);
constructor; rew_app;
apply IHHT;
destruct HSubst as [GT];
exists GT; permut_simpl;
rew_app in H; assumption.
(* unbox_fetch *)
destruct HSubst as [GT].
replace ((G & Gamma ++ G') ++ GT) with (G & Gamma ++ (G'++GT)) in H by (rew_app; reflexivity).
assert (exists GH0, exists GT0, G'0 = GH0 & Gamma ++ GT0).
  apply PermutationElementSplit with (G:=G) (G':=G'++GT); assumption.
destruct H0 as [GH0]; destruct H0 as [GT0]. 
subst G'0.
constructor.
apply IHHT.
exists GT; 
permut_simpl.
apply PermutationElemInside in H.
assumption.
(* get_here *)
destruct HSubst as [GT].
replace ((G & Gamma ++ G') ++ GT) with (G & Gamma ++ (G'++GT)) in H by (rew_app; reflexivity).
assert (exists GH0, exists GT0, G'0 = GH0 & Gamma ++ GT0).
  apply PermutationElementSplit with (G:=G) (G':=G'++GT); assumption.
destruct H0 as [GH0]; destruct H0 as [GT0]. 
subst G'0.
constructor.
apply IHHT.
exists GT; 
permut_simpl.
apply PermutationElemInside in H.
assumption.
(* letdia *)
apply t_letdia with (A:=A). 
apply IHHT1; assumption.
apply IHHT2.
destruct HSubst as [GT];
exists GT.
permut_simpl; assumption.
(* letdia_get *)
destruct HSubst as [GT].
replace ((G & Gamma ++ G') ++ GT) with (G & Gamma ++ (G'++GT)) in H by (rew_app; reflexivity).
assert (exists GH0, exists GT0, G'0 = GH0 & Gamma ++ GT0).
  apply PermutationElementSplit with (G:=G) (G':=G'++GT); assumption.
destruct H0 as [GH0]; destruct H0 as [GT0]. 
subst G'0.
apply t_letdia_get with (A:=A).
apply IHHT1.
exists GT; 
permut_simpl.
apply PermutationElemInside in H.
assumption.
apply IHHT2.
exists GT; 
permut_simpl.
apply PermutationElemInside in H.
assumption.
Qed.

Lemma GlobalWeakening:
forall G G' Gamma M A Ctx
  (HT: G ++ G' |= Gamma |- M ::: A),
  G & Ctx ++ G' |= Gamma |- M ::: A.
intros; rew_app;
apply BackgroundSubsetImpl with (G:=G++G');
[exists (Ctx::nil); permut_simpl | assumption].
Qed.

(* TODO: uglier... *)
Lemma Weakening_general:
forall G Gamma M A
  (HT: G |= Gamma |- M ::: A),
  (forall G' Delta Delta',
    permut G (G' & Delta) ->
    G' & (Delta ++ Delta') |= Gamma |- M ::: A) /\ 
  (forall Gamma', G |= Gamma ++ Gamma' |- M ::: A).
intros.
induction HT; split; intros.
(* hyp *)
eauto using types.
constructor.
generalize dependent v_n.
induction Gamma; destruct v_n; intros;
simpl in HT; try discriminate; simpl.
  assumption.
  apply IHGamma; assumption.
(* lam *)
constructor;
eapply IHHT; eassumption.
constructor;
eapply IHHT; eassumption.
(* appl *)
econstructor; [eapply IHHT1| eapply IHHT2]; eauto.
econstructor; [eapply IHHT1| eapply IHHT2]; eauto.
(* box 1 *)
constructor.
apply IHHT.
permut_simpl; assumption.
(* box 2 *)
constructor.
destruct IHHT as (IHHT1, IHHT2).
apply BackgroundSubsetImpl with (G:= (G ++ G') & (Gamma ++ Gamma')).
  exists nil; permut_simpl.
apply IHHT1. permut_simpl. 
(* unbox *)
constructor; apply IHHT; assumption.
constructor; apply IHHT; assumption.
(* unbox_fetch 1 *)
destruct (eq_context_dec Gamma Delta).
(* = *)
subst.
apply BackgroundSubsetImpl with (G:=(G & (Delta ++ Delta') ++ G')).
  exists nil. permut_simpl. 
  replace (G'0 & Delta) with (G'0 & Delta ++ nil) in H by (rew_app; reflexivity).
  apply PermutationElemInside in H. 
  rew_app in H; assumption.
constructor.
apply IHHT.
(* <> *)
assert (exists G0, exists G1, G'0 = G0 & Gamma ++ G1).
  apply PermutationElementSplit_Neq with (G:=G) (G':=G') (elem':=Delta); assumption.
destruct H0 as [G0]; destruct H0 as [G1].
subst G'0.
replace ((G0 & Gamma ++ G1) & (Delta ++Delta')) with (G0 & Gamma ++ (G1 & (Delta ++Delta'))) by (rew_app; reflexivity).
constructor .
replace (G0 & Gamma' ++ G1 & (Delta ++Delta')) with ((G0 & Gamma' ++ G1) & (Delta ++Delta')) by (rew_app; reflexivity).
apply IHHT.
permut_simpl.
replace ((G0 & Gamma ++ G1) & Delta) with (G0 & Gamma ++ (G1 & Delta)) in H by (rew_app; reflexivity).
apply PermutationElemInside in H.
assumption. 
(* unbox_fetch 2 *)
constructor.
assert (exists GG, permut (G & (Gamma' ++ Gamma'0) ++ G') (GG & (Gamma' ++Gamma'0))).
exists (G++G'); permut_simpl.
destruct IHHT as (IHHT1, IHHT2).
destruct H as [GG]. 
apply BackgroundSubsetImpl with (G:=GG & (Gamma' ++ Gamma'0)).
exists nil; apply permut_sym; permut_simpl. rew_app in *; assumption.
apply IHHT1.
permut_simpl.
replace (GG & (Gamma' ++Gamma'0)) with (GG & (Gamma' ++Gamma'0) ++ nil) in H by (rew_app; reflexivity).
apply PermutationElemInside in H.
rew_app in H.
assumption.
(* here *)
constructor; apply IHHT; assumption.
constructor; apply IHHT; assumption.
(* get_here 1 *)
destruct (eq_context_dec Gamma Delta).
(* = *)
subst.
apply BackgroundSubsetImpl with (G:=(G & (Delta ++Delta') ++ G')).
  exists nil. permut_simpl. 
  replace (G'0 & Delta) with (G'0 & Delta ++ nil) in H by (rew_app; reflexivity).
  apply PermutationElemInside in H. 
  rew_app in H; assumption.
constructor.
apply IHHT.
(* <> *)
assert (exists G0, exists G1, G'0 = G0 & Gamma ++ G1).
  apply PermutationElementSplit_Neq with (G:=G) (G':=G') (elem':=Delta); assumption.
destruct H0 as [G0]; destruct H0 as [G1].
subst G'0.
replace ((G0 & Gamma ++ G1) & (Delta ++ Delta')) with (G0 & Gamma ++ (G1 & (Delta ++Delta'))) by (rew_app; reflexivity).
constructor .
replace (G0 & Gamma' ++ G1 & (Delta ++Delta')) with ((G0 & Gamma' ++ G1) & (Delta ++Delta')) by (rew_app; reflexivity).
apply IHHT.
permut_simpl.
replace ((G0 & Gamma ++ G1) & Delta) with (G0 & Gamma ++ (G1 & Delta)) in H by (rew_app; reflexivity).
apply PermutationElemInside in H.
assumption. 
(* get_here 2 *)
constructor.
assert (exists GG, permut (G & (Gamma' ++Gamma'0) ++ G') (GG & (Gamma'++Gamma'0))).
exists (G++G'); permut_simpl.
destruct IHHT as (IHHT1, IHHT2).
destruct H as [GG]. 
apply BackgroundSubsetImpl with (G:=GG & (Gamma' ++ Gamma'0)).
exists nil; apply permut_sym; permut_simpl. rew_app in *; assumption.
apply IHHT1.
permut_simpl.
replace (GG & (Gamma' ++ Gamma'0)) with (GG & (Gamma'  ++ Gamma'0) ++ nil) in H by (rew_app; reflexivity).
apply PermutationElemInside in H.
rew_app in H.
assumption.
(* letdia *)
apply t_letdia with (A:=A).
apply IHHT1; assumption.
apply IHHT2 with (G':=(A::nil)::G'). 
permut_simpl.
assumption.
apply t_letdia with (A:=A).
apply IHHT1; assumption.
apply IHHT2. 
(* letdia_get 1 *)
destruct (eq_context_dec Gamma Delta).
(* = *)
subst.
apply BackgroundSubsetImpl with (G:=(G & (Delta ++Delta') ++ G')).
  exists nil. permut_simpl. 
  replace (G'0 & Delta) with (G'0 & Delta ++ nil) in H by (rew_app; reflexivity).
  apply PermutationElemInside in H. 
  rew_app in H; assumption.
apply t_letdia_get with (A:=A).
apply IHHT1.
assumption.
(* <> *)
assert (exists G0, exists G1, G'0 = G0 & Gamma ++ G1).
  apply PermutationElementSplit_Neq with (G:=G) (G':=G') (elem':=Delta); assumption.
destruct H0 as [G0]; destruct H0 as [G1].
subst G'0.
replace ((G0 & Gamma ++ G1) & (Delta ++Delta')) with (G0 & Gamma ++ (G1 & (Delta ++Delta'))) by (rew_app; reflexivity).
apply t_letdia_get with (A:=A).
replace (G0 & Gamma' ++ G1 & (Delta ++Delta')) with ((G0 & Gamma' ++ G1) & (Delta ++Delta')) by (rew_app; reflexivity).
apply IHHT1.
permut_simpl.
replace ((G0 & Gamma ++ G1) & Delta) with (G0 & Gamma ++ (G1 & Delta)) in H by (rew_app; reflexivity).
apply PermutationElemInside in H.
assumption. 
replace ( (A :: nil) :: G0 ++ G1 & (Delta ++Delta')) with (((A :: nil) :: G0 ++ G1) & (Delta ++Delta')) by (rew_app;reflexivity).
apply IHHT2.
permut_simpl.
replace ((G0 & Gamma ++ G1) & Delta) with (G0 & Gamma ++ (G1 & Delta)) in H by (rew_app; reflexivity).
apply PermutationElemInside in H.
assumption. 
(* letdia_get 2 *)
apply t_letdia_get with (A:=A). 
assert (exists GG, permut (G & (Gamma' ++Gamma'0) ++ G') (GG & (Gamma' ++Gamma'0))).
exists (G++G'); permut_simpl.
destruct H as [GG]. 
apply BackgroundSubsetImpl with (G:=GG & (Gamma' ++ Gamma'0)).
exists nil; apply permut_sym; permut_simpl. rew_app in *; assumption.
apply IHHT1.
permut_simpl.
replace (GG & (Gamma' ++Gamma'0)) with (GG & (Gamma' ++ Gamma'0) ++ nil) in H by (rew_app; reflexivity).
apply PermutationElemInside in H.
rew_app in H.
assumption.
apply IHHT2.
Qed.

Lemma WeakeningBackgroundElem:
forall G G' Delta Delta' Gamma M A
  (HT: G & Delta ++ G' |= Gamma |- M ::: A),
  G & (Delta ++ Delta') ++ G' |= Gamma |- M ::: A.
intros.
apply BackgroundSubsetImpl with (G:=(G++G') & (Delta ++ Delta')).
exists nil; permut_simpl.
assert (permut (G & Delta ++ G') ((G++G') & Delta)).
  permut_simpl.
eapply Weakening_general; eassumption.
Qed.

Lemma Weakening:
forall G Gamma Gamma' M A
  (HT: G |= Gamma |- M ::: A),
  G |= Gamma ++ Gamma' |- M ::: A.
intros;
eapply Weakening_general; eassumption.
Qed.

Lemma Progress:
forall G M A
  (EmptyCtx: forall Ctx, Mem Ctx G -> Ctx = nil)
  (HT: G |= nil |- M ::: A),
  value M \/ exists N, M |-> N.
induction M; intros; eauto using value.
(* hyp *)
inversion HT; destruct n; discriminate.
(* appl *)
right; inversion HT; subst;
destruct (IHM1 (A0 ---> A) EmptyCtx HT1).
  inversion H; subst; inversion HT1; subst; eexists; constructor.
  destruct H; eexists; constructor; eapply H.
(* unbox *)
right; inversion HT; subst;
destruct (IHM ([*]A) EmptyCtx HT0).
  inversion H; subst; inversion HT0; subst; eexists; constructor.
  destruct H; eexists; constructor; eapply H.
(* unbox_fetch *)
right; inversion HT; subst.
destruct (IHM ([*]A) EmptyCtx).
assert (Gamma = nil).
  apply EmptyCtx;
  rewrite Mem_app_or_eq; left; rewrite Mem_app_or_eq; right;
  rewrite Mem_cons_eq; left; reflexivity.
subst; assumption.
inversion H; subst; inversion HT0; subst; eexists; constructor.
destruct H; eexists; constructor; eapply H.
(* here *)
inversion HT; subst.
destruct (IHM A0 EmptyCtx HT0).
left; apply val_here; assumption.
right; destruct H; exists (here x); eauto using step.
(* get_here *)
inversion HT; subst.
destruct (IHM A0 EmptyCtx).
assert (Gamma = nil).
  apply EmptyCtx;
  rewrite Mem_app_or_eq; left; rewrite Mem_app_or_eq; right;
  rewrite Mem_cons_eq; left; reflexivity.
subst; assumption.
left; econstructor; eassumption.
right; destruct H; exists (get_here x); eauto using step.
(* letdia *)
right; inversion HT; subst.
destruct (IHM1 (<*>A0) EmptyCtx HT1).
inversion H; subst; inversion HT1; subst.
  exists [M//0]M2; eauto using step.
  exists [M//0]M2; eauto using step.
destruct H; exists (letdia x M2); eauto using step.
(* letdia_get *)
right; inversion HT; subst.
destruct (IHM1 (<*>A0) EmptyCtx).
assert (Gamma = nil).
  apply EmptyCtx;
  rewrite Mem_app_or_eq; left; rewrite Mem_app_or_eq; right;
  rewrite Mem_cons_eq; left; reflexivity.
subst; assumption.
inversion H; subst; inversion HT1; subst.
  exists [M//0]M2; eauto using step.
  exists [M//0]M2; eauto using step.
destruct H; exists (letdia_get x M2); eauto using step.
Qed.

Fixpoint subst_typing G L D : Prop :=
match L, D with
| nil, nil => True
| M::L', A::D' => G |= nil |- M ::: A /\ (subst_typing G L' D')
| _, _ => False
end.

Lemma subst_t_type_preserv:
forall Delta G L Gamma N A
  (HT1: subst_typing G L Delta)
  (HT2: G |= Gamma ++ Delta |- N ::: A),
  G |= Gamma |- subst_list L (length Gamma) N ::: A.
Admitted.

Lemma WorldsCollapse:
forall G Delta G' Gamma M A,
  G & Delta ++ G'|= Gamma |- M ::: A
    <->
  G ++ G' |= Gamma ++ Delta |- M ::: A.
Admitted.

Lemma Preservation:
forall M A N G 
  (EmptyCtx: forall X, Mem X G -> X = nil)
  (HType: G |= nil |- M ::: A)
  (HStep: M |-> N),
  G |= nil |- N ::: A.
intros.
remember (@nil ty) as Gamma.
generalize dependent N.
induction HType; intros;
inversion HStep; subst;
eauto using types.
(* red_appl_lam *)
inversion HType1; subst.
replace ([N//0]M0) with (subst_list (N::nil) (length (@nil te)) M0) by auto.
apply subst_t_type_preserv with (Delta:=A::nil).
  simpl; split; auto.
assumption.
(* red_unbox_box *)
inversion HType; subst.
replace (@nil ty) with ((@nil ty)++(@nil ty)).
apply WorldsCollapse; assumption.
rew_app; reflexivity.
(* red_unbox_fetch_box *)
inversion HType; subst.
apply BackgroundSubsetImpl with (G':=G & nil ++ G' & Gamma) in HT.
apply WorldsCollapse in HT.
rew_app in HT.
apply BackgroundSubsetImpl with (G := G ++ G' & Gamma).
exists nil; permut_simpl.
assumption.
exists nil; permut_simpl.
apply permut_trans with (l2:= G & nil ++ G').
rewrite H0; permut_simpl.
permut_simpl.
(* red_unbox_fetch *)
constructor.
assert (Gamma = nil).
  apply EmptyCtx.
  rew_app; rewrite Mem_app_or_eq.
  right; rewrite Mem_cons_eq; 
  left; reflexivity.
subst.
apply IHHType; auto.
(* red_get_here *)
constructor.
assert (Gamma = nil).
  apply EmptyCtx.
  rew_app; rewrite Mem_app_or_eq.
  right; rewrite Mem_cons_eq; 
  left; reflexivity.
subst.
apply IHHType; auto.
(* red_letdia_here *)
inversion HType1; subst.
replace ([M0//0]N) with (subst_list (M0::nil) (length (@nil te)) N) by auto.
apply subst_t_type_preserv with (Delta:=A::nil).
  simpl; split; auto.
rew_app.
replace (A::nil) with (nil ++ (A::nil)) by (rew_app; reflexivity).
replace G with (G ++ nil) by (rew_app; reflexivity).
apply WorldsCollapse.
rew_app.
apply BackgroundSubsetImpl with (G:=(A::nil)::G).
exists nil; permut_simpl.
assumption.
(* red_letdia__get_here *)
inversion HType1; subst.
replace ([M0//0]N) with (subst_list (M0::nil) (length (@nil te)) N) by auto.
apply subst_t_type_preserv with (Delta:=A::nil).
  simpl; split; auto.
apply WorldsCollapse in HT.
apply <- WorldsCollapse.
rew_app in *.
assumption.
clear IHHType1 IHHType2 HType1 EmptyCtx.
apply -> WorldsCollapse.
apply BackgroundSubsetImpl with (G:=(A :: nil) :: G0 & Gamma ++ G').
exists nil; permut_simpl.
assumption.
(* red_letdia_get__here *)
inversion HType1; subst.
replace ([M0//0]N) with (subst_list (M0::nil) (length (@nil te)) N) by auto.
apply subst_t_type_preserv with (Delta:=A::nil).
  simpl; split; auto.
apply WorldsCollapse in HT.
apply <- WorldsCollapse.
rew_app in *.
assumption.
apply GlobalWeakening.
clear IHHType1 IHHType2 HType1 EmptyCtx.
apply -> WorldsCollapse.
apply BackgroundSubsetImpl with (G:=(A :: nil) :: G ++ G').
exists nil; permut_simpl.
assumption.
(* red_letdia_get_get_here *)
inversion HType1; subst.
replace ([M0//0]N) with (subst_list (M0::nil) (length (@nil te)) N) by auto.
apply subst_t_type_preserv with (Delta:=A::nil).
  simpl; split; auto.
replace Gamma0 with (nil++Gamma0) in HT by auto.
apply WorldsCollapse in HT.
apply BackgroundSubsetImpl with (G':= G & Gamma & nil ++ G') in HT.
replace (@nil ty) with ((@nil ty) ++ (@nil ty)) by auto.
apply -> WorldsCollapse.
assumption.
exists nil. permut_simpl. rew_app in *. rewrite H0. permut_simpl.
clear IHHType1 IHHType2 HType1 EmptyCtx HT H0.
apply GlobalWeakening.
apply -> WorldsCollapse.
apply BackgroundSubsetImpl with (G:=(A :: nil) :: G ++ G').
exists nil; permut_simpl.
assumption.
(* red_letia_get *)
assert (Gamma = nil).
  apply EmptyCtx.
  rew_app; rewrite Mem_app_or_eq.
  right; rewrite Mem_cons_eq; 
  left; reflexivity.
subst.
apply t_letdia_get with (A:=A).
apply IHHType1; auto.
assumption.
Qed.

End Lemmas.

Close Scope is5_scope.