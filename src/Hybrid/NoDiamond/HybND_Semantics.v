Add LoadPath "../..".
Require Import HybND_Substitution.
Require Import Setoid.
Require Import LibList.
Require Import PermutLib.
Require Import HybND_PPermutLib.
Require Import HybND_OkLib.
Require Import HybND_EmptyEquivLib.

Open Scope hybrid_is5_scope.
Open Scope is5_scope.
Open Scope permut_scope.

(* Notation for term typing *)
Global Reserved Notation " G '|=' Ctx '|-' M ':::' A " (at level 70).


(*** Definitions ::: Statics ***)


(*
   For each full context (that is, context and background), we require
   that the variables - both for terms and worlds - are unique.
*)
Inductive types_Hyb: bg_Hyb -> ctx_Hyb -> te_Hyb -> ty -> Prop :=

| t_hyp_Hyb: forall A G w (Gamma: list (prod var ty)) v
  (Ok_Bg: ok_Bg_Hyb ((w, Gamma) :: G))
  (HT: Mem (v, A) Gamma),
  G |= (w, Gamma) |- hyp_Hyb (fte v) ::: A

| t_lam_Hyb: forall L A B G w Gamma M
  (Ok_Bg: ok_Bg_Hyb ((w, Gamma) :: G))
  (HT: forall v', v' \notin L ->
    G |= (w, (v', A) :: Gamma) |- M ^t^ (hyp_Hyb (fte v')) ::: B),
  G |= (w, Gamma) |- (lam_Hyb A M) ::: A ---> B

| t_appl_Hyb: forall A B G w Gamma M N
  (Ok_Bg: ok_Bg_Hyb ((w, Gamma) :: G))
  (HT1: G |= (w, Gamma) |- M ::: A ---> B)
  (HT2: G |= (w, Gamma) |- N ::: A),
  G |= (w, Gamma) |- (appl_Hyb M N) ::: B

| t_box_Hyb: forall L A G w Gamma M
  (Ok_Bg: ok_Bg_Hyb (G & (w, Gamma)))
  (HT: forall w', w' \notin L ->
    G & (w, Gamma) |= (w', nil) |- M ^w^ (fwo w') ::: A),
  G |= (w, Gamma) |- box_Hyb M ::: [*] A

| t_unbox_Hyb: forall A G w Gamma M
  (Ok_Bg: ok_Bg_Hyb ((w, Gamma) :: G))
  (HT: G |= (w, Gamma) |- M ::: [*] A),
  G |= (w, Gamma) |- unbox_fetch_Hyb (fwo w) M ::: A

| t_unbox_fetch_Hyb: forall A G w Gamma w' Gamma' M
  (Ok_Bg: ok_Bg_Hyb ((w, Gamma) :: G & (w', Gamma')))
  (HT: (G & (w', Gamma')) |= (w, Gamma) |- M ::: [*] A),
  forall G', (G & (w, Gamma)) ~=~ G' ->
    G' |= (w', Gamma') |- unbox_fetch_Hyb (fwo w) M ::: A

where " G '|=' Ctx '|-' M ':::' A " := (types_Hyb G Ctx M A)
  : hybrid_is5_scope.


(*** Definitions ::: Dynamics ***)


Inductive value_Hyb: te_Hyb -> Prop :=
| val_lam_Hyb: forall A M, value_Hyb (lam_Hyb A M)
| val_box_Hyb: forall M, value_Hyb (box_Hyb M)
.


Global Reserved Notation " M |-> N " (at level 70).

(*
   In order to define a step of reduction we require that certain terms
   are locally closed.
*)
Inductive step_Hyb: (te_Hyb * vwo) -> (te_Hyb * vwo) -> Prop :=
| red_appl_lam_Hyb: forall ctx M A N,
  lc_w_Hyb M ->
  lc_t_n_Hyb 1 M ->
  lc_w_Hyb N -> lc_t_Hyb N ->
  (appl_Hyb (lam_Hyb A M) N, ctx) |-> ( M ^t^ N , ctx)

| red_unbox_fetch_box_Hyb: forall ctx ctx' M,
   lc_w_n_Hyb 1 M ->
  lc_t_Hyb M ->
  (unbox_fetch_Hyb ctx' (box_Hyb M), ctx) |-> (M ^w^ ctx, ctx)

| red_appl_Hyb: forall ctx M N M'
  (HT: (M, ctx) |-> (M', ctx)),
  lc_w_Hyb M -> lc_t_Hyb M ->
  lc_w_Hyb N -> lc_t_Hyb N ->
  (appl_Hyb M N, ctx) |-> (appl_Hyb M' N, ctx)

| red_unbox_fetch_Hyb: forall ctx' M M' ctx
  (HT: (M, ctx') |-> (M', ctx')),
  lc_w_Hyb M -> lc_t_Hyb M ->
  (unbox_fetch_Hyb ctx' M, ctx) |-> (unbox_fetch_Hyb ctx' M', ctx)

where " M |-> N " := (step_Hyb M N ) : hybrid_is5_scope.

Inductive steps_Hyb : te_Hyb * vwo -> te_Hyb * vwo -> Prop :=
| single_step_Hyb: forall M M' w, (M, w) |-> (M', w) -> steps_Hyb (M, w) (M', w)
| multi_step_Hyb: forall M M' M'' w,
  (M, w) |-> (M', w) -> steps_Hyb (M', w) (M'', w)
  -> steps_Hyb (M, w) (M'', w)
.


(*** Properties ***)


(*
   Properties of background and context:
   * Background is defined up to ~=~ relation
   * Context is defined up to *=* relation
   * Weakening rules for
     * Background
     * Specific element of background
     * Main context
*)

(* Proof: simple induction on typing rules *)
Lemma BackgroundSubsetImpl_Hyb:
forall G G' Ctx M A
  (HT: G |= Ctx |- M ::: A)
  (HSubst: exists GT, (G++GT) ~=~ G')
  (H_ok: ok_Bg_Hyb (Ctx :: G')),
  G' |= Ctx |- M ::: A.
intros;
generalize dependent G';
induction HT; intros.
(* hyp *)
constructor; auto.
(* lam *)
apply t_lam_Hyb with (L:=L \u used_t_vars_Hyb ((w, Gamma)::G'));
[assumption | intros; eapply H; auto].
(* appl *)
econstructor; auto.
(* box *)
destruct HSubst as [GT];
apply t_box_Hyb with (L:=L \u used_w_vars_Hyb (G' & (w, Gamma))); intros;
[ apply ok_Bg_Hyb_cons_last |
  apply H; [ | exists GT | ] ]; auto; try PPermut_Hyb_simpl;
eapply ok_Bg_Hyb_fresh_wo;
[ apply ok_Bg_Hyb_cons_last |
  rewrite notin_union in H1; destruct H1]; auto.
(* unbox *)
constructor; auto.
(* unbox_fetch *)
destruct HSubst as [GT];
apply t_unbox_fetch_Hyb with (Gamma:=Gamma) (G:=G++GT).
apply ok_Bg_Hyb_ppermut with (G:=(w', Gamma')::G'0);
  [rewrite <- H0; rewrite <- H; rew_app | ]; auto.
apply IHHT; [exists GT | ]; auto; try PPermut_Hyb_simpl.
apply ok_Bg_Hyb_ppermut with (G:=(w', Gamma')::G'0); auto.
rewrite <- H0; rewrite <- H; rew_app; auto.
transitivity (G' ++ GT); PPermut_Hyb_simpl; auto.
Qed.


(*
   Proof: using BackgroundSubsetImpl with some tweaks to remove ok_Bg_Hyb from
   assumptions.
*)
Lemma PPermut_Hyb_bg:
forall G Gamma w M A,
  G |= (w, Gamma) |- M ::: A ->
    forall G',
      G ~=~ G' ->
      G' |= (w, Gamma) |- M ::: A.
intros; apply BackgroundSubsetImpl_Hyb with (G:=G);
[ | exists (@nil ctx_Hyb) | ]; rew_app; auto;
inversion H; subst;
try (apply ok_Bg_Hyb_ppermut with (G:=(w, Gamma) :: G); auto);
apply ok_Bg_Hyb_cons_last; auto;
rewrite <- H6 || rewrite <- H1;
apply ok_Bg_Hyb_ppermut with (G:=(w0, Gamma0) :: G0 & (w, Gamma)); eauto.
Qed.


(*
   Adding types_Hyb as morphism for PPermut_Hyb will allow us to simply rewrite
   PPermut_Hybations of backgrounds.
*)
Add Morphism types_Hyb : PPermut_Hyb_types.
split; intros; destruct y0;
[ apply PPermut_Hyb_bg with (G:=x) |
  apply PPermut_Hyb_bg with (G:=y) ]; auto.
Qed.


(* Proof: Simple induction on typing rules *)
Lemma ContextPermutImpl_Hyb:
forall G Gamma Gamma' w M A
  (HPerm: Gamma *=* Gamma')
  (HT: G |= (w, Gamma) |- M ::: A),
  G |= (w, Gamma') |- M ::: A.
intros; generalize dependent Gamma';
remember (w, Gamma) as Ctx; generalize dependent Gamma;
induction HT;
intros; simpl in *; try (inversion HeqCtx; subst).
(* hyp *)
constructor;
[ eapply ok_Bg_Hyb_permut |
  eapply Mem_permut]; eauto.
(* lam *)
econstructor; [ eapply ok_Bg_Hyb_permut | ]; eauto.
(* appl *)
econstructor; [ eapply ok_Bg_Hyb_permut | | ]; eauto.
(* box *)
econstructor; [ eapply ok_Bg_Hyb_permut_last | intros]; eauto;
assert (G & (w, Gamma') ~=~ G & (w, Gamma0)) by auto;
rewrite H1; apply HT; eauto.
(* unbox *)
econstructor; [ eapply ok_Bg_Hyb_permut | ]; eauto.
(* unbox_fetch *)
apply t_unbox_fetch_Hyb with (G:=G) (Gamma:=Gamma); auto.
apply ok_Bg_Hyb_ppermut with (G:=(w0, Gamma) :: G & (w, Gamma0)); auto.
assert (G & (w, Gamma'0) ~=~ (G & (w, Gamma0))) as H0 by auto;
rewrite H0; auto.
Qed.


(* Weakening lemmas *)

Lemma GlobalWeakening_Hyb:
forall G G' Ctx Ctx' M A
  (HT: G ++ G' |= Ctx |- M ::: A)
  (H_ok: ok_Bg_Hyb (Ctx :: G & Ctx' ++ G')),
  G & Ctx' ++ G' |= Ctx |- M ::: A.
intros; rew_app;
apply BackgroundSubsetImpl_Hyb with (G:=G++G'); auto;
[ exists (Ctx'::nil); rew_app; symmetry |
  rew_app in *]; auto.
Qed.

(*
Proof: induction on typing
  * we need to be carefull when switching contexts - it's important to know
  if the context we're switching to is the one we intend to extend
  * if it is the case, it implies certain equivalences between pairs of
  backgrounds, which then help to use the induction hypothesis
  * otherwise we have to deconstruct background in order to extract the context
  that we want to switch
*)
Lemma Weakening_general_Hyb:
  forall G w Gamma M A
  (HT: G |= (w, Gamma) |- M ::: A),
  (forall G' w' Delta Delta',
    G ~=~ (G' & (w', Delta)) ->
    ok_Bg_Hyb ((w, Gamma) :: G' & (w', Delta ++ Delta')) ->
    G' & (w', Delta ++ Delta') |= (w, Gamma) |- M ::: A) /\
  (forall Gamma',
    ok_Bg_Hyb ((w, Gamma ++ Gamma') :: G) ->
    G |= (w, Gamma ++ Gamma') |- M ::: A).
intros;
remember (w, Gamma) as Ctx;
generalize dependent Gamma;
generalize dependent w;
induction HT; split;
intros; subst; simpl;
try (inversion HeqCtx; subst).
(* hyp *)
constructor; auto.
constructor; auto; rewrite Mem_app_or_eq; left; assumption.
(* lam *)
apply t_lam_Hyb with
  (L:=L \u used_t_vars_Hyb ((w0, Gamma0) :: G' & (w', Delta ++ Delta')));
[ | intros; eapply H]; auto.
apply t_lam_Hyb with (L:=L \u used_t_vars_Hyb ((w0, Gamma0++Gamma')::G));
[ | intros; eapply H with (v':=v')  (w:=w0) (Gamma:=(v' ,A)::Gamma0)]; auto;
rew_app; auto.
(* appl *)
econstructor; [ | eapply IHHT1| eapply IHHT2]; eauto.
econstructor; [ | eapply IHHT1| eapply IHHT2]; eauto.
(* box *)
apply t_box_Hyb with
  (L:=L \u used_w_vars_Hyb (G' & (w0, Gamma0) & (w', Delta ++ Delta')));
intros;
assert (G' & (w', Delta ++ Delta') & (w0, Gamma0) ~=~
        G' & (w0, Gamma0) & (w', Delta ++ Delta')) by (rew_app; auto);
[ apply ok_Bg_Hyb_ppermut with (G:=(w0, Gamma0) :: G' & (w', Delta ++ Delta')) |
  rewrite H3]; auto; try PPermut_Hyb_simpl;
apply H with (w:=w'0) (Gamma:=nil);
[ | | rewrite H0 | rewrite H0 in Ok_Bg]; auto; try PPermut_Hyb_simpl.
apply ok_Bg_Hyb_fresh_wo; auto;
apply ok_Bg_Hyb_ppermut with
  (G:=((w0, Gamma0) :: G' & (w', Delta ++ Delta')));
auto.
apply t_box_Hyb with (L:=L \u used_w_vars_Hyb (G & (w0, Gamma0++Gamma')));
[ apply ok_Bg_Hyb_ppermut with (G:= (w0, Gamma0++Gamma') :: G) |
  intros; eapply H]; auto; try PPermut_Hyb_simpl;
apply ok_Bg_Hyb_fresh_wo; auto;
apply ok_Bg_Hyb_ppermut with (G:=(w0, Gamma0++Gamma')::G); auto;
PPermut_Hyb_simpl.
(* unbox *)
constructor; [ | eapply IHHT]; eauto.
constructor; [ | eapply IHHT]; eauto.
(* unbox_fetch 1 *)
destruct (permut_context_Hyb_dec (w'0, Delta) (w, Gamma)) as [Eq|Neq];
simpl in *.
(* = *)
destruct Eq; subst;
assert (G ~=~ G'0) by
   (apply PPermut_Hyb_last_rev with (Gamma := Gamma) (Gamma':= Delta) (w:=w);
    [ apply permut_sym |
      transitivity G' ]; auto);
assert ((w0, Gamma0) :: G'0 & (w, Delta ++ Delta') ~=~
        (w, Gamma ++ Delta') :: G & (w0, Gamma0)) by
  (rewrite H3;
   transitivity ((w, Delta ++ Delta') :: G'0 & (w0, Gamma0));
     [ transitivity ((w0, Gamma0) :: (w, Delta ++ Delta') :: G'0) | ]; auto;
       transitivity ((w, Delta ++ Delta') :: (w0, Gamma0) :: G'0);
       auto; PPermut_Hyb_simpl);
apply t_unbox_fetch_Hyb with (G:=G) (Gamma:=Gamma++Delta');
[rewrite <- H4 | apply IHHT | rewrite H3]; auto; rewrite <- H4; auto.
(* <> *)
assert (exists Gamma', exists G0, exists G1,
  Gamma' *=* Gamma /\ G'0 = G0 & (w, Gamma') ++ G1) as H2 by
  ( apply PPermut_Hyb_split_neq with (G':=G) (w:=w'0) (Gamma := Delta);
    [ symmetry; transitivity G' | ]; auto);
destruct H2 as (Gamma', (GH, (GT, (H2a, H2b)))); subst;
apply t_unbox_fetch_Hyb with
  (Gamma:=Gamma) (G:=GH ++ GT & (w'0, Delta ++ Delta')).
apply ok_Bg_Hyb_ppermut with
  (G := (w0, Gamma0) :: (GH & (w, Gamma) ++ GT) & (w'0, Delta ++ Delta')); auto.
rew_app; PPermut_Hyb_simpl.
assert ((w0, Gamma0) :: (GH & (w, Gamma) ++ GT) & (w'0, Delta ++ Delta') ~=~
       ((w0, Gamma0) :: (GH & (w, Gamma') ++ GT) & (w'0, Delta ++ Delta')))
  by PPermut_Hyb_simpl.
rewrite H2; auto.
apply PPermut_Hyb_bg with
  (G:= (GH ++ GT & (w0, Gamma0)) & (w'0, Delta ++ Delta')).
  apply IHHT with (w1:=w) (Gamma1:=Gamma) (G':=GH ++ GT & (w0, Gamma0));
  assert (G ~=~ GH ++ GT & (w'0, Delta)) by
  ( apply PPermut_Hyb_last_rev_simpl with (a:=(w, Gamma)); auto;
    transitivity G'; [ | rewrite H0]; auto; PPermut_Hyb_simpl);
  auto; try PPermut_Hyb_simpl.
  apply ok_Bg_Hyb_ppermut with (G:= (w0, Gamma0) :: GH ++ (w, Gamma) :: GT &
     (w'0, Delta ++ Delta')); auto; try PPermut_Hyb_simpl.
  assert ((w0, Gamma0) :: GH ++ (w, Gamma) :: GT & (w'0, Delta ++ Delta') ~=~
       ((w0, Gamma0) :: (GH & (w, Gamma') ++ GT) & (w'0, Delta ++ Delta')))
  by PPermut_Hyb_simpl.
  rewrite H3; auto.
  transitivity (((w0, Gamma0) :: GH ++ GT) &
    (w'0, Delta++Delta')); [rew_app | ]; auto; PPermut_Hyb_simpl.
  transitivity (((w, Gamma) :: GH ++ GT ) &
    (w'0, Delta ++ Delta')); [ | rew_app]; auto; PPermut_Hyb_simpl.
(* unbox_fetch 2 *)
apply t_unbox_fetch_Hyb with (G:=G) (Gamma:=Gamma);
rewrite <- H in H0; [ | apply IHHT with (w1:=w) (Gamma1:=Gamma) |]; auto.
Qed.

Lemma WeakeningBackgroundElem_Hyb:
forall G G' w Delta Delta' Ctx M A
  (H_ok: ok_Bg_Hyb (Ctx :: G & (w, Delta ++ Delta') ++ G'))
  (HT: G & (w, Delta) ++ G' |= Ctx |- M ::: A),
  G & (w, Delta ++ Delta') ++ G' |= Ctx |- M ::: A.
intros;
assert ( G & (w, Delta ++ Delta') ++ G' ~=~ (G++G') & (w, Delta ++ Delta'))
  by (rew_app; auto);
rewrite H;
destruct Ctx; eapply Weakening_general_Hyb; auto.
rew_app; assert (G ++ G' & (w, Delta) ~=~ G & (w, Delta) ++ G') by auto;
rewrite H0; assumption.
apply ok_Bg_Hyb_ppermut with (G:=(v, l) :: G & (w, Delta ++ Delta') ++ G');
auto.
Qed.

Lemma Weakening_Hyb:
forall G w Gamma Gamma' M A
  (H_ok: ok_Bg_Hyb ((w,Gamma++Gamma')::G))
  (HT: G |= (w, Gamma) |- M ::: A),
  G |= (w, Gamma ++ Gamma') |- M ::: A.
intros;
eapply Weakening_general_Hyb; eassumption.
Qed.

(*
   When we can prove something in empty context and background, then we
   can also do it in any "full" version of this context & background
*)
Lemma types_weakened_Hyb:
forall G G' w Gamma M A
  (Ok: ok_Bg_Hyb ((w, Gamma)::G ++ G'))
  (HT: emptyEquiv_Hyb G ++ G' |= (w, nil) |- M ::: A),
  G ++ G'|= (w, Gamma) |- M ::: A.
induction G; intros; simpl in *; rew_app in *; auto.
apply Weakening_Hyb with (Gamma':=Gamma) in HT; rew_app in *; auto.
destruct a; rew_app in *.
assert ((v,l) :: G ++ G' ~=~ G ++ (v,l)::G') by PPermut_Hyb_simpl;
rewrite H; apply IHG.
rewrite <- H; auto.
assert (emptyEquiv_Hyb G ++ (v, l) :: G' ~=~
  emptyEquiv_Hyb G & (v, nil ++ l) ++ G')
  by PPermut_Hyb_simpl; rewrite H0; eapply WeakeningBackgroundElem_Hyb.
rew_app.
apply ok_Bg_Hyb_empty_first in Ok.
assert ((w, nil) :: (v, l) :: G ++ G' ~=~ ((w, nil) :: G) ++ (v, l) :: G') by
  PPermut_Hyb_simpl; rewrite H1 in Ok;
eapply emptyEquiv_Hyb_ok_Bg_Hyb_part in Ok; simpl in *; rew_app in *; auto.
assert (emptyEquiv_Hyb G & (v, nil) ++ G' ~=~
  (v, nil) :: emptyEquiv_Hyb G ++ G') by
  PPermut_Hyb_simpl; rewrite H1; auto.
Qed.


(* Type preservation under various types of substitution *)


(*
Proof: induction on typing
  * for hypothesis case we simply use weakening
  * for cases where we change worlds, we have to find the element, for
  which the substitution is defined - in other words, the context, from
  which the variable to substitute comes from; there are always two
  options: either it is the marked element or we have to do a manual
  split in order to find it
*)
Lemma subst_t_Hyb_preserv_types:
forall G w Gamma B M N v A
  (H_lc_t: lc_t_Hyb M)
  (H_lc_w: lc_w_Hyb M)
  (HT: G |= (w, Gamma) |- N ::: B),
  (* "inner" substitution *)
  ( forall Gamma0,
    permut Gamma ((v, A) :: Gamma0) ->
    emptyEquiv_Hyb G |= (w, nil) |- M ::: A ->
    G |= (w, Gamma0) |- [M // fte v] N ::: B)
  /\
  (* "outer" substitution *)
  ( forall G0 G' G'' w' Gamma',
    G ~=~ (G0 & (w', (v,A)::Gamma')) ->
    G' ~=~ (G0 & (w, Gamma)) ->
    G'' ~=~ (G0 & (w', Gamma')) ->
    emptyEquiv_Hyb G' |= (w', nil) |- M ::: A ->
    G'' |= (w, Gamma) |- [M // fte v] N ::: B).
intros;
remember (w, Gamma) as Ctx;
generalize dependent v;
generalize dependent A;
generalize dependent M;
generalize dependent w;
generalize dependent Gamma;
induction HT; split; intros;
inversion HeqCtx; subst;
simpl in *.

(* hyp *)
case_if.
inversion H1; subst;
assert (A = A0) by (eapply ok_Bg_Hyb_Mem_eq; eauto);
subst; replace G with (G ++ nil) by (rew_app; auto);
apply types_weakened_Hyb;
[eapply ok_Bg_Hyb_permut_first_tail with (C:=Gamma0) | ]; rew_app; eauto.
constructor;
[ apply ok_Bg_Hyb_permut_first_tail with (C:=Gamma0) (x:=v0) (A:=A0) |
  apply Mem_permut with (l' := (v0, A0) :: Gamma1) in HT]; eauto.
rewrite Mem_cons_eq in HT; destruct HT; auto;
inversion H2; subst; elim H1; reflexivity.

case_if.
inversion H3; subst;
eapply ok_Bg_Hyb_Mem_contradict in Ok_Bg;
contradiction || eauto.
constructor; auto;
apply ok_Bg_Hyb_ppermut with (G:=((w0, Gamma0)::G0) & (w', Gamma'));
[ rewrite H1 |
  eapply ok_Bg_Hyb_permut_no_last; rewrite H in Ok_Bg; rew_app]; eauto.

(* lam *)
apply t_lam_Hyb with (L:=L \u \{v});
[ apply ok_Bg_Hyb_permut_first_tail with (C:=Gamma0) (x:=v) (A:=A0) |
  intros]; auto;
rewrite notin_union in H2; rewrite notin_singleton in H2; destruct H2;
unfold open_t_Hyb in *;
rewrite <- subst_t_Hyb_comm; auto;
eapply H; auto;
permut_simpl || rew_app; eauto.

apply t_lam_Hyb with (L:=L \u \{v});
[ apply ok_Bg_Hyb_ppermut with (G:=((w0, Gamma0)::G0) & (w', Gamma'));
  [ rewrite H2 |
    rewrite H0 in Ok_Bg; rew_app] |
  intros]; eauto with ok_bg_hyb_rew;
rewrite notin_union in H4; rewrite notin_singleton in H4; destruct H4;
unfold open_t_Hyb in *;
rewrite <- subst_t_Hyb_comm; auto;
eapply H with (G0:=G0) (w':=w'); eauto;
assert (emptyEquiv_Hyb G' ~=~
  emptyEquiv_Hyb (G0 ++ nil & (w0, (v', A) :: Gamma0))) as E
 by (rewrite H1; rew_app; eapply emptyEquiv_Hyb_last_change; auto);
rew_app in *; rewrite <- E; auto.

(* appl *)
econstructor;  [ | eapply IHHT1 | eapply IHHT2];
try apply ok_Bg_Hyb_permut_first_tail with (C:=Gamma0) (x:=v) (A:=A0); eauto.

econstructor;
[ apply ok_Bg_Hyb_ppermut with (G:=((w0, Gamma0)::G0) & (w', Gamma'));
  [rewrite H1 | rewrite H in Ok_Bg] |
  eapply IHHT1 |
  eapply IHHT2]; eauto;
apply ok_Bg_Hyb_permut_no_last_spec in Ok_Bg; rew_app; auto.

(* box *)
apply t_box_Hyb with (L:=L \u used_w_vars_Hyb (emptyEquiv_Hyb G & (w0, nil)));
[ apply ok_Bg_Hyb_permut_no_last with (v:=v) (A:=A0);
  eapply ok_Bg_Hyb_permut_last |
  intros; unfold open_w_Hyb]; eauto;
rewrite <- subst_Hyb_order_irrelevant_bound;
[ eapply H; eauto |
  repeat rewrite emptyEquiv_Hyb_rewrite];
simpl; rew_app; auto;
apply BackgroundSubsetImpl_Hyb with (G:=emptyEquiv_Hyb G); auto;
[ exists ((w', (@nil (prod var ty))) :: nil); rew_app; auto |
  assert ((w0, nil) :: emptyEquiv_Hyb G & (w', nil) ~=~
    (w', nil) :: emptyEquiv_Hyb G & (w0, nil)) by auto];
rew_app; rewrite emptyEquiv_Hyb_rewrite_last; simpl; auto;
rewrite H3;
apply ok_Bg_Hyb_fresh_wo; auto;
apply emptyEquiv_Hyb_ok_Bg_Hyb in Ok_Bg;
rewrite emptyEquiv_Hyb_rewrite in Ok_Bg;
simpl in *; auto.

apply t_box_Hyb with
  (L:=L \u used_w_vars_Hyb(emptyEquiv_Hyb G0 ++ (w', nil) :: (w0, nil) :: nil));
[ rewrite H2; rewrite H0 in Ok_Bg |
  intros; unfold open_w_Hyb; rewrite <- subst_Hyb_order_irrelevant_bound];
eauto with ok_bg_hyb_rew;
eapply H with (G'' := G'' & (w0, Gamma0)) (G0:=G0 & (w0, Gamma0)) (w'0:=w')
  (Gamma':=Gamma') (A0:=A0); auto;
repeat rewrite emptyEquiv_Hyb_rewrite;
simpl; rew_app; try PPermut_Hyb_simpl;
apply BackgroundSubsetImpl_Hyb with (G:=emptyEquiv_Hyb G0 & (w0, nil));
[ rewrite H1 in H3; rewrite emptyEquiv_Hyb_rewrite in H3 |
  exists ((w'0, (@nil (var * ty)))::nil); rew_app |
  apply emptyEquiv_Hyb_ok_Bg_Hyb in Ok_Bg; rewrite H0 in Ok_Bg]; auto;
repeat rewrite emptyEquiv_Hyb_rewrite in Ok_Bg;
simpl in *; rew_app in *;
apply ok_Bg_Hyb_ppermut with
  (G:=(w'0, nil) :: emptyEquiv_Hyb G0 ++ (w', nil) :: (w0, nil) :: nil);
[eauto with ppermut_rew | apply ok_Bg_Hyb_fresh_wo ]; auto.

(* unbox *)
econstructor; [ | eapply IHHT];
try apply ok_Bg_Hyb_permut_first_tail with (C:=Gamma0) (x:=v) (A:=A0); eauto.

econstructor;
[ rewrite H1; rewrite H in Ok_Bg |
  eapply IHHT]; eauto with ok_bg_hyb_rew.

(* unbox_fetch *)
apply t_unbox_fetch_Hyb with (G:=G) (Gamma:=Gamma); auto;
[ apply ok_Bg_Hyb_permut_no_last_spec with (v:=v) (A:=A0);
  apply ok_Bg_Hyb_ppermut with (G:= (w, Gamma) :: G & (w0, Gamma0)) |
  eapply IHHT; eauto; rewrite <- H in H1; rew_app]; auto.

destruct (eq_var_dec w w'0).
(* = *)
subst;
assert (G ~=~ G0 /\ Gamma *=* (v, A0) :: Gamma'0) as HP by
  (apply ok_Bg_Hyb_impl_ppermut with (w:=w'0);
   [eauto with ok_bg_hyb_rew | transitivity G'; auto]);
destruct HP;
apply t_unbox_fetch_Hyb with (G:=G) (Gamma:=Gamma'0);
eauto with ok_bg_hyb_rew;
specialize IHHT with (Gamma1:=Gamma) (w:=w'0);
destruct IHHT with (M0:=M0) (A0:=A0) (v:=v); auto;
[ apply H6; auto; rewrite H1 in H3; rewrite H4 |
  rewrite H4; symmetry]; auto.
(* <> *)
assert (exists Gamma', exists GH, exists GT,
  Gamma' *=* (v, A0)::Gamma'0 /\ G = GH & (w'0, Gamma') ++ GT) as HP by
  (apply PPermut_Hyb_split_neq with (w:=w) (Gamma:=Gamma) (G':=G0);
    auto; transitivity G'; auto).
destruct HP as (Gamma', (GH, (GT, (HPa, HPb)))).
assert (GH & (w'0, Gamma') ++ GT ~=~ GH & (w'0, (v, A0)::Gamma'0) ++ GT)
  by PPermut_Hyb_simpl;
apply t_unbox_fetch_Hyb with (G:=GH ++ GT & (w'0, Gamma'0)) (Gamma:=Gamma).
subst;
apply ok_Bg_Hyb_ppermut with
  (G:= (((w, Gamma) :: (GH & (w0, Gamma0) ++ GT)) & (w'0, Gamma'0)));
[rew_app | ]; auto;
apply ok_Bg_Hyb_permut_no_last_spec with (v:=v)(A:=A0).
apply ok_Bg_Hyb_ppermut with
  (G:=(w, Gamma):: (GH & (w'0, Gamma') ++ GT) & (w0, Gamma0));
rew_app in *; auto; PPermut_Hyb_simpl.
eapply IHHT with (w1:=w) (Gamma1:=Gamma) (w':=w'0) (Gamma':=Gamma'0)
                 (G0:=GH ++ GT & (w0, Gamma0)); rew_app; auto; subst;
rew_app; auto;
rewrite H1 in H3;
assert (GH ++ (w, Gamma) :: GT ~=~ G0) by
  (apply PPermut_Hyb_last_rev_simpl with (a:=(w'0, (v, A0) :: Gamma'0));
  rew_app in *; rewrite <- H0; rewrite <- H; auto; PPermut_Hyb_simpl).
PPermut_Hyb_simpl; eauto.
assert (GH ++ (w, Gamma) :: GT & (w0, Gamma0) ~=~ G0 & (w0,Gamma0)) by
  (rewrite <- H5; rew_app; auto; PPermut_Hyb_simpl);
rewrite H6; auto.
subst; rewrite H2; PPermut_Hyb_simpl.
apply PPermut_Hyb_last_rev with (w:=w'0) (Gamma:=Gamma')
  (Gamma':=(v,A0)::Gamma'0);
[ | symmetry]; auto; transitivity G'; auto; rewrite <- H; PPermut_Hyb_simpl.
Qed.

Lemma subst_t_Hyb_preserv_types_inner:
forall G w Gamma A B M N v
  (H_lc_t: lc_t_Hyb M)
  (H_lc_w: lc_w_Hyb M)
  (HT: G |= (w, (v, A) :: Gamma) |- N ::: B)
  (HM: emptyEquiv_Hyb G |= (w, nil) |- M ::: A),
  G |= (w, Gamma) |- [M//fte v] N ::: B.
intros; eapply subst_t_Hyb_preserv_types with (Gamma := (v, A) :: Gamma); eauto.
Qed.

Lemma subst_t_Hyb_preserv_types_outer:
forall G0 G G' G'' w w' Gamma Gamma' A B M N v
  (H_lc_t: lc_t_Hyb M)
  (H_lc_w: lc_w_Hyb M)
  (G0G: G ~=~ (G0 & (w', (v, A) :: Gamma')))
  (G0G': G' ~=~ (G0 & (w, Gamma)))
  (G0G'': G'' ~=~ (G0 & (w', Gamma')))
  (HM: emptyEquiv_Hyb G' |= (w', nil) |- M ::: A)
  (HT: G |= (w, Gamma) |- N ::: B),
  G'' |= (w, Gamma) |- [M // fte v] N ::: B.
intros; eapply subst_t_Hyb_preserv_types; eauto.
Qed.

(*
Proof: induction on typing
  * for terms with world change: we again have to check whether the
  world which we will switch into is one of those in renaming
*)
Lemma rename_w_Hyb_preserv_types:
forall G w Gamma A M G' w' Gamma'
  (HT: G |= (w, Gamma) |- M ::: A),
  (* "new" substitution *)
  ( G ~=~ (G' & (w', Gamma')) ->
    G' |= (w, Gamma ++ Gamma') |- {{ fwo w // fwo w' }} M ::: A) /\
  (* "old" substitution *)
  ( G ~=~ (G' & (w', Gamma')) ->
    G' |= (w', Gamma' ++ Gamma) |- {{ fwo w' // fwo w }} M ::: A) /\
  (* "outer" substitution *)
  (forall G0 w'' Gamma'',
    G ~=~ (G0 & (w', Gamma') & (w'', Gamma'')) ->
    G' ~=~ (G0 & (w', Gamma' ++ Gamma'')) ->
    G' |= (w, Gamma) |- {{ fwo w' // fwo w''}} M ::: A).
intros;
remember (w, Gamma) as Ctx;
generalize dependent Gamma;
generalize dependent w;
generalize dependent w';
generalize dependent Gamma';
generalize dependent G';
induction HT; repeat split; intros;
inversion HeqCtx; subst;
simpl in *.

(* hyp *)
constructor;
[ rewrite H in Ok_Bg  |
  rewrite Mem_app_or_eq; left ]; auto;
eapply ok_Bg_Hyb_split2; eauto.
constructor;
[ rewrite H in Ok_Bg |
  rewrite Mem_app_or_eq; right ]; auto;
eapply ok_Bg_Hyb_split2; eauto.
constructor;
[ rewrite H in Ok_Bg; rewrite H0 | ]; auto;
eapply ok_Bg_Hyb_split3; eauto.

(* lam *)
apply t_lam_Hyb with (L := L);
[ rewrite H0 in Ok_Bg; apply ok_Bg_Hyb_split2 with (w:=w'); eauto |
  intros; unfold open_t_Hyb in *];
rewrite subst_Hyb_order_irrelevant_free; simpl; auto;
apply H with (v':=v') (G':=G') (Gamma := (v',A)::Gamma0); auto.
apply t_lam_Hyb with (L := L).
rewrite H0 in Ok_Bg; apply ok_Bg_Hyb_split2 with (w:=w0); eauto.
intros; unfold open_t_Hyb in *;
rewrite subst_Hyb_order_irrelevant_free;
destruct H with (v':=v') (G':=G') (Gamma':=Gamma')
(w':=w')(w:=w0) (Gamma:=(v',A)::Gamma0); eauto; destruct H3;
[ apply ContextPermutImpl_Hyb with (Gamma := (Gamma' ++ (v', A) :: Gamma0));
  [permut_simpl | ] | simpl; apply notin_empty ]; eauto.

apply t_lam_Hyb with (L := L);
[ rewrite H0 in Ok_Bg |
  intros];
rewrite H1; try eapply ok_Bg_Hyb_split3; eauto;
unfold open_t_Hyb in *;
rewrite subst_Hyb_order_irrelevant_free;
destruct H with (v':=v') (G':=G0 & (w', Gamma'++Gamma'')) (Gamma':=Gamma')
(w':=w')(w:=w0) (Gamma:=(v',A)::Gamma0); eauto. destruct H4.
apply H5 with (G1:=G0) (Gamma''0:=Gamma''); eauto.
simpl; apply notin_empty.

(* appl *)
apply t_appl_Hyb with (A:=A);
[ rewrite H in Ok_Bg |
  apply IHHT1 with (Gamma:=Gamma0) |
  apply IHHT2 with (Gamma:=Gamma0) ];
eauto; eapply ok_Bg_Hyb_split2; eauto.
apply t_appl_Hyb with (A:=A);
[ rewrite H in Ok_Bg |
  apply IHHT1 with (Gamma:=Gamma0) |
  apply IHHT2 with (Gamma:=Gamma0) ];
eauto; eapply ok_Bg_Hyb_split2; eauto.
apply t_appl_Hyb with (A:=A);
[ rewrite H in Ok_Bg; rewrite H0 |
  eapply IHHT1 |
  eapply IHHT2 ]; eauto;
eapply ok_Bg_Hyb_split3; eauto.

(* box *)
apply t_box_Hyb with (L:=\{w'} \u L);
[ rewrite H0 in Ok_Bg; apply ok_Bg_Hyb_split4 with (w:=w'); eauto |
  intros];
unfold open_w_Hyb in *; rewrite notin_union in H1; destruct H1;
rewrite notin_singleton in *; rewrite <- subst_w_Hyb_comm; auto.
destruct H with (w':=w'0) (G':=G' & (w0, Gamma0++Gamma')) (Gamma':=Gamma0)
                          (w'0:=w0) (w:=w'0)
                          (Gamma:=(@nil (var * ty))); auto.
destruct H4. eapply H5; eauto; PPermut_Hyb_simpl.
apply t_box_Hyb with (L:=\{w0} \u L);
[ rewrite H0 in Ok_Bg; apply ok_Bg_Hyb_split4 with (w:=w0);
  apply ok_Bg_Hyb_ppermut with (G:=G' & (w', Gamma') & (w0, Gamma0)); auto |
  intros]; try PPermut_Hyb_simpl;
unfold open_w_Hyb in *; rewrite notin_union in H1; destruct H1;
rewrite notin_singleton in *; rewrite <- subst_w_Hyb_comm; auto;
eapply H; eauto.
apply t_box_Hyb with (L:=\{w''} \u L);
[ rewrite H0 in Ok_Bg; rewrite H1; eapply ok_Bg_Hyb_split6; eauto |
  intros];
unfold open_w_Hyb in *;
rewrite notin_union in H2; destruct H2;
rewrite notin_singleton in *;
rewrite <- subst_w_Hyb_comm; auto;
eapply H with (G0:=G0 & (w0, Gamma0)) (Gamma':=Gamma') (Gamma'':=Gamma''); auto;
try PPermut_Hyb_simpl; rewrite H0; PPermut_Hyb_simpl.

(* unbox *)
case_if.
inversion H0; subst; rewrite H in Ok_Bg;
apply ok_Bg_Hyb_first_last_neq in Ok_Bg; elim Ok_Bg; auto.
constructor; [rewrite H in Ok_Bg | apply IHHT with (Gamma:=Gamma0)]; eauto;
eapply ok_Bg_Hyb_split2; eauto.

case_if; constructor;
[ rewrite H in Ok_Bg |
  apply IHHT with (Gamma:=Gamma0) ]; eauto;
eapply ok_Bg_Hyb_split2; eauto.

case_if.
inversion H1; subst; rewrite H in Ok_Bg;
apply ok_Bg_Hyb_first_last_neq in Ok_Bg; elim Ok_Bg; auto.
constructor; [rewrite H0; rewrite H in Ok_Bg | eapply IHHT]; eauto;
eapply ok_Bg_Hyb_split3; eauto.

(* unbox_fetch *)
case_if.
inversion H1; subst;
assert (G ~=~ G'0 /\ Gamma *=* Gamma'0) as HP by
  (apply ok_Bg_Hyb_impl_ppermut with (w:=w'0);
   [eauto | rewrite H; rewrite H0; auto]);
destruct HP; constructor.
rewrite <- H2; apply ok_Bg_Hyb_split2 with (w:=w'0);
eapply ok_Bg_Hyb_permut; eauto.
apply ContextPermutImpl_Hyb with (Gamma:=Gamma0 ++ Gamma);
[ permut_simpl |
  apply IHHT] ; auto.
assert (G'0 & (w'0, Gamma'0) ~=~ G & (w, Gamma)) by
  (symmetry; transitivity G'; auto);
assert (exists Gamma'', exists GH, exists GT,
  Gamma'' *=* Gamma /\ G'0 = GH & (w, Gamma'') ++ GT) as Split by
  (eapply PPermut_Hyb_split_neq; eauto; right; intro; subst;
    elim H1; reflexivity);
destruct Split as (Gamma'', (GH, Split)); destruct Split as (GT, H3);
destruct H3 as (H3a, H3b).
apply t_unbox_fetch_Hyb with (G:=GH++GT) (Gamma:=Gamma).
assert ((w, Gamma) :: G & (w0, Gamma0) ~=~ G & (w, Gamma) & (w0, Gamma0)) by
  auto.
rewrite H3 in Ok_Bg; rewrite <- H2 in Ok_Bg; rew_app in *;
assert (GH & (w, Gamma) ++ GT ~=~ (w, Gamma) :: GH ++ GT)
  by (PPermut_Hyb_simpl);
apply ok_Bg_Hyb_ppermut with
  (G:= (GH & (w, Gamma) ++ GT) & (w0, Gamma0 ++ Gamma'0));
[ rewrite H4 |
  apply ok_Bg_Hyb_split4 with (w:=w'0)]; rew_app; auto.
subst; rew_app in *;
apply ok_Bg_Hyb_ppermut with
  (G:=(GH ++ (w, Gamma'') :: GT ++ (w'0, Gamma'0) :: (w0, Gamma0) :: nil));
try PPermut_Hyb_simpl; auto.
eapply IHHT with (w1:=w) (Gamma1:=Gamma); auto; subst; symmetry;
PPermut_Hyb_simpl;
apply PPermut_Hyb_last_rev_simpl with (a:=(w, Gamma)); rew_app in *; auto;
rew_app; auto; rewrite <- H2; PPermut_Hyb_simpl.
apply PPermut_Hyb_last_rev_simpl with (a:=(w, Gamma)); rew_app in *;
auto; subst; PPermut_Hyb_simpl.

case_if;
[ inversion H1; subst; apply ok_Bg_Hyb_first_last_neq in Ok_Bg;
  elim Ok_Bg; auto | destruct (eq_var_dec w w'0)].
subst; assert (G ~=~ G'0 /\ Gamma *=* Gamma'0) by
  (apply ok_Bg_Hyb_impl_ppermut with (w:=w'0); [ | rewrite <- H0]; eauto);
destruct H2; constructor.
rewrite <- H2; apply ok_Bg_Hyb_permut with (Ctx := (Gamma ++ Gamma0)); eauto;
eapply ok_Bg_Hyb_split2; eauto.
apply ContextPermutImpl_Hyb with (Gamma:=Gamma ++ Gamma0);
[ permut_simpl |
  eapply IHHT with (w:=w'0) (Gamma1:=Gamma) (Gamma':=Gamma0)] ; auto.
assert (G'0 & (w'0, Gamma'0) ~=~ G & (w, Gamma)) by
  (symmetry; transitivity G'; auto);
assert (exists Gamma'', exists GH, exists GT,
  Gamma'' *=* Gamma /\ G'0 = GH & (w, Gamma'') ++ GT) as Split by
  (eapply PPermut_Hyb_split_neq; eauto; right; intro; subst;
    elim H1; reflexivity);
destruct Split as (Gamma'', (GH, Split));
destruct Split as (GT, (Ha, Hb)); subst;
apply t_unbox_fetch_Hyb with (G:=GH++GT) (Gamma:=Gamma).
assert (GH & (w, Gamma) ++ GT ~=~ (w, Gamma) :: GH ++ GT)
  by PPermut_Hyb_simpl;
apply ok_Bg_Hyb_ppermut with
  (G:= (GH & (w, Gamma'') ++ GT) & (w'0, Gamma0 ++ Gamma'0));
[ PPermut_Hyb_simpl | apply ok_Bg_Hyb_split4 with (w:=w0)]; rew_app; auto.
assert ((w, Gamma) :: G & (w0, Gamma0) ~=~
  (G & (w, Gamma)) & (w0, Gamma0)) by auto;
rewrite H4 in Ok_Bg; rewrite <- H2 in Ok_Bg; rew_app in *;
remember (GH ++ (w, Gamma'') :: GT) as GHT;
assert (GH ++ (w, Gamma'') :: GT ++ (w0, Gamma'0) :: (w'0, Gamma0) :: nil ~=~
  GHT & (w0, Gamma'0) & (w'0, Gamma0)) by (subst; rew_app; auto).
rewrite H5; apply ok_Bg_Hyb_swap_worlds; subst; rew_app in *; auto.
eapply IHHT; auto; PPermut_Hyb_simpl.
apply PPermut_Hyb_last_rev_simpl with (a:=(w, Gamma)); rew_app in *;
rewrite H; rewrite H0; PPermut_Hyb_simpl.
transitivity (GH & (w, Gamma) ++ GT); PPermut_Hyb_simpl.

case_if.
inversion H2; subst;
assert (G ~=~ G0 & (w'0, Gamma'0) /\ Gamma *=* Gamma'') by
  (apply ok_Bg_Hyb_impl_ppermut with (w:=w''); [ | rewrite H; rewrite H0];
    eauto);
destruct H3; apply t_unbox_fetch_Hyb with (G:=G0) (Gamma := Gamma'0 ++ Gamma);
[ rewrite H3 in Ok_Bg | apply IHHT | rewrite H1]; eauto.
apply ok_Bg_Hyb_split9 with (w':=w'');
apply ok_Bg_Hyb_ppermut with (G:= (w'', Gamma)::G0 & (w'0, Gamma'0) &
  (w0, Gamma0));
eauto; PPermut_Hyb_simpl.
rewrite H3; PPermut_Hyb_simpl.
destruct (eq_var_dec w w'0).
subst; assert (G ~=~ G0 & (w'', Gamma'') /\ Gamma *=* Gamma'0) by
  (apply ok_Bg_Hyb_impl_ppermut with (w:=w'0); [ | rewrite H; rewrite H0];
   eauto; PPermut_Hyb_simpl);
destruct H3;
apply t_unbox_fetch_Hyb with (G:=G0) (Gamma := Gamma ++ Gamma'');
[ rewrite H3 in Ok_Bg |
  eapply IHHT with (G':=G0 & (w0, Gamma0)) (Gamma' := Gamma'') |
  rewrite H1]; eauto.
eapply ok_Bg_Hyb_split9; eauto.
rewrite H3; PPermut_Hyb_simpl.
assert (G0 & (w'0, Gamma'0) & (w'', Gamma'')  ~=~ G & (w, Gamma)) by
  (symmetry; transitivity G'; auto);
assert (exists Gamma'', exists GH, exists GT,
  Gamma'' *=* Gamma /\ G0 & (w'0, Gamma'0) = GH & (w, Gamma'') ++ GT)
  as Split.
apply PPermut_Hyb_split_neq with (w:=w'')
  (Gamma:=Gamma'') (G':= G); auto; right; intro; subst; elim H2; auto.
assert (exists Gamma'', exists GH, exists GT,
  Gamma'' *=* Gamma /\ G0 = GH & (w, Gamma'') ++ GT) as Split' by
  (destruct Split as (Gamma''', (GH, Split));
    destruct Split as (GT, (Ha, Hb));
   apply PPermut_Hyb_split_neq with (w:=w'0) (Gamma:=Gamma'0) (G':=GH ++ GT);
   [ rew_app; transitivity (GH & (w, Gamma) ++ GT) |
     right; intro; subst; elim n]; auto; rewrite Hb; auto);
destruct Split' as (Gamma''',(GH, Split'));
destruct Split' as (GT, (Ha, Hb));
apply t_unbox_fetch_Hyb with (G:=GH++GT & (w'0, Gamma'0++Gamma''))
  (Gamma:=Gamma).
apply ok_Bg_Hyb_ppermut with (G':=(G' & (w0, Gamma0))) in Ok_Bg;
[ | rewrite <- H; auto]; rewrite H0 in Ok_Bg; subst G0.
apply ok_Bg_Hyb_ppermut with
  (G:= (GH & (w, Gamma''') ++ GT) & (w'0, Gamma'0 ++ Gamma'') & (w0, Gamma0));
[ rew_app | ]; auto; try PPermut_Hyb_simpl; eapply ok_Bg_Hyb_split6; eauto.
eapply IHHT with (w1:=w) (Gamma1:=Gamma) (G0:=GH++GT & (w0,Gamma0))
  (Gamma':=Gamma'0) (Gamma'':=Gamma''); auto.
PPermut_Hyb_simpl. apply PPermut_Hyb_last_rev_simpl with (a:=(w, Gamma));
rewrite <- H3; subst; PPermut_Hyb_simpl.
PPermut_Hyb_simpl.
rewrite H1; subst; PPermut_Hyb_simpl.
Qed.

Lemma rename_w_Hyb_preserv_types_new:
forall G w Gamma A M G' w' Gamma'
  (HT: G |= (w, Gamma) |- M ::: A)
  (GG': PPermut_Hyb G (G' & (w', Gamma'))),
  G' |= (w, Gamma ++ Gamma') |- {{ fwo w // fwo w' }} M ::: A.
intros; apply rename_w_Hyb_preserv_types with (G := G) (w := w) (w':= w');
eauto.
Qed.

Lemma rename_w_Hyb_preserv_types_old:
forall G w Gamma A M G' w' Gamma'
  (HT: G |= (w, Gamma) |- M ::: A)
  (GG': PPermut_Hyb G (G' & (w', Gamma'))),
  G' |= (w', Gamma' ++ Gamma) |- {{ fwo w' // fwo w }} M ::: A.
intros; apply rename_w_Hyb_preserv_types with (G := G) (w := w) (w':= w');
eauto.
Qed.

Lemma rename_w_Hyb_preserv_types_outer:
forall G G0 w Gamma A M G' w' Gamma' w'' Gamma''
  (HT: G |= (w, Gamma) |- M ::: A)
  (GG: PPermut_Hyb G (G0 & (w', Gamma') & (w'', Gamma'')))
  (GG': PPermut_Hyb G' (G0 & (w', Gamma' ++ Gamma''))),
  G' |= (w, Gamma) |- {{ fwo w' // fwo w'' }} M ::: A.
intros; eapply rename_w_Hyb_preserv_types; eauto.
Qed.

(*
Proof sketch: double induction: on term and on typing
  * for hypothesis, it is not possible to type it in empty context
  * for cases where M is already a value, there is no problem
  * otherwise we know, that for a simple term the theorem was true,
  so we do case analysis to obtain the step
  * the only exception is here M, where we know it is a value when
  M was also a value
*)
Lemma Progress_Hyb:
forall G w M A
  (H_lc_w: lc_w_Hyb M)
  (H_lc_t: lc_t_Hyb M)
  (HT: emptyEquiv_Hyb G |= (w, nil) |- M ::: A),
  value_Hyb M \/ exists N, (M, fwo w) |-> (N, fwo w).
intros;
remember (w, (@nil ty)) as Ctx;
generalize dependent Ctx;
generalize dependent A;
generalize dependent w;
generalize dependent G;
induction M; intros; eauto using value_Hyb;
inversion HeqCtx; subst.
(* hyp *)
inversion HT; subst;
rewrite Mem_nil_eq in HT0;
contradiction.
(* appl *)
right; inversion HT; subst;
inversion H_lc_t; subst;
inversion H_lc_w; subst;
edestruct IHM1 with (A := A0 ---> A); eauto;
[ inversion H0; subst; inversion HT1; subst; inversion H3 |
  inversion H0];
eexists; constructor; eauto;
inversion H5; subst; auto.
(* unbox & unbox_fetch *)
right; inversion HT; subst;
inversion H_lc_w; subst;
inversion H_lc_t; subst.
(* unbox *)
edestruct IHM with (A := [*]A); eauto;
[ inversion H0; subst; inversion HT0; subst; inversion H3 |
  destruct H0];
eexists; constructor; eauto;
inversion H1; inversion H2; subst; auto;
erewrite closed_var_subst_ctx; eauto; constructor.
(* unbox_fetch *)
assert (Gamma = nil) by
  ( apply emptyEquiv_Hyb_permut_empty with
    (G:= (G0 & (w0, Gamma))) (G':=G) (w:=w0); auto;
    apply Mem_last); subst;
destruct IHM with (A := [*]A)
                  (Ctx := (w0, (@nil ty)))
                  (G := G0 & (w, nil))
                  (w := w0);
eauto.
assert (emptyEquiv_Hyb (G0 & (w, nil)) = G0 & (w, nil)) by
  ( repeat rewrite emptyEquiv_Hyb_rewrite; simpl;
   apply emptyEquiv_Hyb_permut_split_last in H6; rewrite H6; reflexivity);
rewrite H0; auto.
inversion H0; subst; inversion HT0; subst;
eexists; constructor; eauto; inversion H2; auto; subst.
inversion H3; subst; auto.
destruct H0; eexists; constructor; eauto.
Qed.

(*
   Proof sketch: double induction on typing and making a step
   * FIXME: eauto takes ages :(
   * for beta reduction we take a fresh variable and expand the
   substitution a little bit, then apply the previously proven lemma
   that substitution preserves types
   * for unbox box reduction, the schema is basically the same
   * for letdia here we combine the two above + use the knowledge
   that term and world substitution can be done in any order
*)
Lemma Preservation_Hyb:
forall G M N A w
  (HT: emptyEquiv_Hyb G |= (w, nil) |- M ::: A)
  (HS: (M, fwo w) |-> (N, fwo w)),
  emptyEquiv_Hyb G |= (w, nil) |- N ::: A.
intros;
remember (w, (@nil (var * ty))) as Ctx;
remember (emptyEquiv_Hyb G) as G';
generalize dependent w;
generalize dependent N;
generalize dependent G;
induction HT; intros;
inversion HS; subst;
try (inversion HeqCtx; subst);
try (econstructor; eauto).
(* appl_lam *)
inversion HT1; subst;
unfold open_t_Hyb in *;
assert (exists v, v \notin L \u free_vars_Hyb M0) as HF by apply Fresh;
destruct HF as (v_fresh).
rewrite subst_t_Hyb_neutral_free with (v:=v_fresh);
[ eapply subst_t_Hyb_preserv_types_inner; eauto |
  rewrite notin_union in H; destruct H]; auto.
rewrite <- double_emptyEquiv_Hyb; auto.
(* unbox_box *)
inversion HT; subst;
assert (exists v, v \notin L \u (free_worlds_Hyb M0)) as HF by apply Fresh;
destruct HF as (w_fresh);
unfold open_w_Hyb in *;
replace ({{fwo w0 // bwo 0}}M0)
  with ({{fwo w0 // fwo w_fresh}} {{fwo w_fresh // bwo 0}}M0)
  by (rewrite subst_w_Hyb_neutral_free; auto);
replace (@nil (var * ty)) with (nil ++ (@nil (var * ty))); eauto;
apply rename_w_Hyb_preserv_types_old with (G := emptyEquiv_Hyb G0 & (w0, nil));
auto.
(* unbox_fetch_box *)
inversion HT; subst;
assert (exists v, v \notin L \u (free_worlds_Hyb M0)) as HF by apply Fresh;
destruct HF as (w_fresh);
unfold open_w_Hyb in *;
replace ({{fwo w0 // bwo 0}}M0)
  with ({{fwo w0 // fwo w_fresh}} {{fwo w_fresh // bwo 0}}M0)
  by (rewrite subst_w_Hyb_neutral_free; auto);
replace (@nil (var * ty)) with (nil ++ (@nil (var * ty))); eauto;
apply rename_w_Hyb_preserv_types_old with (G := G & (w0, nil) & (w, Gamma));
auto; PPermut_Hyb_simpl.
(* unbox_fetch *)
assert (Gamma = nil) by
  ( apply emptyEquiv_Hyb_permut_empty with (G:= (G & (w, Gamma))) (G':=G0)
    (w:=w);
    auto; apply Mem_last); subst;
eapply IHHT with (G0:=G & (w0, nil)); eauto;
repeat rewrite emptyEquiv_Hyb_rewrite; simpl;
apply emptyEquiv_Hyb_permut_split_last in H; rewrite H; reflexivity.
Qed.

Lemma lc_t_step_Hyb:
forall M N w,
  lc_t_Hyb M ->
  (M, w) |-> (N, w) ->
  lc_t_Hyb N.
induction M; intros; inversion H0; subst.
apply lc_t_subst_Hyb; auto.
constructor; eauto. apply IHM1 with w; auto.
apply lc_t_subst_w_Hyb; auto.
constructor; apply IHM with v; auto.
Qed.

Lemma lc_w_step_Hyb:
forall M M' w,
  lc_w_Hyb M ->
  step_Hyb (M, fwo w) (M', fwo w) ->
  lc_w_Hyb M'.
induction M; intros; inversion H0; subst.
apply lc_w_subst_t_Hyb; auto.
constructor; eauto. apply IHM1 with w; auto.
apply lc_w_subst_Hyb; auto.
inversion H; subst; try omega; constructor; apply IHM with w0; auto.
Qed.

Lemma value_no_step:
forall M,
  value_Hyb M ->
  forall N w, (M,  w) |-> (N, w) ->
             False.
induction M; intros;
try inversion H; subst;
inversion H0; subst;
rewrite IHM; eauto.
Qed.


Lemma types_Hyb_lc_w_Hyb:
forall G Gamma M A w,
  G |= (w, Gamma) |- M ::: A -> lc_w_Hyb M.
intros; induction H; constructor; try apply IHHT;
unfold open_w_Hyb in *; unfold open_t_Hyb in *;
auto.
assert (exists x, x \notin L) by apply Fresh; destruct H0;
specialize H with x; apply H in H0; apply lc_w_n_Hyb_subst_t in H0; auto.
assert (exists x, x \notin L) by apply Fresh; destruct H0;
specialize H with x; apply H in H0; apply lc_w_n_Hyb_subst_w in H0; auto.
Qed.

Lemma types_Hyb_lc_t_Hyb:
forall G Gamma M A w,
  G |= (w, Gamma) |- M ::: A -> lc_t_Hyb M.
intros; induction H; constructor; try apply IHHT;
unfold open_w_Hyb in *; unfold open_t_Hyb in *;
auto.
assert (exists x, x \notin L) by apply Fresh; destruct H0;
specialize H with x; apply H in H0;
apply lc_t_n_Hyb_subst_t in H0; auto; constructor.
assert (exists x, x \notin L) by apply Fresh; destruct H0;
specialize H with x; apply H in H0;
apply lc_t_n_Hyb_subst_w in H0; auto; constructor.
Qed.


Close Scope hybrid_is5_scope.
Close Scope is5_scope.
Close Scope permut_scope.
