Add LoadPath "..".
Require Import Hyb_Substitution.
Require Import Setoid.
Require Import LibList.
Require Import PermutLib.
Require Import Hyb_PPermutLib.
Require Import Hyb_OkLib.
Require Import Hyb_EmptyEquivLib.

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

| t_here_Hyb: forall A G w Gamma M
  (Ok_Bg: ok_Bg_Hyb ((w, Gamma) :: G))
  (HT: G |= (w, Gamma) |- M ::: A),
  G |= (w, Gamma) |- get_here_Hyb (fwo w) M ::: <*> A

| t_get_here_Hyb: forall A G w Gamma w' Gamma' M
  (Ok_Bg: ok_Bg_Hyb ((w, Gamma) :: G & (w', Gamma')))
  (HT: G & (w', Gamma') |= (w, Gamma) |- M ::: A),
  forall G', (G & (w, Gamma)) ~=~ G' ->
    G' |= (w', Gamma') |- get_here_Hyb (fwo w) M ::: <*> A

| t_letdia_Hyb: forall L_w L_t A B G w Gamma M N
  (Ok_Bg: ok_Bg_Hyb ((w, Gamma) :: G))
  (HT1: G |= (w, Gamma) |- M ::: <*> A)
  (HT2: forall v', v' \notin L_t -> forall w', w' \notin L_w ->
    (w', (v', A) :: nil) :: G |=
      (w, Gamma) |- (N ^w^ (fwo w')) ^t^ (hyp_Hyb (fte v')) ::: B),
  G |= (w, Gamma) |- letdia_get_Hyb (fwo w) M N ::: B

| t_letdia_get_Hyb: forall L_w L_t A B G w (Gamma: list (prod var ty)) Ctx' M N
  (Ok_Bg: ok_Bg_Hyb ((w, Gamma) :: G & Ctx'))
  (HT1: G & Ctx' |= (w, Gamma) |- M ::: <*> A)
  (HT2: forall v', v' \notin L_t -> forall w', w' \notin L_w ->
    (w', ((v', A) :: nil)) :: G & (w, Gamma) |=
      Ctx' |- (N ^w^ (fwo w')) ^t^ (hyp_Hyb (fte v')) ::: B),
  forall G0, (G & (w, Gamma)) ~=~ G0 ->
    G0 |= Ctx' |- letdia_get_Hyb (fwo w) M N ::: B

where " G '|=' Ctx '|-' M ':::' A " := (types_Hyb G Ctx M A)
  : hybrid_is5_scope.


(*** Definitions ::: Dynamics ***)


Inductive value_Hyb: te_Hyb -> Prop :=
| val_lam_Hyb: forall A M, value_Hyb (lam_Hyb A M)
| val_box_Hyb: forall M, value_Hyb (box_Hyb M)
| val_get_here_Hyb: forall M Ctx, value_Hyb M -> value_Hyb (get_here_Hyb Ctx M)
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

| red_letdia_get_get_here_Hyb: forall ctx ctx' ctx'' M N,
  lc_w_Hyb M -> lc_t_Hyb M ->
  lc_w_n_Hyb 1 N ->
  lc_t_n_Hyb 1 N -> value_Hyb M ->
  (letdia_get_Hyb ctx' (get_here_Hyb ctx'' M) N, ctx) |->
    ((N ^w^ ctx'') ^t^ M, ctx)

| red_appl_Hyb: forall ctx M N M'
  (HT: (M, ctx) |-> (M', ctx)),
  lc_w_Hyb M -> lc_t_Hyb M ->
  lc_w_Hyb N -> lc_t_Hyb N ->
  (appl_Hyb M N, ctx) |-> (appl_Hyb M' N, ctx)

| red_unbox_fetch_Hyb: forall ctx' M M' ctx
  (HT: (M, ctx') |-> (M', ctx')),
  lc_w_Hyb M -> lc_t_Hyb M ->
  (unbox_fetch_Hyb ctx' M, ctx) |-> (unbox_fetch_Hyb ctx' M', ctx)

| red_get_here_Hyb: forall ctx ctx' M M'
  (HT: (M, ctx) |-> (M', ctx)),
  lc_w_Hyb M -> lc_t_Hyb M ->
  (get_here_Hyb ctx M, ctx') |-> (get_here_Hyb ctx M', ctx')

| red_letdia_get_Hyb: forall ctx ctx' M N M'
  (HT: (M, ctx) |-> (M', ctx)),
  lc_w_Hyb M -> lc_t_Hyb M ->
  lc_w_n_Hyb 1 N ->
  lc_t_n_Hyb 1 N ->
  (letdia_get_Hyb ctx M N, ctx') |-> (letdia_get_Hyb ctx M' N, ctx')

where " M |-> N " := (step_Hyb M N ) : hybrid_is5_scope.


Inductive steps_Hyb : te_Hyb * vwo -> te_Hyb * vwo -> Prop :=
| single_step_Hyb: forall M M' w, (M, w) |-> (M', w) -> steps_Hyb (M, w) (M', w)
| multi_step_Hyb: forall M M' M'' w,
  (M, w) |-> (M', w) -> steps_Hyb (M', w) (M'', w)
  -> steps_Hyb (M, w) (M'', w)
.

Notation " M |->+ N " := (steps_Hyb M N) (at level 70) : hybrid_is5_scope.


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
(* here *)
constructor; auto.
(* get_here *)
destruct HSubst as [GT];
apply t_get_here_Hyb with (Gamma:=Gamma) (G:=G++GT).
apply ok_Bg_Hyb_ppermut with (G:=(w', Gamma')::G'0);
  [rewrite <- H0; rewrite <- H; rew_app | ]; auto.
apply IHHT; [exists GT | ]; auto; try PPermut_Hyb_simpl;
  apply ok_Bg_Hyb_ppermut with (G:=(w', Gamma')::G'0); auto;
  rewrite <- H0; rewrite <- H; rew_app; auto.
rewrite <- H0; rewrite <- H; rew_app; auto.
(* letdia *)
apply t_letdia_Hyb with (A:=A) (L_t:=L_t \u used_t_vars_Hyb ((w, Gamma) :: G'))
  (L_w:=L_w \u used_w_vars_Hyb ((w, Gamma)::G'));
[  | | intros; apply H]; auto;
destruct HSubst as [GT];
[ exists GT; rew_app; auto |
  rewrite notin_union in *; destruct H1; destruct H0];
apply ok_Bg_Hyb_ppermut with (G:= (w', (v', A) :: nil ) :: (w, Gamma) :: G');
[ | apply ok_Bg_Hyb_fresh_wo_te]; auto.
(* letdia_get *)
destruct HSubst as [GT];
apply t_letdia_get_Hyb with (A:=A) (Gamma:=Gamma) (G:=G++GT)
                           (L_t:=L_t \u used_t_vars_Hyb (Ctx'::G'))
                           (L_w:=L_w \u used_w_vars_Hyb (Ctx'::G')).
apply ok_Bg_Hyb_ppermut with (G:=Ctx' :: G');
  [rewrite <- H1; rewrite <- H0; rew_app | ]; auto.
apply IHHT.
  exists GT; rew_app; auto.
  apply ok_Bg_Hyb_ppermut with (G:=Ctx' :: G');
  [ rewrite <- H1; rewrite <- H0; rew_app | ]; auto.
  intros; apply H; auto.
  exists GT; rew_app; auto.
  apply ok_Bg_Hyb_ppermut with (G:=(w', (v', A) :: nil) :: Ctx' :: G'); auto;
  rewrite <- H1; rewrite <- H0;
  assert ((G & (w, Gamma) ++ GT)  ~=~ (G ++ GT) & (w, Gamma))
    by (symmetry; rew_app; auto);
  rewrite H4; destruct Ctx'; auto.
rewrite <- H1; rewrite <- H0; rew_app; auto.
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
(* here *)
econstructor; [ eapply ok_Bg_Hyb_permut | ]; eauto.
(* get_here *)
apply t_get_here_Hyb with (G:=G) (Gamma:=Gamma); auto.
apply ok_Bg_Hyb_ppermut with (G:=(w0, Gamma) :: G & (w, Gamma0)); auto.
assert (G & (w, Gamma'0) ~=~ (G & (w, Gamma0))) as H1 by auto;
rewrite H1; auto.
(* letdia *)
econstructor; [ eapply ok_Bg_Hyb_permut | | ]; eauto.
(* letdia_get *)
apply t_letdia_get_Hyb with (L_w:=L_w) (L_t:=L_t) (A:=A) (Gamma:=Gamma) (G:=G).
apply ok_Bg_Hyb_ppermut with (G:=(w0, Gamma) :: G & (w, Gamma0)); auto.
assert (G & (w, Gamma') ~=~ (G & (w, Gamma0))) as H2 by auto;
rewrite H2; auto.
intros; eapply H; eauto.
auto.
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
(* here *)
constructor; [ | apply IHHT with (w:=w0)(Gamma:=Gamma0)]; auto.
constructor; [ | apply IHHT]; auto.
(* get_here 1 *)
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
apply t_get_here_Hyb with (G:=G) (Gamma:=Gamma++Delta');
[rewrite <- H4 | apply IHHT | rewrite H3]; auto; rewrite <- H4; auto.
(* <> *)
assert (exists Gamma', exists G0, exists G1,
  Gamma' *=* Gamma /\ G'0 = G0 & (w, Gamma') ++ G1) as H2 by
  ( apply PPermut_Hyb_split_neq with (G':=G) (w:=w'0) (Gamma := Delta);
    [ symmetry; transitivity G' | ]; auto);
destruct H2 as (Gamma', (GH, (GT, (H2a, H2b)))); subst;
apply t_get_here_Hyb with
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
(* get_here 2 *)
apply t_get_here_Hyb with (G:=G) (Gamma:=Gamma);
rewrite <- H in H0; [ | apply IHHT with (w1:=w) (Gamma1:=Gamma) |]; auto.
(* letdia *)
apply t_letdia_Hyb with (A:=A)
  (L_w:=L_w \u used_w_vars_Hyb((w0, Gamma0) :: G' & (w', Delta ++ Delta')))
  (L_t:=L_t \u used_t_vars_Hyb ((w0, Gamma0) :: G' & (w', Delta ++ Delta')));
[ | apply IHHT with (w:=w0) (Gamma:=Gamma0) | ]; auto;
intros; destruct H with (v':=v') (w':=w'0) (w:=w0) (Gamma:=Gamma0); auto;
replace ((w'0, (v', A) :: nil) :: G' & (w', Delta ++ Delta')) with
   (((w'0, (v', A) :: nil) :: G') & (w', Delta ++ Delta')) by
   (rew_app; reflexivity);
apply H4; rew_app; auto;
apply ok_Bg_Hyb_ppermut with
  (G:=(w'0, (v', A) :: nil) :: (w0, Gamma0) :: G' & (w', Delta ++ Delta'));
auto.
eapply t_letdia_Hyb with (A:=A)
  (L_t := L_t \u used_t_vars_Hyb ((w0, Gamma0 ++ Gamma') :: G))
  (L_w := L_w \u used_w_vars_Hyb ((w0, Gamma0 ++ Gamma') :: G));
[ | apply IHHT | ]; auto;
intros; eapply H; auto;
apply ok_Bg_Hyb_ppermut with
  (G:=(w', (v', A) :: nil) :: (w0, Gamma0 ++ Gamma') :: G);
auto.
(* letdia_get 1 *)
destruct (permut_context_Hyb_dec (w', Delta) (w, Gamma)) as [Eq | Neq];
simpl in *.
(* = *)
destruct Eq; subst;
assert (G ~=~ G') by
  (apply PPermut_Hyb_last_rev with (w:=w) (Gamma:=Gamma) (Gamma':=Delta);
   [apply permut_sym | transitivity G0]; auto);
apply t_letdia_get_Hyb with (Gamma:=Gamma++Delta') (G:=G) (A:=A)
  (L_w:=L_w \u used_w_vars_Hyb ((w0, Gamma0) :: G' & (w, Gamma ++ Delta')))
  (L_t:=L_t \u used_t_vars_Hyb ((w0, Gamma0) :: G & (w, Gamma ++ Delta'))).
apply ok_Bg_Hyb_ppermut with (G:=(w0, Gamma0) :: G' & (w, Delta ++ Delta'));
[rewrite <- H4 | auto];
transitivity ((w, Delta ++ Delta') :: G & (w0, Gamma0)); auto.
apply IHHT; auto;
apply ok_Bg_Hyb_ppermut with (G:=(w0, Gamma0) :: G' & (w, Delta ++ Delta'));
[rewrite <- H4 | auto];
transitivity ((w, Delta ++ Delta') :: G & (w0, Gamma0)); auto.
intros; destruct H with (v':=v') (w':=w') (w1:=w0) (Gamma1:=Gamma0); eauto;
replace ( (w', (v', A) :: nil) :: G & (w, Gamma ++ Delta') ) with
  (( (w', (v', A) :: nil) :: G) & (w, Gamma ++ Delta')) by
  (rew_app; reflexivity);
eapply H7; auto;
apply ok_Bg_Hyb_ppermut with
  (G:=(w', (v', A) :: nil ) :: (w0, Gamma0) :: G & (w, Gamma ++ Delta'));
[ rew_app | rewrite H4]; auto;
apply ok_Bg_Hyb_fresh_wo_te;
[ apply ok_Bg_Hyb_ppermut
  with (G:=(w0, Gamma0) :: G' & (w, Delta ++ Delta')) | | ];
auto.
rewrite notin_union in *; destruct H5; auto;
rewrite <- H4; auto.
rewrite <- H4; auto.
(* <> *)
assert (exists Gamma', exists G0, exists G1,
  Gamma' *=* Gamma /\ G' = G0 & (w, Gamma') ++ G1) by
  ( apply PPermut_Hyb_split_neq with (G':=G) (w:=w') (Gamma := Delta);
    [ symmetry; transitivity G0 | ]; auto).
destruct H3 as (Gamma', (GH, (GT, (H3a, H3b)))); subst;
assert ((w0, Gamma0) :: (GH & (w, Gamma') ++ GT) & (w', Delta ++ Delta') ~=~
  (w0, Gamma0) :: (GH & (w, Gamma) ++ GT) & (w', Delta ++ Delta'))
by PPermut_Hyb_simpl;
assert (G ~=~ GH ++ GT & (w', Delta)) by
  ( apply PPermut_Hyb_last_rev_simpl with (a:=(w, Gamma));
    transitivity G0; auto; rewrite H1; PPermut_Hyb_simpl);
apply t_letdia_get_Hyb with
  (Gamma:=Gamma) (G:=GH ++ GT & (w', Delta ++ Delta'))
  (L_w:=L_w \u used_w_vars_Hyb ((w0, Gamma0) :: (GH & (w, Gamma) ++ GT) &
    (w', Delta ++ Delta')))
  (L_t:=L_t \u used_t_vars_Hyb ((w0, Gamma0) :: (GH & (w, Gamma) ++ GT) &
    (w', Delta ++ Delta')))(A:=A).
apply ok_Bg_Hyb_ppermut with
  (G:=(w0, Gamma0) :: (GH & (w, Gamma') ++ GT) & (w', Delta ++ Delta'));
rew_app in *; auto; try PPermut_Hyb_simpl.
apply PPermut_Hyb_bg with
  (G:= (GH ++ GT & (w0, Gamma0)) & (w', Delta ++ Delta'));
[ | rew_app]; auto;
apply IHHT with (w1:=w) (Gamma1:=Gamma); auto;
[ rewrite H4 | ]; rew_app; auto;
rew_app; apply ok_Bg_Hyb_ppermut with
  (G:=(w0, Gamma0) :: (GH & (w, Gamma') ++ GT) & (w', Delta ++ Delta')); auto;
rew_app; try PPermut_Hyb_simpl.
intros; destruct H with (v':=v')(w':=w'0) (w1:=w0) (Gamma1:=Gamma0); auto;
apply PPermut_Hyb_bg with
  (G:=((w'0, (v', A)::nil) :: GH++GT & (w, Gamma)) & (w', Delta ++ Delta'));
[ | rew_app]; auto;
apply H7; rew_app; [constructor | ]; auto;
[ rewrite H4; rew_app; auto | ];
apply ok_Bg_Hyb_ppermut with
  (G:= ((w'0, (v', A) :: nil) ::(w0, Gamma0) :: GH & (w, Gamma') ++ GT) &
    (w', Delta ++ Delta')); rew_app; auto;
[ transitivity (((w'0, (v', A) :: nil) ::(w0, Gamma0) :: GH ++GT & (w, Gamma))
  & (w', Delta ++ Delta')); rew_app |
 rew_app in *; apply ok_Bg_Hyb_fresh_wo_te]; auto; try PPermut_Hyb_simpl.
rewrite H3; auto.
rewrite H3; auto.
rew_app; PPermut_Hyb_simpl.
(* letdia_get 2 *)
apply t_letdia_get_Hyb with (G:=G) (Gamma:=Gamma) (A:=A)
  (L_w:=L_w \u used_w_vars_Hyb (((w0, Gamma0 ++ Gamma') :: G & (w, Gamma))))
  (L_t:=L_t \u used_t_vars_Hyb ((w0, Gamma0 ++ Gamma') :: G & (w, Gamma))).
rewrite <- H0 in H1; apply ok_Bg_Hyb_ppermut with
  (G:=(w0, Gamma0 ++ Gamma') :: G & (w, Gamma)); auto.
apply IHHT with (w1:=w) (Gamma1:=Gamma); auto.
rewrite <- H0 in H1; apply ok_Bg_Hyb_ppermut with
  (G:=(w0, Gamma0 ++ Gamma') :: G & (w, Gamma)); auto.
intros; destruct H with (v':=v')(w':=w') (w1:=w0)(Gamma1:=Gamma0); auto;
apply H5; apply ok_Bg_Hyb_ppermut with
  (G:= (w', (v', A)::nil) :: (w0, Gamma0 ++ Gamma') :: G & (w, Gamma));
[ | apply ok_Bg_Hyb_fresh_wo_te ]; auto; rewrite H0; auto.
assumption.
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

(* here *)
econstructor; [ | eapply IHHT];
try apply ok_Bg_Hyb_permut_first_tail with (C:=Gamma0) (x:=v) (A:=A0); eauto.

econstructor;
[ rewrite H1; rewrite H in Ok_Bg |
  eapply IHHT]; eauto with ok_bg_hyb_rew.

(* get_here *)
apply t_get_here_Hyb with (G:=G) (Gamma:=Gamma); auto;
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
apply t_get_here_Hyb with (G:=G) (Gamma:=Gamma'0);
eauto with ok_bg_hyb_rew;
specialize IHHT with (Gamma1:=Gamma) (w:=w'0);
destruct IHHT with (M0:=M0) (A0:=A0) (v:=v); auto;
[ apply H6; auto; rewrite H1 in H3; rewrite H4 |
  rewrite H4; symmetry]; auto.
(* <> *)
assert (exists Gamma', exists GH, exists GT,
  Gamma' *=* (v, A0)::Gamma'0 /\ G = GH & (w'0, Gamma') ++ GT) as HP by
  (apply PPermut_Hyb_split_neq with (w:=w) (Gamma:=Gamma) (G':=G0);
    eauto; transitivity G'; auto).
destruct HP as (Gamma', (GH, (GT, (HPa, HPb)))).
assert (GH & (w'0, Gamma') ++ GT ~=~ GH & (w'0, (v, A0)::Gamma'0) ++ GT)
  by PPermut_Hyb_simpl;
apply t_get_here_Hyb with (G:=GH ++ GT & (w'0, Gamma'0)) (Gamma:=Gamma).
subst;
apply ok_Bg_Hyb_ppermut with
  (G:= (((w, Gamma) :: (GH & (w0, Gamma0) ++ GT)) & (w'0, Gamma'0)));
[rew_app | ]; auto;
apply ok_Bg_Hyb_permut_no_last_spec with (v:=v)(A:=A0).
apply ok_Bg_Hyb_ppermut with
  (G:=(w, Gamma):: (GH & (w'0, Gamma') ++ GT) & (w0, Gamma0));
rew_app in *; auto; PPermut_Hyb_simpl.
eapply IHHT with (w1:=w) (Gamma1:=Gamma) (w':=w'0) (Gamma':=Gamma'0)
                 (G0:=GH ++ GT & (w0, Gamma0)) (A0:=A0); rew_app; auto; subst;
rew_app; auto;
rewrite H1 in H3;
assert (GH ++ (w, Gamma) :: GT ~=~ G0) by
  (apply PPermut_Hyb_last_rev_simpl with (a:=(w'0, (v, A0) :: Gamma'0));
  rew_app in *; rewrite <- H0; rewrite <- H; auto; PPermut_Hyb_simpl).
PPermut_Hyb_simpl; auto.
assert (GH ++ (w, Gamma) :: GT & (w0, Gamma0) ~=~ G0 & (w0,Gamma0)) by
  (rewrite <- H5; rew_app; auto; PPermut_Hyb_simpl);
rewrite H6; auto.
subst; rewrite H2; PPermut_Hyb_simpl.
apply PPermut_Hyb_last_rev with (w:=w'0) (Gamma:=Gamma')
  (Gamma':=(v,A0)::Gamma'0);
[ | symmetry]; auto; transitivity G'; auto; rewrite <- H; PPermut_Hyb_simpl.

(* letdia *)
apply t_letdia_Hyb with
  (L_t := L_t \u \{v})
  (L_w := L_w \u used_w_vars_Hyb ((w0, nil) :: emptyEquiv_Hyb G)) (A:=A);
[ apply ok_Bg_Hyb_permut_first_tail with (C:=Gamma0) (x:=v) (A:=A0) |
  eapply IHHT |
  intros]; eauto;
unfold open_t_Hyb in *; unfold open_w_Hyb in *;
rewrite notin_union in H2; rewrite notin_singleton in H2; destruct H2;
rewrite <- subst_Hyb_order_irrelevant_bound;
[ rewrite <- subst_t_Hyb_comm | assumption ];
[ eapply H | |] ; eauto;
apply BackgroundSubsetImpl_Hyb with (G:=emptyEquiv_Hyb G); auto;
[ exists ((w', (@nil (var*ty)))::nil);
  PPermut_Hyb_simpl ; rew_app; PPermut_Hyb_simpl | ].
assert ((w0, nil) :: (w', nil) :: emptyEquiv_Hyb G ~=~
  (w',nil) :: (w0, nil) :: emptyEquiv_Hyb G) by PPermut_Hyb_simpl;
rewrite H5; apply ok_Bg_Hyb_fresh_wo;
[ apply emptyEquiv_Hyb_ok_Bg_Hyb in Ok_Bg;  simpl in * | ]; auto.

eapply t_letdia_Hyb with
  (L_t := L_t \u \{v})
  (L_w := L_w \u  used_w_vars_Hyb ((w', nil) ::
    emptyEquiv_Hyb (G0 & (w0, Gamma0))));
[ rewrite H2; rewrite H0 in Ok_Bg | eapply IHHT | intros];
eauto with ok_bg_hyb_rew;
unfold open_t_Hyb in *; unfold open_w_Hyb in *.
rewrite notin_union in H4; rewrite notin_singleton in H4; destruct H4;
rewrite <- subst_Hyb_order_irrelevant_bound;
[ rewrite <- subst_t_Hyb_comm | assumption ];
[ eapply H with (G0:=(w'0, (v',A)::nil)::G0) (w'0:=w')
  (Gamma':=Gamma') (A0:=A0) | | ]; auto;
rew_app; rewrite H1 in H3; rew_app in *; simpl; try PPermut_Hyb_simpl;
apply BackgroundSubsetImpl_Hyb with (G:= emptyEquiv_Hyb (G0 & (w0, Gamma0)));
auto; [exists ((w'0, (@nil (var*ty))):: nil); PPermut_Hyb_simpl | ];
assert ((w'0, nil) :: (w', nil)::emptyEquiv_Hyb(G0 & (w0, Gamma0)) ~=~
  (w', nil) :: (w'0, nil) :: emptyEquiv_Hyb (G0 & (w0, Gamma0))) by auto;
rewrite <- H7; apply ok_Bg_Hyb_fresh_wo;
[rewrite H0 in Ok_Bg; apply emptyEquiv_Hyb_ok_Bg_Hyb in Ok_Bg | ]; auto;
  assert (emptyEquiv_Hyb((w', (v, A0) :: Gamma') :: G0 & (w0, Gamma0)) ~=~
    (w', nil) :: emptyEquiv_Hyb (G0 & (w0, Gamma0))) by (simpl; auto);
rewrite <- H8;
assert ((w0, Gamma0) :: G0 & (w', (v, A0) :: Gamma') ~=~
  ((w', (v, A0) :: Gamma') :: G0 & (w0, Gamma0))) by auto;
rewrite <- H9; auto.

(* letdia_get *)
assert (w <> w0) by
  (apply ok_Bg_Hyb_first_last_neq with (C:=Gamma) (C':=Gamma0) (G:=G); auto).
eapply t_letdia_get_Hyb with (G:=G) (Gamma:=Gamma) (L_t := L_t \u \{v}) (A:=A)
  (L_w:=L_w \u used_w_vars_Hyb ((w0, nil) :: emptyEquiv_Hyb (G & (w, Gamma))));
auto.
apply ok_Bg_Hyb_permut_no_last_spec with (v:=v) (A:=A0);
apply ok_Bg_Hyb_ppermut with (G:= (w, Gamma) :: G & (w0, Gamma0)); auto.
eapply IHHT with (w':=w0) (Gamma':=Gamma1) (v:=v) (A0:=A0); auto.
rew_app; rewrite <- H0 in H2; auto.
intros; unfold open_t_Hyb in *; unfold open_w_Hyb in *;
rewrite notin_union in H5; rewrite notin_singleton in H5; destruct H5;
rewrite <- subst_Hyb_order_irrelevant_bound;
[rewrite <- subst_t_Hyb_comm | ]; auto.
eapply H with (v:=v) (A0:=A0); auto.
rewrite <- H0 in H2;
apply BackgroundSubsetImpl_Hyb with (G:=emptyEquiv_Hyb (G & (w, Gamma))); auto;
[ exists ((w', (@ nil (var * ty)))::nil); PPermut_Hyb_simpl | ];
assert ((w0, nil) :: (w', nil) :: emptyEquiv_Hyb (G & (w, Gamma)) ~=~
  (w', nil) :: (w0, nil) ::emptyEquiv_Hyb (G & (w, Gamma)))
by PPermut_Hyb_simpl;
rewrite H8;
apply ok_Bg_Hyb_fresh_wo; [apply emptyEquiv_Hyb_ok_Bg_Hyb in Ok_Bg | auto];
assert ((w, Gamma) :: G & (w0, Gamma0) ~=~ (w0, Gamma0):: G & (w, Gamma)) by
  auto;
rewrite H9 in Ok_Bg; simpl in Ok_Bg; auto.

assert (w <> w0) by
  (apply ok_Bg_Hyb_first_last_neq with (C:=Gamma) (C':=Gamma0) (G:=G); auto).
destruct (eq_var_dec w w'); subst.
(* = *)
assert (G ~=~ G1 /\ Gamma *=* (v, A0) :: Gamma') by
  (apply ok_Bg_Hyb_impl_ppermut with (w:=w');
    [ | rewrite H0; rewrite <- H1]; eauto);
destruct H7; rewrite H3; rewrite <- H7;
apply t_letdia_get_Hyb with (G:=G) (Gamma:=Gamma') (L_t:=L_t \u \{v}) (A:=A)
  (L_w:=L_w \u used_w_vars_Hyb ((w', nil) ::
    emptyEquiv_Hyb (G1 & (w0, Gamma0)))).
eauto with ok_bg_hyb_rew.
eapply IHHT with (v:=v) (A0:=A0); auto;
rewrite H2 in H4; rewrite H7; auto.
intros; unfold open_t_Hyb in *; unfold open_w_Hyb in *;
rewrite notin_union in H9; rewrite notin_singleton in H9; destruct H9;
rewrite <- subst_Hyb_order_irrelevant_bound;
[ rewrite <- subst_t_Hyb_comm | ]; auto.
edestruct H with (v:=v) (w'0 := w'0) (Gamma1:=Gamma0) (A0:=A0)
  (v':=v') (M:=M0) as (Ha, Hb);
auto.
eapply Hb with (G0 := (w'0, (v',A)::nil) ::G) (w'1 := w') (Gamma':=Gamma');
[ | auto |  | ]; try PPermut_Hyb_simpl.
rewrite H2 in H4; rewrite H7.
apply BackgroundSubsetImpl_Hyb with (G:=emptyEquiv_Hyb (G1 & (w0, Gamma0)));
auto. exists (((w'0, (@nil (prod var ty))) :: nil)); rew_app; simpl; auto;
PPermut_Hyb_simpl.
assert ((w', nil) :: (w'0, nil) :: emptyEquiv_Hyb (G1 & (w0, Gamma0)) ~=~
  (w'0, nil) :: (w',nil) :: emptyEquiv_Hyb (G1 & (w0, Gamma0))) by auto;
rewrite H12; apply ok_Bg_Hyb_fresh_wo; auto;
assert ((w', nil) :: emptyEquiv_Hyb (G1 & (w0, Gamma0)) ~=~
  emptyEquiv_Hyb ((w', Gamma) :: G & (w0, Gamma0))) by
  (simpl in *; rewrite H7; auto);
rewrite H13; apply emptyEquiv_Hyb_ok_Bg_Hyb in Ok_Bg; auto.
auto.
(* <> *)
assert (G & (w, Gamma) ~=~ G1 & (w', (v, A0) :: Gamma')) by
  (transitivity G0; auto);
symmetry in H7;
assert (exists Gamma0, exists GH, exists GT,
  Gamma0 *=* Gamma /\ G1 = GH & (w, Gamma0) ++ GT) by
  (apply PPermut_Hyb_split_neq with (w:=w') (Gamma:=(v,A0) :: Gamma') (G':=G);
    auto);
destruct H8 as (Gamma'', (GH, H8)); destruct H8 as (GT, H8);
destruct H8.
apply t_letdia_get_Hyb with (G:=GH++GT & (w', Gamma')) (Gamma:=Gamma) (A:=A)
  (L_t:=L_t \u \{v}) (L_w:=L_w \u used_w_vars_Hyb
     ((w', nil) :: emptyEquiv_Hyb
       (GH ++ GT ++ (w, Gamma) :: (w0, Gamma0) :: nil))).
assert (G & (w, Gamma) & (w0, Gamma0) ~=~ (w, Gamma) :: G & (w0, Gamma0)) by
  auto.
rewrite <- H10 in Ok_Bg; rewrite <- H7 in Ok_Bg;
subst; apply ok_Bg_Hyb_ppermut with
  (G:=((w, Gamma) :: (GH & (w', Gamma') ++ GT) & (w0, Gamma0))); [ | rew_app];
auto.
apply ok_Bg_Hyb_ppermut with
  (G:= (((w, Gamma) :: (GH & (w0, Gamma0) ++ GT)) & (w', Gamma')));
[rew_app; PPermut_Hyb_simpl | apply ok_Bg_Hyb_permut_no_last_spec
  with (v:=v)(A:=A0)];
apply ok_Bg_Hyb_ppermut with
  ((GH & (w, Gamma'') ++ GT) & (w', (v, A0) :: Gamma') & (w0, Gamma0));
[ rew_app | ]; auto; try PPermut_Hyb_simpl.
eapply IHHT with (w1:=w) (Gamma1:=Gamma) (A0:=A0) (w':=w')
  (G0:=GH++GT & (w0,Gamma0)) (Gamma':=Gamma'); auto;
[ symmetry; subst; rew_app in * | rew_app | ]; auto.
PPermut_Hyb_simpl; apply PPermut_Hyb_last_rev_simpl with (a:=(w, Gamma));
rewrite <- H7; PPermut_Hyb_simpl.
rewrite H2 in H4; rewrite H9 in H4;
assert ((GH & (w, Gamma'') ++ GT) & (w0, Gamma0) ~=~
  (GH ++ GT & (w0, Gamma0)) ++ nil & (w, Gamma))
  by (rew_app; PPermut_Hyb_simpl);
rewrite <- H10; auto.
intros; unfold open_t_Hyb in *; unfold open_w_Hyb in *;
rewrite notin_union in H10; rewrite notin_singleton in H10; destruct H10;
rewrite <- subst_Hyb_order_irrelevant_bound;
[rewrite <- subst_t_Hyb_comm | ]; auto;
eapply H with (v':=v') (w':=w'0) (Gamma1:=Gamma0) (w1:=w0) (A0:=A0)
              (v:=v) (G0:=(w'0, (v', A) :: nil) :: (GH ++ GT) & (w, Gamma))
              (w'0:=w') (Gamma':=Gamma'); auto; try PPermut_Hyb_simpl.
apply PPermut_Hyb_last_rev_simpl with (a:=(w, Gamma)); rewrite <- H7;
subst; PPermut_Hyb_simpl.
rew_app; rewrite H2 in H4; rewrite H9 in H4; simpl;
apply BackgroundSubsetImpl_Hyb with
  (G:=emptyEquiv_Hyb (GH ++ GT ++ (w, Gamma) :: (w0, Gamma0) :: nil)); auto.
assert (GH ++ GT ++ (w, Gamma) :: (w0, Gamma0) :: nil ~=~
  (GH & (w, Gamma'') ++ GT) & (w0, Gamma0)) by (rew_app; PPermut_Hyb_simpl);
rewrite H13; auto.
exists ((w'0, (@nil (var*ty))) :: nil); PPermut_Hyb_simpl.
assert ((w, Gamma) :: G & (w0, Gamma0) ~=~ G0 & (w0, Gamma0)) by
  (rewrite <- H0; auto).
rewrite H13 in Ok_Bg; rewrite H1 in Ok_Bg; subst;
assert ((w', nil)
      :: (w'0, nil)
         :: emptyEquiv_Hyb (GH ++ GT ++ (w, Gamma) :: (w0, Gamma0) :: nil) ~=~
      (w'0, nil)
      :: (w', nil)
         :: emptyEquiv_Hyb (GH ++ GT ++ (w, Gamma) :: (w0, Gamma0) :: nil))
by auto.
rewrite H9; apply ok_Bg_Hyb_fresh_wo;
assert (((GH & (w, Gamma'') ++ GT) & (w', (v, A0) :: Gamma')) & (w0, Gamma0) ~=~
  ((w', (v, A0) :: Gamma') :: GH ++ GT ++ (w, Gamma) :: nil) &  (w0, Gamma0))
  by PPermut_Hyb_simpl;
rew_app in *; [rewrite H14 in Ok_Bg | auto];
apply emptyEquiv_Hyb_ok_Bg_Hyb in Ok_Bg; simpl in *; auto.
symmetry; transitivity (G1 & (w', Gamma')); subst; rew_app in *;
PPermut_Hyb_simpl.
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

(* here *)
case_if.
inversion H0; subst; rewrite H in Ok_Bg;
apply ok_Bg_Hyb_first_last_neq in Ok_Bg; elim Ok_Bg; auto.
constructor;
[ rewrite H in Ok_Bg | apply IHHT with (Gamma:=Gamma0)]; eauto;
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

(* get_here *)
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
  (eapply PPermut_Hyb_split_neq; eauto; right; intro; subst; elim H1;
    reflexivity);
destruct Split as (Gamma'', (GH, Split)); destruct Split as (GT, H3);
destruct H3 as (H3a, H3b).
apply t_get_here_Hyb with (G:=GH++GT) (Gamma:=Gamma).
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
apply PPermut_Hyb_last_rev_simpl with (a:=(w, Gamma)); rew_app in *; auto;
subst; PPermut_Hyb_simpl.

case_if;
[ inversion H1; subst; apply ok_Bg_Hyb_first_last_neq in Ok_Bg; elim Ok_Bg;
  auto | destruct (eq_var_dec w w'0)].
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
  (eapply PPermut_Hyb_split_neq; eauto; right; intro; subst; elim H1;
    reflexivity);
destruct Split as (Gamma'', (GH, Split));
destruct Split as (GT, (Ha, Hb)); subst;
apply t_get_here_Hyb with (G:=GH++GT) (Gamma:=Gamma).
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
  (apply ok_Bg_Hyb_impl_ppermut with (w:=w''); [ | rewrite H; rewrite H0]; eauto);
destruct H3; apply t_get_here_Hyb with (G:=G0) (Gamma := Gamma'0 ++ Gamma);
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
apply t_get_here_Hyb with (G:=G0) (Gamma := Gamma ++ Gamma'');
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
apply t_get_here_Hyb with (G:=GH++GT & (w'0, Gamma'0++Gamma''))
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

(* letdia *)
case_if.
inversion H1; subst; rewrite H0 in Ok_Bg;
apply ok_Bg_Hyb_first_last_neq in Ok_Bg; elim Ok_Bg; auto.
apply t_letdia_Hyb with (L_w:=L_w \u \{w'}) (L_t:=L_t) (A:=A);
[ rewrite H0 in Ok_Bg |
  eapply IHHT with (w:=w0) (Gamma:=Gamma0) | ]; eauto.
eapply ok_Bg_Hyb_split2; eauto.
intros; rewrite notin_union in H3; destruct H3;
rewrite notin_singleton in H4;
unfold open_t_Hyb in *; unfold open_w_Hyb in *;
rewrite <- subst_w_Hyb_comm; auto;
rewrite subst_Hyb_order_irrelevant_free;
[ eapply H with (w:=w0) (Gamma:=Gamma0) (w':=w'0) | simpl]; eauto;
rewrite H0; PPermut_Hyb_simpl.

case_if.
apply t_letdia_Hyb with (L_w:=L_w \u \{w0}) (L_t:=L_t) (A:=A);
[ rewrite H0 in Ok_Bg | eapply IHHT with (w:=w0) (Gamma:=Gamma0) | ]; eauto.
eapply ok_Bg_Hyb_split2; eauto.
intros; rewrite notin_union in H2; destruct H2;
rewrite notin_singleton in H3;
unfold open_t_Hyb in *; unfold open_w_Hyb in *;
rewrite <- subst_w_Hyb_comm; auto;
rewrite subst_Hyb_order_irrelevant_free;
[ eapply H with (w:=w0) (Gamma:=Gamma0) (w':=w'0) | simpl]; eauto;
rewrite H0; PPermut_Hyb_simpl.

case_if.
inversion H2; subst; rewrite H0 in Ok_Bg;
apply ok_Bg_Hyb_first_last_neq in Ok_Bg; elim Ok_Bg; auto.
apply t_letdia_Hyb with (L_w:=L_w \u \{w''}) (L_t:=L_t) (A:=A);
[ rewrite H0 in Ok_Bg; rewrite H1 |
  eapply IHHT with (w:=w0) (Gamma:=Gamma0) | ]; eauto.
eapply ok_Bg_Hyb_split3; eauto.
intros; rewrite notin_union in H4; destruct H4;
rewrite notin_singleton in H5;
unfold open_t_Hyb in *; unfold open_w_Hyb in *;
rewrite <- subst_w_Hyb_comm; auto;
rewrite subst_Hyb_order_irrelevant_free; simpl; auto;
eapply H with (w:=w0) (Gamma:=Gamma0) (G0:=G0 & ((w'0, (v', A)::nil)))
  (Gamma':=Gamma') (Gamma'':=Gamma''); auto;
[ rewrite H0 |rewrite H1 ]; rew_app; auto;
PPermut_Hyb_simpl.

(* letdia_get *)
case_if.
inversion H3; subst;
assert (G ~=~ G' /\ Gamma *=* Gamma') by
  (apply ok_Bg_Hyb_impl_ppermut with (w:=w'); [ | transitivity G0]; eauto);
destruct H4;
eapply t_letdia_Hyb with (L_w := L_w \u \{w'}).
rewrite <- H4; apply ok_Bg_Hyb_permut with (Ctx:=(Gamma0 ++ Gamma)); auto;
eapply ok_Bg_Hyb_split1; eauto.
apply ContextPermutImpl_Hyb with (Gamma := Gamma0++Gamma); [permut_simpl|];
auto; eapply IHHT; auto.
intros; rewrite notin_union in H7; destruct H7;
rewrite notin_singleton in H8;
unfold open_t_Hyb in *; unfold open_w_Hyb in *;
rewrite <- subst_w_Hyb_comm; auto;
rewrite subst_Hyb_order_irrelevant_free; simpl; auto;
eapply H with (v':=v') (w'0:=w'0) (w:=w0); auto;
[ | rew_app]; eauto.
destruct (eq_var_dec w w0).
subst; apply ok_Bg_Hyb_first_last_neq in Ok_Bg; elim Ok_Bg; auto.
assert (G' & (w', Gamma') ~=~ G & (w, Gamma)) by
  (symmetry; transitivity G0; auto);
assert (exists Gamma'', exists GH, exists GT,
  Gamma'' *=* Gamma /\ G' = GH & (w, Gamma'') ++ GT) by
  (eapply PPermut_Hyb_split_neq; eauto; right; intro; subst; eauto);
destruct H5 as (Gamma'', (GH, (GT, (Ha, Hb))));
assert (G & (w, Gamma) ~=~
       (GH ++ GT ++ (w', Gamma') :: nil) &  (w, Gamma));
[subst; symmetry | rew_app]; auto.
rewrite <- H4; PPermut_Hyb_simpl.
apply t_letdia_get_Hyb with (L_w:=L_w \u \{w'}) (L_t:=L_t) (A:=A)
  (G:=GH++GT) (Gamma:=Gamma);
assert ((w, Gamma) :: G & (w0, Gamma0) ~=~
  (GH ++ GT & (w', Gamma')) & (w, Gamma) & (w0, Gamma0)) by
  (PPermut_Hyb_simpl; apply PPermut_Hyb_last_rev_simpl with (a:=(w,Gamma)); auto).
rewrite H6 in Ok_Bg.
apply ok_Bg_Hyb_ppermut with (G:=(GH ++ GT & (w, Gamma)) &
  (w0, Gamma0 ++ Gamma')).
PPermut_Hyb_simpl.
rew_app in *; eauto. eapply ok_Bg_Hyb_split8; eauto.
eapply IHHT with (w1:=w) (G0:=GH++GT) (w':=w0)
  (Gamma':=Gamma0) (Gamma'':=Gamma');
auto.
PPermut_Hyb_simpl; apply PPermut_Hyb_last_rev_simpl with (a:=(w, Gamma));
rewrite H5; PPermut_Hyb_simpl.
intros; rewrite notin_union in H8; destruct H8;
rewrite notin_singleton in H9;
unfold open_t_Hyb in *; unfold open_w_Hyb in *;
rewrite <- subst_w_Hyb_comm; auto;
rewrite subst_Hyb_order_irrelevant_free; simpl; auto;
eapply H with (w1:=w0) (Gamma1:=Gamma0); auto.
rewrite H5; PPermut_Hyb_simpl.
subst; PPermut_Hyb_simpl.

case_if.
inversion H3; subst;
apply ok_Bg_Hyb_first_last_neq in Ok_Bg; elim Ok_Bg; auto.
destruct (eq_var_dec w w').
subst; assert (G ~=~ G' /\ Gamma *=* Gamma').
  apply ok_Bg_Hyb_impl_ppermut with (w:=w'); auto. eauto with ok_bg_hyb_rew.
  transitivity G0; auto.
destruct H4;
apply t_letdia_Hyb with (L_w:=L_w \u \{w0}) (L_t:=L_t) (A:=A).
rewrite <- H4; apply ok_Bg_Hyb_permut with (Ctx := Gamma ++ Gamma0); auto;
eapply ok_Bg_Hyb_split2; eauto.
apply ContextPermutImpl_Hyb with (Gamma:=Gamma++Gamma0); auto;
eapply IHHT with (Gamma1:=Gamma); eauto.
intros; rewrite <- H4;
apply ContextPermutImpl_Hyb with (Gamma:=Gamma++Gamma0); auto;
unfold open_t_Hyb in *; unfold open_w_Hyb in *;
rewrite <- subst_w_Hyb_comm; auto;
rewrite subst_Hyb_order_irrelevant_free; simpl; auto.
eapply H with (w'0 := w'0); eauto.
assert (G' & (w', Gamma') ~=~ G & (w, Gamma)) by
  (symmetry; transitivity G0; auto);
assert (exists Gamma'', exists GH, exists GT,
  Gamma'' *=* Gamma /\ G' = GH & (w, Gamma'') ++ GT) by
  (eapply PPermut_Hyb_split_neq; eauto).
destruct H5 as (Gamma'', (GH, (GT, (Ha, Hb)))).
apply t_letdia_get_Hyb with (L_w:=L_w \u \{w0})
  (L_t:=L_t) (A:=A) (G:=GH++GT) (Gamma:=Gamma).
subst; assert ((w, Gamma) :: G & (w0, Gamma0) ~=~
  (GH & (w, Gamma'') ++ GT) & (w', Gamma') & (w0, Gamma0)) by
(rewrite H4; auto).
rewrite H5 in Ok_Bg.
apply ok_Bg_Hyb_ppermut with (G:= GH & (w, Gamma'') ++ GT &
  (w', Gamma' ++ Gamma0));
rew_app in *; [ PPermut_Hyb_simpl | ];
apply ok_Bg_Hyb_ppermut with
  (G:=(GH ++ (w, Gamma'') :: GT) & (w', Gamma' ++ Gamma0));
[ | apply ok_Bg_Hyb_split4 with (w:=w0)]; rew_app; auto;
apply ok_Bg_Hyb_ppermut with (G:=GH ++ (w, Gamma'') :: GT ++ (w', Gamma') ::
  (w0, Gamma0) :: nil); eauto.
eapply IHHT; auto.
PPermut_Hyb_simpl; apply PPermut_Hyb_last_rev_simpl with (a:=(w, Gamma));
rewrite <- H4; subst; PPermut_Hyb_simpl.
intros. rewrite notin_union in H6; destruct H6;
rewrite notin_singleton in H7; unfold open_t_Hyb in *; unfold open_w_Hyb in *;
rewrite <- subst_w_Hyb_comm; auto;
rewrite subst_Hyb_order_irrelevant_free; simpl; auto;
eapply H with (w1:=w0) (Gamma1:=Gamma0); auto; PPermut_Hyb_simpl.
apply PPermut_Hyb_last_rev_simpl with (a:=(w,Gamma));
rewrite <- H4; subst; PPermut_Hyb_simpl.
subst; PPermut_Hyb_simpl.

case_if.
inversion H4; subst;
assert (G ~=~ G1 & (w', Gamma') /\ Gamma *=* Gamma'') by
 (apply ok_Bg_Hyb_impl_ppermut with (w:=w'');
  [ | transitivity G0]; eauto);
destruct H5;
eapply t_letdia_get_Hyb with (G:=G1) (Gamma:=Gamma'++Gamma)
  (L_w:=L_w \u \{w''}).
rewrite H5 in Ok_Bg; eauto.
clear H HT2 IHHT.
eapply ok_Bg_Hyb_split2; eauto; apply ok_Bg_Hyb_ppermut with
  (G:=(w'', Gamma) :: G1 & (w', Gamma') & (w0, Gamma0));
eauto; PPermut_Hyb_simpl.
eapply IHHT with (Gamma':=Gamma'); auto;
try PPermut_Hyb_simpl.
intros; unfold open_t_Hyb in *; unfold open_w_Hyb in *;
rewrite <- subst_w_Hyb_comm; auto;
rewrite subst_Hyb_order_irrelevant_free; simpl; auto;
eapply H with (w:=w0) (G0:=(w'0, (v',A)::nil)::G1)
  (Gamma':=Gamma') (Gamma'':=Gamma); auto;
[ eauto | rew_app]; constructor; [ | symmetry]; auto;
rewrite H5; rew_app; auto.
rewrite H2; PPermut_Hyb_simpl.
destruct (eq_var_dec w w').
subst.
assert (G ~=~ G1 & (w'', Gamma'') /\ Gamma *=* Gamma').
  apply ok_Bg_Hyb_impl_ppermut with (w:=w'); [ | transitivity G0]; eauto;
  rewrite H1; PPermut_Hyb_simpl.
destruct H5;
eapply t_letdia_get_Hyb with (G:=G1) (Gamma:=Gamma++Gamma'')
  (L_w:=L_w \u \{w''}) (L_t := L_t).
clear H HT2 IHHT.
rewrite H5 in Ok_Bg; eapply ok_Bg_Hyb_split9; eauto.
eapply IHHT with (w:=w'); auto; PPermut_Hyb_simpl.
intros; unfold open_t_Hyb in *; unfold open_w_Hyb in *;
rewrite <- subst_w_Hyb_comm; auto;
rewrite subst_Hyb_order_irrelevant_free; simpl; auto;
eapply H with (w:=w0) (G0:=(w'0, (v',A)::nil)::G1)
  (Gamma':=Gamma) (Gamma'':=Gamma''); auto;
rew_app; constructor; auto;
symmetry; transitivity ((G1 ++ (w'', Gamma'')::nil) & (w', Gamma)); auto;
rew_app; auto.
rewrite H2; PPermut_Hyb_simpl.
assert (G & (w, Gamma) ~=~ G1 & (w', Gamma') & (w'', Gamma'')) by
  (symmetry; transitivity G0; symmetry; auto);
assert (exists Gamma0, exists GH, exists GT,
  Gamma0 *=* Gamma /\ G1 & (w'', Gamma'') = GH & (w, Gamma0) ++ GT) by
  (apply PPermut_Hyb_split_neq with (w:=w') (G':=G) (Gamma:=Gamma');
   try symmetry; auto; transitivity (G1 & (w', Gamma') & (w'', Gamma'')); auto;
  PPermut_Hyb_simpl).
assert (exists Gamma0, exists GH, exists GT,
  Gamma0 *=* Gamma /\ G1 = GH & (w, Gamma0) ++ GT) by
  (destruct H6 as (Gamma5, (GH, (GT, (H6a, H6b)))); subst;
   apply PPermut_Hyb_split_neq with (w:=w'') (G':=GH++GT) (Gamma:=Gamma'');
   auto; [rewrite H6b; rew_app; auto | right; intro; subst; elim H4;
     reflexivity];
  PPermut_Hyb_simpl).
destruct H7 as (Gamma'1, (GH, (GT, (H7a, H7b)))); subst.
apply t_letdia_get_Hyb with (L_w:=L_w \u \{w''})
  (L_t:=L_t) (A:=A) (G:=GH++GT & (w', Gamma'++Gamma'')) (Gamma:=Gamma).
assert ((w, Gamma) :: G & (w0, Gamma0) ~=~ G0  & (w0, Gamma0)) by
  (rewrite <- H0; auto);
rewrite H7 in Ok_Bg; rewrite H1 in Ok_Bg.
apply ok_Bg_Hyb_ppermut with (G:= (GH & (w, Gamma'1) ++ GT) &
  (w', Gamma' ++ Gamma'') & (w0, Gamma0));
rew_app in *; eauto; try PPermut_Hyb_simpl.
clear IHHT H HT2. eapply ok_Bg_Hyb_split10; eauto.
eapply IHHT with (w1:=w) (G0:=GH++GT & (w0, Gamma0))
  (Gamma':=Gamma') (Gamma'':=Gamma''); rew_app; auto;
rew_app in *; transitivity ((GH ++ GT ++ (w', Gamma') ::
  (w'', Gamma'') :: nil) & (w0, Gamma0));
[ PPermut_Hyb_simpl | rew_app]; auto;
apply PPermut_Hyb_last_rev_simpl with (a:=(w, Gamma));
rewrite H5; symmetry; transitivity (GH ++ GT ++ (w, Gamma) :: (w', Gamma') ::
  (w'', Gamma'') :: nil); [rew_app |  apply PPermut_Hyb_app_head; symmetry];
auto; try PPermut_Hyb_simpl.
intros; unfold open_t_Hyb in *; unfold open_w_Hyb in *;
rewrite <- subst_w_Hyb_comm; auto;
rewrite subst_Hyb_order_irrelevant_free; simpl; auto;
eapply H with (G0:=(w'0, (v', A) :: nil) :: (GH ++ GT) & (w, Gamma))
  (Gamma':=Gamma') (Gamma'':=Gamma''); auto; PPermut_Hyb_simpl.
apply PPermut_Hyb_last_rev_simpl with (a:=(w, Gamma)); rewrite H5;
PPermut_Hyb_simpl.
rewrite H2; PPermut_Hyb_simpl.
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
(* here & get_here *)
inversion HT; subst;
inversion H_lc_w; subst;
inversion H_lc_t; subst.
(* here *)
edestruct IHM; eauto;
[ left; econstructor|
  right; destruct H0; eexists];
eauto using step_Hyb.
(* get_here *)
assert (Gamma = nil) by
  ( apply emptyEquiv_Hyb_permut_empty with
    (G:= (G0 & (w0, Gamma))) (G':=G) (w:=w0); auto;
    apply Mem_last); subst;
destruct IHM with (A := A0)
                  (Ctx := (w0, (@nil ty)))
                  (G := G0 & (w, nil))
                  (w := w0);
eauto.
assert (emptyEquiv_Hyb (G0 & (w, nil)) = G0 & (w, nil)) by
  ( repeat rewrite emptyEquiv_Hyb_rewrite; simpl;
   apply emptyEquiv_Hyb_permut_split_last in H6; rewrite H6; reflexivity);
rewrite H0; auto.
left; inversion H0; subst; inversion HT0; subst;
econstructor; eauto using step_Hyb.
right; destruct H0; eexists;
econstructor; eauto using step_Hyb.
(* letdia & letdia_get *)
right; inversion HT; subst;
inversion H_lc_w; subst;
inversion H_lc_t; subst.
(* letdia *)
edestruct IHM1 with (A := <*>A0); eauto;
[ inversion H0; subst; inversion HT1; subst |
  destruct H0];
eexists; constructor; eauto.
inversion H5; subst; auto.
inversion H7; subst; auto.
inversion H5; subst; auto.
inversion H7; subst; auto.
(* letdia_get *)
assert (Gamma = nil) by
  ( apply emptyEquiv_Hyb_permut_empty
    with (G:= (G0 & (w0, Gamma))) (G':=G) (w:=w0);
    auto; apply Mem_last); subst;
edestruct IHM1 with (G := G0 & (w, nil))
                    (w := w0)
                    (Ctx := (w0, (@nil ty)))
                    (A := <*>A0); eauto.
assert ( emptyEquiv_Hyb (G0 & (w, nil)) = G0 & (w, nil)) by
   ( repeat rewrite emptyEquiv_Hyb_rewrite; simpl;
     apply emptyEquiv_Hyb_permut_split_last in H6; rewrite H6; reflexivity).
rewrite H0; auto.
inversion H0; subst; inversion HT1; subst;
eexists; constructor; eauto;
try apply closed_t_succ; auto;
inversion H5; inversion H8; subst; auto.
destruct H0;
eexists; constructor; eauto;
try apply closed_t_succ; auto;
inversion H5; inversion H8; subst; auto.
Qed.

(*
   Proof sketch: double induction on typing and making a step
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
(* get_here *)
assert (Gamma = nil) by
  ( apply emptyEquiv_Hyb_permut_empty with (G:= (G & (w, Gamma))) (G':=G0)
    (w:=w);
    auto; apply Mem_last); subst;
eapply IHHT with (G0:=G & (w0, nil)); eauto;
repeat rewrite emptyEquiv_Hyb_rewrite; simpl;
apply emptyEquiv_Hyb_permut_split_last in H; rewrite H; reflexivity.
(* letdia + (here | get_here ) *)
assert (exists w1, w1 \notin L_w \u free_worlds_Hyb N) as HF by apply Fresh;
assert (exists v1, v1 \notin L_t \u free_vars_Hyb N) as HF2 by apply Fresh;
destruct HF as (w_fresh); destruct HF2 as (v_fresh);
inversion HT; subst.
(* letdia #1 *)
rewrite notin_union in *; destruct H0; destruct H1;
unfold open_t_Hyb in *; unfold open_w_Hyb in *;
rewrite subst_t_Hyb_neutral_free with (v:=v_fresh);
[ rewrite subst_Hyb_order_irrelevant_bound |
  apply subst_w_Hyb_preserv_free_vars]; auto;
[ rewrite <- subst_w_Hyb_neutral_free with (w0:=w_fresh) |
  constructor];
[ apply subst_t_Hyb_preserv_types_inner with (A:=A) |
  apply subst_t_Hyb_preserv_free_worlds]; auto;
[ | rewrite <- double_emptyEquiv_Hyb; auto];
replace ((v_fresh, A) :: nil) with (nil ++ (v_fresh, A) :: nil) by auto;
apply rename_w_Hyb_preserv_types_new with
  (G:= (w_fresh, (v_fresh, A)::nil) :: emptyEquiv_Hyb G0);
[ rewrite <- subst_Hyb_order_irrelevant_bound |
  rew_app]; auto; try PPermut_Hyb_simpl; constructor.
(* letdia #2 *)
rewrite notin_union in *; destruct H0; destruct H1;
unfold open_t_Hyb in *; unfold open_w_Hyb in *;
rewrite subst_t_Hyb_neutral_free with (v:=v_fresh);
[ rewrite subst_Hyb_order_irrelevant_bound |
  apply subst_w_Hyb_preserv_free_vars]; auto;
[ rewrite <- subst_w_Hyb_neutral_free with (w0:=w_fresh) |
  constructor];
[ eapply subst_t_Hyb_preserv_types_outer with (A:=A) (G0:=G)
  (Gamma':=Gamma) (w':=w) |
  apply subst_t_Hyb_preserv_free_worlds]; auto;
rew_app;
assert ( emptyEquiv_Hyb (G & (w0, nil)) = G & (w0, nil)) by
   ( repeat rewrite emptyEquiv_Hyb_rewrite; simpl;
     apply emptyEquiv_Hyb_permut_split_last in H4; rewrite H4; reflexivity);
assert (Gamma = nil) by
  ( apply emptyEquiv_Hyb_permut_empty with (G:= (G & (w, Gamma)))
    (G':=G0) (w:=w); auto; apply Mem_last).
subst; rew_app. rewrite <- H10 in HT0; auto.
apply rename_w_Hyb_preserv_types_outer with (G0:=G)
  (Gamma'':=(v_fresh,A) :: nil)
  (Gamma':=Gamma) (G:=G & (w, Gamma) & (w_fresh, (v_fresh,A)::nil));
assert (G & (w, Gamma) & (w_fresh, (v_fresh, A) :: nil) ~=~
  (w_fresh, (v_fresh, A) :: nil) :: emptyEquiv_Hyb G0) by PPermut_Hyb_simpl.
rewrite H12; rewrite <- subst_Hyb_order_irrelevant_bound;
[eapply HT2; auto | constructor].
PPermut_Hyb_simpl; auto.
PPermut_Hyb_simpl.
(* letdia *)
assert (exists w1, w1 \notin L_w \u free_worlds_Hyb N) as HF by apply Fresh;
assert (exists v1, v1 \notin L_t \u free_vars_Hyb N) as HF2 by apply Fresh;
destruct HF as (w_fresh); destruct HF2 as (v_fresh);
inversion HT; subst.
(* letdia #1 *)
rewrite notin_union in *; destruct H1; destruct H2;
unfold open_t_Hyb in *; unfold open_w_Hyb in *;
rewrite subst_t_Hyb_neutral_free with (v:=v_fresh);
[ rewrite subst_Hyb_order_irrelevant_bound |
  apply subst_w_Hyb_preserv_free_vars]; auto;
[ rewrite <- subst_w_Hyb_neutral_free with (w0:=w_fresh) |
  constructor];
[ eapply subst_t_Hyb_preserv_types_outer with (A:=A) (G0:=G) (w':=w)
  (Gamma':=Gamma) |
 apply subst_t_Hyb_preserv_free_worlds]; eauto;
assert (Gamma = nil) by
  (apply emptyEquiv_Hyb_permut_empty with
    (G:= (G & (w, Gamma))) (G':=G1) (w:=w); auto; apply Mem_last); subst;
rew_app;
assert ( emptyEquiv_Hyb (G & (w0, nil)) = G & (w0, nil)) by
   ( repeat rewrite emptyEquiv_Hyb_rewrite; simpl;
     apply emptyEquiv_Hyb_permut_split_last in H0; rewrite H0; reflexivity);
[ rewrite <- H5 in HT0 |
  eapply rename_w_Hyb_preserv_types_outer
    with (G:= (w_fresh, (v_fresh,A)::nil):: G & (w,nil))
         (Gamma'':=(v_fresh,A)::nil) (Gamma':=nil) (G0:=G)]; auto.
rewrite <- subst_Hyb_order_irrelevant_bound;
[ eapply HT2; eauto | constructor].
PPermut_Hyb_simpl.
(* letdia #2 *)
assert (Gamma = nil) by
  (apply emptyEquiv_Hyb_permut_empty with
    (G:= (G & (w, Gamma))) (G':=G1) (w:=w); auto; apply Mem_last); subst.
assert (w <> w0) by eauto with ok_bg_hyb_rew.
assert (w1 <> w) by eauto with ok_bg_hyb_rew.
rewrite <- H0; rewrite notin_union in *; destruct H1; destruct H2;
unfold open_t_Hyb in *; unfold open_w_Hyb in *; destruct (eq_var_dec w1 w0);
subst.
assert (G0  ~=~ G /\ Gamma0 *=* nil) by
  (apply ok_Bg_Hyb_impl_ppermut with (w:=w0); eauto);
destruct H13; symmetry in H14; apply permut_nil_eq in H14;
rewrite subst_t_Hyb_neutral_free with (v:=v_fresh);
[ eapply subst_t_Hyb_preserv_types_inner with (A:=A) |
  apply subst_w_Hyb_preserv_free_vars]; eauto;
[ rewrite subst_Hyb_order_irrelevant_bound |
  assert ( emptyEquiv_Hyb (G & (w, nil)) = G & (w, nil)) by
    ( repeat rewrite emptyEquiv_Hyb_rewrite; simpl;
      apply emptyEquiv_Hyb_permut_split_last in H0; rewrite H0; reflexivity)];
[ rewrite <- subst_w_Hyb_neutral_free with (w0:=w_fresh) |
  constructor | ]; auto;
[ replace ((v_fresh,A)::nil) with (nil++(v_fresh,A)::nil) by auto |
  apply subst_t_Hyb_preserv_free_worlds | ]; auto.
apply rename_w_Hyb_preserv_types_new with
  (G:= (w_fresh, (v_fresh,A)::nil) :: G0 & (w, nil));
[ rewrite <- subst_Hyb_order_irrelevant_bound; try constructor; subst |
  rew_app; eauto].
rewrite H13; eapply HT2; auto.
PPermut_Hyb_simpl.
rewrite H15; rewrite <- H13; subst; auto.
assert (Gamma0 = nil) by
  ( apply emptyEquiv_Hyb_permut_empty with (G:= (G0 & (w1, Gamma0)))
      (G':=G & (w0, nil)) (w:=w1); auto;
    assert (emptyEquiv_Hyb G = G) by
      (apply emptyEquiv_Hyb_permut_split_last with (C:=(w, nil)) (H:=G1); auto);
    [ rewrite emptyEquiv_Hyb_rewrite; simpl | apply Mem_last ];
rewrite H13; auto); subst; assert (exists Gamma'', exists GH, exists GT,
  Gamma'' *=* nil /\ G = GH & (w1, Gamma'') ++ GT) by
  ( apply PPermut_Hyb_split_neq with (w:=w0) (G':=G0) (Gamma:=nil);
    [ symmetry | right; intro; subst; elim n]; auto);
destruct H13 as (Gamma'', (GH, (GT, (H12a, H12b))));
symmetry in H12a; apply permut_nil_eq in H12a; subst;
rewrite subst_t_Hyb_neutral_free with (v:=v_fresh);
[ apply subst_t_Hyb_preserv_types_outer with (A:=A) (G0 :=GH ++ GT & (w, nil))
          (G := GH ++ GT & (w,nil) & (w1, (v_fresh, A) :: nil))
       (G' := GH ++ GT & (w,nil) & (w0, nil)) (w' :=w1) (Gamma':=nil) |
  apply subst_w_Hyb_preserv_free_vars]; auto; subst; rew_app; auto.
assert (G0 & (w, nil) ~=~ GH ++ GT & (w,nil) & (w0, nil)) by
  ( transitivity ((GH++GT & (w0,nil) &(w, nil))); auto;
    assert (G0 & (w1, nil) ~=~  (GH ++ GT & (w0, nil) & (w1, nil))) by
      (transitivity ((GH & (w1, nil) ++ GT) & (w0, nil)); rew_app in *; auto);
    assert (G0 ~=~ GH ++ GT & (w0, nil)) by
      (apply PPermut_Hyb_last_rev_simpl with (a:=(w1,nil)); rew_app in *; auto);
  try PPermut_Hyb_simpl;
  rewrite H14; rew_app; auto); rew_app in *; rewrite <- H13.
assert (emptyEquiv_Hyb G0 = G0) by
( assert (G0 ~=~ GH ++ GT & (w0, nil)) by
    ( apply PPermut_Hyb_last_rev_simpl with (a:=(w, nil));
      transitivity (GH ++ GT & (w, nil) & (w0, nil)); rew_app in *; auto);
  apply emptyEquiv_Hyb_permut_split_last with (C:=(w1, nil)) (H := (w0, nil) ::
    GH & (w1, nil) ++ GT);
  assert (emptyEquiv_Hyb ((w0, nil) :: GH & (w1, nil) ++ GT) = ((w0, nil) ::
    GH & (w1, nil) ++ GT)) by
  ( apply emptyEquiv_Hyb_permut_split_last with (C:=(w, nil))
    (H:= (w0,nil)::G1); simpl; rewrite <- H0; rew_app; symmetry; auto);
  rewrite H14; rewrite H15; rew_app;
  transitivity (GH ++ (w0, nil) :: (w1, nil)::GT); auto; PPermut_Hyb_simpl);
rewrite emptyEquiv_Hyb_rewrite; simpl; rewrite H14; auto.
rewrite subst_Hyb_order_irrelevant_bound;
[ rewrite <- subst_w_Hyb_neutral_free with (w0:=w_fresh) | constructor];
[ apply rename_w_Hyb_preserv_types_outer
    with (G0 := GH ++ GT & (w,nil))
         (G := (w_fresh, (v_fresh, A) :: nil) :: (GH & (w1, nil) ++ GT) &
           (w, nil))
         (Gamma':=nil)
         (Gamma'':=(v_fresh, A)::nil) |
  apply subst_t_Hyb_preserv_free_worlds]; auto.
rewrite <- subst_Hyb_order_irrelevant_bound;
[eapply HT2; eauto | constructor].
PPermut_Hyb_simpl.
PPermut_Hyb_simpl.
(* letdia_step *)
destruct (eq_var_dec w0 w); subst.
eapply ok_Bg_Hyb_first_last_neq in Ok_Bg;
elim Ok_Bg; auto.
assert (Gamma = nil) by
  ( apply emptyEquiv_Hyb_permut_empty with (G:= (G & (w, Gamma))) (G':=G1)
    (w:=w); auto; apply Mem_last);
subst;
apply IHHT with (G0:=G & (w0,nil)) (w1:=w); auto;
assert (emptyEquiv_Hyb G = G) by
  (apply emptyEquiv_Hyb_permut_split_last with (C:=(w,nil)) (H:=G1); auto);
rewrite emptyEquiv_Hyb_rewrite; simpl; rewrite H1; reflexivity.
Qed.

(*
   Lemmas needed for properties like termination or lang. equivalence.
*)

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
assert (exists x, x \notin L_t) by apply Fresh; destruct H1;
assert (exists x, x \notin L_w) by apply Fresh; destruct H2;
specialize H0 with x x0; apply H0 with (w':=x0) in H1; auto;
apply lc_w_n_Hyb_subst_t in H1; apply lc_w_n_Hyb_subst_w in H1; auto.
assert (exists x, x \notin L_t) by apply Fresh; destruct H2;
assert (exists x, x \notin L_w) by apply Fresh; destruct H3;
specialize H0 with x x0; apply H0 with (w':=x0) in H2; auto;
apply lc_w_n_Hyb_subst_t in H2; apply lc_w_n_Hyb_subst_w in H2; auto.
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
assert (exists x, x \notin L_t) by apply Fresh; destruct H1;
assert (exists x, x \notin L_w) by apply Fresh; destruct H2;
specialize H0 with x x0; apply H0 with (w':=x0) in H1; auto;
apply lc_t_n_Hyb_subst_t in H1; try constructor;
apply lc_t_n_Hyb_subst_w in H1; auto.
assert (exists x, x \notin L_t) by apply Fresh; destruct H2;
assert (exists x, x \notin L_w) by apply Fresh; destruct H3;
specialize H0 with x x0; apply H0 with (w':=x0) in H2; auto;
apply lc_t_n_Hyb_subst_t in H2; try constructor;
apply lc_t_n_Hyb_subst_w in H2; auto.
Qed.

Lemma lc_w_step_Hyb_preserv:
forall M M' w,
  lc_w_Hyb M ->
  step_Hyb (M, fwo w) (M', fwo w) ->
  lc_w_Hyb M'.
induction M; intros; inversion H0; subst; auto;
unfold open_t_Hyb in *; unfold open_w_Hyb in *; simpl in *.
apply lc_w_subst_t_Hyb; auto.
constructor; [eapply IHM1 |]; eauto.
inversion H; subst; try omega; auto.
destruct v; [inversion H; subst; omega | constructor; eapply IHM; eauto].
inversion H; subst; try omega; constructor; eauto.
apply IHM with w0; auto.
inversion H; subst; try omega; inversion H11; subst; try omega;
apply lc_w_subst_t_Hyb; auto;
apply lc_w_n_L_subst_w; auto.
inversion H; subst; try omega; constructor; auto.
apply IHM1 with w0; auto.
Qed.

Lemma lc_t_step_Hyb_preserv:
forall M M' w,
  lc_t_Hyb M ->
  step_Hyb (M, w) (M', w) ->
  lc_t_Hyb M'.
induction M; intros; inversion H0; subst; auto;
unfold open_t_Hyb in *; unfold open_w_Hyb in *; simpl in *.
apply lc_t_subst_Hyb; auto.
constructor; [eapply IHM1 |]; eauto.
inversion H; subst; try omega; auto.
inversion H; subst; try omega; constructor; eapply IHM; eauto.
inversion H; subst; try omega; constructor; eapply IHM; eauto.
inversion H; subst; try omega; inversion H11; subst; try omega;
apply lc_t_subst_Hyb; auto;
apply lc_t_n_L_subst_w; auto.
inversion H; subst; try omega; constructor; auto.
apply IHM1 with v; auto.
Qed.

Lemma lc_w_steps_Hyb_preserv:
forall M M' w,
  lc_w_Hyb M ->
  steps_Hyb (M, fwo w) (M', fwo w) ->
  lc_w_Hyb M'.
intros; remember (M, fwo w) as M0; remember (M', fwo w) as M1;
generalize dependent M; generalize dependent M'; generalize dependent w.
induction H0; intros; inversion HeqM0; inversion HeqM1; subst;
apply lc_w_step_Hyb_preserv in H; eauto.
Qed.

Lemma lc_t_steps_Hyb_preserv:
forall M M' w,
  lc_t_Hyb M ->
  steps_Hyb (M, fwo w) (M', fwo w) ->
  lc_t_Hyb M'.
intros; remember (M, fwo w) as M0; remember (M', fwo w) as M1;
generalize dependent M; generalize dependent M'; generalize dependent w.
induction H0; intros; inversion HeqM0; inversion HeqM1; subst;
apply lc_t_step_Hyb_preserv in H; eauto.
Qed.

Lemma steps_Hyb_unbox:
forall M w' w M',
 lc_w_Hyb M -> lc_t_Hyb M ->
 steps_Hyb (M, fwo w') (M', fwo w') ->
 steps_Hyb
   (unbox_fetch_Hyb (fwo w') M, w)
   (unbox_fetch_Hyb (fwo w') M', w).
intros; remember (M, fwo w') as M0; remember (M', fwo w') as M1;
generalize dependent M;
generalize dependent M';
generalize dependent w';
generalize dependent w;
induction H1; intros; inversion HeqM1; inversion HeqM0; subst;
[constructor; constructor; auto | ];
apply multi_step_Hyb with (M':=unbox_fetch_Hyb (fwo w') M');
[ constructor | eapply IHsteps_Hyb ]; eauto;
[eapply lc_w_step_Hyb_preserv | eapply lc_t_step_Hyb_preserv]; eauto.
Qed.

Lemma steps_Hyb_get:
forall M M'' w0 w1 w M' w'0,
  (w0 = fwo w'0 \/ w0 = bwo 0) ->
  lc_w_Hyb M' -> lc_t_Hyb M' ->
  lc_w_n_Hyb 1 M -> lc_t_n_Hyb 1 M ->
  steps_Hyb (M', fwo w) (M'', fwo w) ->
  steps_Hyb
    (letdia_get_Hyb (fwo w) M' (get_here_Hyb w0 M), w1)
    (letdia_get_Hyb (fwo w) M'' (get_here_Hyb w0 M), w1).
intros.
remember (M', fwo w) as M0; remember (M'', fwo w) as M1;
generalize dependent M;
generalize dependent M';
generalize dependent M''.
generalize dependent w;
generalize dependent w0;
generalize dependent w'0;
generalize dependent w1.
induction H4; intros; inversion HeqM1; inversion HeqM0; subst;
[constructor; constructor; auto |].
inversion H0; subst; constructor; try omega; auto.
constructor; auto.
apply multi_step_Hyb
with (M':= letdia_get_Hyb (fwo w2) M' (get_here_Hyb w0 M0));
[ constructor | eapply IHsteps_Hyb ]; eauto.
inversion H0; subst; constructor; try omega; auto.
constructor; auto.
eapply lc_w_step_Hyb_preserv in H1; eauto.
eapply lc_t_step_Hyb_preserv in H2; eauto.
Qed.

Lemma steps_Hyb_letdia_here0:
forall M N w0 w1 w M',
  lc_w_Hyb (letdia_get_Hyb w (get_here_Hyb w0 M) M') ->
  lc_t_Hyb (letdia_get_Hyb w (get_here_Hyb w0 M) M') ->
  steps_Hyb (M, w0) (N, w0) -> value_Hyb N ->
  steps_Hyb
    (letdia_get_Hyb w (get_here_Hyb w0 M) M', w1)
    (letdia_get_Hyb w (get_here_Hyb w0 N) M', w1).
intros.
remember (M, w0) as M0; remember (N, w0) as M1;
generalize dependent M;
generalize dependent N;
generalize dependent w0.
generalize dependent w1;
generalize dependent w.
generalize dependent M'.
induction H1; intros; inversion HeqM1; inversion HeqM0; subst.
inversion H0; inversion H1; inversion H9; inversion H15; subst; try omega;
repeat constructor; auto.
inversion H0; inversion H3; inversion H10; inversion H16; subst; try omega.
apply multi_step_Hyb
with (M':= letdia_get_Hyb (fwo w) (get_here_Hyb (fwo w4) M') M'0).
repeat constructor; auto.
apply IHsteps_Hyb; auto; repeat constructor; auto.
eapply lc_w_step_Hyb_preserv in H; eauto.
eapply lc_t_step_Hyb_preserv in H; eauto.
Qed.

Lemma steps_reorder:
forall M M' M'' w,
  (M, w) |->+ (M', w) -> (M', w)|-> (M'', w) -> (M, w) |->+ (M'', w).
intros.
remember (M, w) as M0; remember (M', w) as M1;
generalize dependent M;
generalize dependent M';
generalize dependent M'';
generalize dependent w.
induction H; intros; inversion HeqM0; inversion HeqM1; subst.
apply multi_step_Hyb with (M':=M'0); auto; repeat constructor; auto.
apply multi_step_Hyb with (M':=M'); auto.
apply IHsteps_Hyb with (M:=M') (M'1:=M'0); auto.
Qed.

Lemma steps_Hyb_letdia_here:
forall M N w0 w1 w M',
  lc_w_Hyb (letdia_get_Hyb w (get_here_Hyb w0 M) M') ->
  lc_t_Hyb (letdia_get_Hyb w (get_here_Hyb w0 M) M') ->
  steps_Hyb (M, w0) (N, w0) -> value_Hyb N ->
  steps_Hyb
    (letdia_get_Hyb w (get_here_Hyb w0 M) M', w1)
    ((M' ^w^ w0) ^t^ N, w1).
intros.
assert ((letdia_get_Hyb w (get_here_Hyb w0 M) M', w1) |->+
 (letdia_get_Hyb w (get_here_Hyb w0 N) M', w1)).
apply steps_Hyb_letdia_here0; auto.
assert ((letdia_get_Hyb w (get_here_Hyb w0 N) M', w1) |->
((M' ^w^ w0 ) ^t^ N, w1)).
inversion H; inversion H0; inversion H9; inversion H15; subst; try omega;
constructor; auto.
eapply lc_w_steps_Hyb_preserv in H1; eauto.
eapply lc_t_steps_Hyb_preserv in H1; eauto.
apply steps_reorder with (M':=(letdia_get_Hyb w (get_here_Hyb w0 N) M'));
auto.
Qed.

Lemma steps_Hyb_appl:
forall M N w M',
  lc_w_Hyb (appl_Hyb M M') -> lc_t_Hyb (appl_Hyb M M') ->
  steps_Hyb (M, fwo w) (N, fwo w) ->
  steps_Hyb
    (appl_Hyb M M', fwo w)
    (appl_Hyb N M', fwo w).
intros; remember (M, fwo w) as M0; remember (N, fwo w) as M1;
generalize dependent M;
generalize dependent N;
generalize dependent w;
generalize dependent M'.
induction H1; intros; inversion HeqM1; inversion HeqM0; subst.
inversion H0; inversion H1; subst.
repeat constructor; auto.
inversion H0; inversion H2; subst.
apply multi_step_Hyb with (M':=appl_Hyb M' M'0);
[ constructor | eapply IHsteps_Hyb ]; eauto; try constructor; auto.
apply lc_w_step_Hyb_preserv in H; auto.
eapply lc_t_step_Hyb_preserv in H; eauto.
Qed.

Lemma steps_Hyb_letdia:
forall M w' w M' N,
  lc_w_Hyb (letdia_get_Hyb (fwo w') M N) ->
  lc_t_Hyb (letdia_get_Hyb (fwo w') M N) ->
  steps_Hyb (M, fwo w') (M', fwo w') ->
  steps_Hyb
    (letdia_get_Hyb (fwo w') M N, fwo w)
    (letdia_get_Hyb (fwo w') M' N, fwo w).
intros; remember (M, fwo w') as M0; remember (M', fwo w') as M1;
generalize dependent M;
generalize dependent M'.
generalize dependent w;
generalize dependent N.
generalize dependent w'.
induction H1; intros; inversion HeqM1; inversion HeqM0; subst.
inversion H0; inversion H1; subst.
repeat constructor; auto.
inversion H0; inversion H2; subst.
apply multi_step_Hyb with (M':=letdia_get_Hyb (fwo w') M' N);
[ constructor | eapply IHsteps_Hyb ]; eauto; try constructor; auto.
apply lc_w_step_Hyb_preserv in H; auto.
eapply lc_t_step_Hyb_preserv in H; eauto.
Qed.

Lemma steps_Hyb_here:
forall M w' w M',
 lc_w_Hyb M -> lc_t_Hyb M ->
 steps_Hyb (M, fwo w') (M', fwo w') ->
 steps_Hyb
   (get_here_Hyb (fwo w') M, w)
   (get_here_Hyb (fwo w') M', w).
intros; remember (M, fwo w') as M0; remember (M', fwo w') as M1;
generalize dependent M;
generalize dependent M';
generalize dependent w';
generalize dependent w;
induction H1; intros; inversion HeqM1; inversion HeqM0; subst;
[constructor; constructor; auto | ];
apply multi_step_Hyb with (M':=get_here_Hyb (fwo w') M');
[ constructor | eapply IHsteps_Hyb ]; eauto;
[eapply lc_w_step_Hyb_preserv | eapply lc_t_step_Hyb_preserv]; eauto.
Qed.


Close Scope hybrid_is5_scope.
Close Scope is5_scope.
Close Scope permut_scope.
