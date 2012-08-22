Require Import LFSubstitution.
Require Import Setoid.

Require Import PermutLib.
Require Import PPermutLib.
Require Import OkLib.
Require Import EmptyEquivLib.

Open Scope label_free_is5_scope.
Open Scope is5_scope.
Open Scope permut_scope.

(* Notation for term typing *)
Global Reserved Notation " G '|=' Ctx '|-' M ':::' A " (at level 70).


(*** Definitions ::: Statics ***)


(*
   For each full context (that is, context and background), we require
   that the variables - both for terms and worlds - are unique.
*)
Inductive types_LF: Background_LF -> Context_LF -> te_LF -> ty -> Prop :=

| t_hyp_LF: forall A G w (Gamma: list (prod var ty)) v
  (Ok_Bg: ok_Bg ((w, Gamma) :: G))
  (HT: Mem (v, A) Gamma),
  G |= (w, Gamma) |- hyp_LF (fte v) ::: A

| t_lam_LF: forall L A B G w Gamma M
  (Ok_Bg: ok_Bg ((w, Gamma) :: G))
  (HT: forall v', v' \notin L ->
    G |= (w, (v', A) :: Gamma) |- M ^t^ (hyp_LF (fte v')) ::: B),
  G |= (w, Gamma) |- (lam_LF A M) ::: A ---> B

| t_appl_LF: forall A B G w Gamma M N
  (Ok_Bg: ok_Bg ((w, Gamma) :: G))
  (HT1: G |= (w, Gamma) |- M ::: A ---> B)
  (HT2: G |= (w, Gamma) |- N ::: A),
  G |= (w, Gamma) |- (appl_LF M N) ::: B

| t_box_LF: forall L A G w Gamma M
  (Ok_Bg: ok_Bg (G & (w, Gamma)))
  (HT: forall w', w' \notin L ->
    G & (w, Gamma) |= (w', nil) |- M ^w^ (fwo w') ::: A),
  G |= (w, Gamma) |- box_LF M ::: [*] A

| t_unbox_LF: forall A G w Gamma M
  (Ok_Bg: ok_Bg ((w, Gamma) :: G))
  (HT: G |= (w, Gamma) |- M ::: [*] A),
  G |= (w, Gamma) |- unbox_fetch_LF (fwo w) M ::: A

| t_unbox_fetch_LF: forall A G w Gamma w' Gamma' M
  (Ok_Bg: ok_Bg ((w, Gamma) :: G & (w', Gamma')))
  (HT: (G & (w', Gamma')) |= (w, Gamma) |- M ::: [*] A),
  forall G', (G & (w, Gamma)) ~=~ G' ->
    G' |= (w', Gamma') |- unbox_fetch_LF (fwo w) M ::: A

| t_here_LF: forall A G w Gamma M
  (Ok_Bg: ok_Bg ((w, Gamma) :: G))
  (HT: G |= (w, Gamma) |- M ::: A),
  G |= (w, Gamma) |- get_here_LF (fwo w) M ::: <*> A

| t_get_here_LF: forall A G w Gamma Ctx' M
  (Ok_Bg: ok_Bg ((w, Gamma) :: G & Ctx'))
  (HT: G & Ctx' |= (w, Gamma) |- M ::: A),
  forall G', (G & (w, Gamma)) ~=~ G' ->
    G' |= Ctx' |- get_here_LF (fwo w) M ::: <*> A

| t_letdia_LF: forall L_w L_t A B G w Gamma M N
  (Ok_Bg: ok_Bg ((w, Gamma) :: G))
  (HT1: G |= (w, Gamma) |- M ::: <*> A)
  (HT2: forall v', v' \notin L_t -> forall w', w' \notin L_w ->
    (w', (v', A) :: nil) :: G |=
      (w, Gamma) |- (N ^w^ (fwo w')) ^t^ (hyp_LF (fte v')) ::: B),
  G |= (w, Gamma) |- letdia_get_LF (fwo w) M N ::: B

| t_letdia_get_LF: forall L_w L_t A B G w (Gamma: list (prod var ty)) Ctx' M N
  (Ok_Bg: ok_Bg ((w, Gamma) :: G & Ctx'))
  (HT1: G & Ctx' |= (w, Gamma) |- M ::: <*> A)
  (HT2: forall v', v' \notin L_t -> forall w', w' \notin L_w ->
    (w', ((v', A) :: nil)) :: G & (w, Gamma) |=
      Ctx' |- (N ^w^ (fwo w')) ^t^ (hyp_LF (fte v')) ::: B),
  forall G0, (G & (w, Gamma)) ~=~ G0 ->
    G0 |= Ctx' |- letdia_get_LF (fwo w) M N ::: B

where " G '|=' Ctx '|-' M ':::' A " := (types_LF G Ctx M A)
  : label_free_is5_scope.


(*** Definitions ::: Dynamics ***)


Inductive value_LF: te_LF -> Prop :=
| val_lam_LF: forall A M, value_LF (lam_LF A M)
| val_box_LF: forall M, value_LF (box_LF M)
| val_get_here_LF: forall M Ctx, value_LF M -> value_LF (get_here_LF Ctx M)
.


Global Reserved Notation " M |-> N " (at level 70).

(*
   In order to define a step of reduction we require that certain terms
   are locally closed.
*)
Inductive step_LF: (te_LF * vwo) -> (te_LF * vwo) -> Prop :=
| red_appl_lam_LF: forall ctx M A N,
  lc_w_LF M -> (* lc_t_LF M -> *)
  lc_w_LF N -> lc_t_LF N ->
  (appl_LF (lam_LF A M) N, ctx) |-> ( M ^t^ N , ctx)

| red_unbox_fetch_box_LF: forall ctx ctx' M,
  (* lc_w_LF M -> *) lc_t_LF M ->
  (unbox_fetch_LF ctx' (box_LF M), ctx) |-> (M ^w^ ctx, ctx)

| red_letdia_get_get_here_LF: forall ctx ctx' ctx'' M N,
  lc_w_LF M -> lc_t_LF M ->
  (* lc_w_LF N -> lc_t_LF N -> *)
  (letdia_get_LF ctx' (get_here_LF ctx'' M) N, ctx) |->
    ((N ^w^ ctx'') ^t^ M, ctx)

| red_appl_LF: forall ctx M N M'
  (HT: (M, ctx) |-> (M', ctx)),
  lc_w_LF M -> lc_t_LF M ->
  lc_w_LF N -> lc_t_LF N ->
  (appl_LF M N, ctx) |-> (appl_LF M' N, ctx)

| red_unbox_fetch_LF: forall ctx' M M' ctx
  (HT: (M, ctx') |-> (M', ctx')),
  lc_w_LF M -> lc_t_LF M ->
  (unbox_fetch_LF ctx' M, ctx) |-> (unbox_fetch_LF ctx' M', ctx)

| red_get_here_LF: forall ctx ctx' M M'
  (HT: (M, ctx) |-> (M', ctx)),
  lc_w_LF M -> lc_t_LF M ->
  (get_here_LF ctx M, ctx') |-> (get_here_LF ctx M', ctx')

| red_letdia_get_LF: forall ctx ctx' M N M'
  (HT: (M, ctx) |-> (M', ctx)),
  lc_w_LF M -> lc_t_LF M ->
  (* lc_w_LF N -> lc_t_LF N -> *)
  (letdia_get_LF ctx M N, ctx') |-> (letdia_get_LF ctx M' N, ctx')

where " M |-> N " := (step_LF M N ) : label_free_is5_scope.


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
Lemma BackgroundSubsetImpl:
forall G G' Ctx M A
  (HT: G |= Ctx |- M ::: A)
  (HSubst: exists GT, (G++GT) ~=~ G')
  (H_ok: ok_Bg (Ctx :: G')),
  G' |= Ctx |- M ::: A.
intros;
generalize dependent G';
induction HT; intros.
(* hyp *)
constructor; auto.
(* lam *)
apply t_lam_LF with (L:=L \u used_t_vars ((w, Gamma)::G'));
[assumption | intros; eapply H; auto].
(* appl *)
econstructor; auto.
(* box *)
destruct HSubst as [GT];
apply t_box_LF with (L:=L \u used_w_vars (G' & (w, Gamma))); intros;
[ apply ok_Bg_cons_last |
  apply H; [ | exists GT | ] ]; auto;
apply ok_Bg_fresh_wo;
[ apply ok_Bg_cons_last |
  rewrite notin_union in H1; destruct H1]; auto.
(* unbox *)
constructor; auto.
(* unbox_fetch *)
destruct HSubst as [GT];
apply t_unbox_fetch_LF with (Gamma:=Gamma) (G:=G++GT).
apply ok_Bg_ppermut with (G:=(w', Gamma')::G'0);
  [rewrite <- H0; rewrite <- H; rew_app | ]; auto.
apply IHHT; [exists GT | ]; auto;
  apply ok_Bg_ppermut with (G:=(w', Gamma')::G'0); auto;
  rewrite <- H0; rewrite <- H; rew_app; auto.
transitivity (G' ++ GT); auto;
transitivity (G & (w, Gamma) ++ GT); [symmetry | ]; auto.
(* here *)
constructor; auto.
(* get_here *)
destruct HSubst as [GT];
apply t_get_here_LF with (Gamma:=Gamma) (G:=G++GT).
apply ok_Bg_ppermut with (G:=Ctx'::G'0);
  [rewrite <- H0; rewrite <- H; rew_app | ]; auto.
apply IHHT; [exists GT | ]; auto;
  apply ok_Bg_ppermut with (G:=Ctx'::G'0); auto;
  rewrite <- H0; rewrite <- H; rew_app; auto.
transitivity (G' ++ GT); auto;
transitivity (G & (w, Gamma) ++ GT); [symmetry | ]; auto.
(* letdia *)
apply t_letdia_LF with (A:=A) (L_t:=L_t)
  (L_w:=L_w \u used_w_vars ((w, Gamma)::G'));
[  | | intros; apply H]; auto;
destruct HSubst as [GT];
[ exists GT; rew_app; auto |
  rewrite notin_union in *; destruct H1];
apply ok_Bg_ppermut with (G:= (w', (v', A) :: nil ) :: (w, Gamma) :: G');
auto.
(* letdia_get *)
destruct HSubst as [GT];
apply t_letdia_get_LF with (A:=A) (Gamma:=Gamma) (G:=G++GT)
                           (L_t:=L_t) (L_w:=L_w \u used_w_vars (Ctx'::G')).
apply ok_Bg_ppermut with (G:=Ctx' :: G');
  [rewrite <- H1; rewrite <- H0; rew_app | ]; auto.
apply IHHT.
  exists GT; auto.
  apply ok_Bg_ppermut with (G:=Ctx' :: G');
  [ rewrite <- H1; rewrite <- H0; rew_app | ]; auto.
  intros; apply H; auto.
  exists GT; rew_app; auto.
  apply ok_Bg_ppermut with (G:=(w', (v', A) :: nil) :: Ctx' :: G'); auto;
  rewrite <- H1; rewrite <- H0;
  assert ((G & (w, Gamma) ++ GT)  ~=~ (G ++ GT) & (w, Gamma))
    by (symmetry; auto);
  rewrite H4; destruct Ctx'; auto.
rewrite <- H1; rewrite <- H0; rew_app; auto.
Qed.


(*
   Proof: using BackgroundSubsetImpl with some tweaks to remove ok_Bg from
   assumptions.
*)
Lemma PPermut_bg:
forall G Gamma w M A,
  G |= (w, Gamma) |- M ::: A ->
    forall G',
      G ~=~ G' ->
      G' |= (w, Gamma) |- M ::: A.
intros; apply BackgroundSubsetImpl with (G:=G);
[ | exists (@nil Context_LF) | ]; rew_app; auto;
inversion H; subst;
try (apply ok_Bg_ppermut with (G:=(w, Gamma) :: G); auto);
apply ok_Bg_cons_last; auto;
rewrite <- H6 || rewrite <- H1;
apply ok_Bg_ppermut with (G:=(w0, Gamma0) :: G0 & (w, Gamma)); eauto.
Qed.


(*
   Adding types_LF as morphism for PPermut will allow us to simply rewrite
   PPermutations of backgrounds.
*)
Add Morphism types_LF : PPermut_types.
split; intros; destruct y0;
[ apply PPermut_bg with (G:=x) |
  apply PPermut_bg with (G:=y) ]; auto.
Qed.


(* Proof: Simple induction on typing rules *)
Lemma ContextPermutImpl:
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
[ eapply ok_Bg_permut |
  eapply Mem_permut]; eauto.
(* lam *)
econstructor; [ eapply ok_Bg_permut | ]; eauto.
(* appl *)
econstructor; [ eapply ok_Bg_permut | | ]; eauto.
(* box *)
econstructor; [ eapply ok_Bg_permut_last | intros]; eauto;
assert (G & (w, Gamma') ~=~ G & (w, Gamma0)) by auto;
rewrite H1; apply HT; eauto.
(* unbox *)
econstructor; [ eapply ok_Bg_permut | ]; eauto.
(* unbox_fetch *)
apply t_unbox_fetch_LF with (G:=G) (Gamma:=Gamma); auto.
apply ok_Bg_ppermut with (G:=(w0, Gamma) :: G & (w, Gamma0)); auto.
assert (G & (w, Gamma'0) ~=~ (G & (w, Gamma0))) as H0 by auto;
rewrite H0; auto.
(* here *)
econstructor; [ eapply ok_Bg_permut | ]; eauto.
(* get_here *)
apply t_get_here_LF with (G:=G) (Gamma:=Gamma); auto.
apply ok_Bg_ppermut with (G:=(w0, Gamma) :: G & (w, Gamma0)); auto.
assert (G & (w, Gamma') ~=~ (G & (w, Gamma0))) as H1 by auto;
rewrite H1; auto.
(* letdia *)
econstructor; [ eapply ok_Bg_permut | | ]; eauto.
(* letdia_get *)
apply t_letdia_get_LF with (L_w:=L_w) (L_t:=L_t) (A:=A) (Gamma:=Gamma) (G:=G).
apply ok_Bg_ppermut with (G:=(w0, Gamma) :: G & (w, Gamma0)); auto.
assert (G & (w, Gamma') ~=~ (G & (w, Gamma0))) as H2 by auto;
rewrite H2; auto.
intros; eapply H; eauto.
auto.
Qed.


(* Weakening lemmas *)

Lemma GlobalWeakening:
forall G G' Ctx Ctx' M A
  (HT: G ++ G' |= Ctx |- M ::: A)
  (H_ok: ok_Bg (Ctx :: G & Ctx' ++ G')),
  G & Ctx' ++ G' |= Ctx |- M ::: A.
intros; rew_app;
apply BackgroundSubsetImpl with (G:=G++G'); auto;
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
Lemma Weakening_general:
  forall G w Gamma M A
  (HT: G |= (w, Gamma) |- M ::: A),
  (forall G' w' Delta Delta',
    G ~=~ (G' & (w', Delta)) ->
    ok_Bg ((w, Gamma) :: G' & (w', Delta ++ Delta')) ->
    G' & (w', Delta ++ Delta') |= (w, Gamma) |- M ::: A) /\
  (forall Gamma',
    ok_Bg ((w, Gamma ++ Gamma') :: G) ->
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
apply t_lam_LF with
  (L:=L \u used_t_vars ((w0, Gamma0) :: G' & (w', Delta ++ Delta')));
[ | intros; eapply H]; auto.
apply t_lam_LF with (L:=L \u used_t_vars ((w0, Gamma0++Gamma')::G));
[ | intros; eapply H with (v':=v')  (w:=w0) (Gamma:=(v' ,A)::Gamma0)]; auto;
rew_app; auto.
(* appl *)
econstructor; [ | eapply IHHT1| eapply IHHT2]; eauto.
econstructor; [ | eapply IHHT1| eapply IHHT2]; eauto.
(* box *)
apply t_box_LF with
  (L:=L \u used_w_vars (G' & (w0, Gamma0) & (w', Delta ++ Delta')));
intros;
assert (G' & (w', Delta ++ Delta') & (w0, Gamma0) ~=~
        G' & (w0, Gamma0) & (w', Delta ++ Delta')) by auto;
[ apply ok_Bg_ppermut with (G:=(w0, Gamma0) :: G' & (w', Delta ++ Delta')) |
  rewrite H3]; auto;
apply H with (w:=w'0) (Gamma:=nil);
[ | | rewrite H0 | rewrite H0 in Ok_Bg]; auto;
apply ok_Bg_fresh_wo; auto;
apply ok_Bg_ppermut with
  (G:=((w0, Gamma0) :: G' & (w', Delta ++ Delta')));
auto.
apply t_box_LF with (L:=L \u used_w_vars (G & (w0, Gamma0++Gamma')));
[ apply ok_Bg_ppermut with (G:= (w0, Gamma0++Gamma') :: G) |
  intros; eapply H]; auto;
apply ok_Bg_fresh_wo; auto;
apply ok_Bg_ppermut with (G:=(w0, Gamma0++Gamma')::G); auto.
(* unbox *)
constructor; [ | eapply IHHT]; eauto.
constructor; [ | eapply IHHT]; eauto.
(* unbox_fetch 1 *)
destruct (permut_context_LF_dec (w'0, Delta) (w, Gamma)) as [Eq|Neq];
simpl in *.
(* = *)
destruct Eq; subst;
assert (G ~=~ G'0) by
   (apply PPermut_last_rev with (Gamma := Gamma) (Gamma':= Delta) (w:=w);
    [ apply permut_sym |
      transitivity G' ]; auto);
assert ((w0, Gamma0) :: G'0 & (w, Delta ++ Delta') ~=~
        (w, Gamma ++ Delta') :: G & (w0, Gamma0)) by
  (rewrite H3;
   transitivity ((w, Delta ++ Delta') :: G'0 & (w0, Gamma0));
     [ transitivity ((w0, Gamma0) :: (w, Delta ++ Delta') :: G'0) | ]; auto;
       transitivity ((w, Delta ++ Delta') :: (w0, Gamma0) :: G'0); auto);
apply t_unbox_fetch_LF with (G:=G) (Gamma:=Gamma++Delta');
[rewrite <- H4 | apply IHHT | rewrite H3]; auto; rewrite <- H4; auto.
(* <> *)
assert (exists G0, exists G1, G'0 = G0 & (w, Gamma) ++ G1) as H2 by
  ( apply PPermut_split_neq with (G':=G) (w:=w'0) (Gamma := Delta);
    [ symmetry; transitivity G' | ]; auto);
destruct H2 as [GH]; destruct H2 as [GT]; subst G'0;
apply t_unbox_fetch_LF with
  (Gamma:=Gamma) (G:=GH ++ GT & (w'0, Delta ++ Delta')).
apply ok_Bg_ppermut with
  (G := (w0, Gamma0) :: (GH & (w, Gamma) ++ GT) & (w'0, Delta ++ Delta')); auto;
rew_app;
assert ( GH ++ (w, Gamma) :: GT & (w'0, Delta ++ Delta') ~=~
       (w, Gamma) :: GH ++ GT ++ (w'0, Delta ++ Delta') :: nil) by auto;
rewrite H2;
transitivity (((w, Gamma) :: GH ++ GT ++ (w'0, Delta ++ Delta') :: nil) &
  (w0, Gamma0)); [ | rew_app]; auto.
apply PPermut_bg with (G:= (GH ++ GT & (w0, Gamma0)) & (w'0, Delta ++ Delta')).
 apply IHHT with (w1:=w) (Gamma1:=Gamma) (G':=GH ++ GT & (w0, Gamma0));
 assert (G ~=~ GH ++ GT & (w'0, Delta)) by
   ( apply PPermut_last_rev_simpl with (a:=(w, Gamma)); transitivity G';
     [ | rew_app in *; transitivity (GH ++ (w, Gamma) :: GT & (w'0, Delta))];
     auto);
 [ |
   rewrite H2; rew_app |
   apply ok_Bg_ppermut with (G:= (w0, Gamma0) :: GH ++ (w, Gamma) :: GT &
     (w'0, Delta ++ Delta'))]; rew_app in *; auto;
  transitivity (((w0, Gamma0) :: GH ++ GT ++ (w, Gamma) :: nil) &
    (w'0, Delta++Delta')); [rew_app | ]; auto;
  transitivity (((w, Gamma) :: GH ++ GT ++ (w0, Gamma0) :: nil) &
    (w'0, Delta ++ Delta')); [ | rew_app]; auto.
  rew_app; auto.
rew_app; transitivity (GH ++ GT ++ (w, Gamma) :: (w'0, Delta++Delta') :: nil);
[ | symmetry]; auto.
(* unbox_fetch 2 *)
apply t_unbox_fetch_LF with (G:=G) (Gamma:=Gamma);
rewrite <- H in H0; [ | apply IHHT with (w1:=w) (Gamma1:=Gamma) |]; auto.
(* here *)
constructor; [ | apply IHHT with (w:=w0)(Gamma:=Gamma0)]; auto.
constructor; [ | apply IHHT]; auto.
(* get_here 1 *)
destruct (permut_context_LF_dec (w', Delta) (w, Gamma)) as [Eq|Neq];
simpl in *.
(* = *)
destruct Eq; subst;
assert (G ~=~ G'0) by
   (apply PPermut_last_rev with (Gamma := Gamma) (Gamma':= Delta) (w:=w);
    [ apply permut_sym |
      transitivity G' ]; auto);
assert ((w0, Gamma0) :: G'0 & (w, Delta ++ Delta') ~=~
        (w, Gamma ++ Delta') :: G & (w0, Gamma0)) by
  (rewrite H3;
   transitivity ((w, Delta ++ Delta') :: G'0 & (w0, Gamma0));
     [ transitivity ((w0, Gamma0) :: (w, Delta ++ Delta') :: G'0) | ]; auto;
       transitivity ((w, Delta ++ Delta') :: (w0, Gamma0) :: G'0); auto);
apply t_get_here_LF with (G:=G) (Gamma:=Gamma++Delta');
[rewrite <- H4 | apply IHHT | rewrite H3]; auto; rewrite <- H4; auto.
(* <> *)
assert (exists G0, exists G1, G'0 = G0 & (w, Gamma) ++ G1) as H2 by
  ( apply PPermut_split_neq with (G':=G) (w:=w') (Gamma := Delta);
    [ symmetry; transitivity G' | ]; auto);
destruct H2 as [GH]; destruct H2 as [GT]; subst G'0;
apply t_get_here_LF with
  (Gamma:=Gamma) (G:=GH ++ GT & (w', Delta ++ Delta')).
apply ok_Bg_ppermut with
  (G := (w0, Gamma0) :: (GH & (w, Gamma) ++ GT) & (w', Delta ++ Delta')); auto;
rew_app;
assert ( GH ++ (w, Gamma) :: GT & (w', Delta ++ Delta') ~=~
       (w, Gamma) :: GH ++ GT ++ (w', Delta ++ Delta') :: nil) by auto;
rewrite H2;
transitivity (((w, Gamma) :: GH ++ GT ++ (w', Delta ++ Delta') :: nil) &
  (w0, Gamma0)); [ | rew_app]; auto.
apply PPermut_bg with (G:= (GH ++ GT & (w0, Gamma0)) & (w', Delta ++ Delta')).
 apply IHHT with (w1:=w) (Gamma1:=Gamma) (G':=GH ++ GT & (w0, Gamma0));
 assert (G ~=~ GH ++ GT & (w', Delta)) by
   ( apply PPermut_last_rev_simpl with (a:=(w, Gamma)); transitivity G';
     [ | rew_app in *; transitivity (GH ++ (w, Gamma) :: GT & (w', Delta))];
     auto);
 [ |
   rewrite H2; rew_app |
   apply ok_Bg_ppermut with (G:= (w0, Gamma0) :: GH ++ (w, Gamma) :: GT &
     (w', Delta ++ Delta'))]; rew_app in *; auto;
  transitivity (((w0, Gamma0) :: GH ++ GT ++ (w, Gamma) :: nil) &
    (w', Delta++Delta')); [rew_app | ]; auto;
  transitivity (((w, Gamma) :: GH ++ GT ++ (w0, Gamma0) :: nil) &
    (w', Delta ++ Delta')); [ | rew_app]; auto.
  rew_app; auto.
rew_app; transitivity (GH ++ GT ++ (w, Gamma) :: (w', Delta++Delta') :: nil);
[ | symmetry]; auto.
(* get_here 2 *)
apply t_get_here_LF with (G:=G) (Gamma:=Gamma);
rewrite <- H in H0; [ | apply IHHT with (w1:=w) (Gamma1:=Gamma) |]; auto.
(* letdia *)
apply t_letdia_LF with (A:=A)
  (L_w:=L_w \u used_w_vars((w0, Gamma0) :: G' & (w', Delta ++ Delta')))
  (L_t:=L_t \u used_t_vars ((w0, Gamma0) :: G' & (w', Delta ++ Delta')));
[ | apply IHHT with (w:=w0) (Gamma:=Gamma0) | ]; auto;
intros; destruct H with (v':=v') (w':=w'0) (w:=w0) (Gamma:=Gamma0); auto;
replace ((w'0, (v', A) :: nil) :: G' & (w', Delta ++ Delta')) with
   (((w'0, (v', A) :: nil) :: G') & (w', Delta ++ Delta')) by
   (rew_app; reflexivity);
apply H4; rew_app; auto;
apply ok_Bg_ppermut with
  (G:=(w'0, (v', A) :: nil) :: (w0, Gamma0) :: G' & (w', Delta ++ Delta'));
auto.
eapply t_letdia_LF with (A:=A)
  (L_t := L_t \u used_t_vars ((w0, Gamma0 ++ Gamma') :: G))
  (L_w := L_w \u used_w_vars ((w0, Gamma0 ++ Gamma') :: G));
[ | apply IHHT | ]; auto;
intros; eapply H; auto;
apply ok_Bg_ppermut with
  (G:=(w', (v', A) :: nil) :: (w0, Gamma0 ++ Gamma') :: G);
auto.
(* letdia_get 1 *)
destruct (permut_context_LF_dec (w', Delta) (w, Gamma)) as [Eq | Neq];
simpl in *.
(* = *)
destruct Eq; subst;
assert (G ~=~ G') by
  (apply PPermut_last_rev with (w:=w) (Gamma:=Gamma) (Gamma':=Delta);
   [apply permut_sym | transitivity G0]; auto);
apply t_letdia_get_LF with (Gamma:=Gamma++Delta') (G:=G) (A:=A)
  (L_w:=L_w \u used_w_vars ((w0, Gamma0) :: G' & (w, Gamma ++ Delta')))
  (L_t:=L_t \u used_t_vars ((w0, Gamma0) :: G & (w, Gamma ++ Delta'))).
apply ok_Bg_ppermut with (G:=(w0, Gamma0) :: G' & (w, Delta ++ Delta'));
[rewrite <- H4 | auto];
transitivity ((w, Delta ++ Delta') :: G & (w0, Gamma0)); auto.
apply IHHT; auto;
apply ok_Bg_ppermut with (G:=(w0, Gamma0) :: G' & (w, Delta ++ Delta'));
[rewrite <- H4 | auto];
transitivity ((w, Delta ++ Delta') :: G & (w0, Gamma0)); auto.
intros; destruct H with (v':=v') (w':=w') (w1:=w0) (Gamma1:=Gamma0); eauto;
replace ( (w', (v', A) :: nil) :: G & (w, Gamma ++ Delta') ) with
  (( (w', (v', A) :: nil) :: G) & (w, Gamma ++ Delta')) by
  (rew_app; reflexivity);
eapply H7; auto;
apply ok_Bg_ppermut with
  (G:=(w', (v', A) :: nil ) :: (w0, Gamma0) :: G & (w, Gamma ++ Delta'));
[ rew_app | rewrite H4]; auto;
apply ok_Bg_fresh_wo_te;
[ apply ok_Bg_ppermut with (G:=(w0, Gamma0) :: G' & (w, Delta ++ Delta')) | ];
auto.
rewrite <- H4; auto.
(* <> *)
assert (exists G0, exists G1, G' = G0 & (w, Gamma) ++ G1) by
  ( apply PPermut_split_neq with (G':=G) (w:=w') (Gamma := Delta);
    [ symmetry; transitivity G0 | ]; auto);
destruct H3 as [GH]; destruct H3 as [GT]; subst G';
assert (G ~=~ GH ++ GT & (w', Delta)) by
  ( apply PPermut_last_rev_simpl with (a:=(w, Gamma));
    transitivity G0; auto;
    rew_app in *; transitivity (GH ++ (w, Gamma) :: GT & (w', Delta)); auto;
    transitivity (GH ++ GT ++ (w, Gamma) :: (w', Delta) :: nil); auto);
apply t_letdia_get_LF with
  (Gamma:=Gamma) (G:=GH ++ GT & (w', Delta ++ Delta'))
  (L_w:=L_w \u used_w_vars ((w0, Gamma0) :: (GH & (w, Gamma) ++ GT) &
    (w', Delta ++ Delta')))
  (L_t:=L_t \u used_t_vars ((w0, Gamma0) :: (GH & (w, Gamma) ++ GT) &
    (w', Delta ++ Delta')))(A:=A).
apply ok_Bg_ppermut with
  (G:=(w0, Gamma0) :: (GH & (w, Gamma) ++ GT) & (w', Delta ++ Delta'));
rew_app in *; auto;
transitivity ((w0, Gamma0) :: (w, Gamma) :: GH ++ GT & (w', Delta ++ Delta'));
auto;
transitivity (((w,Gamma) :: GH ++ GT & (w', Delta++Delta')) & (w0, Gamma0));
[ | rew_app]; auto.
apply PPermut_bg with (G:= (GH ++ GT & (w0, Gamma0)) & (w', Delta ++ Delta'));
[ | rew_app]; auto;
apply IHHT with (w1:=w) (Gamma1:=Gamma); auto;
[ rewrite H3 | ]; rew_app; auto;
rew_app; apply ok_Bg_ppermut with
  (G:=(w0, Gamma0) :: (GH & (w, Gamma) ++ GT) & (w', Delta ++ Delta')); auto;
rew_app;
transitivity ((w0, Gamma0) :: (w, Gamma) :: GH ++ GT & (w', Delta ++ Delta'));
auto;
transitivity (((w,Gamma) :: GH ++ GT & (w', Delta++Delta')) & (w0, Gamma0));
[ | rew_app]; auto.
intros; destruct H with (v':=v')(w':=w'0) (w1:=w0) (Gamma1:=Gamma0); auto;
apply PPermut_bg with
  (G:=((w'0, (v', A)::nil) :: GH++GT & (w, Gamma)) & (w', Delta ++ Delta'));
[ | rew_app]; auto;
apply H6; rew_app; [constructor | ]; auto;
[ rewrite H3; rew_app; auto | ];
apply ok_Bg_ppermut with
  (G:= ((w'0, (v', A) :: nil) ::(w0, Gamma0) :: GH & (w, Gamma) ++ GT) &
    (w', Delta ++ Delta')); rew_app; auto;
[ transitivity (((w'0, (v', A) :: nil) ::(w0, Gamma0) :: GH ++GT & (w, Gamma))
  & (w', Delta ++ Delta')); rew_app |
 rew_app in *; apply ok_Bg_fresh_wo_te]; auto.
rew_app; auto.
(* letdia_get 2 *)
apply t_letdia_get_LF with (G:=G) (Gamma:=Gamma) (A:=A)
  (L_w:=L_w \u used_w_vars (((w0, Gamma0 ++ Gamma') :: G & (w, Gamma))))
  (L_t:=L_t \u used_t_vars ((w0, Gamma0 ++ Gamma') :: G & (w, Gamma))).
rewrite <- H0 in H1; apply ok_Bg_ppermut with
  (G:=(w0, Gamma0 ++ Gamma') :: G & (w, Gamma)); auto.
apply IHHT with (w1:=w) (Gamma1:=Gamma); auto.
rewrite <- H0 in H1; apply ok_Bg_ppermut with
  (G:=(w0, Gamma0 ++ Gamma') :: G & (w, Gamma)); auto.
intros; destruct H with (v':=v')(w':=w') (w1:=w0)(Gamma1:=Gamma0); auto;
apply H5; apply ok_Bg_ppermut with
  (G:= (w', (v', A)::nil) :: (w0, Gamma0 ++ Gamma') :: G & (w, Gamma));
[ | apply ok_Bg_fresh_wo_te ]; auto; rewrite H0; auto.
assumption.
Qed.

Lemma WeakeningBackgroundElem:
forall G G' w Delta Delta' Ctx M A
  (H_ok: ok_Bg (Ctx :: G & (w, Delta ++ Delta') ++ G'))
  (HT: G & (w, Delta) ++ G' |= Ctx |- M ::: A),
  G & (w, Delta ++ Delta') ++ G' |= Ctx |- M ::: A.
intros;
assert ( G & (w, Delta ++ Delta') ++ G' ~=~ (G++G') & (w, Delta ++ Delta'))
  by (rew_app; auto);
rewrite H;
destruct Ctx; eapply Weakening_general; auto.
rew_app; assert (G ++ G' & (w, Delta) ~=~ G & (w, Delta) ++ G') by auto;
rewrite H0; assumption.
apply ok_Bg_ppermut with (G:=(v, l) :: G & (w, Delta ++ Delta') ++ G'); auto.
Qed.

Lemma Weakening:
forall G w Gamma Gamma' M A
  (H_ok: ok_Bg ((w,Gamma++Gamma')::G))
  (HT: G |= (w, Gamma) |- M ::: A),
  G |= (w, Gamma ++ Gamma') |- M ::: A.
intros;
eapply Weakening_general; eassumption.
Qed.

(*
   When we can prove something in empty context and background, then we
   can also do it in any "full" version of this context & background
   Proof: ???
*)
(* FIXME *)
Lemma types_weakened:
forall G w Gamma M A
  (Ok: ok_Bg ((w, Gamma)::G))
  (Ht: emptyEquiv G |= (w, nil) |- M ::: A),
  G |= (w, Gamma) |- M ::: A.
Admitted.


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
Lemma subst_t_preserv_types:
forall G w Gamma B M N v A
  (H_lc_t: lc_t_LF M)
  (H_lc_w: lc_w_LF M)
  (HT: G |= (w, Gamma) |- N ::: B),
  (* "inner" substitution *)
  ( forall Gamma0,
    permut Gamma ((v, A) :: Gamma0) ->
    emptyEquiv G |= (w, nil) |- M ::: A ->
    G |= (w, Gamma0) |- [M // fte v] N ::: B)
  /\
  (* "outer" substitution *)
  ( forall G0 G' G'' w' Gamma',
    G ~=~ (G0 & (w', (v,A)::Gamma')) ->
    G' ~=~ (G0 & (w, Gamma)) ->
    G'' ~=~ (G0 & (w', Gamma')) ->
    emptyEquiv G' |= (w', nil) |- M ::: A ->
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
assert (A = A0) by (eapply ok_Bg_Mem_eq; eauto);
subst; apply types_weakened;
[eapply ok_Bg_permut_first_tail | ]; eauto.
constructor;
[ apply ok_Bg_permut_first_tail with (C:=Gamma0) (x:=v0) (A:=A0) |
  apply Mem_permut with (L2 := (v0, A0) :: Gamma1) in HT]; auto;
rewrite Mem_cons_eq in HT; destruct HT; auto;
inversion H2; subst; elim H1; reflexivity.

case_if.
inversion H3; subst;
eapply ok_Bg_Mem_contradict in Ok_Bg;
contradiction || eauto.
constructor; auto;
apply ok_Bg_ppermut with (G:=((w0, Gamma0)::G0) & (w', Gamma'));
[ rewrite H1 |
  eapply ok_Bg_permut_no_last; rewrite H in Ok_Bg; rew_app]; eauto.

(* lam *)
apply t_lam_LF with (L:=L \u \{v});
[ apply ok_Bg_permut_first_tail with (C:=Gamma0) (x:=v) (A:=A0) |
  intros]; auto;
rewrite notin_union in H2; rewrite notin_singleton in H2; destruct H2;
unfold open_var in *;
rewrite <- subst_t_comm; auto;
eapply H; auto;
permut_simpl || rew_app; eauto.

apply t_lam_LF with (L:=L \u \{v});
[ apply ok_Bg_ppermut with (G:=((w0, Gamma0)::G0) & (w', Gamma'));
  [ rewrite H2 |
    rewrite H0 in Ok_Bg; rew_app] |
  intros]; eauto;
rewrite notin_union in H4; rewrite notin_singleton in H4; destruct H4;
unfold open_var in *;
rewrite <- subst_t_comm; auto;
eapply H with (G0:=G0) (w':=w'); eauto;
assert (emptyEquiv G' ~=~ emptyEquiv (G0 ++ nil & (w0, (v', A) :: Gamma0))) as E
 by (rewrite H1; rew_app; eapply emptyEquiv_last_change; eauto);
rew_app in *; rewrite <- E; auto.

(* appl *)
econstructor;  [ | eapply IHHT1 | eapply IHHT2];
try apply ok_Bg_permut_first_tail with (C:=Gamma0) (x:=v) (A:=A0); eauto.

econstructor;
[ apply ok_Bg_ppermut with (G:=((w0, Gamma0)::G0) & (w', Gamma'));
  [rewrite H1 | rewrite H in Ok_Bg] |
  eapply IHHT1 |
  eapply IHHT2]; eauto.

(* box *)
apply t_box_LF with (L:=L \u used_w_vars (emptyEquiv G & (w0, nil)));
[ apply ok_Bg_permut_no_last with (v:=v) (A:=A0);
  eapply ok_Bg_permut_last |
  intros; unfold open_ctx]; eauto;
rewrite <- subst_order_irrelevant_bound;
[ eapply H; eauto |
  repeat rewrite emptyEquiv_rewrite];
simpl; rew_app; auto;
apply BackgroundSubsetImpl with (G:=emptyEquiv G); auto;
[ exists ((w', (@nil (prod var ty))) :: nil); rew_app; auto |
  assert ((w0, nil) :: emptyEquiv G & (w', nil) ~=~
    (w', nil) :: emptyEquiv G & (w0, nil)) by auto];
rew_app; rewrite emptyEquiv_rewrite_last; simpl; auto;
rewrite H3;
apply ok_Bg_fresh_wo; auto;
apply emptyEquiv_ok in Ok_Bg;
rewrite emptyEquiv_rewrite in Ok_Bg;
simpl in *; auto.

apply t_box_LF with
  (L:=L \u used_w_vars(emptyEquiv G0 ++ (w', nil) :: (w0, nil) :: nil));
[ rewrite H2; rewrite H0 in Ok_Bg |
  intros; unfold open_ctx; rewrite <- subst_order_irrelevant_bound]; eauto;
eapply H with (G'' := G'' & (w0, Gamma0)) (G0:=G0 & (w0, Gamma0)) (w'0:=w')
  (Gamma':=Gamma') (A0:=A0); auto;
repeat rewrite emptyEquiv_rewrite;
simpl; rew_app;
apply BackgroundSubsetImpl with (G:=emptyEquiv G0 & (w0, nil));
[ rewrite H1 in H3; rewrite emptyEquiv_rewrite in H3 |
  exists ((w'0, (@nil (var * ty)))::nil); rew_app |
  apply emptyEquiv_ok in Ok_Bg; rewrite H0 in Ok_Bg]; auto;
repeat rewrite emptyEquiv_rewrite in Ok_Bg;
simpl in *; rew_app in *;
apply ok_Bg_ppermut with
  (G:=(w'0, nil) :: emptyEquiv G0 ++ (w', nil) :: (w0, nil) :: nil);
[ transitivity ((w', nil) :: (w'0, nil):: emptyEquiv G0 & (w0, nil)); auto;
  transitivity ((w'0, nil) :: (w', nil) :: emptyEquiv G0 & (w0, nil)) |
    apply ok_Bg_fresh_wo];
auto.

(* unbox *)
econstructor; [ | eapply IHHT];
try apply ok_Bg_permut_first_tail with (C:=Gamma0) (x:=v) (A:=A0); eauto.

econstructor;
[ rewrite H1; rewrite H in Ok_Bg |
  eapply IHHT]; eauto.

(* unbox_fetch *)
apply t_unbox_fetch_LF with (G:=G) (Gamma:=Gamma); auto;
[ apply ok_Bg_permut_no_last_spec with (v:=v) (A:=A0);
  apply ok_Bg_ppermut with (G:= (w, Gamma) :: G & (w0, Gamma0)) |
  eapply IHHT; eauto; rewrite <- H in H1; rew_app]; auto.

destruct (eq_var_dec w w'0).
(* = *)
subst;
assert (G ~=~ G0 /\ Gamma *=* (v, A0) :: Gamma'0) as HP by
  (apply ok_Bg_impl_ppermut with (w:=w'0); eauto);
destruct HP;
apply t_unbox_fetch_LF with (G:=G) (Gamma:=Gamma'0);
eauto;
specialize IHHT with (Gamma1:=Gamma) (w:=w'0);
destruct IHHT with (M0:=M0) (A0:=A0) (v:=v); auto;
apply H6; eauto;
rewrite H1 in H3; rewrite H4; auto.
(* <> *)
assert (exists GH, exists GT, G = GH & (w'0, (v, A0)::Gamma'0) ++ GT) as HP by
  (apply PPermut_split_neq with (w:=w) (Gamma:=Gamma) (G':=G0); eauto);
destruct HP as (GH, HP); destruct HP as (GT, HP);
apply t_unbox_fetch_LF with (G:=GH ++ GT & (w'0, Gamma'0)) (Gamma:=Gamma).
subst;
apply ok_Bg_ppermut with
  (G:= (((w, Gamma) :: (GH & (w0, Gamma0) ++ GT)) & (w'0, Gamma'0)));
[rew_app | ]; auto;
apply ok_Bg_permut_no_last_spec with (v:=v)(A:=A0);
apply ok_Bg_ppermut with
  (G:=(w, Gamma):: (GH & (w'0, (v, A0) :: Gamma'0) ++ GT) & (w0, Gamma0));
rew_app in *; auto.
eapply IHHT with (w1:=w) (Gamma1:=Gamma) (w':=w'0) (Gamma':=Gamma'0)
                 (G0:=GH ++ GT & (w0, Gamma0)); rew_app; auto; subst;
rew_app; auto;
rewrite H1 in H3;
assert (GH ++ (w, Gamma) :: GT ~=~ G0) by
  (apply PPermut_last_rev_simpl with (a:=(w'0, (v, A0) :: Gamma'0));
  rew_app in *; rewrite <- H0; rewrite <- H; auto);
assert (GH ++ (w, Gamma) :: GT & (w0, Gamma0) ~=~ G0 & (w0,Gamma0)) by
  (rewrite <- H4; rew_app; auto);
rewrite H5; auto.
subst; rew_app in *;
transitivity (G0 & (w'0, Gamma'0)); [ | symmetry]; eauto.

(* here *)
econstructor; [ | eapply IHHT];
try apply ok_Bg_permut_first_tail with (C:=Gamma0) (x:=v) (A:=A0); eauto.

econstructor;
[ rewrite H1; rewrite H in Ok_Bg |
  eapply IHHT]; eauto.

(* get_here *)
apply t_get_here_LF with (G:=G) (Gamma:=Gamma); auto;
[ apply ok_Bg_permut_no_last_spec with (v:=v) (A:=A0);
  apply ok_Bg_ppermut with (G:= (w, Gamma) :: G & (w0, Gamma0)) |
  eapply IHHT; eauto; rewrite <- H in H1; rew_app]; auto.

destruct (eq_var_dec w w').
(* = *)
subst;
assert (G ~=~ G0 /\ Gamma *=* (v, A0) :: Gamma') as HP by
  (apply ok_Bg_impl_ppermut with (w:=w'); eauto);
destruct HP;
apply t_get_here_LF with (G:=G) (Gamma:=Gamma');
eauto;
specialize IHHT with (Gamma1:=Gamma) (w:=w');
destruct IHHT with (M0:=M0) (A0:=A0) (v:=v); auto;
apply H7; eauto;
rewrite H1 in H3; rewrite H5; auto.
(* <> *)
assert (exists GH, exists GT, G = GH & (w', (v, A0)::Gamma') ++ GT) as HP by
  (apply PPermut_split_neq with (w:=w) (Gamma:=Gamma) (G':=G0); eauto);
destruct HP as (GH, HP); destruct HP as (GT, HP);
apply t_get_here_LF with (G:=GH ++ GT & (w', Gamma')) (Gamma:=Gamma).
subst;
apply ok_Bg_ppermut with
  (G:= (((w, Gamma) :: (GH & (w0, Gamma0) ++ GT)) & (w', Gamma')));
[rew_app | ]; auto;
apply ok_Bg_permut_no_last_spec with (v:=v)(A:=A0);
apply ok_Bg_ppermut with
  (G:=(w, Gamma):: (GH & (w', (v, A0) :: Gamma') ++ GT) & (w0, Gamma0));
rew_app in *; auto.
eapply IHHT with (w1:=w) (Gamma1:=Gamma) (w':=w') (Gamma':=Gamma')
                 (G0:=GH ++ GT & (w0, Gamma0)); rew_app; auto; subst;
rew_app; auto;
rewrite H1 in H3;
assert (GH ++ (w, Gamma) :: GT ~=~ G0) by
  (apply PPermut_last_rev_simpl with (a:=(w', (v, A0) :: Gamma'));
  rew_app in *; rewrite <- H0; rewrite <- H; auto);
assert (GH ++ (w, Gamma) :: GT & (w0, Gamma0) ~=~ G0 & (w0,Gamma0)) by
  (rewrite <- H5; rew_app; auto);
rewrite H6; auto.
subst; rew_app in *;
transitivity (G0 & (w', Gamma')); [ | symmetry]; eauto.

(* letdia *)
apply t_letdia_LF with
  (L_t := L_t \u \{v})
  (L_w := L_w \u used_w_vars ((w0, nil) :: emptyEquiv G)) (A:=A);
[ apply ok_Bg_permut_first_tail with (C:=Gamma0) (x:=v) (A:=A0) |
  eapply IHHT |
  intros]; eauto;
unfold open_var in *; unfold open_ctx in *;
rewrite notin_union in H2; rewrite notin_singleton in H2; destruct H2;
rewrite <- subst_order_irrelevant_bound;
[ rewrite <- subst_t_comm | assumption ];
[ eapply H | |] ; eauto;
apply BackgroundSubsetImpl with (G:=emptyEquiv G); auto;
[ eauto | ];
assert ((w0, nil) :: (w', nil) :: emptyEquiv G ~=~
  (w',nil) :: (w0, nil) :: emptyEquiv G) by auto;
rewrite H5; apply ok_Bg_fresh_wo;
[ apply emptyEquiv_ok in Ok_Bg;  simpl in * | ]; auto.

eapply t_letdia_LF with
  (L_t := L_t \u \{v})
  (L_w := L_w \u  used_w_vars ((w', nil) :: emptyEquiv (G0 & (w0, Gamma0))));
[ rewrite H2; rewrite H0 in Ok_Bg | eapply IHHT | intros]; eauto;
unfold open_var in *; unfold open_ctx in *;
rewrite notin_union in H4; rewrite notin_singleton in H4; destruct H4;
rewrite <- subst_order_irrelevant_bound;
[ rewrite <- subst_t_comm | assumption ];
[ eapply H with (G0:=(w'0, (v',A)::nil)::G0) (w'0:=w')
  (Gamma':=Gamma') (A0:=A0) | | ]; eauto;
rew_app; rewrite H1 in H3; rew_app in *; simpl;
apply BackgroundSubsetImpl with (G:= emptyEquiv (G0 & (w0, Gamma0))); auto;
[eauto | ];
assert ((w'0, nil) :: (w', nil)::emptyEquiv(G0 & (w0, Gamma0)) ~=~
  (w', nil) :: (w'0, nil) :: emptyEquiv (G0 & (w0, Gamma0))) by auto;
rewrite <- H7; apply ok_Bg_fresh_wo;
[rewrite H0 in Ok_Bg; apply emptyEquiv_ok in Ok_Bg | ]; auto;
  assert (emptyEquiv((w', (v, A0) :: Gamma') :: G0 & (w0, Gamma0)) ~=~
    (w', nil) :: emptyEquiv (G0 & (w0, Gamma0))) by (simpl; auto);
rewrite <- H8;
assert ((w0, Gamma0) :: G0 & (w', (v, A0) :: Gamma') ~=~
  ((w', (v, A0) :: Gamma') :: G0 & (w0, Gamma0))) by auto;
rewrite <- H9; auto.

(* letdia_get *)
assert (w <> w0) by eauto;
eapply t_letdia_get_LF with (G:=G) (Gamma:=Gamma) (L_t := L_t \u \{v})
  (L_w:=L_w \u used_w_vars ((w0, nil) :: emptyEquiv (G & (w, Gamma)))); auto.
apply ok_Bg_permut_no_last_spec with (v:=v) (A:=A0);
apply ok_Bg_ppermut with (G:= (w, Gamma) :: G & (w0, Gamma0)); auto.
eapply IHHT; eauto.
rew_app; rewrite <- H0 in H2; auto.
intros; unfold open_var in *; unfold open_ctx in *;
rewrite notin_union in H5; rewrite notin_singleton in H5; destruct H5;
rewrite <- subst_order_irrelevant_bound;
[rewrite <- subst_t_comm | ]; auto;
eapply H; eauto;
rewrite <- H0 in H2;
apply BackgroundSubsetImpl with (G:=emptyEquiv (G & (w, Gamma))); auto;
[ eauto | ];
assert ((w0, nil) :: (w', nil) :: emptyEquiv (G & (w, Gamma)) ~=~
  (w', nil) :: (w0, nil) ::emptyEquiv (G & (w, Gamma))); auto;
rewrite H8;
apply ok_Bg_fresh_wo; [apply emptyEquiv_ok in Ok_Bg | auto];
assert ((w, Gamma) :: G & (w0, Gamma0) ~=~ (w0, Gamma0):: G & (w, Gamma)) by
  auto;
rewrite H9 in Ok_Bg; simpl in Ok_Bg; auto.

assert (w <> w0) by eauto;
destruct (eq_var_dec w w'); subst.
(* = *)
assert (G ~=~ G1 /\ Gamma *=* (v, A0) :: Gamma') by
  (apply ok_Bg_impl_ppermut with (w:=w');
    [ | rewrite H0; rewrite <- H1]; eauto);
destruct H7;
eapply t_letdia_get_LF with (G:=G) (Gamma:=Gamma') (L_t:=L_t \u \{v})
  (L_w:=L_w \u used_w_vars ((w', nil) :: emptyEquiv (G1 & (w0, Gamma0)))); auto;
[eauto | eapply IHHT; eauto; rewrite H2 in H4; rewrite H7; auto | | ].
intros; unfold open_var in *; unfold open_ctx in *;
rewrite notin_union in H9; rewrite notin_singleton in H9; destruct H9;
rewrite <- subst_order_irrelevant_bound;
[ rewrite <- subst_t_comm | ]; auto;
eapply H with (v:=v); eauto; rew_app;
rewrite H2 in H4; rewrite H7;
apply BackgroundSubsetImpl with (G:=emptyEquiv (G1 & (w0, Gamma0))); auto.
exists (((w'0, (@nil (prod var ty))) :: nil)); rew_app; simpl; auto.
assert ((w', nil) :: (w'0, nil) :: emptyEquiv (G1 & (w0, Gamma0)) ~=~
  (w'0, nil) :: (w',nil) :: emptyEquiv (G1 & (w0, Gamma0))) by auto;
rewrite H12; apply ok_Bg_fresh_wo; auto;
assert ((w', nil) :: emptyEquiv (G1 & (w0, Gamma0)) ~=~
  emptyEquiv ((w', Gamma) :: G & (w0, Gamma0))) by
  (simpl in *; rewrite H7; auto);
rewrite H13; apply emptyEquiv_ok in Ok_Bg; auto.
symmetry; rewrite H7; auto.
(* <> *)
assert (G & (w, Gamma) ~=~ G1 & (w', (v, A0) :: Gamma')) by
  (transitivity G0; auto);
symmetry in H7;
assert (exists GH, exists GT, G1 = GH & (w, Gamma) ++ GT) by
  (apply PPermut_split_neq with (w:=w') (Gamma:=(v,A0) :: Gamma') (G':=G);
    auto);
destruct H8 as (GH, H8); destruct H8 as (GT, H8);
eapply t_letdia_get_LF with (G:=GH++GT & (w', Gamma')) (Gamma:=Gamma)
  (L_t:=L_t \u \{v}) (L_w:=L_w \u used_w_vars
     ((w', nil) :: emptyEquiv (GH ++ GT ++ (w, Gamma) :: (w0, Gamma0) :: nil))).
assert (G & (w, Gamma) & (w0, Gamma0) ~=~ (w, Gamma) :: G & (w0, Gamma0)) by
  auto;
rewrite <- H9 in Ok_Bg; rewrite <- H7 in Ok_Bg; rewrite H8 in Ok_Bg;
subst; apply ok_Bg_ppermut with
  (G:=((w, Gamma) :: (GH & (w', Gamma') ++ GT) & (w0, Gamma0))); [ | rew_app];
auto;
apply ok_Bg_ppermut with
  (G:= (((w, Gamma) :: (GH & (w0, Gamma0) ++ GT)) & (w', Gamma')));
[rew_app; auto | apply ok_Bg_permut_no_last_spec with (v:=v)(A:=A0)];
apply ok_Bg_ppermut with
  ((GH & (w, Gamma) ++ GT) & (w', (v, A0) :: Gamma') & (w0, Gamma0));
[ rew_app | ]; auto.
eapply IHHT with (w1:=w) (Gamma1:=Gamma) (A0:=A0) (w':=w')
  (G0:=GH++GT & (w0,Gamma0)) (Gamma':=Gamma'); auto;
[ symmetry; subst; rew_app in * | rew_app | ]; eauto;
rewrite H2 in H4; rewrite H8 in H4;
assert ((GH & (w, Gamma) ++ GT) & (w0, Gamma0) ~=~
  (GH ++ GT & (w0, Gamma0)) ++ nil & (w, Gamma)) by (rew_app; auto);
rewrite <- H9; auto.
intros; unfold open_var in *; unfold open_ctx in *;
rewrite notin_union in H9; rewrite notin_singleton in H9; destruct H9;
rewrite <- subst_order_irrelevant_bound;
[rewrite <- subst_t_comm | ]; auto;
eapply H with (v':=v') (w':=w'0) (Gamma1:=Gamma0) (w1:=w0) (A0:=A0)
              (v:=v) (G0:=(w'0, (v', A) :: nil) :: (GH ++ GT) & (w, Gamma))
              (w'0:=w') (Gamma':=Gamma'); auto.
rew_app; constructor; auto.
symmetry; transitivity (G1 & (w', (v, A0) :: Gamma')); auto;
subst; rew_app; auto.
rew_app; constructor; auto.
rew_app; rewrite H2 in H4; rewrite H8 in H4; simpl;
apply BackgroundSubsetImpl with
  (G:=emptyEquiv (GH ++ GT ++ (w, Gamma) :: (w0, Gamma0) :: nil)); auto.
assert (GH ++ GT ++ (w, Gamma) :: (w0, Gamma0) :: nil ~=~
  (GH & (w, Gamma) ++ GT) & (w0, Gamma0)) by (rew_app; auto);
rewrite H12; auto.
eauto.
assert ((w, Gamma) :: G & (w0, Gamma0) ~=~ G0 & (w0, Gamma0)) by
  (rewrite <- H0; auto);
rewrite H12 in Ok_Bg; rewrite H1 in Ok_Bg; subst;
assert ((w', nil)
      :: (w'0, nil)
         :: emptyEquiv (GH ++ GT ++ (w, Gamma) :: (w0, Gamma0) :: nil) ~=~
      (w'0, nil)
      :: (w', nil)
         :: emptyEquiv (GH ++ GT ++ (w, Gamma) :: (w0, Gamma0) :: nil)) by auto;
rewrite H8; apply ok_Bg_fresh_wo;
assert ( ((GH & (w, Gamma) ++ GT) & (w', (v, A0) :: Gamma')) & (w0, Gamma0) ~=~
  ((w', (v, A0) :: Gamma') :: GH ++ GT ++ (w, Gamma) :: nil) &  (w0, Gamma0)) by
  (eapply PPermut_last; auto);
rew_app in *; [rewrite H13 in Ok_Bg | auto];
apply emptyEquiv_ok in Ok_Bg; simpl in *; auto.
symmetry; transitivity (G1 & (w', Gamma')); subst; rew_app in *; auto.
Qed.

Lemma subst_t_preserv_types_inner:
forall G w Gamma A B M N v
  (H_lc_t: lc_t_LF M)
  (H_lc_w: lc_w_LF M)
  (HT: G |= (w, (v, A) :: Gamma) |- N ::: B)
  (HM: emptyEquiv G |= (w, nil) |- M ::: A),
  G |= (w, Gamma) |- [M//fte v] N ::: B.
intros; eapply subst_t_preserv_types with (Gamma := (v, A) :: Gamma); eauto.
Qed.

Lemma subst_t_preserv_types_outer:
forall G0 G G' G'' w w' Gamma Gamma' A B M N v
  (H_lc_t: lc_t_LF M)
  (H_lc_w: lc_w_LF M)
  (G0G: G ~=~ (G0 & (w', (v, A) :: Gamma')))
  (G0G': G' ~=~ (G0 & (w, Gamma)))
  (G0G'': G'' ~=~ (G0 & (w', Gamma')))
  (HM: emptyEquiv G' |= (w', nil) |- M ::: A)
  (HT: G |= (w, Gamma) |- N ::: B),
  G'' |= (w, Gamma) |- [M // fte v] N ::: B.
intros; eapply subst_t_preserv_types; eauto.
Qed.

(*
Proof: induction on typing
  * for terms with world change: we again have to check whether the
  world which we will switch into is one of those in renaming
*)
Lemma rename_w_preserv_types:
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
  rewrite Mem_app_or_eq; left ]; eauto.
constructor;
[ rewrite H in Ok_Bg |
  rewrite Mem_app_or_eq; right ]; eauto.
constructor;
[ rewrite H in Ok_Bg; rewrite H0 | ]; eauto.

(* lam *)
apply t_lam_LF with (L := L);
[ rewrite H0 in Ok_Bg; eauto |
  intros; unfold open_var in *];
rewrite subst_order_irrelevant_free; simpl; auto;
apply H with (v':=v') (G':=G') (Gamma := (v',A)::Gamma0); auto.
apply t_lam_LF with (L := L);
[ rewrite H0 in Ok_Bg; eauto |
  intros]; unfold open_var in *;
rewrite subst_order_irrelevant_free;
edestruct H; eauto; destruct H3;
[ apply ContextPermutImpl with (Gamma := (Gamma' ++ (v', A) :: Gamma0));
  [permut_simpl | ] | simpl; apply notin_empty ]; eauto.
apply t_lam_LF with (L := L);
[ rewrite H0 in Ok_Bg |
  intros];
rewrite H1; eauto;
unfold open_var in *;
rewrite subst_order_irrelevant_free;
edestruct H; eauto; destruct H4;
eauto;
simpl; apply notin_empty.

(* appl *)
apply t_appl_LF with (A:=A);
[ rewrite H in Ok_Bg |
  apply IHHT1 with (Gamma:=Gamma0) |
  apply IHHT2 with (Gamma:=Gamma0) ];
eauto.
apply t_appl_LF with (A:=A);
[ rewrite H in Ok_Bg |
  apply IHHT1 with (Gamma:=Gamma0) |
  apply IHHT2 with (Gamma:=Gamma0) ];
eauto.
apply t_appl_LF with (A:=A);
[ rewrite H in Ok_Bg; rewrite H0 |
  eapply IHHT1 |
  eapply IHHT2 ]; eauto.

(* box *)
apply t_box_LF with (L:=\{w'} \u L);
[ rewrite H0 in Ok_Bg; eauto |
  intros];
unfold open_ctx in *; rewrite notin_union in H1; destruct H1;
rewrite notin_singleton in *; rewrite <- subst_w_comm; auto;
eapply H; eauto.
apply t_box_LF with (L:=\{w0} \u L);
[ rewrite H0 in Ok_Bg; apply ok_Bg_split4 with (w:=w0);
  apply ok_Bg_ppermut with (G:=G' & (w', Gamma') & (w0, Gamma0)); auto |
  intros];
unfold open_ctx in *; rewrite notin_union in H1; destruct H1;
rewrite notin_singleton in *; rewrite <- subst_w_comm; auto;
eapply H; eauto.
apply t_box_LF with (L:=\{w''} \u L);
[ rewrite H0 in Ok_Bg; rewrite H1; eauto |
  intros];
unfold open_ctx in *;
rewrite notin_union in H2; destruct H2;
rewrite notin_singleton in *;
rewrite <- subst_w_comm; auto;
eapply H with (G0:=G0 & (w0, Gamma0)) (Gamma':=Gamma') (Gamma'':=Gamma''); auto;
rewrite H0; auto.

(* unbox *)
case_if.
inversion H0; subst; rewrite H in Ok_Bg;
apply ok_Bg_first_last_neq in Ok_Bg; elim Ok_Bg; auto.
constructor; [rewrite H in Ok_Bg | apply IHHT with (Gamma:=Gamma0)]; eauto.

case_if; constructor;
[ rewrite H in Ok_Bg |
  apply IHHT with (Gamma:=Gamma0) ]; eauto.

case_if.
inversion H1; subst; rewrite H in Ok_Bg;
apply ok_Bg_first_last_neq in Ok_Bg; elim Ok_Bg; auto.
constructor; [rewrite H0; rewrite H in Ok_Bg | eapply IHHT]; eauto.

(* unbox_fetch *)
case_if.
inversion H1; subst;
assert (G ~=~ G'0 /\ Gamma *=* Gamma'0) as HP by
  (apply ok_Bg_impl_ppermut with (w:=w'0);
   [eauto | rewrite H; rewrite H0; auto]);
destruct HP; constructor.
rewrite <- H2; apply ok_Bg_split2 with (w:=w'0);
eapply ok_Bg_permut; eauto.
apply ContextPermutImpl with (Gamma:=Gamma0 ++ Gamma);
[ permut_simpl |
  apply IHHT] ; auto.
assert (G'0 & (w'0, Gamma'0) ~=~ G & (w, Gamma)) by
  (symmetry; transitivity G'; auto);
assert (exists GH, exists GT, G'0 = GH & (w, Gamma) ++ GT) as Split by
  (eapply PPermut_split_neq; eauto; right; intro; subst; elim H1; reflexivity);
destruct Split as (GH, Split); destruct Split as (GT); subst;
apply t_unbox_fetch_LF with (G:=GH++GT) (Gamma:=Gamma).
assert ((w, Gamma) :: G & (w0, Gamma0) ~=~ G & (w, Gamma) & (w0, Gamma0)) by
  auto;
rewrite H3 in Ok_Bg; rewrite <- H2 in Ok_Bg; rew_app in *;
assert (GH & (w, Gamma) ++ GT ~=~ (w, Gamma) :: GH ++ GT) by (symmetry; eauto);
apply ok_Bg_ppermut with
  (G:= (GH & (w, Gamma) ++ GT) & (w0, Gamma0 ++ Gamma'0));
[ rewrite H4 |
  apply ok_Bg_split4 with (w:=w'0)]; rew_app; auto.
eapply IHHT with (w1:=w) (Gamma1:=Gamma); auto.
apply PPermut_last_rev_simpl with (a:=(w, Gamma)); rew_app in *; auto.
rew_app; auto.

case_if;
[ inversion H1; subst; apply ok_Bg_first_last_neq in Ok_Bg; elim Ok_Bg; auto |
  destruct (eq_var_dec w w'0)].
subst; assert (G ~=~ G'0 /\ Gamma *=* Gamma'0) by
  (apply ok_Bg_impl_ppermut with (w:=w'0); [ | rewrite <- H0]; eauto);
destruct H2; constructor.
rewrite <- H2; apply ok_Bg_permut with (Ctx := (Gamma ++ Gamma0)); eauto.
apply ContextPermutImpl with (Gamma:=Gamma ++ Gamma0);
[ permut_simpl |
  eapply IHHT with (w:=w'0) (Gamma1:=Gamma) (Gamma':=Gamma0)] ; auto.
assert (G'0 & (w'0, Gamma'0) ~=~ G & (w, Gamma)) by
  (symmetry; transitivity G'; auto);
assert (exists GH, exists GT, G'0 = GH & (w, Gamma) ++ GT) as Split by
  (eapply PPermut_split_neq; eauto; right; intro; subst; elim H1; reflexivity);
destruct Split as (GH, Split); destruct Split as (GT); subst;
apply t_unbox_fetch_LF with (G:=GH++GT) (Gamma:=Gamma).
assert (GH & (w, Gamma) ++ GT ~=~ (w, Gamma) :: GH ++ GT) by (symmetry; eauto);
apply ok_Bg_ppermut with
  (G:= (GH & (w, Gamma) ++ GT) & (w'0, Gamma0 ++ Gamma'0));
[ rewrite H3 | apply ok_Bg_split4 with (w:=w0)]; rew_app; auto;
assert ((w, Gamma) :: G & (w0, Gamma0) ~=~
  (G & (w, Gamma)) & (w0, Gamma0)) by auto;
rewrite H4 in Ok_Bg; rewrite <- H2 in Ok_Bg; rew_app in *;
remember (GH ++ (w, Gamma) :: GT) as GHT;
assert (GH ++ (w, Gamma) :: GT ++ (w0, Gamma'0) :: (w'0, Gamma0) :: nil ~=~
  GHT & (w0, Gamma'0) & (w'0, Gamma0)) by (subst; rew_app; auto);
rewrite H5; apply ok_Bg_swap_worlds; subst; rew_app in *; auto.
eapply IHHT; auto.
apply PPermut_last_rev_simpl with (a:=(w, Gamma)); rew_app in *;
transitivity (GH ++ GT ++ (w0, Gamma0) :: (w'0, Gamma'0) :: (w, Gamma) :: nil);
auto.
rew_app; auto.

case_if.
inversion H2; subst;
assert (G ~=~ G0 & (w'0, Gamma'0) /\ Gamma *=* Gamma'') by
  (apply ok_Bg_impl_ppermut with (w:=w''); [ | rewrite H; rewrite H0]; eauto);
destruct H3; apply t_unbox_fetch_LF with (G:=G0) (Gamma := Gamma'0 ++ Gamma);
[ rewrite H3 in Ok_Bg | apply IHHT | rewrite H1]; eauto.
destruct (eq_var_dec w w'0).
subst; assert (G ~=~ G0 & (w'', Gamma'') /\ Gamma *=* Gamma'0) by
  (apply ok_Bg_impl_ppermut with (w:=w'0); [ | rewrite H; rewrite H0]; eauto);
destruct H3;
apply t_unbox_fetch_LF with (G:=G0) (Gamma := Gamma ++ Gamma'');
[ rewrite H3 in Ok_Bg |
  eapply IHHT with (G':=G0 & (w0, Gamma0)) (Gamma' := Gamma'') |
  rewrite H1]; eauto.
assert (G0 & (w'0, Gamma'0) & (w'', Gamma'')  ~=~ G & (w, Gamma)) by
  (symmetry; transitivity G'; auto);
assert (exists GH, exists GT, G0 & (w'0, Gamma'0) = GH & (w, Gamma) ++ GT)
  as Split by (apply PPermut_split_neq with (w:=w'')
               (Gamma:=Gamma'') (G':= G); eauto);
assert (exists GH, exists GT, G0 = GH & (w, Gamma) ++ GT) as Split' by
  (destruct Split as (GH, Split); destruct Split as (GT);
   apply PPermut_split_neq with (w:=w'0) (Gamma:=Gamma'0) (G':=GH ++ GT);
   [ rew_app; transitivity (GH & (w, Gamma) ++ GT) |
     right; intro; subst; elim n]; auto; rewrite H4; auto);
destruct Split' as (GH, Split'); destruct Split' as (GT);
apply t_unbox_fetch_LF with (G:=GH++GT & (w'0, Gamma'0++Gamma''))
  (Gamma:=Gamma).
apply ok_Bg_ppermut with (G':=(G' & (w0, Gamma0))) in Ok_Bg;
[ | rewrite <- H; auto]; rewrite H0 in Ok_Bg; subst G0;
apply ok_Bg_ppermut with
  (G:= (GH & (w, Gamma) ++ GT) & (w'0, Gamma'0 ++ Gamma'') & (w0, Gamma0));
[ rew_app | ]; auto || eauto.
eapply IHHT with (w1:=w) (Gamma1:=Gamma) (G0:=GH++GT & (w0,Gamma0))
  (Gamma':=Gamma'0) (Gamma'':=Gamma''); auto.
assert (G & (w, Gamma) ~=~ G0 & (w'0, Gamma'0) & (w'', Gamma'')) by
  (transitivity G'; auto);
subst; rew_app in *;
assert (G & (w, Gamma) ~=~
       (GH ++ GT ++ (w'0, Gamma'0) :: (w'', Gamma'') :: nil) &  (w, Gamma)) by
 (transitivity (GH ++ (w, Gamma) :: GT ++  (w'0, Gamma'0) ::
   (w'', Gamma'') :: nil); auto);
transitivity ((GH ++ GT ++ (w'0, Gamma'0) :: (w'', Gamma'') :: nil) &
  (w0, Gamma0)); [ | rew_app; auto];
apply PPermut_last; auto; apply PPermut_last_rev_simpl with (a:=(w, Gamma));
eauto; rew_app; auto.
rew_app; auto.
rew_app; symmetry;
transitivity (G0 & (w'0, Gamma'0 ++ Gamma'')); auto;
subst; rew_app; auto.

(* here *)
case_if.
inversion H0; subst; rewrite H in Ok_Bg;
apply ok_Bg_first_last_neq in Ok_Bg; elim Ok_Bg; auto.
constructor;
[ rewrite H in Ok_Bg | apply IHHT with (Gamma:=Gamma0)]; eauto.

case_if; constructor;
[ rewrite H in Ok_Bg |
  apply IHHT with (Gamma:=Gamma0) ]; eauto.

case_if.
inversion H1; subst; rewrite H in Ok_Bg;
apply ok_Bg_first_last_neq in Ok_Bg; elim Ok_Bg; auto.
constructor; [rewrite H0; rewrite H in Ok_Bg | eapply IHHT]; eauto.

(* get_here *)
case_if.
inversion H2; subst;
assert (G ~=~ G'0 /\ Gamma *=* Gamma') as HP by
  (apply ok_Bg_impl_ppermut with (w:=w');
   [eauto | rewrite H; rewrite H0; auto]);
destruct HP; constructor.
rewrite <- H3; apply ok_Bg_split2 with (w:=w');
eapply ok_Bg_permut; eauto.
apply ContextPermutImpl with (Gamma:=Gamma0 ++ Gamma);
[ permut_simpl |
  apply IHHT] ; auto.
assert (G'0 & (w', Gamma') ~=~ G & (w, Gamma)) by
  (symmetry; transitivity G'; auto);
assert (exists GH, exists GT, G'0 = GH & (w, Gamma) ++ GT) as Split by
  (eapply PPermut_split_neq; eauto; right; intro; subst; elim H1; reflexivity);
destruct Split as (GH, Split); destruct Split as (GT); subst;
apply t_get_here_LF with (G:=GH++GT) (Gamma:=Gamma).
assert ((w, Gamma) :: G & (w0, Gamma0) ~=~ G & (w, Gamma) & (w0, Gamma0)) by
  auto;
rewrite H4 in Ok_Bg; rewrite <- H3 in Ok_Bg; rew_app in *;
assert (GH & (w, Gamma) ++ GT ~=~ (w, Gamma) :: GH ++ GT) by (symmetry; eauto);
apply ok_Bg_ppermut with
  (G:= (GH & (w, Gamma) ++ GT) & (w0, Gamma0 ++ Gamma'));
[ rewrite H5 |
  apply ok_Bg_split4 with (w:=w')]; rew_app; auto.
eapply IHHT with (w1:=w) (Gamma1:=Gamma); auto.
apply PPermut_last_rev_simpl with (a:=(w, Gamma)); rew_app in *; auto.
rew_app; auto.

case_if;
[ inversion H2; subst; apply ok_Bg_first_last_neq in Ok_Bg; elim Ok_Bg; auto |
  destruct (eq_var_dec w w')].
subst; assert (G ~=~ G'0 /\ Gamma *=* Gamma') by
  (apply ok_Bg_impl_ppermut with (w:=w'); [ | rewrite <- H0]; eauto);
destruct H3; constructor.
rewrite <- H3; apply ok_Bg_permut with (Ctx := (Gamma ++ Gamma0)); eauto.
apply ContextPermutImpl with (Gamma:=Gamma ++ Gamma0);
[ permut_simpl |
  eapply IHHT with (w:=w') (Gamma1:=Gamma) (Gamma':=Gamma0)] ; auto.
assert (G'0 & (w', Gamma') ~=~ G & (w, Gamma)) by
  (symmetry; transitivity G'; auto);
assert (exists GH, exists GT, G'0 = GH & (w, Gamma) ++ GT) as Split by
  (eapply PPermut_split_neq; eauto; right; intro; subst; elim H1; reflexivity);
destruct Split as (GH, Split); destruct Split as (GT); subst;
apply t_get_here_LF with (G:=GH++GT) (Gamma:=Gamma).
assert (GH & (w, Gamma) ++ GT ~=~ (w, Gamma) :: GH ++ GT) by (symmetry; eauto);
apply ok_Bg_ppermut with
  (G:= (GH & (w, Gamma) ++ GT) & (w', Gamma0 ++ Gamma'));
[ rewrite H4 | apply ok_Bg_split4 with (w:=w0)]; rew_app; auto;
assert ((w, Gamma) :: G & (w0, Gamma0) ~=~
  (G & (w, Gamma)) & (w0, Gamma0)) by auto;
rewrite H5 in Ok_Bg; rewrite <- H3 in Ok_Bg; rew_app in *;
remember (GH ++ (w, Gamma) :: GT) as GHT;
assert (GH ++ (w, Gamma) :: GT ++ (w0, Gamma') :: (w', Gamma0) :: nil ~=~
  GHT & (w0, Gamma') & (w', Gamma0)) by (subst; rew_app; auto);
rewrite H6; apply ok_Bg_swap_worlds; subst; rew_app in *; auto.
eapply IHHT; auto.
apply PPermut_last_rev_simpl with (a:=(w, Gamma)); rew_app in *;
transitivity (GH ++ GT ++ (w0, Gamma0) :: (w', Gamma') :: (w, Gamma) :: nil);
auto.
rew_app; auto.

case_if.
inversion H3; subst;
assert (G ~=~ G0 & (w', Gamma') /\ Gamma *=* Gamma'') by
  (apply ok_Bg_impl_ppermut with (w:=w'');
   [ | rewrite H; rewrite H0]; eauto);
destruct H4; apply t_get_here_LF with (G:=G0) (Gamma := Gamma' ++ Gamma);
[ rewrite H4 in Ok_Bg | apply IHHT | rewrite H1]; eauto.
destruct (eq_var_dec w w').
subst; assert (G ~=~ G0 & (w'', Gamma'') /\ Gamma *=* Gamma') by
  (apply ok_Bg_impl_ppermut with (w:=w'); [ | rewrite H; rewrite H0]; eauto);
destruct H4;
apply t_get_here_LF with (G:=G0) (Gamma := Gamma ++ Gamma'');
[ rewrite H4 in Ok_Bg |
  eapply IHHT with (G':=G0 & (w0, Gamma0)) (Gamma' := Gamma'') |
  rewrite H1]; eauto.
assert (G0 & (w', Gamma') & (w'', Gamma'')  ~=~ G & (w, Gamma)) by
  (symmetry; transitivity G'; auto);
assert (exists GH, exists GT, G0 & (w', Gamma') = GH & (w, Gamma) ++ GT)
  as Split by (apply PPermut_split_neq with (w:=w'')
               (Gamma:=Gamma'') (G':= G); eauto);
assert (exists GH, exists GT, G0 = GH & (w, Gamma) ++ GT) as Split' by
  (destruct Split as (GH, Split); destruct Split as (GT);
   apply PPermut_split_neq with (w:=w') (Gamma:=Gamma') (G':=GH ++ GT);
   [ rew_app; transitivity (GH & (w, Gamma) ++ GT) |
     right; intro; subst; elim n]; auto; rewrite H5; auto);
destruct Split' as (GH, Split'); destruct Split' as (GT);
apply t_get_here_LF with (G:=GH++GT & (w', Gamma'++Gamma''))
  (Gamma:=Gamma).
apply ok_Bg_ppermut with (G':=(G' & (w0, Gamma0))) in Ok_Bg;
[ | rewrite <- H; auto]; rewrite H0 in Ok_Bg; subst G0;
apply ok_Bg_ppermut with
  (G:= (GH & (w, Gamma) ++ GT) & (w', Gamma' ++ Gamma'') & (w0, Gamma0));
[ rew_app | ]; auto || eauto.
eapply IHHT with (w1:=w) (Gamma1:=Gamma) (G0:=GH++GT & (w0,Gamma0))
  (Gamma':=Gamma') (Gamma'':=Gamma''); auto.
assert (G & (w, Gamma) ~=~ G0 & (w', Gamma') & (w'', Gamma'')) by
  (transitivity G'; auto);
subst; rew_app in *;
assert (G & (w, Gamma) ~=~
       (GH ++ GT ++ (w', Gamma') :: (w'', Gamma'') :: nil) &  (w, Gamma)) by
 (transitivity (GH ++ (w, Gamma) :: GT ++  (w', Gamma') ::
   (w'', Gamma'') :: nil); auto);
transitivity ((GH ++ GT ++ (w', Gamma') :: (w'', Gamma'') :: nil) &
  (w0, Gamma0)); [ | rew_app; auto];
apply PPermut_last; auto; apply PPermut_last_rev_simpl with (a:=(w, Gamma));
eauto; rew_app; auto.
rew_app; auto.
rew_app; symmetry;
transitivity (G0 & (w', Gamma' ++ Gamma'')); auto;
subst; rew_app; auto.

(* letdia *)
case_if.
inversion H1; subst; rewrite H0 in Ok_Bg;
apply ok_Bg_first_last_neq in Ok_Bg; elim Ok_Bg; auto.
apply t_letdia_LF with (L_w:=L_w \u \{w'}) (L_t:=L_t) (A:=A);
[ rewrite H0 in Ok_Bg |
  eapply IHHT with (w:=w0) (Gamma:=Gamma0) | ]; eauto;
intros; rewrite notin_union in H3; destruct H3;
rewrite notin_singleton in H4;
unfold open_var in *; unfold open_ctx in *;
rewrite <- subst_w_comm; auto;
rewrite subst_order_irrelevant_free;
[ eapply H with (w:=w0) (Gamma:=Gamma0) (w':=w'0) | simpl]; eauto.

case_if.
apply t_letdia_LF with (L_w:=L_w \u \{w0}) (L_t:=L_t) (A:=A);
[ rewrite H0 in Ok_Bg | eapply IHHT with (w:=w0) (Gamma:=Gamma0) | ]; eauto;
intros; rewrite notin_union in H2; destruct H2;
rewrite notin_singleton in H3;
unfold open_var in *; unfold open_ctx in *;
rewrite <- subst_w_comm; auto;
rewrite subst_order_irrelevant_free;
[ eapply H with (w:=w0) (Gamma:=Gamma0) (w':=w'0) | simpl]; eauto.

case_if.
inversion H2; subst; rewrite H0 in Ok_Bg;
apply ok_Bg_first_last_neq in Ok_Bg; elim Ok_Bg; auto.
apply t_letdia_LF with (L_w:=L_w \u \{w''}) (L_t:=L_t) (A:=A);
[ rewrite H0 in Ok_Bg; rewrite H1 |
  eapply IHHT with (w:=w0) (Gamma:=Gamma0) | ]; eauto;
intros; rewrite notin_union in H4; destruct H4;
rewrite notin_singleton in H5;
unfold open_var in *; unfold open_ctx in *;
rewrite <- subst_w_comm; auto;
rewrite subst_order_irrelevant_free; simpl; auto;
eapply H with (w:=w0) (Gamma:=Gamma0) (G0:=G0 & ((w'0, (v', A)::nil)))
  (Gamma':=Gamma') (Gamma'':=Gamma''); auto;
[ rewrite H0 |rewrite H1 ]; rew_app; auto.

(* letdia_get *)
case_if.
inversion H3; subst;
assert (G ~=~ G' /\ Gamma *=* Gamma') by
  (apply ok_Bg_impl_ppermut with (w:=w'); [ | transitivity G0]; eauto);
destruct H4;
eapply t_letdia_LF with (L_w := L_w \u \{w'}).
rewrite <- H4; apply ok_Bg_permut with (Ctx:=(Gamma0 ++ Gamma)); auto || eauto.
apply ContextPermutImpl with (Gamma := Gamma0++Gamma); [permut_simpl|]; auto;
eapply IHHT; auto.
intros; rewrite notin_union in H7; destruct H7;
rewrite notin_singleton in H8;
unfold open_var in *; unfold open_ctx in *;
rewrite <- subst_w_comm; auto;
rewrite subst_order_irrelevant_free; simpl; auto;
eapply H with (v':=v') (w'0:=w'0) (w:=w0); auto;
[ | rew_app]; eauto.
destruct (eq_var_dec w w0).
subst; apply ok_Bg_first_last_neq in Ok_Bg; elim Ok_Bg; auto.
assert (G' & (w', Gamma') ~=~ G & (w, Gamma)) by
  (symmetry; transitivity G0; auto);
assert (exists GH, exists GT, G' = GH & (w, Gamma) ++ GT) by
  (eapply PPermut_split_neq; eauto);
destruct H5 as (GH, H5); destruct H5 as (GT, H5);
assert (G & (w, Gamma) ~=~
       (GH ++ GT ++ (w', Gamma') :: nil) &  (w, Gamma));
[subst; symmetry | rew_app]; auto.
apply PPermut_last; auto;
apply PPermut_last_rev_simpl with (a:=(w, Gamma)); auto;
transitivity ((GH & (w, Gamma) ++ GT) & (w', Gamma'));
[rew_app in *; symmetry | ]; auto.
apply t_letdia_get_LF with (L_w:=L_w \u \{w'}) (L_t:=L_t) (A:=A)
  (G:=GH++GT) (Gamma:=Gamma);
assert ((w, Gamma) :: G & (w0, Gamma0) ~=~
  (GH ++ GT & (w', Gamma')) & (w, Gamma) & (w0, Gamma0)) by
(rewrite <- H6; auto);
rewrite H7 in Ok_Bg.
apply ok_Bg_ppermut with (G:=(GH ++ GT & (w, Gamma)) & (w0, Gamma0 ++ Gamma')).
transitivity (((w, Gamma)::(GH++GT)) & (w0, Gamma0++Gamma'));
[ | rew_app in *]; eauto.
rew_app in *; eauto.
eapply IHHT with (w1:=w) (G0:=GH++GT) (w':=w0)
  (Gamma':=Gamma0) (Gamma'':=Gamma');
auto.
transitivity ((GH ++ GT & (w', Gamma')) & (w0, Gamma0));
[ apply PPermut_last; auto;
  apply PPermut_last_rev_simpl with (a:=(w, Gamma)) |
  rew_app]; auto.
intros; rewrite notin_union in H9; destruct H9;
rewrite notin_singleton in H10;
unfold open_var in *; unfold open_ctx in *;
rewrite <- subst_w_comm; auto;
rewrite subst_order_irrelevant_free; simpl; auto;
eapply H with (w1:=w0) (Gamma1:=Gamma0); auto.
rew_app; constructor; auto.
transitivity ((GH ++ GT & (w', Gamma')) & (w, Gamma)); [ | rew_app]; auto.
subst; rew_app; auto.

case_if.
inversion H3; subst;
apply ok_Bg_first_last_neq in Ok_Bg; elim Ok_Bg; auto.
destruct (eq_var_dec w w').
subst; assert (G ~=~ G' /\ Gamma *=* Gamma') by
( apply ok_Bg_impl_ppermut with (w:=w'); eauto);
destruct H4;
apply t_letdia_LF with (L_w:=L_w \u \{w0}) (L_t:=L_t) (A:=A).
rewrite <- H4; apply ok_Bg_permut with (Ctx := Gamma ++ Gamma0); auto || eauto.
apply ContextPermutImpl with (Gamma:=Gamma++Gamma0); auto;
eapply IHHT with (Gamma1:=Gamma); eauto.
intros; rewrite <- H4;
apply ContextPermutImpl with (Gamma:=Gamma++Gamma0); auto;
unfold open_var in *; unfold open_ctx in *;
rewrite <- subst_w_comm; auto;
rewrite subst_order_irrelevant_free; simpl; auto;
eapply H with (w'0 := w'0); eauto.
assert (G' & (w', Gamma') ~=~ G & (w, Gamma)) by
  (symmetry; transitivity G0; auto);
assert (exists GH, exists GT, G' = GH & (w, Gamma) ++ GT) by
  (eapply PPermut_split_neq; eauto);
destruct H5 as (GH, H5); destruct H5 as (GT, H5);
apply t_letdia_get_LF with (L_w:=L_w \u \{w0})
  (L_t:=L_t) (A:=A) (G:=GH++GT) (Gamma:=Gamma).
subst; assert ((w, Gamma) :: G & (w0, Gamma0) ~=~
  (GH & (w, Gamma) ++ GT) & (w', Gamma') & (w0, Gamma0)) by (rewrite H4; auto);
rewrite H5 in Ok_Bg;
apply ok_Bg_ppermut with (G:= GH & (w, Gamma) ++ GT & (w', Gamma' ++ Gamma0));
rew_app in *; [ auto | ];
apply ok_Bg_ppermut with (G:=(GH ++ (w, Gamma) :: GT) & (w', Gamma' ++ Gamma0));
[ | apply ok_Bg_split4 with (w:=w0)]; rew_app; auto;
apply ok_Bg_ppermut with (G:=GH ++ (w, Gamma) :: GT ++ (w', Gamma') ::
  (w0, Gamma0) :: nil); eauto.
eapply IHHT; auto;
apply PPermut_last; auto; apply PPermut_last_rev_simpl with (a:=(w, Gamma));
transitivity (GH & (w, Gamma) ++ GT & (w', Gamma')); [ | rew_app]; auto;
subst; symmetry; rew_app in *; auto.
intros; rewrite notin_union in H7; destruct H7;
rewrite notin_singleton in H8; unfold open_var in *; unfold open_ctx in *;
rewrite <- subst_w_comm; auto;
rewrite subst_order_irrelevant_free; simpl; auto;
eapply H with (w1:=w0) (Gamma1:=Gamma0); auto;
rew_app; constructor; auto;
subst; rew_app in *; symmetry;
transitivity ( GH ++ (w, Gamma) :: GT & (w', Gamma')); auto.
subst; symmetry; auto.

case_if.
inversion H4; subst;
assert (G ~=~ G1 & (w', Gamma') /\ Gamma *=* Gamma'') by
 (apply ok_Bg_impl_ppermut with (w:=w'');
  [ | transitivity G0]; eauto);
destruct H5;
eapply t_letdia_get_LF with (G:=G1) (Gamma:=Gamma'++Gamma) (L_w:=L_w \u \{w''}).
rewrite H5 in Ok_Bg; eauto.
eapply IHHT with (Gamma':=Gamma'); auto.
intros; unfold open_var in *; unfold open_ctx in *;
rewrite <- subst_w_comm; auto;
rewrite subst_order_irrelevant_free; simpl; auto;
eapply H with (w:=w0) (G0:=(w'0, (v',A)::nil)::G1)
  (Gamma':=Gamma') (Gamma'':=Gamma); auto;
[ eauto | rew_app]; constructor; [ | symmetry]; auto;
rewrite H5; rew_app; auto.
symmetry; transitivity (G1 & (w', Gamma' ++ Gamma'')); auto.
destruct (eq_var_dec w w'); subst.
assert (G ~=~ G1 & (w'', Gamma'') /\ Gamma *=* Gamma') by
  (apply ok_Bg_impl_ppermut with (w:=w'); [ | transitivity G0]; eauto);
destruct H5;
eapply t_letdia_get_LF with (G:=G1) (Gamma:=Gamma++Gamma'')
  (L_w:=L_w \u \{w''}) (L_t := L_t).
rewrite H5 in Ok_Bg; eauto.
eapply IHHT with (w:=w'); auto.
intros; unfold open_var in *; unfold open_ctx in *;
rewrite <- subst_w_comm; auto;
rewrite subst_order_irrelevant_free; simpl; auto;
eapply H with (w:=w0) (G0:=(w'0, (v',A)::nil)::G1)
  (Gamma':=Gamma) (Gamma'':=Gamma''); auto;
rew_app; constructor; auto;
symmetry; transitivity ((G1 ++ (w'', Gamma'')::nil) & (w', Gamma)); auto;
rew_app; auto.
symmetry; transitivity (G1 & (w', Gamma' ++ Gamma'')); auto.
assert (G & (w, Gamma) ~=~ G1 & (w', Gamma') & (w'', Gamma'')) by
  (symmetry; transitivity G0; symmetry; auto);
assert (exists GH, exists GT, G1 & (w'', Gamma'') = GH & (w, Gamma) ++ GT) by
  (apply PPermut_split_neq with (w:=w') (G':=G) (Gamma:=Gamma');
   try symmetry; auto; transitivity (G1 & (w', Gamma') & (w'', Gamma'')); auto);
assert (exists GH, exists GT, G1 = GH & (w, Gamma) ++ GT) by
  (destruct H6 as (GH, H6); destruct H6 as (GT, H6); subst;
   apply PPermut_split_neq with (w:=w'') (G':=GH++GT) (Gamma:=Gamma''); auto;
   [rewrite H6; rew_app; auto | right; intro; subst; elim H4; reflexivity]);
destruct H7 as (GH, H7); destruct H7 as (GT, H7); subst;
apply t_letdia_get_LF with (L_w:=L_w \u \{w''})
  (L_t:=L_t) (A:=A) (G:=GH++GT & (w', Gamma'++Gamma'')) (Gamma:=Gamma).
assert ((w, Gamma) :: G & (w0, Gamma0) ~=~ G0  & (w0, Gamma0)) by
  (rewrite <- H0; auto);
rewrite H7 in Ok_Bg; rewrite H1 in Ok_Bg;
apply ok_Bg_ppermut with (G:= (GH & (w, Gamma) ++ GT) &
  (w', Gamma' ++ Gamma'') & (w0, Gamma0));
rew_app in *; eauto.
eapply IHHT with (w1:=w) (G0:=GH++GT & (w0, Gamma0))
  (Gamma':=Gamma') (Gamma'':=Gamma''); rew_app; auto;
rew_app in *; transitivity ((GH ++ GT ++ (w', Gamma') ::
  (w'', Gamma'') :: nil) & (w0, Gamma0));
[ apply PPermut_last | rew_app]; auto;
apply PPermut_last_rev_simpl with (a:=(w, Gamma));
rewrite H5; symmetry; transitivity (GH ++ GT ++ (w, Gamma) :: (w', Gamma') ::
  (w'', Gamma'') :: nil); [rew_app |  apply PPermut_app_head; symmetry]; auto.
intros; unfold open_var in *; unfold open_ctx in *;
rewrite <- subst_w_comm; auto;
rewrite subst_order_irrelevant_free; simpl; auto;
eapply H with (G0:=(w'0, (v', A) :: nil) :: (GH ++ GT) & (w, Gamma))
  (Gamma':=Gamma') (Gamma'':=Gamma''); auto.
rew_app in *; constructor; auto;
transitivity (GH ++ (w, Gamma) :: GT ++ (w', Gamma') :: (w'', Gamma'') :: nil);
auto; rew_app in *; constructor; auto.
rew_app in *; constructor; auto;
transitivity (GH ++ (w, Gamma) :: GT ++ (w', Gamma') :: (w'', Gamma'') :: nil);
auto; rew_app in *; constructor; auto.
rew_app; symmetry;
transitivity ((GH & (w, Gamma) ++ GT) & (w', Gamma'++ Gamma''));
[ | rew_app]; auto.
Admitted. (* "No more subgoals but non-instantiated existential variables" *)

Lemma rename_w_preserv_types_new:
forall G w Gamma A M G' w' Gamma'
  (HT: G |= (w, Gamma) |- M ::: A)
  (GG': PPermut G (G' & (w', Gamma'))),
  G' |= (w, Gamma ++ Gamma') |- {{ fwo w // fwo w' }} M ::: A.
intros; apply rename_w_preserv_types with (G := G) (w := w) (w':= w'); eauto.
Qed.

Lemma rename_w_preserv_types_old:
forall G w Gamma A M G' w' Gamma'
  (HT: G |= (w, Gamma) |- M ::: A)
  (GG': PPermut G (G' & (w', Gamma'))),
  G' |= (w', Gamma' ++ Gamma) |- {{ fwo w' // fwo w }} M ::: A.
intros; apply rename_w_preserv_types with (G := G) (w := w) (w':= w'); eauto.
Qed.

Lemma rename_w_preserv_types_outer:
forall G G0 w Gamma A M G' w' Gamma' w'' Gamma''
  (HT: G |= (w, Gamma) |- M ::: A)
  (GG: PPermut G (G0 & (w', Gamma') & (w'', Gamma'')))
  (GG': PPermut G' (G0 & (w', Gamma' ++ Gamma''))),
  G' |= (w, Gamma) |- {{ fwo w' // fwo w'' }} M ::: A.
intros; eapply rename_w_preserv_types; eauto.
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
Lemma Progress:
forall G w M A
  (H_lc_w: lc_w_LF M)
  (H_lc_t: lc_t_LF M)
  (HT: emptyEquiv G |= (w, nil) |- M ::: A),
  value_LF M \/ exists N, (M, fwo w) |-> (N, fwo w).
intros;
remember (w, (@nil ty)) as Ctx;
generalize dependent Ctx;
generalize dependent A;
generalize dependent w;
generalize dependent G;
induction M; intros; eauto using value_LF;
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
[ inversion H0; subst; inversion HT1; subst |
  destruct H0];
eexists; constructor; eauto;
inversion H4; subst; auto.
(* unbox & unbox_fetch *)
right; inversion HT; subst;
inversion H_lc_w; subst;
inversion H_lc_t; subst.
(* unbox *)
edestruct IHM with (A := [*]A); eauto;
[ inversion H0; subst; inversion HT0; subst |
  destruct H0];
eexists; constructor; eauto;
inversion H1; inversion H2; subst; auto.
(* unbox_fetch *)
assert (Gamma = nil) by
  ( apply emptyEquiv_permut_empty with
    (G:= (G0 & (w0, Gamma))) (G':=G) (w:=w0); auto;
    apply Mem_last); subst;
destruct IHM with (A := [*]A)
                  (Ctx := (w0, (@nil ty)))
                  (G := G0 & (w, nil))
                  (w := w0);
eauto.
assert (emptyEquiv (G0 & (w, nil)) = G0 & (w, nil)) by
  ( repeat rewrite emptyEquiv_rewrite; simpl;
   apply emptyEquiv_permut_split_last in H6; rewrite H6; reflexivity);
rewrite H0; auto.
inversion H0; subst; inversion HT0; subst;
eexists; constructor; eauto; inversion H2; auto.
destruct H0; eexists; constructor; eauto.
(* here & get_here *)
inversion HT; subst;
inversion H_lc_w; subst;
inversion H_lc_t; subst.
(* here *)
edestruct IHM; eauto;
[ left; econstructor|
  right; destruct H0; eexists];
eauto using step_LF.
(* get_here *)
assert (Gamma = nil) by
  ( apply emptyEquiv_permut_empty with
    (G:= (G0 & (w0, Gamma))) (G':=G) (w:=w0); auto; apply Mem_last);
subst; edestruct IHM with (A := A0) (G := G0 & (w, nil)) (w:=w0); eauto;
assert (emptyEquiv (G0 & (w, nil)) = G0 & (w, nil)) by
  (repeat rewrite emptyEquiv_rewrite; simpl;
   apply emptyEquiv_permut_split_last in H5; rewrite H5; reflexivity).
rewrite H0; auto.
left; inversion H0; subst; inversion HT0; subst;
econstructor; eauto using step_LF.
right; destruct H0; eexists;
econstructor; eauto using step_LF.
(* letdia & letdia_get *)
right; inversion HT; subst;
inversion H_lc_w; subst;
inversion H_lc_t; subst.
(* letdia *)
edestruct IHM1 with (A := <*>A0); eauto;
[ inversion H0; subst; inversion HT1; subst |
  destruct H0];
eexists; constructor; eauto;
try apply closed_t_succ; auto;
inversion H4; inversion H6; subst; auto.
(* letdia_get *)
assert (Gamma = nil) by
  ( apply emptyEquiv_permut_empty with (G:= (G0 & (w0, Gamma))) (G':=G) (w:=w0);
    auto; apply Mem_last); subst;
edestruct IHM1 with (G := G0 & (w, nil))
                    (w := w0)
                    (Ctx := (w0, (@nil ty)))
                    (A := <*>A0); eauto;
assert ( emptyEquiv (G0 & (w, nil)) = G0 & (w, nil)) by
   ( repeat rewrite emptyEquiv_rewrite; simpl;
     apply emptyEquiv_permut_split_last in H6; rewrite H6; reflexivity).
rewrite H0; auto.
inversion H0; subst; inversion HT1; subst;
eexists; constructor; eauto;
try apply closed_t_succ; auto;
inversion H4; inversion H7; subst; auto.
destruct H0;
eexists; constructor; eauto;
try apply closed_t_succ; auto;
inversion H5; inversion H8; subst; auto.
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
Lemma Preservation:
forall G M N A w
  (HT: emptyEquiv G |= (w, nil) |- M ::: A)
  (HS: (M, fwo w) |-> (N, fwo w)),
  emptyEquiv G |= (w, nil) |- N ::: A.
intros;
remember (w, (@nil (var * ty))) as Ctx;
remember (emptyEquiv G) as G';
generalize dependent w;
generalize dependent N;
generalize dependent G;
induction HT; intros;
inversion HS; subst;
try (inversion HeqCtx; subst);
eauto using types_LF.
(* appl_lam *)
inversion HT1; subst;
unfold open_var in *;
assert (exists v, v \notin L \u free_vars_LF M0) as HF by apply Fresh;
destruct HF as (v_fresh);
rewrite subst_t_neutral_free with (v:=v_fresh).
eapply subst_t_preserv_types_inner; eauto;
rewrite <- double_emptyEquiv; auto.
rewrite notin_union in H; destruct H; auto.
(* unbox_box *)
inversion HT; subst;
assert (exists v, v \notin L \u (free_worlds_LF M0)) as HF by apply Fresh;
destruct HF as (w_fresh);
unfold open_ctx in *;
replace ({{fwo w0 // bwo 0}}M0)
  with ({{fwo w0 // fwo w_fresh}} {{fwo w_fresh // bwo 0}}M0)
  by (rewrite subst_w_neutral_free; auto);
replace (@nil (var * ty)) with (nil ++ (@nil (var * ty))); eauto;
apply rename_w_preserv_types_old with (G := emptyEquiv G0 & (w0, nil));
auto.
(* unbox_fetch_box *)
inversion HT; subst;
assert (exists v, v \notin L \u (free_worlds_LF M0)) as HF by apply Fresh;
destruct HF as (w_fresh);
unfold open_ctx in *;
replace ({{fwo w0 // bwo 0}}M0)
  with ({{fwo w0 // fwo w_fresh}} {{fwo w_fresh // bwo 0}}M0)
  by (rewrite subst_w_neutral_free; auto);
replace (@nil (var * ty)) with (nil ++ (@nil (var * ty))); eauto;
apply rename_w_preserv_types_old with (G := G & (w0, nil) & (w, Gamma));
auto.
(* unbox_fetch *)
econstructor; eauto;
assert (Gamma = nil).
  apply emptyEquiv_permut_empty with (G:= (G & (w, Gamma))) (G':=G0) (w:=w);
    auto; apply Mem_last.
subst.
eapply IHHT with (G0:=G & (w0, nil)); eauto.
   repeat rewrite emptyEquiv_rewrite; simpl.
   apply emptyEquiv_permut_split_last in H; rewrite H; reflexivity.
(* get_here *)
econstructor; eauto;
assert (Gamma = nil).
  apply emptyEquiv_permut_empty with (G:= (G & (w, Gamma))) (G':=G0) (w:=w);
    auto; apply Mem_last.
subst; eapply IHHT with (G0:=G & (w0, nil)); eauto.
   repeat rewrite emptyEquiv_rewrite; simpl.
   apply emptyEquiv_permut_split_last in H; rewrite H; reflexivity.
(* letdia + (here | get_here ) *)
assert (exists w1, w1 \notin L_w \u free_worlds_LF N) as HF by apply Fresh;
assert (exists v1, v1 \notin L_t \u free_vars_LF N) as HF2 by apply Fresh;
destruct HF as (w_fresh); destruct HF2 as (v_fresh);
inversion HT; subst.
(* letdia #1 *)
rewrite notin_union in *; destruct H0; destruct H1;
unfold open_var in *; unfold open_ctx in *;
rewrite subst_t_neutral_free with (v:=v_fresh).
rewrite subst_order_irrelevant_bound; auto.
rewrite <- subst_w_neutral_free with (w0:=w_fresh).
apply subst_t_preserv_types_inner with (A:=A); eauto.
replace ((v_fresh, A) :: nil) with (nil ++ (v_fresh, A) :: nil) by auto.
apply rename_w_preserv_types_new with
  (G:= (w_fresh, (v_fresh, A)::nil) :: emptyEquiv G0).
rewrite <- subst_order_irrelevant_bound.
eapply HT2; auto.
constructor.
rew_app; auto.
rewrite <- double_emptyEquiv; auto.
apply subst_var_preserv_free_worlds; auto.
constructor.
apply subst_world_preserv_free_vars; auto.
(* letdia #2 *)
rewrite notin_union in *; destruct H0; destruct H1.
unfold open_var in *; unfold open_ctx in *.
rewrite subst_t_neutral_free with (v:=v_fresh).
rewrite subst_order_irrelevant_bound.
rewrite <- subst_w_neutral_free with (w0:=w_fresh).
eapply subst_t_preserv_types_outer with (A:=A) (G0:=G)
  (Gamma':=Gamma) (w':=w); auto.
rew_app;
assert ( emptyEquiv (G & (w0, nil)) = G & (w0, nil)).
   repeat rewrite emptyEquiv_rewrite; simpl.
   apply emptyEquiv_permut_split_last in H7; rewrite H7; reflexivity.
assert (Gamma = nil).
  apply emptyEquiv_permut_empty with (G:= (G & (w, Gamma)))
    (G':=G0) (w:=w); auto.
  apply Mem_last.
subst;
rewrite <- H5 in HT0; auto.
apply rename_w_preserv_types_outer with (G0:=G) (Gamma'':=(v_fresh,A) :: nil)
      (Gamma':=Gamma) (G:=G & (w, Gamma) & (w_fresh, (v_fresh,A)::nil)).
assert (G & (w, Gamma) & (w_fresh, (v_fresh, A) :: nil) ~=~
  (w_fresh, (v_fresh, A) :: nil) :: emptyEquiv G0) by auto. rewrite H5.
rewrite <- subst_order_irrelevant_bound.
eapply HT2; auto.
constructor.
rew_app; auto.
rew_app. apply PPermut_last; [permut_simpl | ]; auto.
apply subst_var_preserv_free_worlds; auto.
constructor.
apply subst_world_preserv_free_vars; auto.

assert (exists w1, w1 \notin L_w \u free_worlds_LF N) as HF by apply Fresh;
assert (exists v1, v1 \notin L_t \u free_vars_LF N) as HF2 by apply Fresh;
destruct HF as (w_fresh); destruct HF2 as (v_fresh);
inversion HT; subst.
(* letdia #1 *)
rewrite notin_union in *; destruct H1; destruct H2.
unfold open_var in *; unfold open_ctx in *.
rewrite subst_t_neutral_free with (v:=v_fresh).
rewrite subst_order_irrelevant_bound.
rewrite <- subst_w_neutral_free with (w0:=w_fresh).
eapply subst_t_preserv_types_outer with (A:=A) (G0:=G) (w':=w)
  (Gamma':=Gamma); eauto.
assert (Gamma = nil).
  apply emptyEquiv_permut_empty with
    (G:= (G & (w, Gamma))) (G':=G1) (w:=w); auto.
  apply Mem_last.
subst. rew_app.
assert ( emptyEquiv (G & (w0, nil)) = G & (w0, nil)).
   repeat rewrite emptyEquiv_rewrite; simpl.
   apply emptyEquiv_permut_split_last in H0. rewrite H0; reflexivity.
rewrite <- H6 in HT0; auto.
assert (Gamma = nil).
  apply emptyEquiv_permut_empty with (G:= (G & (w, Gamma))) (G':=G1) (w:=w);
    auto.
  apply Mem_last.
subst.
eapply rename_w_preserv_types_outer
  with (G:= (w_fresh, (v_fresh,A)::nil):: G & (w,nil))
       (Gamma'':=(v_fresh,A)::nil) (Gamma':=nil) (G0:=G).
rewrite <- subst_order_irrelevant_bound.
eapply HT2; eauto.
constructor.
auto.
rew_app; auto.
apply subst_var_preserv_free_worlds; auto.
constructor.
apply subst_world_preserv_free_vars; auto.
(* letdia #2 *)
assert (Gamma = nil).
  apply emptyEquiv_permut_empty with (G:= (G & (w, Gamma))) (G':=G1) (w:=w);
  auto.
  apply Mem_last.
subst.
assert (w <> w0) by eauto.
assert (w1 <> w) by eauto.
rewrite <- H0.
rewrite notin_union in *; destruct H1; destruct H2.
unfold open_var in *; unfold open_ctx in *.
destruct (eq_var_dec w1 w0).
subst.
assert (G0  ~=~ G /\ Gamma0 *=* nil).
  apply ok_Bg_impl_ppermut with (w:=w0).
  eauto.
  auto.
destruct H10.
apply permut_nil_eq in H11.
rewrite subst_t_neutral_free with (v:=v_fresh).
eapply subst_t_preserv_types_inner with (A:=A); eauto.
rewrite subst_order_irrelevant_bound.
rewrite <- subst_w_neutral_free with (w0:=w_fresh).
replace ((v_fresh,A)::nil) with (nil++(v_fresh,A)::nil) by auto.
apply rename_w_preserv_types_new with (G:= (w_fresh, (v_fresh,A)::nil) ::
  G0 & (w, nil));
auto.
rewrite <- subst_order_irrelevant_bound.
rewrite H10; eapply HT2; auto.
constructor.
apply subst_var_preserv_free_worlds; auto.
constructor.
assert ( emptyEquiv (G & (w, nil)) = G & (w, nil)).
   repeat rewrite emptyEquiv_rewrite; simpl.
   apply emptyEquiv_permut_split_last in H0. rewrite H0; reflexivity.
rewrite H12; rewrite <- H10; subst; auto.
apply subst_world_preserv_free_vars; auto.
assert (Gamma0 = nil).
  apply emptyEquiv_permut_empty with (G:= (G0 & (w1, Gamma0)))
    (G':=G & (w0, nil)) (w:=w1); auto.
  assert (emptyEquiv G = G).
    apply emptyEquiv_permut_split_last with (C:=(w, nil)) (H:=G1); auto.
  rewrite emptyEquiv_rewrite; simpl. rewrite H10. auto.
  apply Mem_last.
subst.
assert (exists GH, exists GT, G = GH & (w1, nil) ++ GT).
  apply PPermut_split_neq with (w:=w0) (G':=G0) (Gamma:=nil).
  symmetry; auto.
  right; intro; subst; elim n; reflexivity.
destruct H10 as (GH, H12);
destruct H12 as (GT, H12).
rewrite subst_t_neutral_free with (v:=v_fresh).
apply subst_t_preserv_types_outer
  with (A:=A)
       (G0 :=GH ++ GT & (w, nil))
       (G  := GH ++ GT & (w,nil) & (w1, (v_fresh, A) :: nil))
       (G' := GH ++ GT & (w,nil) & (w0, nil))
       (w' :=w1)
       (Gamma':=nil); auto.
rew_app; auto.
rew_app; auto.
subst; rew_app; auto.
subst.
clear HT2 H IHHT.
assert (G0 & (w, nil) ~=~ GH ++ GT & (w,nil) & (w0, nil)).
  transitivity ((GH++GT & (w0,nil) &(w, nil))); auto.
  assert (G0 & (w1, nil) ~=~  (GH ++ GT & (w0, nil) & (w1, nil))).
    transitivity ((GH & (w1, nil) ++ GT) & (w0, nil)); rew_app in *; auto.
  assert (G0 ~=~ GH ++ GT & (w0, nil)).
  apply PPermut_last_rev_simpl with (a:=(w1,nil)); rew_app in *; auto.
  rewrite H10; rew_app; auto.
rewrite <- H.
assert (emptyEquiv G0 = G0).
  assert (G0 ~=~ GH ++ GT & (w0, nil)).
    apply PPermut_last_rev_simpl with (a:=(w, nil)).
    transitivity (GH ++ GT & (w, nil) & (w0, nil)); rew_app in *; auto.
  apply emptyEquiv_permut_split_last with (C:=(w1, nil)) (H := (w0, nil) ::
    GH & (w1, nil) ++ GT).
  assert (emptyEquiv ((w0, nil) :: GH & (w1, nil) ++ GT) = ((w0, nil) ::
    GH & (w1, nil) ++ GT)).
  apply emptyEquiv_permut_split_last with (C:=(w, nil)) (H:= (w0,nil)::G1).
  simpl. rewrite <- H0; rew_app; symmetry; auto.
  rewrite H11. rewrite H10; rew_app.
  transitivity (GH ++ (w0, nil) :: (w1, nil)::GT); auto.
rewrite emptyEquiv_rewrite; simpl;
rewrite H10; auto.
rewrite subst_order_irrelevant_bound.
rewrite <- subst_w_neutral_free with (w0:=w_fresh).
apply rename_w_preserv_types_outer
  with (G0 := GH ++ GT & (w,nil))
       (G := (w_fresh, (v_fresh, A) :: nil) :: G & (w, nil))
       (Gamma':=nil)
       (Gamma'':=(v_fresh, A)::nil); auto.
rewrite <- subst_order_irrelevant_bound.
eapply HT2; eauto.
constructor.
subst; rew_app.
transitivity ((w_fresh, (v_fresh, A) :: nil) :: GH ++ GT ++
  (w, nil) :: (w1, nil) :: nil);
auto.
transitivity ((GH ++ GT ++ (w, nil) :: (w1, nil) :: nil) &
  (w_fresh, (v_fresh, A) :: nil)).
auto. rew_app; auto.
rew_app; auto.
apply subst_var_preserv_free_worlds; auto.
constructor.
apply subst_world_preserv_free_vars; auto.

(* letdia_step *)
destruct (eq_var_dec w0 w).
subst.
eapply ok_Bg_first_last_neq in Ok_Bg;
elim Ok_Bg; auto.
assert (Gamma = nil).
  apply emptyEquiv_permut_empty with (G:= (G & (w, Gamma))) (G':=G1) (w:=w);
  auto.
  apply Mem_last.
subst.
rewrite <- H0.
eapply t_letdia_get_LF ; eauto.
apply IHHT with (G0:=G & (w0,nil)) (w1:=w); auto.
assert (emptyEquiv G = G).
apply emptyEquiv_permut_split_last with (C:=(w,nil)) (H:=G1); auto.
rewrite emptyEquiv_rewrite; simpl; rewrite H1; reflexivity.
Qed.

End Lemmas.

Close Scope label_free_is5_scope.
