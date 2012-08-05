(* TODO: imports are messed up now that there's a module *) 
Add LoadPath "./..".

Require Import Utf8.

Require Import Syntax.
Require Import Substitution.
Require Import LibList.

(*
Require Import Metatheory.
Require Import LibListSorted.
Require Import Arith.
*)
Require Import PermutLib.
Require Import PPermutLib.
Require Import OkLib.

Open Scope label_free_is5_scope.
Open Scope is5_scope.
Open Scope permut_scope.


Global Reserved Notation " G '|=' Ctx '|-' M ':::' A " (at level 70).
 
(* Statics *) 

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
  forall G', PPermut (G & (w, Gamma)) G' -> 
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
  forall G0, PPermut (G & (w, Gamma)) G0 -> 
    G0 |= Ctx' |- letdia_get_LF (fwo w) M N ::: B
where " G '|=' Ctx '|-' M ':::' A " := (types_LF G Ctx M A) : label_free_is5_scope.


(* Dynamics *)

Inductive value_LF: te_LF -> Prop :=
| val_lam_LF: forall A M, value_LF (lam_LF A M)
| val_box_LF: forall M, value_LF (box_LF M)
| val_get_here_LF: forall M Ctx, value_LF M -> value_LF (get_here_LF Ctx M)
.

Global Reserved Notation " M |-> N " (at level 70).

Inductive step_LF: (te_LF * vwo) -> (te_LF * vwo) -> Prop :=
| red_appl_lam_LF: forall ctx M A N,
  lc_w_LF M -> lc_t_n_LF M 1 ->
  lc_w_LF N -> lc_t_LF N ->
  (appl_LF (lam_LF A M) N, ctx) |-> ( M ^t^ N , ctx)

| red_unbox_fetch_box_LF: forall ctx ctx' M,
  lc_w_n_LF M 1 -> lc_t_LF M ->
  (unbox_fetch_LF ctx' (box_LF M), ctx) |-> (M ^w^ ctx, ctx)

| red_letdia_get_get_here_LF: forall ctx ctx' ctx'' M N,
  lc_w_LF M -> lc_t_LF M ->
  lc_w_n_LF N 1 -> lc_t_n_LF N 1 ->
  (letdia_get_LF ctx' (get_here_LF ctx'' M) N, ctx) |-> ((N ^w^ ctx'') ^t^ M, ctx)

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
  lc_w_n_LF N 1 -> lc_t_n_LF N 1 ->
  (letdia_get_LF ctx M N, ctx') |-> (letdia_get_LF ctx M' N, ctx')

where " M |-> N " := (step_LF M N ) : label_free_is5_scope.

Section Lemmas.

Lemma Fresh: 
  forall (L:fset var), exists w0, w0 \notin L.
intro;
exists (var_gen L);
apply var_gen_spec.
Qed.

(* FIXME: Move to OkLib *)
Lemma ok_Bg_cons_last:
forall G a,
  ok_Bg (G & a) <-> ok_Bg (a :: G).
Admitted.

Lemma ok_Bg_swap:
forall C C' G,
  ok_Bg (C :: G & C') ->
  ok_Bg (C' :: G & C).
Admitted.
Hint Resolve ok_Bg_cons_last ok_Bg_swap.
(* / FIXME *)

(* FIXME: Move to PPermutLib *)
Lemma PPermut_swap_inner:
forall G G' C C',
  C :: G ++ C' :: G' ~=~ C' :: G ++ G' & C.
Admitted.

Lemma PPermut_swap_inner2:
forall G G' C C',
  C :: G ++ G' & C' ~=~ C' :: G ++ G' & C.
Admitted.

Lemma PPermut_swap3:
forall C C' G,
  C :: G & C' ~=~ C' :: G & C.
Admitted.

Hint Resolve PPermut_swap_inner.
Hint Resolve PPermut_swap_inner2.
Hint Resolve PPermut_swap3.
(* /FIXME *)

Lemma BackgroundSubsetImpl:
forall G G' Ctx M A
  (HT: G |= Ctx |- M ::: A)
  (HSubst: exists GT, PPermut (G++GT) G')
  (H_ok: ok_Bg (Ctx :: G')),
  G' |= Ctx |- M ::: A.
intros;
generalize dependent G';
induction HT; intros;
eauto using types_LF.
(* lam *)
apply t_lam_LF with (L:=L \u used_t_vars ((w, Gamma)::G'));
[assumption | intros; eapply H; auto].
(* box *)
destruct HSubst as [GT];
apply t_box_LF with (L:=L \u used_w_vars (G' & (w, Gamma))); intros.
apply ok_Bg_cons_last; auto. 
apply H; [ | exists GT | ]; auto. 
apply ok_Bg_fresh_wo; 
[ apply ok_Bg_cons_last |
  rewrite notin_union in H1; destruct H1]; auto.
(* unbox_fetch *)
destruct HSubst as [GT];
apply t_unbox_fetch_LF with (Gamma:=Gamma) (G:=G++GT).
apply ok_Bg_ppermut with (G:=(w', Gamma')::G'0); auto.
  rewrite <- H0; rewrite <- H; rew_app; auto.
apply IHHT; [exists GT | ]; auto.
  apply ok_Bg_ppermut with (G:=(w', Gamma')::G'0); auto.
  rewrite <- H0; rewrite <- H; rew_app; auto.
transitivity (G' ++ GT); auto;
transitivity (G & (w, Gamma) ++ GT); [symmetry | ]; auto.
(* get_here *)
destruct HSubst as [GT];
apply t_get_here_LF with (Gamma:=Gamma) (G:=G++GT).
apply ok_Bg_ppermut with (G:=Ctx'::G'0); auto.
  rewrite <- H0; rewrite <- H; rew_app; auto.
apply IHHT; [exists GT | ]; auto.
  apply ok_Bg_ppermut with (G:=Ctx'::G'0); auto.
  rewrite <- H0; rewrite <- H; rew_app; auto.
transitivity (G' ++ GT); auto;
transitivity (G & (w, Gamma) ++ GT); [symmetry | ]; auto.
(* letdia *)
apply t_letdia_LF with (A:=A) (L_t:=L_t)(L_w:=L_w \u used_w_vars ((w, Gamma)::G')).
auto.
apply IHHT; auto.
intros; apply H; auto.
destruct HSubst as [GT];
exists GT; rew_app; auto.
rewrite notin_union in *; destruct H1.
apply ok_Bg_ppermut with (G:= (w', (v', A) :: nil ) :: (w, Gamma) :: G');
auto. 
(* letdia_get *)
destruct HSubst as [GT];
apply t_letdia_get_LF with (A:=A) (Gamma:=Gamma) (G:=G++GT) 
                           (L_t:=L_t) (L_w:=L_w \u used_w_vars (Ctx'::G')).
apply ok_Bg_ppermut with (G:=Ctx' :: G').
rewrite <- H1; rewrite <- H0; rew_app; auto.
auto.
apply IHHT. 
  exists GT; auto.
  apply ok_Bg_ppermut with (G:=Ctx' :: G').
  rewrite <- H1; rewrite <- H0; rew_app; auto.
  auto.
  intros; apply H; auto. 
  exists GT; rew_app; auto.
  apply ok_Bg_ppermut with (G:=(w', (v', A) :: nil) :: Ctx' :: G').
  rewrite <- H1; rewrite <- H0.
assert ((G & (w, Gamma) ++ GT)  ~=~ (G ++ GT) & (w, Gamma)) by (symmetry; auto).
rewrite H4; destruct Ctx'; auto.
auto.
rewrite <- H1; rewrite <- H0; rew_app; auto.
Qed.

Lemma PPermut_bg:
forall G Gamma w M A,
  G |= (w, Gamma) |- M ::: A ->
    forall G',
      G ~=~ G' ->
      G' |= (w, Gamma) |- M ::: A.
intros; apply BackgroundSubsetImpl with (G:=G);
[ | exists (@nil Context_LF) | ]; rew_app; auto;
inversion H; subst; 
try (apply ok_Bg_ppermut with (G:=(w, Gamma) :: G); auto).
apply ok_Bg_cons_last; eauto.
rewrite <- H6; apply ok_Bg_ppermut with (G:=(w0, Gamma0) :: G0 & (w, Gamma)); eauto.
rewrite <- H1; apply ok_Bg_ppermut with (G:=(w0, Gamma0) :: G0 & (w, Gamma)); eauto.
rewrite <- H1; apply ok_Bg_ppermut with (G:=(w0, Gamma0) :: G0 & (w, Gamma)); eauto.
Qed.

Require Import Setoid.
Add Morphism types_LF : PPermut_types.
split; intros; destruct y0.
apply PPermut_bg with (G:=x); auto.
apply PPermut_bg with (G:=y); auto.
Qed.

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
assert (G & (w, Gamma'0) ~=~ (G & (w, Gamma0))) by auto.
rewrite H0; auto.
(* here *)
econstructor; [ eapply ok_Bg_permut | ]; eauto.
(* get_here *)
apply t_get_here_LF with (G:=G) (Gamma:=Gamma); auto.
apply ok_Bg_ppermut with (G:=(w0, Gamma) :: G & (w, Gamma0)); auto.
assert (G & (w, Gamma') ~=~ (G & (w, Gamma0))) by auto.
rewrite H1; auto.
(* letdia *)
econstructor; [ eapply ok_Bg_permut | | ]; eauto.
(* letdia_get *)
apply t_letdia_get_LF with (L_w:=L_w) (L_t:=L_t) (A:=A) (Gamma:=Gamma) (G:=G).
apply ok_Bg_ppermut with (G:=(w0, Gamma) :: G & (w, Gamma0)); auto.
assert (G & (w, Gamma') ~=~ (G & (w, Gamma0))) by auto; rewrite H2; auto.
intros; eapply H; eauto.
auto.
Qed.

Lemma GlobalWeakening:
forall G G' Ctx Ctx' M A
  (HT: G ++ G' |= Ctx |- M ::: A)
  (H_ok: ok_Bg (Ctx :: G & Ctx' ++ G')),
  G & Ctx' ++ G' |= Ctx |- M ::: A.
intros; rew_app.
apply BackgroundSubsetImpl with (G:=G++G'); auto.
exists (Ctx'::nil); rew_app; symmetry; auto.
rew_app in *; auto.
Qed.

Lemma Weakening_general:
  forall G w Gamma M A
  (HT: G |= (w, Gamma) |- M ::: A),
  (forall G' w' Delta Delta',
    PPermut G (G' & (w', Delta)) ->
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
apply t_lam_LF with (L:=L \u used_t_vars ((w0, Gamma0) :: G' & (w', Delta ++ Delta'))).
  auto.
  intros; eapply H; eauto.
apply t_lam_LF with (L:=L \u used_t_vars ((w0, Gamma0++Gamma')::G)). 
auto.
intros; eapply H with (v':=v')  (w:=w0) (Gamma:=(v' ,A)::Gamma0); auto.
rew_app; auto.
(* appl *)
econstructor; [ | eapply IHHT1| eapply IHHT2]; eauto.
econstructor; [ | eapply IHHT1| eapply IHHT2]; eauto.
(* box 1 *)
apply t_box_LF with (L:=L \u used_w_vars (G' & (w0, Gamma0) & (w', Delta ++ Delta'))); 
intros.
apply ok_Bg_ppermut with (G:=(w0, Gamma0) :: G' & (w', Delta ++ Delta')); auto.
assert (G' & (w', Delta ++ Delta') & (w0, Gamma0) ~=~ G' & (w0, Gamma0) & (w', Delta ++ Delta')) by auto;
rewrite H3;
apply H with (w:=w'0) (Gamma:=nil); assumption || eauto.
apply ok_Bg_fresh_wo; auto. 
apply ok_Bg_ppermut with (G:=((w0, Gamma0) :: G' & (w', Delta ++ Delta')));
auto.
(* box 2 *)
apply t_box_LF with (L:=L \u used_w_vars (G & (w0, Gamma0++Gamma'))).
apply ok_Bg_ppermut with (G:= (w0, Gamma0++Gamma') :: G); auto.
intros; eapply H; eauto. 
apply ok_Bg_fresh_wo; auto.
apply ok_Bg_ppermut with (G:=(w0, Gamma0++Gamma')::G); auto.
(* unbox *)
constructor. auto. eapply IHHT; eauto.
constructor. auto. eapply IHHT; eauto.
(* unbox_fetch 1 *)
destruct (permut_context_LF_dec (w'0, Delta) (w, Gamma)) as [Eq|Neq]; simpl in *.
(* = *)
destruct Eq; subst;
assert (G ~=~ G'0) by
   (apply PPermut_last_rev with (Gamma := Gamma) (Gamma':= Delta) (w:=w);
    [ apply permut_sym |
      transitivity G' ]; auto).
assert ((w0, Gamma0) :: G'0 & (w, Delta ++ Delta') ~=~ (w, Gamma ++ Delta') :: G & (w0, Gamma0)).
  rewrite H3.
  transitivity ((w, Delta ++ Delta') :: G'0 & (w0, Gamma0)).
    transitivity ((w0, Gamma0) :: (w, Delta ++ Delta') :: G'0).
      auto.
      transitivity ((w, Delta ++ Delta') :: (w0, Gamma0) :: G'0).
        auto.
        auto.
    auto.
apply t_unbox_fetch_LF with (G:=G) (Gamma:=Gamma++Delta').
rewrite <- H4; auto.
apply IHHT; auto.
rewrite <- H4; auto.
rewrite H3; auto.
(* <> *)
assert (exists G0, exists G1, G'0 = G0 & (w, Gamma) ++ G1) by
  ( apply PPermut_split_neq with (G':=G) (w:=w'0) (Gamma := Delta);
    [ symmetry; transitivity G' | ]; auto).
destruct H2 as [GH]; destruct H2 as [GT]; subst G'0.
apply t_unbox_fetch_LF with (Gamma:=Gamma) (G:=GH ++ GT & (w'0, Delta ++ Delta')).
apply ok_Bg_ppermut with 
  (G := (w0, Gamma0) :: (GH & (w, Gamma) ++ GT) & (w'0, Delta ++ Delta')).
rew_app. assert ( GH ++ (w, Gamma) :: GT & (w'0, Delta ++ Delta') ~=~ (w, Gamma) :: GH ++ GT ++ (w'0, Delta ++ Delta') :: nil) by auto.
rewrite H2. transitivity (((w, Gamma) :: GH ++ GT ++ (w'0, Delta ++ Delta') :: nil) & (w0, Gamma0)). auto. rew_app; auto.
auto.
apply PPermut_bg with (G:= (GH ++ GT & (w0, Gamma0)) & (w'0, Delta ++ Delta')).
  apply IHHT with (w1:=w) (Gamma1:=Gamma) (G':=GH ++ GT & (w0, Gamma0)); auto.
  assert (G ~=~ GH ++ GT & (w'0, Delta)).
     apply PPermut_last_rev_simpl with (a:=(w, Gamma)).
     transitivity G'. 
       auto. 
       rew_app in *; transitivity (GH ++ (w, Gamma) :: GT & (w'0, Delta)).
         auto.
         transitivity (GH ++ GT ++ (w, Gamma) :: (w'0, Delta) :: nil); auto.
  rewrite H2; rew_app; auto.
  rew_app in *.
  apply ok_Bg_ppermut with (G:= (w0, Gamma0) :: GH ++ (w, Gamma) :: GT & (w'0, Delta ++ Delta')); auto.
transitivity (((w0, Gamma0) :: GH ++ GT ++ (w, Gamma) :: nil) & (w'0, Delta++Delta')). 
rew_app; auto.
transitivity (((w, Gamma) :: GH ++ GT ++ (w0, Gamma0) :: nil) & (w'0, Delta ++ Delta')); auto. rew_app; auto.
rew_app; auto.
rew_app; transitivity (GH ++ GT ++ (w, Gamma) :: (w'0, Delta++Delta') :: nil);
[ | symmetry]; auto.
(* unbox_fetch 2 *)
apply t_unbox_fetch_LF with (G:=G) (Gamma:=Gamma).
rewrite <- H in H0.
apply ok_Bg_ppermut with (G:=(w0, Gamma0 ++ Gamma'0) :: G & (w, Gamma)); auto.
apply IHHT with (w1:=w) (Gamma1:=Gamma); auto.
rewrite <- H in H0.
apply ok_Bg_ppermut with (G:=(w0, Gamma0 ++ Gamma'0) :: G & (w, Gamma)); auto.
auto.
(* here *)
constructor. auto. apply IHHT with (w:=w0)(Gamma:=Gamma0); auto. 
constructor. auto. apply IHHT; auto.
(* get_here 1 *)
destruct (permut_context_LF_dec (w', Delta) (w, Gamma)) as [Eq|Neq]; simpl in *.
(* = *)
destruct Eq; subst;
assert (G ~=~ G'0) by
   (apply PPermut_last_rev with (Gamma := Gamma) (Gamma':= Delta) (w:=w);
    [ apply permut_sym |
      transitivity G' ]; auto).
assert ((w0, Gamma0) :: G'0 & (w, Delta ++ Delta') ~=~ (w, Gamma ++ Delta') :: G & (w0, Gamma0)).
  rewrite H3.
  transitivity ((w, Delta ++ Delta') :: G'0 & (w0, Gamma0)).
    transitivity ((w0, Gamma0) :: (w, Delta ++ Delta') :: G'0).
      auto.
      transitivity ((w, Delta ++ Delta') :: (w0, Gamma0) :: G'0).
        auto.
        auto.
    auto.
apply t_get_here_LF with (G:=G) (Gamma:=Gamma++Delta').
rewrite <- H4; auto.
apply IHHT; auto.
rewrite <- H4; auto.
rewrite H3; auto.
(* <> *)
assert (exists G0, exists G1, G'0 = G0 & (w, Gamma) ++ G1) by
  ( apply PPermut_split_neq with (G':=G) (w:=w') (Gamma := Delta);
    [ symmetry; transitivity G' | ]; auto).
destruct H2 as [GH]; destruct H2 as [GT]; subst G'0.
apply t_get_here_LF with (Gamma:=Gamma) (G:=GH ++ GT & (w', Delta ++ Delta')).
apply ok_Bg_ppermut with 
  (G := (w0, Gamma0) :: (GH & (w, Gamma) ++ GT) & (w', Delta ++ Delta')).
rew_app. assert ( GH ++ (w, Gamma) :: GT & (w', Delta ++ Delta') ~=~ (w, Gamma) :: GH ++ GT ++ (w', Delta ++ Delta') :: nil) by auto.
rewrite H2. transitivity (((w, Gamma) :: GH ++ GT ++ (w', Delta ++ Delta') :: nil) & (w0, Gamma0)). auto. rew_app; auto.
auto.
apply PPermut_bg with (G:= (GH ++ GT & (w0, Gamma0)) & (w', Delta ++ Delta')).
  apply IHHT with (w1:=w) (Gamma1:=Gamma) (G':=GH ++ GT & (w0, Gamma0)); auto.
  assert (G ~=~ GH ++ GT & (w', Delta)).
     apply PPermut_last_rev_simpl with (a:=(w, Gamma)).
     transitivity G'. 
       auto. 
       rew_app in *; transitivity (GH ++ (w, Gamma) :: GT & (w', Delta)).
         auto.
         transitivity (GH ++ GT ++ (w, Gamma) :: (w', Delta) :: nil); auto.
  rewrite H2; rew_app; auto.
  rew_app in *.
  apply ok_Bg_ppermut with (G:= (w0, Gamma0) :: GH ++ (w, Gamma) :: GT & (w', Delta ++ Delta')); auto.
transitivity (((w0, Gamma0) :: GH ++ GT ++ (w, Gamma) :: nil) & (w', Delta++Delta')). 
rew_app; auto.
transitivity (((w, Gamma) :: GH ++ GT ++ (w0, Gamma0) :: nil) & (w', Delta ++ Delta')); auto. rew_app; auto.
rew_app; auto.
rew_app; transitivity (GH ++ GT ++ (w, Gamma) :: (w', Delta++Delta') :: nil);
[ | symmetry]; auto.
(* get_here 2 *)
apply t_get_here_LF with (G:=G) (Gamma:=Gamma).
rewrite <- H in H0.
apply ok_Bg_ppermut with (G:=(w0, Gamma0 ++ Gamma') :: G & (w, Gamma)); auto.
apply IHHT with (w1:=w) (Gamma1:=Gamma); auto.
rewrite <- H in H0.
apply ok_Bg_ppermut with (G:=(w0, Gamma0 ++ Gamma') :: G & (w, Gamma)); auto.
auto.
(* letdia *)
apply t_letdia_LF with (A:=A) (L_w:=L_w \u used_w_vars((w0, Gamma0) :: G' & (w', Delta ++ Delta'))) (L_t:=L_t \u used_t_vars ((w0, Gamma0) :: G' & (w', Delta ++ Delta'))).
auto.
apply IHHT with (w:=w0) (Gamma:=Gamma0); auto.
intros; destruct H with (v':=v') (w':=w'0) (w:=w0) (Gamma:=Gamma0); auto.
replace ((w'0, (v', A) :: nil) :: G' & (w', Delta ++ Delta')) with
   (((w'0, (v', A) :: nil) :: G') & (w', Delta ++ Delta')) by
   (rew_app; reflexivity).
apply H4; rew_app; auto.
apply ok_Bg_ppermut with (G:=(w'0, (v', A) :: nil) :: (w0, Gamma0) :: G' & (w', Delta ++ Delta')). auto.
apply ok_Bg_fresh_wo_te; auto.
eapply t_letdia_LF with (A:=A) (L_t := L_t \u used_t_vars ((w0, Gamma0 ++ Gamma') :: G))
  (L_w := L_w \u used_w_vars ((w0, Gamma0 ++ Gamma') :: G)).
auto.
apply IHHT; auto.
intros; eapply H; eauto.
apply ok_Bg_ppermut with (G:=(w', (v', A) :: nil) :: (w0, Gamma0 ++ Gamma') :: G).
auto. 
apply ok_Bg_fresh_wo_te; auto.
(* letdia_get 1 *)
destruct (permut_context_LF_dec (w', Delta) (w, Gamma)) as [Eq | Neq]; simpl in *.
(* = *)
destruct Eq; subst;
assert (G ~=~ G').
  apply PPermut_last_rev with (w:=w) (Gamma:=Gamma) (Gamma':=Delta);
  [apply permut_sym | transitivity G0]; auto. 
apply t_letdia_get_LF with (Gamma:=Gamma++Delta') (G:=G) (A:=A) (L_w:=L_w \u used_w_vars ((w0, Gamma0) :: G & (w, Gamma ++ Delta'))) (L_t:=L_t \u used_t_vars ((w0, Gamma0) :: G & (w, Gamma ++ Delta'))).
apply ok_Bg_ppermut with (G:=(w0, Gamma0) :: G' & (w, Delta ++ Delta')).
rewrite <- H4;
transitivity ((w, Delta ++ Delta') :: G & (w0, Gamma0)); auto.
auto.
apply IHHT; auto.
apply ok_Bg_ppermut with (G:=(w0, Gamma0) :: G' & (w, Delta ++ Delta')).
rewrite <- H4;
transitivity ((w, Delta ++ Delta') :: G & (w0, Gamma0)); auto.
auto.
intros; destruct H with (v':=v') (w':=w') (w1:=w0) (Gamma1:=Gamma0); eauto.
replace ( (w', (v', A) :: nil) :: G & (w, Gamma ++ Delta') ) with
  (( (w', (v', A) :: nil) :: G) & (w, Gamma ++ Delta')) by
  (rew_app; reflexivity).
eapply H7; auto.
apply ok_Bg_ppermut with (G:=(w', (v', A) :: nil ) :: (w0, Gamma0) :: G & (w, Gamma ++ Delta')). rew_app; auto. apply ok_Bg_fresh_wo_te; auto. apply ok_Bg_ppermut with (G:=(w0, Gamma0) :: G' & (w, Delta ++ Delta')); auto.
rewrite H4; auto.
(* <> *)
assert (exists G0, exists G1, G' = G0 & (w, Gamma) ++ G1) by 
  ( apply PPermut_split_neq with (G':=G) (w:=w') (Gamma := Delta);
    [ symmetry; transitivity G0 | ]; auto).
destruct H3 as [GH]; destruct H3 as [GT]; subst G'.
assert (G ~=~ GH ++ GT & (w', Delta)).
  apply PPermut_last_rev_simpl with (a:=(w, Gamma)).
  transitivity G0. 
  auto. 
  rew_app in *; transitivity (GH ++ (w, Gamma) :: GT & (w', Delta)).
  auto.
  transitivity (GH ++ GT ++ (w, Gamma) :: (w', Delta) :: nil); auto.
apply t_letdia_get_LF with 
  (Gamma:=Gamma) (G:=GH ++ GT & (w', Delta ++ Delta')) (L_w:=L_w \u used_w_vars ((w0, Gamma0) :: (GH & (w, Gamma) ++ GT) & (w', Delta ++ Delta'))) (L_t:=L_t \u used_t_vars ((w0, Gamma0) :: (GH & (w, Gamma) ++ GT) & (w', Delta ++ Delta')))(A:=A).
apply ok_Bg_ppermut with (G:=(w0, Gamma0) :: (GH & (w, Gamma) ++ GT) & (w', Delta ++ Delta')); rew_app in *; auto.
transitivity ((w0, Gamma0) :: (w, Gamma) :: GH ++ GT & (w', Delta ++ Delta')).
auto. transitivity (((w,Gamma) :: GH ++ GT & (w', Delta++Delta')) & (w0, Gamma0));
auto. rew_app; auto.
apply PPermut_bg with (G:= (GH ++ GT & (w0, Gamma0)) & (w', Delta ++ Delta')).
apply IHHT with (w1:=w) (Gamma1:=Gamma); auto. 
rewrite H3; rew_app; auto.  
rew_app; apply ok_Bg_ppermut with (G:=(w0, Gamma0) :: (GH & (w, Gamma) ++ GT) & (w', Delta ++ Delta')); auto.
rew_app. transitivity ((w0, Gamma0) :: (w, Gamma) :: GH ++ GT & (w', Delta ++ Delta')).
auto. transitivity (((w,Gamma) :: GH ++ GT & (w', Delta++Delta')) & (w0, Gamma0));
auto. rew_app; auto.
rew_app; auto.
intros; destruct H with (v':=v')(w':=w'0) (w1:=w0) (Gamma1:=Gamma0); auto.
apply PPermut_bg with 
  (G:=((w'0, (v', A)::nil) :: GH++GT & (w, Gamma)) & (w', Delta ++ Delta')).
  apply H6.
  rew_app; constructor; [auto | ].
  rewrite H3; rew_app; auto.
  apply ok_Bg_ppermut with (G:= ((w'0, (v', A) :: nil) ::(w0, Gamma0) :: GH & (w, Gamma) ++ GT) & (w', Delta ++ Delta')).
  rew_app; auto. transitivity (((w'0, (v', A) :: nil) ::(w0, Gamma0) :: GH ++GT & (w, Gamma)) & (w', Delta ++ Delta')); rew_app; auto. 
rew_app in *.
  apply ok_Bg_fresh_wo_te; auto.
  rew_app; auto.
  rew_app; auto.
(* letdia_get 2 *)
apply t_letdia_get_LF with (G:=G) (Gamma:=Gamma) (A:=A) (L_w:=L_w \u used_w_vars (((w0, Gamma0 ++ Gamma') :: G & (w, Gamma))))(L_t:=L_t \u used_t_vars ((w0, Gamma0 ++ Gamma') :: G & (w, Gamma))).
clear IHHT H HT2. rewrite <- H0 in H1. apply ok_Bg_ppermut with (G:=(w0, Gamma0 ++ Gamma') :: G & (w, Gamma)); auto.
apply IHHT with (w1:=w) (Gamma1:=Gamma); auto.
rewrite <- H0 in H1. apply ok_Bg_ppermut with (G:=(w0, Gamma0 ++ Gamma') :: G & (w, Gamma)); auto.
intros; destruct H with (v':=v')(w':=w') (w1:=w0)(Gamma1:=Gamma0); auto.  
apply H5.
apply ok_Bg_ppermut with (G:= (w', (v', A)::nil) :: (w0, Gamma0 ++ Gamma') :: G & (w, Gamma)). auto. apply ok_Bg_fresh_wo_te. clear IHHT H4 H5 HT2 H. rewrite H0; auto.
auto.
assumption.
Qed.

Lemma WeakeningBackgroundElem:
forall G G' w Delta Delta' Ctx M A
  (H_ok: ok_Bg (Ctx :: G & (w, Delta ++ Delta') ++ G'))
  (HT: G & (w, Delta) ++ G' |= Ctx |- M ::: A),
  G & (w, Delta ++ Delta') ++ G' |= Ctx |- M ::: A.
intros;
apply BackgroundSubsetImpl with (G:=(G++G') & (w, Delta ++ Delta')).
destruct Ctx; eapply Weakening_general; eauto.
apply ok_Bg_ppermut with (G:=(v, l) :: G & (w, Delta ++ Delta') ++ G'); auto.
eexists nil; rew_app; symmetry; auto.
auto.
Qed.

Lemma Weakening:
forall G w Gamma Gamma' M A
  (H_ok: ok_Bg ((w,Gamma++Gamma')::G))
  (HT: G |= (w, Gamma) |- M ::: A),
  G |= (w, Gamma ++ Gamma') |- M ::: A.
intros;
eapply Weakening_general; eassumption.
Qed.

(* emptyEquiv = map (fun x => (x, nil)) (map fst G) *)
Fixpoint emptyEquiv (G: Background_LF) : Background_LF :=
match G with
| nil => nil
| (w, a)::G => (w, nil) :: emptyEquiv G
end.

(* FIXME: Admitted :( *)
Lemma types_weakened:
forall G w Gamma M A
  (Ok: ok_Bg ((w, Gamma)::G))
  (HT: emptyEquiv G |= (w, nil) |- M ::: A),
  G |= (w, Gamma) |- M ::: A.
Admitted.

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
    PPermut G (G0 & (w', (v,A)::Gamma')) ->
    PPermut G' (G0 & (w, Gamma)) ->
    PPermut G'' (G0 & (w', Gamma')) ->
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
inversion H1; subst.
assert (A = A0) by skip. (* Ok_Bg + HT *)
subst; apply types_weakened. skip. (* ok_Bg *)
assumption.
constructor.
skip. (* ok_Bg *)
apply Mem_permut with (L2 := (v0, A0) :: Gamma1) in HT; auto;
rewrite Mem_cons_eq in HT; destruct HT; auto;
inversion H2; subst; elim H1; reflexivity.
case_if.
inversion H3; subst.
(* v = v0 ->
   Ok_Bg + H + H0 + HT -->
   v0 occurs both in Gamma0 and in G -->
   contradiction *)
skip.

constructor.
skip. (* ok_Bg *)
assumption.
(* lam *)
apply t_lam_LF with (L:=L \u \{v}).
skip. (* ok_Bg *)
intros.
rewrite notin_union in H2; rewrite notin_singleton in H2; destruct H2.
unfold open_var in *.
rewrite <- subst_var_comm.
eapply H; eauto.
permut_simpl; assumption.
intro; elim H3; subst; auto.
auto.

apply t_lam_LF with (L:=L \u \{v}).
skip. (* ok_Bg *)
intros.
rewrite notin_union in H4; rewrite notin_singleton in H4; destruct H4.
unfold open_var in *.
rewrite <- subst_var_comm.
eapply H; eauto.
skip. (* empty equiv + permut *)
intro; subst; elim H5; auto.
auto.
(* appl *)
econstructor; [ skip | eapply IHHT1 | eapply IHHT2]; eauto.
econstructor; [ skip | eapply IHHT1 | eapply IHHT2]; eauto.
(* box *)
apply t_box_LF with (L:=L); [skip | intros].
unfold open_ctx.
rewrite <- subst_order_irrelevant_bound.
eapply H; eauto.
skip.
auto.

econstructor; [skip | intros].
unfold open_ctx.
rewrite <- subst_order_irrelevant_bound.
eapply H with (G'' := G'' & (w0, Gamma0)); eauto.
skip.
auto.
(* unbox *)
econstructor; [skip | eapply IHHT]; eauto.
econstructor; [skip | eapply IHHT]; eauto.
(* unbox_fetch *)
apply t_unbox_fetch_LF with (G:=G) (Gamma:=Gamma); auto.
skip. (* ok_Bg *)
eapply IHHT; eauto.
skip. (* emptyEquiv + permut *)

assert (w <> w0) by skip. (* from Ok_Bg *)
assert (w <> w'0) by skip. (* Ok_bg + H + H0 *) 
(* H0 + H + ok_Bg + w <> w'0 -->
   G & (w, Gamma) ~=~ G0 & (w'0, (v, A0) :: Gamma'0) -->
   exists GH, exists GT, G = GH & (w'0, (v,A0)::Gamma'0) ++ GT. *)
assert (G & (w, Gamma) ~=~ G0 & (w'0, (v, A0) :: Gamma'0)) by
  (transitivity G'; auto).
assert (exists GH, exists GT, G = GH & (w'0, (v, A0)::Gamma'0) ++ GT) by
  (apply PPermut_split_neq with (w:=w) (Gamma:=Gamma) (G':=G0); auto).
destruct H7 as (GH, H7); destruct H7 as (GT, H7).
apply t_unbox_fetch_LF with (G:=GH ++ GT & (w'0, Gamma'0)) (Gamma:=Gamma).
skip. (* ok_Bg *)
eapply IHHT with (w1:=w) (Gamma1:=Gamma) (w':=w'0) (Gamma':=Gamma'0)
                 (G0:=GH ++ GT & (w0, Gamma0)); rew_app; auto; subst.
rew_app; auto.
skip. (* emptyEquiv + permut *)
subst; rew_app in *.
transitivity (G0 & (w'0, Gamma'0)); 
[ apply PPermut_specialized2 with (Gamma:= (w'0, (v, A0) :: Gamma'0)) | symmetry]; auto.
(* here *)
econstructor; [skip | eapply IHHT]; eauto.
econstructor; [skip | eapply IHHT]; eauto.
(* get_here *)
apply t_get_here_LF with (G:=G) (Gamma:=Gamma); auto.
skip. (* ok_Bg *)
eapply IHHT; eauto.
skip. (* emptyEquiv + permut *)

assert (w <> w0) by skip. (* from Ok_Bg *)
assert (w <> w') by skip. (* Ok_bg + H + H0 *) 
(* H0 + H + ok_Bg + w <> w'0 -->
   G & (w, Gamma) ~=~ G0 & (w'0, (v, A0) :: Gamma'0) -->
   exists GH, exists GT, G = GH & (w', (v,A0)::Gamma'0) ++ GT. *)
assert (G & (w, Gamma) ~=~ G0 & (w', (v, A0) :: Gamma')) by
  (transitivity G'; auto).
assert (exists GH, exists GT, G = GH & (w', (v, A0)::Gamma') ++ GT) by
  (apply PPermut_split_neq with (w:=w) (Gamma:=Gamma) (G':=G0); auto).
destruct H8 as (GH, H8); destruct H8 as (GT, H8).
apply t_get_here_LF with (G:=GH ++ GT & (w', Gamma')) (Gamma:=Gamma).
skip. (* ok_Bg *)
eapply IHHT with (w1:=w) (Gamma1:=Gamma) (w':=w') (Gamma':=Gamma')
                 (G0:=GH ++ GT & (w0, Gamma0)); rew_app; auto; subst.
rew_app; auto.
skip. (* emptyEquiv + permut *)
subst; rew_app in *.
transitivity (G0 & (w', Gamma')); 
[ apply PPermut_specialized2 with (Gamma:= (w', (v, A0) :: Gamma')) | symmetry]; auto.
(* letdia *)
eapply t_letdia_LF with (L_t := L_t \u \{v}); [skip | eapply IHHT | intros]; eauto.
unfold open_var in *. unfold open_ctx in *.
rewrite notin_union in H2; rewrite notin_singleton in H2; destruct H2.
rewrite <- subst_order_irrelevant_bound.
rewrite <- subst_var_comm.
eapply H; eauto.
skip. (* weakening + assumption *)
intro; subst; elim H4; auto.
assumption.
assumption.

eapply t_letdia_LF with (L_t := L_t \u \{v}); [skip | eapply IHHT | intros]; eauto.
unfold open_var in *. unfold open_ctx in *.
rewrite notin_union in H4; rewrite notin_singleton in H4; destruct H4.
rewrite <- subst_order_irrelevant_bound.
rewrite <- subst_var_comm.
eapply H with (G0:=(w'0, (v',A)::nil)::G0) (w'0:=w') (Gamma':=Gamma') (A0:=A0); eauto.
skip.
intro; subst; elim H6; auto.
assumption.
assumption.

(* letdia_get *)
assert (w <> w0) by skip. (* from Ok_bg *)
eapply t_letdia_get_LF with (G:=G) (Gamma:=Gamma) (L_t := L_t \u \{v}); eauto.
skip. (* ok_Bg *)
eapply IHHT; eauto.
skip.
intros. 
unfold open_var in *; unfold open_ctx in *.
rewrite notin_union in H5; rewrite notin_singleton in H5; destruct H5.
rewrite <- subst_order_irrelevant_bound.
rewrite <- subst_var_comm.
eapply H; eauto.
skip. (* weakening + permut + assumption *)
intro; subst; elim H7; auto.
auto.
auto.

assert (w <> w0) by skip. (* from ok_Bg *)
destruct (eq_var_dec w w').
subst.
(* from ok_Bg + H0 + H1 *)
assert (Gamma = (v, A0) :: Gamma') by skip.
assert (G1 = G) by skip.
subst.
eapply t_letdia_get_LF with (G:=G) (Gamma:=Gamma') (L_t:=L_t \u \{v}); auto.
skip. (* ok_Bg *)
eapply IHHT; eauto.
skip. (* permut + emptyEquiv *)
intros.
unfold open_var in *; unfold open_ctx in *.
rewrite notin_union in H7; rewrite notin_singleton in H7; destruct H7.
rewrite <- subst_order_irrelevant_bound.
rewrite <- subst_var_comm.
eapply H with (G0:=G & (w'0, (v', A)::nil) ) (w'1:=w') (Gamma'0:=Gamma'); eauto.
skip. (* Weakening + permut + assumption *)
auto.
auto.
auto.

(* w <> w' /\
   Ok Bg /\
   (G & (w, Gamma)) ~=~ G0
   G0 ~=~ (G1 & (w', (v, A0) :: Gamma')) -->
   G & (w, Gamma) ~=~ G1 & (w', (v,A0)::Gamma') -->
   exists GH, exists GT, G1 = GH & (w, Gamma) ++ GT *)
assert (G & (w, Gamma) ~=~ G1 & (w', (v, A0) :: Gamma')) by
  (transitivity G0; auto).
symmetry in H7.
assert (exists GH, exists GT, G1 = GH & (w, Gamma) ++ GT) by
  (apply PPermut_split_neq with (w:=w') (Gamma:=(v,A0) :: Gamma') (G':=G); auto).
destruct H8 as (GH, H8). destruct H8 as (GT, H8).
eapply t_letdia_get_LF with (G:=GH++GT & (w', Gamma')) (Gamma:=Gamma) (L_t:=L_t \u \{v}) (L_w:=L_w).
skip. (* ok_Bg *)
eapply IHHT with (w1:=w) (Gamma1:=Gamma) (A0:=A0) (w':=w') (G0:=GH++GT & (w0,Gamma0)) (Gamma':=Gamma'); auto.
symmetry; subst; rew_app in *; apply PPermut_specialized2 with (Gamma := (w, Gamma)); auto.
rew_app; auto.
skip. (* permut + assumption *)
intros.
unfold open_var in *; unfold open_ctx in *.
rewrite notin_union in H9; rewrite notin_singleton in H9; destruct H9.
rewrite <- subst_order_irrelevant_bound.
rewrite <- subst_var_comm.
eapply H with (v':=v') (w':=w'0) (Gamma1:=Gamma0) (w1:=w0) (A0:=A0) 
              (v:=v) (G0:=(w'0, (v', A) :: nil) :: (GH ++ GT) & (w, Gamma)) 
              (w'0:=w') (Gamma':=Gamma'); auto.
rew_app; constructor; auto;
symmetry; transitivity (G1 & (w', (v, A0) :: Gamma')); auto;
subst; rew_app; auto.
rew_app; constructor; auto.
skip. (* Weakening + permut + assumption *)
intro; elim H11; auto.
auto.
auto.
symmetry; transitivity (G1 & (w', Gamma')); subst; rew_app in *; auto.
Qed.

Lemma subst_t_preserv_types_inner:
forall G w Gamma A B M N v
  (H_lc_t: lc_t_LF M)
  (H_lc_w: lc_w_LF M)
  (HT: G |= (w, (v, A) :: Gamma) |- N ::: B)
  (HM: emptyEquiv G |= (w, nil) |- M ::: A),
  G |= (w, Gamma) |- [M//fte v] N ::: B.
intros;
eapply subst_t_preserv_types with (Gamma := (v, A) :: Gamma); eauto.
Qed.  

Lemma subst_t_preserv_types_outer:
forall G0 G G' G'' w w' Gamma Gamma' A B M N v
  (H_lc_t: lc_t_LF M)
  (H_lc_w: lc_w_LF M)
  (G0G: PPermut G (G0 & (w', (v, A) :: Gamma')))
  (G0G': PPermut G' (G0 & (w, Gamma)))
  (G0G'': PPermut G'' (G0 & (w', Gamma')))
  (HM: emptyEquiv G' |= (w', nil) |- M ::: A)
  (HT: G |= (w, Gamma) |- N ::: B),
  G'' |= (w, Gamma) |- [M // fte v] N ::: B.
intros; 
eapply subst_t_preserv_types; eauto. 
Qed.  

Lemma rename_w_preserv_types:
forall G w Gamma A M G' w' Gamma'
  (HT: G |= (w, Gamma) |- M ::: A),
  (* "new" substitution *)
  ( PPermut G (G' & (w', Gamma')) ->
    G' |= (w, Gamma ++ Gamma') |- {{ fwo w // fwo w' }} M ::: A) /\
  (* "old" substitution *)
  ( PPermut G (G' & (w', Gamma')) ->
    G' |= (w', Gamma' ++ Gamma) |- {{ fwo w' // fwo w }} M ::: A) /\
  (* "outer" substitution *)
  (forall G0 w'' Gamma'',
    PPermut G (G0 & (w', Gamma') & (w'', Gamma'')) ->
    PPermut G' (G0 & (w', Gamma' ++ Gamma'')) ->
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
[ skip | (* ok_Bg will need some lemmas later on *)
  rewrite Mem_app_or_eq; left; auto].
constructor;
[ skip | (* ok_Bg *)
  rewrite Mem_app_or_eq; right; auto].
constructor; 
[ skip | (* ok_Bg *) 
  auto].
(* lam *)
apply t_lam_LF with (L := L);
[ skip | (* ok_Bg *)
  intros]; unfold open_var in *;
rewrite subst_order_irrelevant_free;
try (eapply H with (v':=v') (G':=G') (Gamma := (v',A)::Gamma0));
eauto;
simpl; apply notin_empty. 
apply t_lam_LF with (L := L);
[ skip | (* ok_Bg *)
  intros]; unfold open_var in *;
rewrite subst_order_irrelevant_free;
edestruct H; eauto; destruct H3.
apply ContextPermutImpl with (Gamma := (Gamma' ++ (v', A) :: Gamma0)); [permut_simpl | ];
eauto.
simpl; apply notin_empty. 
apply t_lam_LF with (L := L);
[ skip | (* ok_Bg *)
  intros]; unfold open_var in *;
rewrite subst_order_irrelevant_free;
edestruct H; eauto; destruct H4;
eauto;
simpl; apply notin_empty. 
(* appl *)
apply t_appl_LF with (A:=A);
[ skip |  (* ok_Bg *)
  apply IHHT1 with (Gamma:=Gamma0) |
  apply IHHT2 with (Gamma:=Gamma0) ]; 
eauto.
apply t_appl_LF with (A:=A);
[ skip |  (* ok_Bg *)
  apply IHHT1 with (Gamma:=Gamma0) |
  apply IHHT2 with (Gamma:=Gamma0) ]; 
eauto.
apply t_appl_LF with (A:=A);
[ skip |  (* ok_Bg *)
  eapply IHHT1 |
  eapply IHHT2 ]; 
eauto.
(* box *)
apply t_box_LF with (L:=\{w'} \u L);
[ skip | (* ok_Bg *)
  intros]; 
unfold open_ctx in *;
rewrite notin_union in H1; destruct H1;
rewrite notin_singleton in *;
rewrite <- subst_ctx_comm; auto;
eapply H; eauto.
apply t_box_LF with (L:=\{w0} \u L);
[ skip | (* ok_Bg *)
  intros]; 
unfold open_ctx in *;
rewrite notin_union in H1; destruct H1;
rewrite notin_singleton in *;
rewrite <- subst_ctx_comm; auto;
eapply H; eauto.
apply t_box_LF with (L:=\{w''} \u L);
[ skip | (* ok_Bg *)
  intros]; 
unfold open_ctx in *;
rewrite notin_union in H2; destruct H2;
rewrite notin_singleton in *;
rewrite <- subst_ctx_comm; auto;
eapply H with (G0:=G0 & (w0, Gamma0)) (Gamma':=Gamma') (Gamma'':=Gamma''); eauto.
(* unbox *)
case_if; 
(* w0 = w' 
   G ~=~ G' & (w', ..)
   ok_Bg (w0, ..) G --> ok_Bg (w0,.. ) (G' & w' ,..)
   -->
   contradiction *)
[ skip |
  constructor];
[ skip | (* ok_Bg *)
  apply IHHT with (Gamma:=Gamma0); eauto].
 
case_if; constructor;
[ skip | (* ok_Bg *)
  apply IHHT with (Gamma:=Gamma0); eauto].

case_if; 
(* ok_Bg ((w'', Gamma0) :: G) & G ~=~ (G0 & (w', ..) & (w'', ..)) -> contradiction*)
[ skip | 
  constructor];
[ skip | (* ok_Bg *)
  eapply IHHT; eauto].

(* unbox_fetch *)
case_if.
(* G' ~=~ G & (w, Gamma)
   G' ~=~ G'0 & (w'0, Gamma'0) -->
   G'0 & (w'0, Gamma'0) ~= G & (w, Gamma) 
   w = w'0
   ok_Bg (w, Gamma) :: G -->
   G'0 = G && Gamma'0 = Gamma *)
inversion H1; subst.
assert (Gamma *=* Gamma'0) by skip. (* H + H0 *)
assert (G ~=~ G'0).
  apply PPermut_last_rev with (w:=w'0) (Gamma:=Gamma) (Gamma':=Gamma'0);
  [ | transitivity G']; auto.
constructor.
skip.
apply ContextPermutImpl with (Gamma:=Gamma0 ++ Gamma);
[ permut_simpl |
  apply IHHT] ; auto.

(* H: G & (w, Gamma) ~=~ G'
   H0: G' ~=~ G'0 & (w'0, Gamma'0) -->
   G'0 & (w'0, Gamma'0) ~= G & (w, Gamma) 
   H1: w <> w'0 -->
   exists GH, exists GT, G'0 = GH & (w, Gamma) ++ GT *)
assert (G'0 & (w'0, Gamma'0) ~=~ G & (w, Gamma)). symmetry; transitivity G'; auto.
assert (exists GH, exists GT, G'0 = GH & (w, Gamma) ++ GT) as Split.
  eapply PPermut_split_neq; eauto; right; intro; subst; elim H1; reflexivity.
destruct Split as (GH, Split); destruct Split as (GT); subst.
apply t_unbox_fetch_LF with (G:=GH++GT) (Gamma:=Gamma).
skip.
eapply IHHT with (w1:=w) (Gamma1:=Gamma); auto.
apply PPermut_last_rev_simpl with (a:=(w, Gamma)); rew_app in *; auto.
rew_app; auto.

case_if.
(* w = w0 --> ok_Bg w,.. :: G & (w0, .. ) --> contradiction *)
skip.
destruct (eq_var_dec w w'0).
(* w = w'0 follows that G = G'0 and Gamma = Gamma'0 *)
subst.
assert (Gamma *=* Gamma'0) by skip. (* H + H0 *)
assert (G ~=~ G'0).
  apply PPermut_last_rev with (w:=w'0) (Gamma:=Gamma) (Gamma':=Gamma'0);
  [ | transitivity G']; auto.
subst; constructor.
skip.
apply ContextPermutImpl with (Gamma:=Gamma ++ Gamma0);
[ permut_simpl |
  eapply IHHT with (w:=w'0) (Gamma1:=Gamma) (Gamma':=Gamma0)] ; auto.

(* w <> w'0
   H & H0 -> G'0 & (w'0, Gamma'0) ~=~ G & (w, Gamma) -->
   exists GH, exists GT, G'0 = GH & (w, Gamma) ++ GT *)
assert (G'0 & (w'0, Gamma'0) ~=~ G & (w, Gamma)). symmetry; transitivity G'; auto.
assert (exists GH, exists GT, G'0 = GH & (w, Gamma) ++ GT) as Split.
  eapply PPermut_split_neq; eauto; right; intro; subst; elim H1; reflexivity.
destruct Split as (GH, Split); destruct Split as (GT); subst.
apply t_unbox_fetch_LF with (G:=GH++GT) (Gamma:=Gamma).
skip.
eapply IHHT; auto.
apply PPermut_last_rev_simpl with (a:=(w, Gamma)); rew_app in *.
transitivity (GH ++ GT ++ (w0, Gamma0) :: (w'0, Gamma'0) :: (w, Gamma) :: nil); auto.
rew_app; auto.

case_if.
(* w = w'' 
   (G0 & (w'0, Gamma'0) & (w'', Gamma'')) ~=~ G & (w, Gamma) -->
   G0 & (w'0, Gamma'0) ~=~ G /\ Gamma'' = Gamma *)
inversion H2; subst.
assert (Gamma *=* Gamma'') by skip. (* H + H0 *)
assert (G ~=~ G0 & (w'0, Gamma'0)).
  apply PPermut_last_rev with (w:=w'') (Gamma:=Gamma) (Gamma':=Gamma'');
  [ | transitivity G']; auto.
apply t_unbox_fetch_LF with (G:=G0) (Gamma := Gamma'0 ++ Gamma).
skip. (* ok_Bg *)
apply IHHT; auto.
rewrite H1; auto.

destruct (eq_var_dec w w'0).
(* w = w'0*)
subst.
assert (Gamma *=* Gamma'0) by skip. (* H + H0 *)
assert (G ~=~ G0 & (w'', Gamma'')).
  apply PPermut_last_rev with (w:=w'0) (Gamma:=Gamma) (Gamma':=Gamma'0);
  [ | transitivity G']; auto.   
  transitivity (G0 & (w'0, Gamma'0) & (w'', Gamma'')); auto.
apply t_unbox_fetch_LF with (G:=G0) (Gamma := Gamma ++ Gamma'').
skip. (* ok_Bg *)
eapply IHHT with (G':=G0 & (w0, Gamma0)) (Gamma' := Gamma''); auto.
rewrite H1; auto.

(* w <> w'0 /\ w <> w'
   H & H0 -> G0 & (w'0, Gamma'0) & (w'', Gamma'') ~=~ G & (w, Gamma) -->
   exists GH, exists GT, G0 = GH & (w, Gamma) ++ GT *)
assert (G0 & (w'0, Gamma'0) & (w'', Gamma'')  ~=~ G & (w, Gamma)). symmetry; transitivity G'; auto.
assert (exists GH, exists GT, G0 & (w'0, Gamma'0) = GH & (w, Gamma) ++ GT) as Split.
  apply PPermut_split_neq with (w:=w'') (Gamma:=Gamma'') (G':= G); eauto.
  right; intro; subst; elim H2; auto.
assert (exists GH, exists GT, G0 = GH & (w, Gamma) ++ GT) as Split'.
  destruct Split as (GH, Split); destruct Split as (GT).
  apply PPermut_split_neq with (w:=w'0) (Gamma:=Gamma'0) (G':=GH ++ GT).
  rew_app; transitivity (GH & (w, Gamma) ++ GT); 
    [ rewrite H4 | rewrite <- app_last; symmetry]; auto.
  right; intro; subst; elim n; reflexivity.
destruct Split' as (GH, Split'); destruct Split' as (GT).
apply t_unbox_fetch_LF with (G:=GH++GT & (w'0, Gamma'0++Gamma'')) (Gamma:=Gamma).
skip.
eapply IHHT with (w1:=w) (Gamma1:=Gamma) (G0:=GH++GT & (w0,Gamma0)) (Gamma':=Gamma'0) (Gamma'':=Gamma''); auto.

assert (G & (w, Gamma) ~=~ G0 & (w'0, Gamma'0) & (w'', Gamma'')) by (transitivity G'; auto).
subst; rew_app in *.
assert (G & (w, Gamma) ~=~ 
       (GH ++ GT ++ (w'0, Gamma'0) :: (w'', Gamma'') :: nil) &  (w, Gamma)).
transitivity (GH ++ (w, Gamma) :: GT ++  (w'0, Gamma'0) :: (w'', Gamma'') :: nil); auto.
transitivity ((GH ++ GT ++ (w'0, Gamma'0) :: (w'', Gamma'') :: nil) & (w0, Gamma0)).
apply PPermut_last; auto.
apply PPermut_last_rev_simpl with (a:=(w, Gamma)); auto.
rew_app; auto.
rew_app; auto.
rew_app; symmetry. 
transitivity (G0 & (w'0, Gamma'0 ++ Gamma'')); auto.
subst; rew_app; auto.

(* here  -- same as unbox *)
case_if; 
(* w0 = w' 
   G ~=~ G' & (w', ..)
   ok_Bg (w0, ..) G --> ok_Bg (w0,.. ) (G' & w' ,..)
   -->
   contradiction *)
[ skip |
  constructor];
[ skip | (* ok_Bg *)
  apply IHHT with (Gamma:=Gamma0); eauto].
 
case_if; constructor;
[ skip | (* ok_Bg *)
  apply IHHT with (Gamma:=Gamma0); eauto].

case_if; 
(* ok_Bg ((w'', Gamma0) :: G) & G ~=~ (G0 & (w', ..) & (w'', ..)) -> contradiction*)
[ skip | 
  constructor];
[ skip | (* ok_Bg *)
  eapply IHHT; eauto].

(* get_here *)
case_if.
(* G' ~=~ G & (w, Gamma)
   G' ~=~ G'0 & (w'0, Gamma'0) -->
   G'0 & (w'0, Gamma'0) ~= G & (w, Gamma) 
   w = w'0
   ok_Bg (w, Gamma) :: G -->
   G'0 = G && Gamma'0 = Gamma *)
inversion H2; subst.
assert (Gamma *=* Gamma') by skip. (* H + H0 *)
assert (G ~=~ G'0).
  apply PPermut_last_rev with (w:=w') (Gamma:=Gamma) (Gamma':=Gamma');
  [ | transitivity G']; auto.
constructor.
skip.
apply ContextPermutImpl with (Gamma:=Gamma0 ++ Gamma);
[ permut_simpl |
  apply IHHT] ; auto.

(* H: G & (w, Gamma) ~=~ G'
   H0: G' ~=~ G'0 & (w'0, Gamma'0) -->
   G'0 & (w'0, Gamma'0) ~= G & (w, Gamma) 
   H1: w <> w'0 -->
   exists GH, exists GT, G'0 = GH & (w, Gamma) ++ GT *)
assert (G'0 & (w', Gamma') ~=~ G & (w, Gamma)). symmetry; transitivity G'; auto.
assert (exists GH, exists GT, G'0 = GH & (w, Gamma) ++ GT) as Split.
  eapply PPermut_split_neq; eauto; right; intro; subst; elim H2; reflexivity.
destruct Split as (GH, Split); destruct Split as (GT); subst.
apply t_get_here_LF with (G:=GH++GT) (Gamma:=Gamma).
skip.
eapply IHHT with (w1:=w) (Gamma1:=Gamma); auto.
apply PPermut_last_rev_simpl with (a:=(w, Gamma)); rew_app in *; auto.
rew_app; auto.

case_if.
(* w = w0 --> ok_Bg w,.. :: G & (w0, .. ) --> contradiction *)
skip.
destruct (eq_var_dec w w').
(* w = w'0 follows that G = G'0 and Gamma = Gamma'0 *)
subst.
assert (Gamma *=* Gamma') by skip. (* H + H0 *)
assert (G ~=~ G'0).
  apply PPermut_last_rev with (w:=w') (Gamma:=Gamma) (Gamma':=Gamma');
  [ | transitivity G']; auto.
subst; constructor.
skip.
apply ContextPermutImpl with (Gamma:=Gamma ++ Gamma0);
[ permut_simpl |
  eapply IHHT with (w:=w') (Gamma1:=Gamma) (Gamma':=Gamma0)] ; auto.

(* w <> w'0
   H & H0 -> G'0 & (w'0, Gamma'0) ~=~ G & (w, Gamma) -->
   exists GH, exists GT, G'0 = GH & (w, Gamma) ++ GT *)
assert (G'0 & (w', Gamma') ~=~ G & (w, Gamma)). symmetry; transitivity G'; auto.
assert (exists GH, exists GT, G'0 = GH & (w, Gamma) ++ GT) as Split.
  eapply PPermut_split_neq; eauto; right; intro; subst; elim H1; reflexivity.
destruct Split as (GH, Split); destruct Split as (GT); subst.
apply t_get_here_LF with (G:=GH++GT) (Gamma:=Gamma).
skip.
eapply IHHT; auto.
apply PPermut_last_rev_simpl with (a:=(w, Gamma)); rew_app in *.
transitivity (GH ++ GT ++ (w0, Gamma0) :: (w', Gamma') :: (w, Gamma) :: nil); auto.
rew_app; auto.

case_if.
(* w = w'' 
   (G0 & (w'0, Gamma'0) & (w'', Gamma'')) ~=~ G & (w, Gamma) -->
   G0 & (w'0, Gamma'0) ~=~ G /\ Gamma'' = Gamma *)
inversion H3; subst.
assert (Gamma *=* Gamma'') by skip. (* H + H0 *)
assert (G ~=~ G0 & (w', Gamma')).
  apply PPermut_last_rev with (w:=w'') (Gamma:=Gamma) (Gamma':=Gamma'');
  [ | transitivity G']; auto.
apply t_get_here_LF with (G:=G0) (Gamma := Gamma' ++ Gamma).
skip. (* ok_Bg *)
apply IHHT; auto.
rewrite H1; auto.

destruct (eq_var_dec w w').
(* w = w'0*)
subst.
assert (Gamma *=* Gamma') by skip. (* H + H0 *)
assert (G ~=~ G0 & (w'', Gamma'')).
  apply PPermut_last_rev with (w:=w') (Gamma:=Gamma) (Gamma':=Gamma');
  [ | transitivity G']; auto.   
  transitivity (G0 & (w', Gamma') & (w'', Gamma'')); auto.
apply t_get_here_LF with (G:=G0) (Gamma := Gamma ++ Gamma'').
skip. (* ok_Bg *)
eapply IHHT with (G':=G0 & (w0, Gamma0)) (Gamma' := Gamma''); auto.
rewrite H1; auto.

(* w <> w'0 /\ w <> w'
   H & H0 -> G0 & (w'0, Gamma'0) & (w'', Gamma'') ~=~ G & (w, Gamma) -->
   exists GH, exists GT, G0 = GH & (w, Gamma) ++ GT *)
assert (G0 & (w', Gamma') & (w'', Gamma'')  ~=~ G & (w, Gamma)). symmetry; transitivity G'; auto.
assert (exists GH, exists GT, G0 & (w', Gamma') = GH & (w, Gamma) ++ GT) as Split.
  apply PPermut_split_neq with (w:=w'') (Gamma:=Gamma'') (G':= G); eauto.
  right; intro; subst; elim H2; auto.
assert (exists GH, exists GT, G0 = GH & (w, Gamma) ++ GT) as Split'.
  destruct Split as (GH, Split); destruct Split as (GT).
  apply PPermut_split_neq with (w:=w') (Gamma:=Gamma') (G':=GH ++ GT).
  rew_app; transitivity (GH & (w, Gamma) ++ GT); 
    [ rewrite H5 | rewrite <- app_last; symmetry]; auto.
  right; intro; subst; elim n; reflexivity.
destruct Split' as (GH, Split'); destruct Split' as (GT).
apply t_get_here_LF with (G:=GH++GT & (w', Gamma'++Gamma'')) (Gamma:=Gamma).
skip.
eapply IHHT with (w1:=w) (Gamma1:=Gamma) (G0:=GH++GT & (w0,Gamma0)) (Gamma':=Gamma') (Gamma'':=Gamma''); auto.

assert (G & (w, Gamma) ~=~ G0 & (w', Gamma') & (w'', Gamma'')) by (transitivity G'; auto).
subst; rew_app in *.
assert (G & (w, Gamma) ~=~ 
       (GH ++ GT ++ (w', Gamma') :: (w'', Gamma'') :: nil) &  (w, Gamma)).
transitivity (GH ++ (w, Gamma) :: GT ++  (w', Gamma') :: (w'', Gamma'') :: nil); auto.
transitivity ((GH ++ GT ++ (w', Gamma') :: (w'', Gamma'') :: nil) & (w0, Gamma0)).
apply PPermut_last; auto.
apply PPermut_last_rev_simpl with (a:=(w, Gamma)); auto.
rew_app; auto.
rew_app; auto.
rew_app; symmetry. 
transitivity (G0 & (w', Gamma' ++ Gamma'')); auto.
subst; rew_app; auto.

(* letdia *)
case_if.
(* w0 = w' ->
   ok_Bg w', Gamma0 :: G' & (w', Gamma') ->
   contradiction *)
skip.
apply t_letdia_LF with (L_w:=L_w \u \{w'}) (L_t:=L_t) (A:=A).
skip. (* ok_Bg *)
eapply IHHT with (w:=w0) (Gamma:=Gamma0); eauto.
intros. 
rewrite notin_union in H3; destruct H3.
rewrite notin_singleton in H4.
unfold open_var in *; unfold open_ctx in *.
rewrite <- subst_ctx_comm.
rewrite subst_order_irrelevant_free.
eapply H with (w:=w0) (Gamma:=Gamma0) (w':=w'0); eauto.
simpl; auto.
intro; subst; elim H4; reflexivity.

case_if.
apply t_letdia_LF with (L_w:=L_w \u \{w0}) (L_t:=L_t) (A:=A).
skip. (* ok_Bg *)
eapply IHHT with (w:=w0) (Gamma:=Gamma0); eauto.
intros. 
rewrite notin_union in H3; destruct H3.
rewrite notin_singleton in H4.
unfold open_var in *; unfold open_ctx in *.
rewrite <- subst_ctx_comm.
rewrite subst_order_irrelevant_free.
eapply H with (w:=w0) (Gamma:=Gamma0) (w':=w'0); eauto.
simpl; auto.
intro; subst; elim H4; reflexivity.

case_if.
(* w0 = w'' -> H0 + Ok_Bg = contradiction *)
skip. 
apply t_letdia_LF with (L_w:=L_w \u \{w''}) (L_t:=L_t) (A:=A).
skip. (* ok_Bg *)
eapply IHHT with (w:=w0) (Gamma:=Gamma0); eauto.
intros. 
rewrite notin_union in H4; destruct H4.
rewrite notin_singleton in H5.
unfold open_var in *; unfold open_ctx in *.
rewrite <- subst_ctx_comm.
rewrite subst_order_irrelevant_free.
eapply H with (w:=w0) (Gamma:=Gamma0) (G0:=G0 & ((w'0, (v', A)::nil))); eauto.
simpl; auto.
intro; subst; elim H5; reflexivity.

(* letdia_get *)
case_if.
inversion H3; subst.
(* w = w' ->
   H1 + H0 = G & w', Gamma ~=~ G' & w', Gamma' ->
   Gamma = Gamma' /\ G = G' *)
assert (Gamma *=* Gamma') by skip.
assert (G ~=~ G').
  apply PPermut_last_rev with (w:=w') (Gamma:=Gamma) (Gamma':=Gamma');
  [ | transitivity G0]; auto.
eapply t_letdia_LF with (L_w := L_w \u \{w'}).
skip. (* ok_Bg *)
apply ContextPermutImpl with (Gamma := Gamma0++Gamma); [permut_simpl|]; auto.
eapply IHHT; auto.
intros. 
rewrite notin_union in H7; destruct H7.
rewrite notin_singleton in H8.
unfold open_var in *; unfold open_ctx in *.
rewrite <- subst_ctx_comm.
rewrite subst_order_irrelevant_free.
eapply H with (v':=v') (w'0:=w'0) (w:=w0); auto. eauto.
rew_app; auto.
simpl; auto.
intro; subst; elim H8; reflexivity.

destruct (eq_var_dec w w0).
subst; skip. (* ok_Bg -> contradiction *)
(* H0 + H1: G & (w, Gamma) ~=~ G' & (w', Gamma') -->
   exists GH, exists GT, G = GH & (w', Gamma') ++ GT *)
assert (G' & (w', Gamma') ~=~ G & (w, Gamma)). symmetry; transitivity G0; auto.
assert (exists GH, exists GT, G' = GH & (w, Gamma) ++ GT).
  eapply PPermut_split_neq; eauto. right; intro; subst. elim H3; reflexivity.
destruct H5 as (GH, H5); destruct H5 as (GT, H5).
assert (G & (w, Gamma) ~=~ 
       (GH ++ GT ++ (w', Gamma') :: nil) &  (w, Gamma));
[subst; symmetry | rew_app]; auto.
apply PPermut_last; auto;
apply PPermut_last_rev_simpl with (a:=(w, Gamma)); auto;
transitivity ((GH & (w, Gamma) ++ GT) & (w', Gamma'));
[rew_app in *; symmetry | ]; auto.
apply t_letdia_get_LF with (L_w:=L_w \u \{w'}) (L_t:=L_t) (A:=A) (G:=GH++GT) (Gamma:=Gamma).
skip. (* ok_Bg *)
eapply IHHT with (w1:=w) (G0:=GH++GT) (w':=w0) (Gamma':=Gamma0) (Gamma'':=Gamma');
auto.
transitivity ((GH ++ GT & (w', Gamma')) & (w0, Gamma0)).
apply PPermut_last; auto.
apply PPermut_last_rev_simpl with (a:=(w, Gamma)); auto.
rew_app; auto.
intros. 
rewrite notin_union in H8; destruct H8.
rewrite notin_singleton in H9.
unfold open_var in *; unfold open_ctx in *.
rewrite <- subst_ctx_comm.
rewrite subst_order_irrelevant_free.
eapply H with (w1:=w0) (Gamma1:=Gamma0); auto.
rew_app; constructor; auto.
transitivity ((GH ++ GT & (w', Gamma')) & (w, Gamma)); [ | rew_app]; auto.
simpl; auto.
intro; subst; elim H9; auto.
subst; rew_app; auto.

case_if.
skip. (* w = w0 --> ok_Bg gives contradiction *)
destruct (eq_var_dec w w').
subst; skip. (* H0 + Ok_Bg gives contradiction *) 
(* H0 + H1: G & (w, Gamma) ~=~ G' & (w', Gamma') -->
   exists GH, exists GT, G = GH & (w', Gamma') ++ GT *)
assert (G' & (w', Gamma') ~=~ G & (w, Gamma)). symmetry; transitivity G0; auto.
assert (exists GH, exists GT, G' = GH & (w, Gamma) ++ GT).
  eapply PPermut_split_neq; eauto. 
destruct H5 as (GH, H5); destruct H5 as (GT, H5).
apply t_letdia_get_LF with (L_w:=L_w \u \{w0}) (L_t:=L_t) (A:=A) (G:=GH++GT) (Gamma:=Gamma).
skip. (* ok_Bg *)
eapply IHHT; auto.
apply PPermut_last; auto; apply PPermut_last_rev_simpl with (a:=(w, Gamma)).
transitivity (GH & (w, Gamma) ++ GT & (w', Gamma')); [ | rew_app]; auto.
subst; symmetry; rew_app in *; auto.
intros. 
rewrite notin_union in H7; destruct H7.
rewrite notin_singleton in H8.
unfold open_var in *; unfold open_ctx in *.
rewrite <- subst_ctx_comm.
rewrite subst_order_irrelevant_free.
eapply H with (w1:=w0) (Gamma1:=Gamma0); auto.
rew_app; constructor; auto.
subst; rew_app in *; symmetry.
transitivity ( GH ++ (w, Gamma) :: GT & (w', Gamma')); auto.
simpl; auto.
intro; subst; elim H8; auto.
subst; symmetry; auto.

case_if.
inversion H4; subst.
(* H0 + H1 + Ok_Bg --> Gamma'' = Gamma & G0 & (w', Gamma') ~=~ G *)
assert (Gamma *=* Gamma'') by skip.
assert (G1 & (w', Gamma') ~=~ G).
  apply PPermut_last_rev with (w:=w'') (Gamma:=Gamma'') (Gamma':=Gamma);
  [ | transitivity G0]; auto. apply permut_sym; auto. 
eapply t_letdia_get_LF with (G:=G1) (Gamma:=Gamma'++Gamma) (L_w:=L_w \u \{w''}).
skip.
eapply IHHT with (Gamma':=Gamma'); auto. 
intros. 
unfold open_var in *; unfold open_ctx in *.
rewrite <- subst_ctx_comm.
rewrite subst_order_irrelevant_free.
eapply H with (w:=w0) (G0:=(w'0, (v',A)::nil)::G1) (Gamma':=Gamma') (Gamma'':=Gamma); auto. eauto. 
rew_app; constructor; [ | symmetry]; auto.
rewrite <- H6; rew_app; auto.
simpl; auto.
rewrite notin_union in H8; 
rewrite notin_singleton in H8;
destruct H8; intro; elim H9; auto.
symmetry; transitivity (G1 & (w', Gamma' ++ Gamma'')); auto.

destruct (eq_var_dec w w').
subst.
(* H0 + H1 + Ok_Bg --> Gamma = Gamma' /\ G0 & (w'',Gamma'') = G *)
assert (Gamma *=* Gamma') by skip.
assert (G1 & (w'', Gamma'') ~=~ G).
  apply PPermut_last_rev with (w:=w') (Gamma:=Gamma') (Gamma':=Gamma);
  [ | transitivity G0]; auto. apply permut_sym; auto. symmetry; auto.
  transitivity (G1 & (w', Gamma') & (w'', Gamma'')); auto.
eapply t_letdia_get_LF with (G:=G1) (Gamma:=Gamma++Gamma'') (L_w:=L_w \u \{w''}) (L_t := L_t).
skip.
eapply IHHT with (w:=w'); auto. 
intros. 
unfold open_var in *; unfold open_ctx in *.
rewrite <- subst_ctx_comm.
rewrite subst_order_irrelevant_free.
eapply H with (w:=w0) (G0:=(w'0, (v',A)::nil)::G1) (Gamma':=Gamma) (Gamma'':=Gamma''); auto.
rew_app; constructor; auto.
symmetry; transitivity ((G1 ++ (w'', Gamma'')::nil) & (w', Gamma)); auto.
rew_app; auto. 
simpl; auto.
rewrite notin_union in H8; 
rewrite notin_singleton in H8.
destruct H8. intro. elim H9; eauto.
symmetry; transitivity (G1 & (w', Gamma' ++ Gamma'')); auto.

(* H0 + H1: G & (w, Gamma) ~=~ G1 & (w', Gamma') & (w'', Gamma'') -->
   exists GH, exists GT, G1 = GH & (w, Gamma) & (w', Gamma') ++ GT *)
assert (G & (w, Gamma) ~=~ G1 & (w', Gamma') & (w'', Gamma'')). symmetry; transitivity G0; symmetry; auto.
assert (exists GH, exists GT, G1 & (w'', Gamma'') = GH & (w, Gamma) ++ GT).
  apply PPermut_split_neq with (w:=w') (G':=G) (Gamma:=Gamma');
  try symmetry; auto. transitivity (G1 & (w', Gamma') & (w'', Gamma'')); auto.
assert (exists GH, exists GT, G1 = GH & (w, Gamma) ++ GT).
  destruct H6 as (GH, H6); destruct H6 as (GT, H6); subst.
  apply PPermut_split_neq with (w:=w'') (G':=GH++GT) (Gamma:=Gamma''); auto.
  rewrite H6; rew_app; auto.
  right; intro; subst; elim H4; reflexivity.
destruct H7 as (GH, H7); destruct H7 as (GT, H7); subst.
apply t_letdia_get_LF with (L_w:=L_w \u \{w''}) 
  (L_t:=L_t) (A:=A) (G:=GH++GT & (w', Gamma'++Gamma'')) (Gamma:=Gamma).
skip. (* ok_Bg *)
eapply IHHT with (w1:=w) (G0:=GH++GT & (w0, Gamma0)) (Gamma':=Gamma') (Gamma'':=Gamma''); auto.
rew_app in *. transitivity ((GH ++ GT ++ (w', Gamma') :: (w'', Gamma'') :: nil) & (w0, Gamma0)). apply PPermut_last; auto. apply PPermut_last_rev_simpl with (a:=(w, Gamma)).
rewrite H5. symmetry. transitivity (GH ++ GT ++ (w, Gamma) :: (w', Gamma') :: (w'', Gamma'') :: nil). rew_app; auto. apply PPermut_app_head; symmetry; auto.
rew_app; auto.
rew_app; auto.
intros. 
unfold open_var in *; unfold open_ctx in *.
rewrite <- subst_ctx_comm.
rewrite subst_order_irrelevant_free.
eapply H with (G0:=(w'0, (v', A) :: nil) :: (GH ++ GT) & (w, Gamma)) (Gamma':=Gamma') (Gamma'':=Gamma''); auto.
rew_app in *; constructor; auto.
transitivity (GH ++ (w, Gamma) :: GT ++ (w', Gamma') :: (w'', Gamma'') :: nil); auto.
rew_app in *; constructor; auto.
simpl; auto.
rewrite notin_union in H8; rewrite notin_singleton in H8; destruct H8.
intro; subst; elim H9; auto.
rew_app; symmetry; transitivity ((GH & (w, Gamma) ++ GT) & (w', Gamma'++ Gamma''));
[ | rew_app]; auto.
Admitted. (* "No more subgoals but non-instantiated existential variables" *)

Lemma rename_w_preserv_types_new:
forall G w Gamma A M G' w' Gamma'
  (HT: G |= (w, Gamma) |- M ::: A)
  (GG': PPermut G (G' & (w', Gamma'))),
  G' |= (w, Gamma ++ Gamma') |- {{ fwo w // fwo w' }} M ::: A.
intros;
apply rename_w_preserv_types with (G := G) (w := w) (w':= w'); eauto.
Qed.

Lemma rename_w_preserv_types_old:
forall G w Gamma A M G' w' Gamma'
  (HT: G |= (w, Gamma) |- M ::: A)
  (GG': PPermut G (G' & (w', Gamma'))),
  G' |= (w', Gamma' ++ Gamma) |- {{ fwo w' // fwo w }} M ::: A.
intros;
apply rename_w_preserv_types with (G := G) (w := w) (w':= w'); eauto.
Qed.

Lemma rename_w_preserv_types_outer:
forall G G0 w Gamma A M G' w' Gamma' w'' Gamma''
  (HT: G |= (w, Gamma) |- M ::: A)
  (GG: PPermut G (G0 & (w', Gamma') & (w'', Gamma'')))
  (GG': PPermut G' (G0 & (w', Gamma' ++ Gamma''))),
  G' |= (w, Gamma) |- {{ fwo w' // fwo w'' }} M ::: A.
intros;
eapply rename_w_preserv_types;
eauto.
Qed.

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
inversion H2; inversion H3; subst; eauto.
(* unbox & unbox_fetch *)
right; inversion HT; subst;
inversion H_lc_w; subst;
inversion H_lc_t; subst.
(* unbox *)
edestruct IHM with (A := [*]A); eauto;
[ inversion H0; subst; inversion HT0; subst |
  destruct H0];
eexists; constructor; eauto;
inversion H3; inversion H4; subst; auto.
(* unbox_fetch *)
(* TODO: permut (G0 & (w0, Gamma)) (emptyEquiv G) --> Gamma = nil *)
assert (Gamma = nil) by skip; subst;
destruct IHM with (A := [*]A) 
                  (Ctx := (w0, (@nil ty)))
                  (G := G0 & (w0, nil))
                  (w := w0); 
eauto;
(* TODO: emptyEqiv (G0 & (w0, nil)) = G0 & (w0, nil) by H6 *) 
[ skip |
  inversion H0; subst; inversion HT0; subst | 
  destruct H0 ];
eexists; constructor; eauto;
inversion H3; inversion H4; subst; 
eauto.
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
(* TODO: permut (G0 & (w0, Gamma)) (emptyEquiv G) --> Gamma = nil *)
assert (Gamma = nil) by skip; subst;
edestruct IHM with (A := A0) (G := G0 & (w0, nil)) (w:=w0); eauto;
(* TODO: emptyEqiv (G0 & (w0, nil)) = G0 & (w0, nil) by H5 *) 
[ skip | 
  left; inversion H0; subst; inversion HT0; subst | 
  right; destruct H0; eexists];
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
inversion H5; inversion H7; subst; auto.
(* letdia_get *)
(* TODO: permut (G0 & (w0, Gamma)) (emptyEquiv G) --> Gamma = nil *)
assert (Gamma = nil) by skip; subst;
edestruct IHM1 with (G := G0 & (w, nil)) 
                    (w := w0) 
                    (Ctx := (w0, (@nil ty)))
                    (A := <*>A0); eauto;
(* TODO: emptyEqiv (G0 & (w0, nil)) = G0 & (w0, nil) by H6 *) 
[ skip |
  inversion H0; subst; inversion HT1; subst |
  destruct H0];
eexists; constructor; eauto;
try apply closed_t_succ; auto;
inversion H5; inversion H8; subst; auto.
Qed.


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
destruct HF as (v_fresh).
rewrite subst_var_neutral_free with (v:=v_fresh).
eapply subst_t_preserv_types_inner; eauto.
(* TODO: Double emptyEquiv doesn't change more than single *)
skip.
rewrite notin_union in H; destruct H; auto.
(* unbox_box *)
inversion HT; subst;
assert (exists v, v \notin L \u (free_worlds_LF M0)) as HF by apply Fresh;
destruct HF as (w_fresh);
unfold open_ctx in *;
replace ({{fwo w0 // bwo 0}}M0)
  with ({{fwo w0 // fwo w_fresh}} {{fwo w_fresh // bwo 0}}M0)
  by (rewrite subst_ctx_neutral_free; auto);
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
  by (rewrite subst_ctx_neutral_free; auto);
replace (@nil (var * ty)) with (nil ++ (@nil (var * ty))); eauto;
apply rename_w_preserv_types_old with (G := G & (w0, nil) & (w, Gamma));
auto.
(* unbox_fetch *)
econstructor; eauto;
(* TODO: permut (G & (w, Gamma)) (emptyEquiv G0) -> Gamma = nil *)
assert (Gamma = nil) by skip; subst;
eapply IHHT with (G0:=G & (w0, nil)); eauto.
(* TODO: by H, G contains no Gammas <> nil, so taking emptyEquiv doesn't change anything *)
skip.
(* get_here *)
econstructor; eauto;
(* TODO: permut (G & (w, Gamma)) (emptyEquiv G0) -> Gamma = nil *)
assert (Gamma = nil) by skip; subst;
eapply IHHT with (G0:=G & (w0, nil)); eauto;
(* TODO: by H, G contains no Gammas <> nil, so taking emptyEquiv doesn't change anything *)
skip.
(* letdia + (here | get_here ) *)
assert (exists w1, w1 \notin L_w \u free_worlds_LF N) as HF by apply Fresh;
assert (exists v1, v1 \notin L_t \u free_vars_LF N) as HF2 by apply Fresh;
destruct HF as (w_fresh); destruct HF2 as (v_fresh);
inversion HT; subst. 
(* letdia #1 *)
rewrite notin_union in *; destruct H0; destruct H1.
unfold open_var in *; unfold open_ctx in *.
rewrite subst_var_neutral_free with (v:=v_fresh).
rewrite subst_order_irrelevant_bound.
rewrite <- subst_ctx_neutral_free with (w0:=w_fresh).
apply subst_t_preserv_types_inner with (A:=A); eauto.
replace ((v_fresh, A) :: nil) with (nil ++ (v_fresh, A) :: nil) by auto.
apply rename_w_preserv_types_new with (G:= (w_fresh, (v_fresh, A)::nil) :: emptyEquiv G0).
rewrite <- subst_order_irrelevant_bound.
eapply HT2; auto.
constructor.
rew_app; auto.
skip. (* double emptyEquiv *)
apply subst_var_preserv_free_worlds; auto.
constructor.
apply subst_world_preserv_free_vars; auto.
(* letdia #2 *)
rewrite notin_union in *; destruct H0; destruct H1.
unfold open_var in *; unfold open_ctx in *.
rewrite subst_var_neutral_free with (v:=v_fresh).
rewrite subst_order_irrelevant_bound.
rewrite <- subst_ctx_neutral_free with (w0:=w_fresh).
eapply subst_t_preserv_types_outer with (A:=A) (G0:=G) (Gamma':=Gamma) (w':=w); auto.
skip. (* permut + assumption *)
apply rename_w_preserv_types_outer with (G0:=G) (Gamma'':=(v_fresh,A) :: nil) 
      (Gamma':=Gamma) (G:=G & (w, Gamma) & (w_fresh, (v_fresh,A)::nil)).
replace (G & (w, Gamma) & (w_fresh, (v_fresh, A) :: nil)) with ((w_fresh, (v_fresh, A) :: nil) :: emptyEquiv G0) by skip. (* H9 + permut_equiv *)
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
rewrite subst_var_neutral_free with (v:=v_fresh).
rewrite subst_order_irrelevant_bound.
rewrite <- subst_ctx_neutral_free with (w0:=w_fresh).
eapply subst_t_preserv_types_outer with (A:=A) (G0:=G) (w':=w) (Gamma':=Gamma); eauto.
skip. (* permut + auto *)
assert (Gamma = nil) by skip; subst. (* H0 *)
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
assert (Gamma = nil) by skip; subst. (* H0 *)
assert (w <> w0) by skip. (* Ok_Bg *)
assert (w1 <> w) by skip. (* Ok_Bg0 *)
replace (emptyEquiv G1) with (G & (w, nil)) by skip. (* permut *)
rewrite notin_union in *; destruct H1; destruct H2.
unfold open_var in *; unfold open_ctx in *.

(* G0 & (w1, Gamma0) ~=~ G & (w0, nil) /\ w1 =?= w0  ? *)
destruct (eq_var_dec w1 w0).

(* =  + Ok_bg --> G0 = G *)
subst.
assert (G = G0) by skip.
assert (Gamma0 = nil) by skip; subst.
rewrite subst_var_neutral_free with (v:=v_fresh).
eapply subst_t_preserv_types_inner with (A:=A); eauto.
rewrite subst_order_irrelevant_bound.
rewrite <- subst_ctx_neutral_free with (w0:=w_fresh).
replace ((v_fresh,A)::nil) with (nil++(v_fresh,A)::nil) by auto.
apply rename_w_preserv_types_new with (G:= (w_fresh, (v_fresh,A)::nil) :: G0 & (w, nil));
auto.
rewrite <- subst_order_irrelevant_bound.
eapply HT2; auto.
constructor.
apply subst_var_preserv_free_worlds; auto.
constructor.
skip. (* emptyEquiv (emptyEquiv.. ) *)
apply subst_world_preserv_free_vars; auto.
(* <> --> exists GH, exists GT, G = GH & (w1, Gamma0) ++ GT *)
assert (Gamma0 = nil) by skip; subst Gamma0. (* H0 + H12 *)
assert (exists GH, exists GT, G = GH & (w1, nil) ++ GT).
  apply PPermut_split_neq with (w:=w0) (G':=G0) (Gamma:=nil).
  symmetry; auto.
  right; intro; subst; elim n; reflexivity.
destruct H12 as (GH, H12); 
destruct H12 as (GT, H12).
rewrite subst_var_neutral_free with (v:=v_fresh).
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
skip. (* emptyEquiv redundant, H10 + HT0 *)

rewrite subst_order_irrelevant_bound.
rewrite <- subst_ctx_neutral_free with (w0:=w_fresh).
apply rename_w_preserv_types_outer
  with (G0 := GH ++ GT & (w,nil)) 
       (G := (w_fresh, (v_fresh, A) :: nil) :: G & (w, nil)) 
       (Gamma':=nil)
       (Gamma'':=(v_fresh, A)::nil); auto.
rewrite <- subst_order_irrelevant_bound.
eapply HT2; eauto.
constructor.
subst; rew_app. 
transitivity ((w_fresh, (v_fresh, A) :: nil) :: GH ++ GT ++ (w, nil) :: (w1, nil) :: nil);
auto.
transitivity ((GH ++ GT ++ (w, nil) :: (w1, nil) :: nil) & (w_fresh, (v_fresh, A) :: nil)).
auto. rew_app; auto.
rew_app; auto.
apply subst_var_preserv_free_worlds; auto.
constructor.
apply subst_world_preserv_free_vars; auto.
(* letdia_step *)
destruct (eq_var_dec w0 w).
subst; skip. (* contradiction in Ok_Bg*)
assert (Gamma = nil) by skip. (* from permut *)
subst.
replace (emptyEquiv G1) with (G & (w, nil)) by skip. (* permut *)
eapply t_letdia_get_LF ; eauto.
apply IHHT with (G0:=G & (w0,nil)) (w1:=w); auto.
skip.
Qed.

End Lemmas.

Close Scope label_free_is5_scope.
