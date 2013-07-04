Add LoadPath "..".
Add LoadPath "../LabelFree".
Add LoadPath "../Hybrid".

Require Import Shared.
Require Import LabelFree.
Require Import Hybrid.
Require Import Arith.
Require Import ListLib.
Require Import Setoid.

Open Scope is5_scope.
Open Scope permut_scope.
Open Scope hybrid_is5_scope.

(* Relation for contexts *)

Definition LF_to_Hyb_ctx (G: bg_LF) (G': bg_Hyb) :=
  PPermut_LF (map snd_ G') G /\ ok_Hyb G' nil.

Lemma ok_LF_ok_Hyb:
forall (G: list (var*ty)) U,
  ok_LF G U -> ok_Hyb G U.
induction G; intros; try constructor; destruct a; inversion H; subst;
constructor; auto.
Qed.

Lemma LF_to_Hyb_ctx_Ok:
forall G' G,
  ok_Bg_LF G -> LF_to_Hyb_ctx G G' -> ok_Bg_Hyb G'.
induction G'; intros; unfold ok_Bg_Hyb in *; unfold ok_Bg_LF in *;
unfold LF_to_Hyb_ctx in *; split; destruct H0; auto; try constructor;
rewrite <- flat_map_concat.
apply ok_LF_PPermut with (G':=map snd_ (a::G')) in H.
destruct a; rew_map in *; simpl in *; rew_concat in *; auto.
apply ok_LF_ok_Hyb; auto.
symmetry; auto.
Qed.

Lemma LF_to_Hyb_ctx_extend_t:
forall G G' w Gamma v A,
LF_to_Hyb_ctx (((v,A)::Gamma)::G) ((w, (v,A)::Gamma)::G') ->
LF_to_Hyb_ctx (Gamma::G) ((w, Gamma)::G').
unfold LF_to_Hyb_ctx in *; intros; destruct H; split; rew_map in *;
simpl in *.
PPermut_LF_simpl.
apply PPermut_LF_last_rev_simpl with (a:=((v,A)::Gamma));
transitivity (((v,A)::Gamma) :: G).
rewrite <- H; PPermut_LF_simpl. PPermut_LF_simpl.
inversion H0; subst; constructor; auto.
Qed.

Lemma LF_to_Hyb_ctx_extend_w:
forall G G' w,
  LF_to_Hyb_ctx (nil::G) ((w, nil)::G') ->
  LF_to_Hyb_ctx G G'.
unfold LF_to_Hyb_ctx in *; intros; destruct H; split; rew_map in *;
simpl in *.
apply PPermut_LF_last_rev_simpl with (a:=nil);
transitivity (nil :: G).
rewrite <- H; PPermut_LF_simpl. PPermut_LF_simpl.
inversion H0; subst. apply ok_Hyb_used_weakening in H6; auto.
Qed.

Lemma LF_to_Hyb_ctx_extend2_t:
forall G G' w Gamma A,
LF_to_Hyb_ctx (Gamma::G) ((w, Gamma)::G') ->
forall v, v \notin \{} ->
LF_to_Hyb_ctx (((v,A)::Gamma)::G) ((w, (v,A)::Gamma)::G').
unfold LF_to_Hyb_ctx in *; intros; destruct H; split;
rew_map in *; simpl in *.
PPermut_LF_simpl.
apply PPermut_LF_last_rev_simpl with (a:=Gamma);
transitivity (Gamma :: G).
rewrite <- H; symmetry; apply PPermut_LF_first_last.
PPermut_LF_simpl.
inversion H1; subst; constructor; auto.
Qed.

Lemma LF_to_Hyb_ctx_extend2_w:
forall G G',
  LF_to_Hyb_ctx G G' ->
  forall w, w \notin used_w_vars_Hyb G' ->
  LF_to_Hyb_ctx (nil::G) ((w, nil)::G').
unfold LF_to_Hyb_ctx in *; intros; destruct H; split;
rew_map in *; simpl in *.
PPermut_LF_simpl; auto.
apply ok_Hyb_fresh_wo_list; auto.
rewrite notin_union; rewrite from_list_nil; split; auto.
Qed.

Lemma LF_to_Hyb_PPermut_LF_bg:
forall G G' G'',
  LF_to_Hyb_ctx G G'' ->
  PPermut_LF G G' ->
  LF_to_Hyb_ctx G' G''.
unfold LF_to_Hyb_ctx in *; intros; destruct H; split; auto.
rewrite H; auto.
Qed.

Lemma LF_to_Hyb_PPermut_Hyb_bg:
forall G' G'' G,
  LF_to_Hyb_ctx G G' ->
  PPermut_Hyb G' G'' ->
  LF_to_Hyb_ctx G G''.
unfold LF_to_Hyb_ctx in *; intros; destruct H; split.
rewrite <- H.
clear G H H1; symmetry; induction H0;
auto;rew_map; simpl; PPermut_LF_simpl.
rewrite H; rewrite H0; auto.
rewrite IHPPermut_Hyb1; rewrite IHPPermut_Hyb2; auto.
rewrite <- H0; auto.
Qed.

Add Morphism LF_to_Hyb_ctx: LF_to_Hyb_ctx_LF.
intros; split; intros.
apply LF_to_Hyb_PPermut_LF_bg with (G:=x); auto;
apply LF_to_Hyb_PPermut_Hyb_bg with (G':=x0); auto.
apply LF_to_Hyb_PPermut_LF_bg with (G:=y); auto;
apply LF_to_Hyb_PPermut_Hyb_bg with (G':=y0); auto.
Qed.

(* Relation for typing terms *)

Inductive LF_to_Hyb_term_R: ctx_LF  -> te_LF  -> ty ->
                         bg_Hyb -> var -> te_Hyb -> Prop :=

| hyp_LF_Hyb:
    forall G Gamma G' w v A,
      types_LF G Gamma (hyp_LF v) A ->
      LF_to_Hyb_ctx (Gamma::G) ((w, Gamma)::G') ->
      LF_to_Hyb_term_R Gamma (hyp_LF v) A
                    G' w (hyp_Hyb v)

| lam_LF_Hyb:
    forall L G Gamma G' w M M' A B,
      types_LF G Gamma (lam_LF A M) (A ---> B) ->
      LF_to_Hyb_ctx (Gamma::G) ((w, Gamma)::G') ->
      (forall v0,
         v0 \notin L ->
         LF_to_Hyb_term_R ((v0, A)::Gamma) (open_LF M (hyp_LF (fte v0))) B
                       G' w
                       (M' ^t^ (hyp_Hyb (fte v0)))) ->
      LF_to_Hyb_term_R Gamma (lam_LF A M) (A ---> B) G' w (lam_Hyb A M')

| appl_LF_Hyb:
    forall G Gamma G' w M1 M2 N1 N2 A B,
      types_LF G Gamma (appl_LF M1 N1) B ->
      LF_to_Hyb_term_R Gamma M1 (A ---> B) G' w M2 ->
      LF_to_Hyb_term_R Gamma N1 A G' w N2 ->
      LF_to_Hyb_ctx (Gamma::G) ((w, Gamma)::G') ->
      LF_to_Hyb_term_R Gamma (appl_LF M1 N1) B G' w (appl_Hyb M2 N2)

| box_LF_Hyb:
    forall L G Gamma G' w M N A,
      types_LF G Gamma (box_LF M) ([*]A) ->
      LF_to_Hyb_ctx (Gamma::G) ((w, Gamma)::G') ->
      (forall w0, w0 \notin L ->
        LF_to_Hyb_term_R (@nil (var*ty)) M A
                      ((w,Gamma)::G') w0 (N ^w^ (fwo w0))) ->
      LF_to_Hyb_term_R Gamma (box_LF M) ([*]A) G' w (box_Hyb N)

| unbox_LF_Hyb:
    forall G Gamma G' w M N A,
      types_LF G Gamma (unbox_LF M) A ->
      LF_to_Hyb_ctx (Gamma::G) ((w, Gamma)::G') ->
      LF_to_Hyb_term_R Gamma M ([*]A) G' w N ->
      LF_to_Hyb_term_R Gamma (unbox_LF M) A
                    G' w (unbox_fetch_Hyb (fwo w) N)

| unbox_fetch_LF_Hyb:
    forall G Gamma Gamma' G' w w' M N A G'',
      w <> w' ->
      types_LF (Gamma'::G) Gamma (unbox_LF M) A ->
      LF_to_Hyb_ctx (Gamma::Gamma'::G) ((w, Gamma)::(w', Gamma')::G') ->
      LF_to_Hyb_term_R Gamma' M ([*]A)
                    ((w, Gamma)::G') w' N ->
      ((w', Gamma')::G') ~=~ G'' ->
      LF_to_Hyb_term_R Gamma (unbox_LF M) A
                    G'' w (unbox_fetch_Hyb (fwo w') N)

| here_LF_Hyb:
    forall G Gamma G' w A M N,
      types_LF G Gamma (here_LF M) (<*>A) ->
      LF_to_Hyb_ctx (Gamma::G) ((w, Gamma)::G') ->
      LF_to_Hyb_term_R Gamma M A G' w N ->
      LF_to_Hyb_term_R Gamma (here_LF M) (<*>A)
                    G' w (get_here_Hyb (fwo w) N)

| get_here_LF_Hyb:
    forall G Gamma Gamma' G' w w' A M N G'',
      w <> w' ->
      types_LF (Gamma'::G) Gamma (here_LF M) (<*>A) ->
      LF_to_Hyb_ctx (Gamma::Gamma'::G) ((w, Gamma)::(w', Gamma')::G') ->
      LF_to_Hyb_term_R Gamma' M A
                    ((w, Gamma)::G') w' N ->
      ((w', Gamma')::G') ~=~ G'' ->
      LF_to_Hyb_term_R Gamma (here_LF M) (<*>A)
                    G'' w (get_here_Hyb (fwo w') N)

| letdia_LF_Hyb:
    forall Lt Lw G Gamma G' w A B M1 M2 N1 N2,
      types_LF G Gamma (letdia_LF M1 N1) B ->
      LF_to_Hyb_term_R Gamma M1 (<*>A) G' w M2 ->
      (forall w'0 v', w'0 \notin Lw -> v' \notin Lt ->
                     LF_to_Hyb_term_R Gamma (open_LF N1 (hyp_LF (fte v'))) B
                                   ((w'0, (v', A) :: nil ) :: G') w
                                   ((N2 ^w^ fwo w'0 ) ^t^ hyp_Hyb (fte v'))) ->
      LF_to_Hyb_ctx (Gamma::G) ((w, Gamma)::G') ->
      LF_to_Hyb_term_R Gamma (letdia_LF M1 N1) B G' w
                    (letdia_get_Hyb (fwo w) M2 N2)

| letdia_get_LF_Hyb:
    forall Lt Lw G Gamma Gamma' G' w w' A B M1 M2 N1 N2 G'',
      types_LF (Gamma'::G) Gamma (letdia_LF M1 N1) B ->
      LF_to_Hyb_term_R Gamma' M1 (<*>A)
                    ((w, Gamma)::G') w' M2 ->
      (forall w'0 v', w'0 \notin Lw -> v' \notin Lt ->
         LF_to_Hyb_term_R Gamma (open_LF N1 (hyp_LF (fte v'))) B
                       (((w'0, (v', A) :: nil ) :: (w', Gamma')::G'))
                       w ((N2 ^w^ fwo w'0 ) ^t^ hyp_Hyb (fte v'))) ->
      LF_to_Hyb_ctx (Gamma::Gamma'::G) ((w, Gamma)::(w', Gamma')::G') ->
      (w', Gamma')::G' ~=~ G'' ->
      LF_to_Hyb_term_R Gamma (letdia_LF M1 N1) B
                    G'' w
                    (letdia_get_Hyb (fwo w') M2 N2)
.

Lemma LF_to_Hyb_term_R_permut_G_Gamma:
forall Gamma Gamma' M A G w M' G',
  Gamma *=* Gamma' ->
  G ~=~ G' ->
  LF_to_Hyb_term_R Gamma M A G w M' ->
  LF_to_Hyb_term_R Gamma' M A G' w M'.
intros; generalize dependent G'; generalize dependent Gamma';
induction H1; intros; try econstructor; eauto.
rewrite <- H1; eauto.
assert (PPermut_LF (Gamma::G) (Gamma'::G)) as HP1 by (rewrite H1; auto);
assert (((w, Gamma) :: G') ~=~ ((w, Gamma') :: G'0)) as HP2 by
    (rewrite H2; PPermut_Hyb_simpl);
rewrite <- HP1; rewrite <- HP2; eauto.
rewrite <- H3; eauto.
assert (PPermut_LF (Gamma::G) (Gamma'::G)) as HP1 by (rewrite H3; auto);
assert (((w, Gamma) :: G') ~=~ ((w, Gamma') :: G'0)) as HP2 by
    (rewrite H4; PPermut_Hyb_simpl);
rewrite <- HP1; rewrite <- HP2; eauto.
rewrite <- H1; eauto.
assert (PPermut_LF (Gamma::G) (Gamma'::G)) as HP1 by (rewrite H1; auto);
assert (((w, Gamma) :: G') ~=~ ((w, Gamma') :: G'0)) as HP2 by
    (rewrite H2; PPermut_Hyb_simpl);
rewrite <- HP1; rewrite <- HP2; eauto.
rewrite <- H3; eauto.
assert (PPermut_LF (Gamma::G) (Gamma'::G)) as HP1 by (rewrite H3; auto);
assert (((w, Gamma) :: G') ~=~ ((w, Gamma') :: G'0)) as HP2 by
    (rewrite H4; PPermut_Hyb_simpl);
rewrite <- HP1; rewrite <- HP2; eauto.
rewrite <- H2; eauto.
assert (PPermut_LF (Gamma::G) (Gamma'::G)) as HP1 by (rewrite H2; auto);
assert (((w, Gamma) :: G') ~=~ ((w, Gamma') :: G'0)) as HP2 by
    (rewrite H3; PPermut_Hyb_simpl);
rewrite <- HP1; rewrite <- HP2; eauto.
rewrite <- H4; eauto.
assert (PPermut_LF (Gamma::Gamma'::G) (Gamma'0::Gamma'::G)) as HP1 by
  (rewrite H4; auto);
assert (((w, Gamma) :: (w', Gamma') :: G') ~=~
  ((w, Gamma'0):: (w', Gamma') :: G')) as HP2 by
    (rewrite H3; PPermut_Hyb_simpl);
rewrite <- HP1; rewrite <- HP2; eauto.
rewrite <- H5; rewrite H3; auto.
rewrite <- H2; eauto.
assert (PPermut_LF (Gamma::G) (Gamma'::G)) as HP1 by (rewrite H2; auto);
assert (((w, Gamma) :: G') ~=~ ((w, Gamma') :: G'0)) as HP2 by
    (rewrite H3; PPermut_Hyb_simpl);
rewrite <- HP1; rewrite <- HP2; eauto.
rewrite <- H4; eauto.
assert (PPermut_LF (Gamma::Gamma'::G) (Gamma'0::Gamma'::G)) as HP1 by
  (rewrite H4; auto);
assert (((w, Gamma) :: (w', Gamma') :: G') ~=~
  ((w, Gamma'0):: (w', Gamma') :: G')) as HP2 by
    (rewrite H3; PPermut_Hyb_simpl);
rewrite <- HP1; rewrite <- HP2; eauto.
rewrite <- H5; rewrite H3; auto.
rewrite <- H4; eauto.
assert (PPermut_LF (Gamma::G) (Gamma'::G)) as HP1 by
  (rewrite H4; auto);
assert (((w, Gamma) :: G') ~=~ ((w, Gamma') :: G'0)) as HP2 by
    (rewrite H5; PPermut_Hyb_simpl);
rewrite <- HP1; rewrite <- HP2; eauto.
rewrite <- H5; eauto.
assert (PPermut_LF (Gamma::Gamma'::G) (Gamma'0::Gamma'::G)) as HP1 by
  (rewrite H5; auto);
assert (((w, Gamma) :: (w', Gamma') :: G') ~=~
  ((w, Gamma'0):: (w', Gamma') :: G')) as HP2 by
    (rewrite H4; PPermut_Hyb_simpl);
rewrite <- HP1; rewrite <- HP2; eauto.
rewrite <- H6; rewrite H4; auto.
Qed.

Add Morphism LF_to_Hyb_term_R: LF_to_Hyb_term_R_G.
split; intros.
eapply LF_to_Hyb_term_R_permut_G_Gamma with (G:=x0) (Gamma:=x); auto.
eapply LF_to_Hyb_term_R_permut_G_Gamma with (G:=y2) (Gamma:=y); auto; symmetry;
auto.
Qed.

(* .. it types! *)

Lemma LF_to_Hyb_types:
forall G' Gamma M A w M',
  LF_to_Hyb_term_R Gamma M A G' w M' ->
  types_Hyb G' (w, Gamma) M' A.
intros; induction H; intros.
(* hyp *)
inversion H; subst; constructor; [eapply LF_to_Hyb_ctx_Ok | ]; eauto.
(* lam *)
inversion H; subst;
apply t_lam_Hyb with (L:=L \u L0); [eapply LF_to_Hyb_ctx_Ok | ]; eauto; intros;
unfold open_t_Hyb in *; unfold open_LF in *;
apply H1; eauto.
(* appl *)
inversion H; subst; econstructor; [eapply LF_to_Hyb_ctx_Ok| | ]; eauto.
(* box *)
inversion H; subst; apply t_box_Hyb with (L:=L);
assert (PPermut_LF (G & Gamma) (Gamma :: G)) as H4 by PPermut_LF_simpl;
assert (G' & (w, Gamma) ~=~ (w, Gamma) :: G') as H3 by PPermut_Hyb_simpl.
rewrite H3; eapply LF_to_Hyb_ctx_Ok; eauto; rewrite H4; auto.
intros; rewrite H3; eapply H2; eauto; rewrite <- H4; auto.
(* unbox *)
inversion H; subst.
constructor; [eapply LF_to_Hyb_ctx_Ok|] ; eauto.
constructor; auto;
eapply LF_to_Hyb_ctx_Ok; eauto;
assert (PPermut_LF (Gamma0 :: G0 & Gamma) (Gamma::G))
       by (rewrite <- H6; PPermut_LF_simpl);
rewrite H2; auto.
(* unbox-fetch *)
rewrite <- H3;
inversion H0; subst.
apply t_unbox_fetch_Hyb with (G:=G') (Gamma:=Gamma').
assert ((w, Gamma) :: (w', Gamma') :: G' ~=~ (w', Gamma') :: G' & (w, Gamma))
  by PPermut_Hyb_simpl;
rewrite <- H4; eapply LF_to_Hyb_ctx_Ok ; eauto.
assert (G' & (w, Gamma) ~=~ (w, Gamma) :: G') by PPermut_Hyb_simpl;
rewrite H4; auto.
PPermut_Hyb_simpl.
apply t_unbox_fetch_Hyb with (G:=G') (Gamma:=Gamma').
assert ((w, Gamma) :: (w', Gamma') :: G' ~=~ (w', Gamma') :: G' & (w, Gamma))
  by PPermut_Hyb_simpl.
assert (PPermut_LF (Gamma0 :: G0 & Gamma) (Gamma :: Gamma' :: G)) by
(transitivity (G0 & Gamma0 & Gamma); [ | rewrite H8 ];
 rew_app; PPermut_LF_simpl).
rewrite H6 in Ok.
rewrite <- H4; eapply LF_to_Hyb_ctx_Ok ; eauto.
assert (G' & (w, Gamma) ~=~ (w, Gamma) :: G') by PPermut_Hyb_simpl;
rewrite H4; auto.
PPermut_Hyb_simpl.
(* here *)
inversion H; subst.
constructor; [eapply LF_to_Hyb_ctx_Ok|] ; eauto.
constructor; auto;
eapply LF_to_Hyb_ctx_Ok; eauto;
assert (PPermut_LF (Gamma0 :: G0 & Gamma) (Gamma::G))
       by (rewrite <- H7; PPermut_LF_simpl);
rewrite H2; auto.
(* get-here *)
rewrite <- H3; inversion H0; subst.
apply t_get_here_Hyb with (G:=G') (Gamma:=Gamma').
assert ((w, Gamma) :: (w', Gamma') :: G' ~=~ (w', Gamma') :: G' & (w, Gamma))
  by PPermut_Hyb_simpl;
rewrite <- H4; eapply LF_to_Hyb_ctx_Ok ; eauto.
assert (G' & (w, Gamma) ~=~ (w, Gamma) :: G') by PPermut_Hyb_simpl;
rewrite H4; auto.
PPermut_Hyb_simpl.
apply t_get_here_Hyb with (G:=G') (Gamma:=Gamma').
assert ((w, Gamma) :: (w', Gamma') :: G' ~=~ (w', Gamma') :: G' & (w, Gamma))
  by PPermut_Hyb_simpl.
assert (PPermut_LF (Gamma0 :: G0 & Gamma) (Gamma :: Gamma' :: G)) by
(transitivity (G0 & Gamma0 & Gamma); [ | rewrite H9 ];
 rew_app; PPermut_LF_simpl).
rewrite H5 in Ok.
rewrite <- H4; eapply LF_to_Hyb_ctx_Ok ; eauto.
assert (G' & (w, Gamma) ~=~ (w, Gamma) :: G') by PPermut_Hyb_simpl;
rewrite H4; auto.
PPermut_Hyb_simpl.
(* letdia *)
inversion H; subst.
econstructor; [eapply LF_to_Hyb_ctx_Ok | | intros] ; eauto.
econstructor; intros; eauto;
eapply LF_to_Hyb_ctx_Ok; eauto;
assert (PPermut_LF (Gamma0 :: G0 & Gamma) (Gamma::G))
       by (rewrite <- H9; PPermut_LF_simpl);
rewrite H4; auto.
(* letdia-get *)
rewrite <- H4; inversion H; subst.
eapply t_letdia_get_Hyb with (G:=G') (Gamma:=Gamma').
assert ((w, Gamma) :: (w', Gamma') :: G' ~=~ (w', Gamma') :: G' & (w, Gamma))
  by PPermut_Hyb_simpl;
rewrite <- H5; eapply LF_to_Hyb_ctx_Ok ; eauto.
assert (G' & (w, Gamma) ~=~ (w, Gamma) :: G') by PPermut_Hyb_simpl;
rewrite H5; eauto.
intros;
assert ((w'0, (v', A) :: nil) :: (w', Gamma') :: G' ~=~
        (w'0, (v', A) :: nil) :: G' & (w', Gamma')) by PPermut_Hyb_simpl;
rewrite <- H7; eauto.
PPermut_Hyb_simpl.
eapply t_letdia_get_Hyb with (G:=G') (Gamma:=Gamma').
assert ((w, Gamma) :: (w', Gamma') :: G' ~=~ (w', Gamma') :: G' & (w, Gamma))
  by PPermut_Hyb_simpl.
assert (PPermut_LF (Gamma0 :: G0 & Gamma) (Gamma :: Gamma' :: G)) by
(transitivity (G0 & Gamma0 & Gamma); [ | rewrite H10 ];
 rew_app; PPermut_LF_simpl).
rewrite H6 in Ok.
rewrite <- H5; eapply LF_to_Hyb_ctx_Ok ; eauto.
assert (G' & (w, Gamma) ~=~ (w, Gamma) :: G') by PPermut_Hyb_simpl;
rewrite H5; eauto.
intros;
assert ((w'0, (v', A) :: nil) :: (w', Gamma') :: G' ~=~
        (w'0, (v', A) :: nil) :: G' & (w', Gamma')) by PPermut_Hyb_simpl;
rewrite <- H7; eauto.
PPermut_Hyb_simpl.
Qed.

(* ...it preserves values! *)

Lemma LF_to_Hyb_value:
forall G' Gamma M A w M',
  LF_to_Hyb_term_R Gamma M A G' w M' ->
  value_LF M -> value_Hyb M'.
intros; induction H; simpl;
inversion H0; subst; constructor; eauto.
Qed.

Close Scope hybrid_is5_scope.
Close Scope permut_scope.
Close Scope is5_scope.
