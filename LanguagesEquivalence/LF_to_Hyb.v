Add LoadPath "..".
Add LoadPath "../LabelFree/SingleUnbox".
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

Fixpoint LF_to_Hyb_ctx_fun (G: bg_LF) (U: list var) :=
match G with
| nil => nil
| Gamma :: G' =>
  let w:= var_gen (from_list U) in
  (w, Gamma) :: LF_to_Hyb_ctx_fun G' (w::U)
end.

Inductive LF_to_Hyb_rel: ctx_LF  -> te_LF  -> ty ->
                         bg_Hyb -> var -> te_Hyb -> Prop :=

| hyp_LF_Hyb:
    forall G Gamma G' w v A,
      types_LF G Gamma (hyp_LF v) A ->
      LF_to_Hyb_ctx (Gamma::G) ((w, Gamma)::G') ->
      LF_to_Hyb_rel Gamma (hyp_LF v) A
                    G' w (hyp_Hyb v)

| lam_LF_Hyb:
    forall L G Gamma G' w M M' A B,
      types_LF G Gamma (lam_LF A M) (A ---> B) ->
      LF_to_Hyb_ctx (Gamma::G) ((w, Gamma)::G') ->
      (forall v0,
         v0 \notin L ->
         LF_to_Hyb_rel ((v0, A)::Gamma) (open_LF M (hyp_LF (fte v0))) B
                       G' w
                       (M' ^t^ (hyp_Hyb (fte v0)))) ->
      LF_to_Hyb_rel Gamma (lam_LF A M) (A ---> B) G' w (lam_Hyb A M')

| appl_LF_Hyb:
    forall G Gamma G' w M1 M2 N1 N2 A B,
      types_LF G Gamma (appl_LF M1 N1) B ->
      LF_to_Hyb_rel Gamma M1 (A ---> B) G' w M2 ->
      LF_to_Hyb_rel Gamma N1 A G' w N2 ->
      LF_to_Hyb_ctx (Gamma::G) ((w, Gamma)::G') ->
      LF_to_Hyb_rel Gamma (appl_LF M1 N1) B G' w (appl_Hyb M2 N2)

| box_LF_Hyb:
    forall L G Gamma G' w M N A,
      types_LF G Gamma (box_LF M) ([*]A) ->
      LF_to_Hyb_ctx (Gamma::G) ((w, Gamma)::G') ->
      (forall w0, w0 \notin L ->
        LF_to_Hyb_rel (@nil (var*ty)) M A
                      ((w,Gamma)::G') w0 (N ^w^ (fwo w0))) ->
      LF_to_Hyb_rel Gamma (box_LF M) ([*]A) G' w (box_Hyb N)

| unbox_LF_Hyb:
    forall G Gamma G' w M N A,
      types_LF G Gamma (unbox_LF M) A ->
      LF_to_Hyb_ctx (Gamma::G) ((w, Gamma)::G') ->
      LF_to_Hyb_rel Gamma M ([*]A) G' w N ->
      LF_to_Hyb_rel Gamma (unbox_LF M) A
                    G' w (unbox_fetch_Hyb (fwo w) N)

| unbox_fetch_LF_Hyb:
    forall G Gamma Gamma' G' w w' M N A G'',
      w <> w' ->
      types_LF (Gamma'::G) Gamma (unbox_LF M) A ->
      LF_to_Hyb_ctx (Gamma::Gamma'::G) ((w, Gamma)::(w', Gamma')::G') ->
      LF_to_Hyb_rel Gamma' M ([*]A)
                    ((w, Gamma)::G') w' N ->
      ((w', Gamma')::G') ~=~ G'' ->
      LF_to_Hyb_rel Gamma (unbox_LF M) A
                    G'' w (unbox_fetch_Hyb (fwo w') N)

| here_LF_Hyb:
    forall G Gamma G' w A M N,
      types_LF G Gamma (here_LF M) (<*>A) ->
      LF_to_Hyb_ctx (Gamma::G) ((w, Gamma)::G') ->
      LF_to_Hyb_rel Gamma M A G' w N ->
      LF_to_Hyb_rel Gamma (here_LF M) (<*>A)
                    G' w (get_here_Hyb (fwo w) N)

| get_here_LF_Hyb:
    forall G Gamma Gamma' G' w w' A M N G'',
      w <> w' ->
      types_LF (Gamma'::G) Gamma (here_LF M) (<*>A) ->
      LF_to_Hyb_ctx (Gamma::Gamma'::G) ((w, Gamma)::(w', Gamma')::G') ->
      LF_to_Hyb_rel Gamma' M A
                    ((w, Gamma)::G') w' N ->
      ((w', Gamma')::G') ~=~ G'' ->
      LF_to_Hyb_rel Gamma (here_LF M) (<*>A)
                    G'' w (get_here_Hyb (fwo w') N)

| letdia_LF_Hyb:
    forall Lt Lw G Gamma G' w A B M1 M2 N1 N2,
      types_LF G Gamma (letdia_LF M1 N1) B ->
      LF_to_Hyb_rel Gamma M1 (<*>A) G' w M2 ->
      (forall w'0 v', w'0 \notin Lw -> v' \notin Lt ->
                     LF_to_Hyb_rel Gamma (open_LF N1 (hyp_LF (fte v'))) B
                                   ((w'0, (v', A) :: nil ) :: G') w
                                   ((N2 ^w^ fwo w'0 ) ^t^ hyp_Hyb (fte v'))) ->
      LF_to_Hyb_ctx (Gamma::G) ((w, Gamma)::G') ->
      LF_to_Hyb_rel Gamma (letdia_LF M1 N1) B G' w
                    (letdia_get_Hyb (fwo w) M2 N2)

| letdia_get_LF_Hyb:
    forall Lt Lw G Gamma Gamma' G' w w' A B M1 M2 N1 N2 G'',
      types_LF (Gamma'::G) Gamma (letdia_LF M1 N1) B ->
      LF_to_Hyb_rel Gamma' M1 (<*>A)
                    ((w, Gamma)::G') w' M2 ->
      (forall w'0 v', w'0 \notin Lw -> v' \notin Lt ->
         LF_to_Hyb_rel Gamma (open_LF N1 (hyp_LF (fte v'))) B
                       (((w'0, (v', A) :: nil ) :: (w', Gamma')::G'))
                       w ((N2 ^w^ fwo w'0 ) ^t^ hyp_Hyb (fte v'))) ->
      LF_to_Hyb_ctx (Gamma::Gamma'::G) ((w, Gamma)::(w', Gamma')::G') ->
      (w', Gamma')::G' ~=~ G'' ->
      LF_to_Hyb_rel Gamma (letdia_LF M1 N1) B
                    G'' w
                    (letdia_get_Hyb (fwo w') M2 N2)
.

Lemma LF_to_Hyb_rel_permut_G_Gamma:
forall Gamma Gamma' M A G w M' G',
  Gamma *=* Gamma' ->
  G ~=~ G' ->
  LF_to_Hyb_rel Gamma M A G w M' ->
  LF_to_Hyb_rel Gamma' M A G' w M'.
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

Add Morphism LF_to_Hyb_rel: LF_to_Hyb_rel_G.
split; intros.
eapply LF_to_Hyb_rel_permut_G_Gamma with (G:=x0) (Gamma:=x); auto.
eapply LF_to_Hyb_rel_permut_G_Gamma with (G:=y2) (Gamma:=y); auto; symmetry;
auto.
Qed.

Lemma LF_to_Hyb_types:
forall G' Gamma M A w M',
  LF_to_Hyb_rel Gamma M A G' w M' ->
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

Lemma LF_to_Hyb_value:
forall G' Gamma M A w M',
  LF_to_Hyb_rel Gamma M A G' w M' ->
  value_LF M -> value_Hyb M'.
intros; induction H; simpl;
inversion H0; subst; constructor; eauto.
Qed.

(* Fixme: rename if this works and stays (being useful) *)
Inductive R: te_LF -> te_Hyb -> Prop :=
| hyp_R: forall v, R (hyp_LF v) (hyp_Hyb v)
| lam_R: forall A M N, R M N -> R (lam_LF A M) (lam_Hyb A N)
| appl_R: forall M1 M2 N1 N2, R M1 N1 -> R M2 N2 ->
                              R (appl_LF M1 M2) (appl_Hyb N1 N2)
| box_R: forall M N, R M N -> R (box_LF M) (box_Hyb N)
| unbox_R: forall M N w, R M N -> R (unbox_LF M) (unbox_fetch_Hyb w N)
| here_R: forall M N w, R M N -> R (here_LF M) (get_here_Hyb w N)
| letdia_R: forall M M' N N' w, R M M' -> R N N' ->
                          R (letdia_LF M N) (letdia_get_Hyb w M' N')
.

Lemma R_subst_t:
forall M1 M2 C1 C2 v,
  R M1 M2 -> R C1 C2 -> R (subst_t_LF C1 v M1) (subst_t_Hyb C2 v M2).
induction M1; intros; inversion H; subst; simpl in *;
repeat case_if; try constructor; eauto.
Qed.

Lemma R_subst_t_rev:
forall M1 M2 v v',
  v' \notin used_vars_te_LF M1 \u free_vars_Hyb M2 ->
  R (subst_t_LF (hyp_LF (fte v')) (bte v) M1)
    (subst_t_Hyb (hyp_Hyb (fte v')) (bte v) M2) ->
  R M1 M2.
induction M1; intros; simpl in *; try case_if.
destruct M2; simpl in *; try case_if; try inversion H0; subst;
try rewrite notin_union in *;
[constructor | destruct H; rewrite notin_singleton in *; elim H2; auto].
destruct M2; simpl in *; try case_if; try inversion H0; subst;
try rewrite notin_union in *;
[destruct H; rewrite notin_singleton in *; elim H; auto | constructor].
destruct M2; simpl in *; try case_if; try inversion H0; subst; constructor;
eapply IHM1; eauto.
destruct M2; simpl in *; try case_if; try inversion H0; subst; constructor;
[eapply IHM1_1 | eapply IHM1_2]; eauto; rewrite notin_union in *; destruct H;
split; eauto.
destruct M2; simpl in *; try case_if; try inversion H0; subst; constructor;
eapply IHM1; eauto.
destruct M2; simpl in *; try case_if; try inversion H0; subst; constructor;
eapply IHM1; eauto.
destruct M2; simpl in *; try case_if; try inversion H0; subst; constructor;
eapply IHM1; eauto.
destruct M2; simpl in *; try case_if; try inversion H0; subst; constructor;
[eapply IHM1_1 | eapply IHM1_2]; eauto; rewrite notin_union in *; destruct H;
split; auto.
Qed.

Lemma R_subst_w:
forall M N w w',
  R M ({{w//w'}}N) <-> R M N.
split;
generalize dependent w';
generalize dependent w;
generalize dependent N;
generalize dependent M.
induction M; intros; inversion H; destruct N; simpl in *;
inversion H2; subst; inversion H; subst; constructor; eauto.
induction M; intros; inversion H; subst; simpl in *; repeat case_if;
constructor; eauto.
Qed.

(* This simply states that LF_to_Hyb_rel is one realisation of R *)
Lemma LF_to_Hyb_rel_R:
forall M1 Gamma A G' w M2,
  LF_to_Hyb_rel Gamma M1 A G' w M2 ->
  R M1 M2.
intros; induction H; constructor; auto.
(* lam *)
assert (exists x, x\notin L \u  used_vars_te_LF M \u free_vars_Hyb M')
  by apply Fresh; destruct H3;
specialize H2 with x;
unfold open_LF in *; unfold open_t_Hyb in *; apply R_subst_t_rev in H2; auto.
(* box *)
assert (exists x, x\notin L) by apply Fresh; destruct H3;
unfold open_w_Hyb in *. eapply R_subst_w; eauto.
(* letdia *)
assert (exists x, x\notin Lw) by apply Fresh.
destruct H4.
assert (exists x0, x0 \notin Lt \u used_vars_te_LF N1 \u
                              free_vars_Hyb {{fwo x // bwo 0}}N2)
  by apply Fresh; destruct H5.
specialize H2 with x x0.
unfold open_LF in *; unfold open_t_Hyb in *;
unfold open_w_Hyb in *.
apply H2 in H4; auto.
assert (R N1 ({{fwo x // bwo 0}} N2)).
apply R_subst_t_rev with (v:=0) (v':=x0); eauto.
apply R_subst_w with (w:=fwo x) (w':=bwo 0); auto.
(* letdia - get *)
assert (exists x, x\notin Lw) by apply Fresh.
destruct H5.
assert (exists x0, x0 \notin Lt \u used_vars_te_LF N1 \u
                              free_vars_Hyb {{fwo x // bwo 0}}N2)
  by apply Fresh; destruct H6.
specialize H2 with x x0.
unfold open_LF in *; unfold open_t_Hyb in *;
unfold open_w_Hyb in *.
apply H2 in H5; auto.
assert (R N1 ({{fwo x // bwo 0}} N2)).
apply R_subst_t_rev with (v:=0) (v':=x0); eauto.
apply R_subst_w with (w:=fwo x) (w':=bwo 0); auto.
Qed.

Lemma R_lc_t:
forall M N n,
  R M N -> lc_t_n_LF n M -> lc_t_n_Hyb n N.
induction M; intros; inversion H; inversion H0; subst; constructor; auto.
Qed.

Lemma R_value:
forall M N,
  R M N -> value_LF M -> value_Hyb N.
intros; induction H; simpl;
inversion H0; subst; constructor; eauto.
Qed.

Lemma R_step:
forall M M' N w,
  lc_w_Hyb N ->
  R M N -> step_LF M M' ->
  exists N', R M' N' /\ step_Hyb (N, w) (N', w).
(* ind: M *)
induction M; intros; inversion H0; inversion H1; subst.
(* appl - lam *)
inversion H4; inversion H; inversion H8; subst.
exists (subst_t_Hyb N2 (bte 0) N); split.
apply R_subst_t; auto.
constructor; try eapply R_lc_t; eauto; inversion H13; auto.
(* appl *)
inversion H; subst.
destruct IHM1 with M'0 N1 w; auto.
destruct H2.
exists (appl_Hyb x N2); split; constructor; auto;
try eapply R_lc_t; eauto.
(* unbox - box *)
inversion H; inversion H3; subst; try omega;
exists (open_w_Hyb N (w)); split;
[unfold open_w_Hyb; apply R_subst_w; auto |
 constructor; try eapply R_lc_t; eauto; inversion H5; auto].
(* unbox *)
inversion H; subst; try omega;
destruct IHM with M'0 N0 (fwo w1); auto; destruct H2;
exists (unbox_fetch_Hyb (fwo w1) x); split;
constructor; auto; try eapply R_lc_t; eauto.
(* here *)
inversion H; subst; try omega;
destruct IHM with M'0 N0 (fwo w1); auto; destruct H2;
exists (get_here_Hyb (fwo w1) x); split;
constructor; auto; try eapply R_lc_t; eauto.
(* letdia-here *)
inversion H; inversion H4; subst; try omega; inversion H11; subst; try omega.
exists ((N' ^w^ (fwo w0) ) ^t^ N0); split.
unfold open_w_Hyb; unfold open_t_Hyb; eapply R_subst_t; auto;
apply R_subst_w; auto.
constructor; try eapply R_lc_t; eauto; eapply R_value; eauto.
(* letdia *)
destruct w0; inversion H; subst; try omega.
destruct IHM1 with M'1 M'0 (fwo v); auto; destruct H2;
exists (letdia_get_Hyb (fwo v) x N'); split; constructor; auto;
try eapply R_lc_t; eauto.
Qed.

Lemma R_total_L:
forall M, exists N, R M N.
induction M; try destruct IHM || (destruct IHM1; destruct IHM2);
eexists; constructor; eauto.
Grab Existential Variables.
exact (bwo 0).
exact (bwo 0).
exact (bwo 0).
Qed.

Lemma R_te_vars:
forall N1 N2,
  R N1 N2 -> used_vars_te_LF N1 = free_vars_Hyb N2.
intros; induction H; simpl in *;
try rewrite IHR || (rewrite IHR1; rewrite IHR2); eauto.
Qed.

(* End of R properties *)

Fixpoint subst_in_ctx_LF (v1: var) (v2: var) (Gamma: ctx_LF) : ctx_LF :=
match Gamma with
| nil => nil
| (v, A) :: Gamma' =>
  let v' := if (eq_var_dec v v2) then v1 else v in
  (v', A):: subst_in_ctx_LF v1 v2 Gamma'
end.

Definition subst_in_ctx_Hyb v1 v2 (Gamma: ctx_Hyb) :=
(fst_ Gamma, subst_in_ctx_LF v1 v2 (snd_ Gamma)).

Lemma subst_in_ctx_LF_no_change:
forall v1 v2 Gamma,
  v2 \notin (from_list (map fst_ Gamma)) ->
  subst_in_ctx_LF v1 v2 Gamma = Gamma.
induction Gamma; intros; simpl in *; auto; destruct a; case_if;
simpl in *; rew_map in *; simpl in *; rewrite from_list_cons in *;
rewrite notin_union in *.
destruct H; elim H; rewrite in_singleton; auto.
rewrite IHGamma; destruct H; eauto.
Qed.

Lemma subst_in_ctx_Hyb_no_change:
forall v1 v2 Gamma,
  v2 \notin (from_list (map fst_ (snd_ Gamma))) ->
  subst_in_ctx_Hyb v1 v2 Gamma = Gamma.
intros; unfold subst_in_ctx_Hyb; destruct Gamma; simpl in *;
rewrite subst_in_ctx_LF_no_change; eauto.
Qed.

Fixpoint vars_from_G_Hyb (G: bg_Hyb) :=
match G with
| nil => \{}
| Gamma :: G' =>
  from_list (map fst_ (snd_ Gamma)) \u vars_from_G_Hyb G'
end.

Lemma subst_in_bg_Hyb_no_change:
forall v1 v2 G,
  v2 \notin vars_from_G_Hyb G ->
  G = map (subst_in_ctx_Hyb v1 v2) G.
induction G; intros; rew_map; auto.
destruct a. simpl in *.
rewrite subst_in_ctx_Hyb_no_change; eauto.
rewrite <- IHG; eauto.
simpl; auto.
Qed.

Lemma ok_Bg_LF_subst_in_bg_subst_in_ctx:
forall G G' Gamma w v1 v,
LF_to_Hyb_ctx (Gamma :: G) ((w, Gamma) :: G') ->
ok_Bg_LF (subst_in_ctx_LF v1 v Gamma ::
                          map (subst_in_ctx_LF v1 v) G).
Admitted.

Lemma Mem_ctx_LF:
forall v v' v0 v1 A Gamma,
  Mem (v, A) Gamma ->
  (v' = if (eq_var_dec v v0) then v1 else v) ->
  Mem (v', A) (subst_in_ctx_LF v1 v0 Gamma).
Admitted.

Lemma LF_to_Hyb_ctx_subst_t:
forall Gamma G w G' v0 v1,
LF_to_Hyb_ctx (Gamma :: G) ((w, Gamma) :: G') ->
LF_to_Hyb_ctx
     (subst_in_ctx_LF v1 v0 Gamma :: map (subst_in_ctx_LF v1 v0) G)
     ((w, subst_in_ctx_LF v1 v0 Gamma) :: map (subst_in_ctx_Hyb v1 v0) G').
Admitted.

Lemma types_renaming:
forall G Gamma M B v0 v,
  types_LF G Gamma M B ->
  types_LF (map (subst_in_ctx_LF v0 v) G)
     (subst_in_ctx_LF v0 v Gamma)
     (subst_t_LF (hyp_LF (fte v0)) (fte v) M) B.
intros; generalize dependent v; generalize dependent v0; induction H; intros.
Admitted.

Lemma LF_to_Hyb_rel_rename_vars:
forall Gamma M B G w N v,
  LF_to_Hyb_rel Gamma M B G w N ->
  forall v0 Gamma' G' M' N',
    v0 \notin \{} ->
    Gamma' = subst_in_ctx_LF v0 v Gamma ->
    G' = map (subst_in_ctx_Hyb v0 v) G ->
    M' = subst_t_LF (hyp_LF (fte v0)) (fte v) M ->
    N' = subst_t_Hyb (hyp_Hyb (fte v0)) (fte v) N ->
    LF_to_Hyb_rel Gamma' M' B G' w N'.
intros Gamma M B G w N v H; generalize dependent v;
induction H; intros; subst; simpl in *; repeat case_if.
(* hyp *)
apply hyp_LF_Hyb with (G:=map (subst_in_ctx_LF v1 v0) G); inversion H; subst.
constructor;
[eapply ok_Bg_LF_subst_in_bg_subst_in_ctx |
 apply Mem_ctx_LF with (v:=v0); auto; case_if]; eauto.
apply LF_to_Hyb_ctx_subst_t; auto.
apply hyp_LF_Hyb with (G:=map (subst_in_ctx_LF v1 v0) G); inversion H; subst.
constructor;
[eapply ok_Bg_LF_subst_in_bg_subst_in_ctx |
 apply Mem_ctx_LF with (v:=v2); auto; case_if]; eauto.
apply LF_to_Hyb_ctx_subst_t; auto.
(* lam *)
apply lam_LF_Hyb with (L:=L \u \{v}) (G:=map (subst_in_ctx_LF v0 v) G);
inversion H; subst.
apply t_lam_LF with (L:=L0 \u L \u \{v});
[eapply ok_Bg_LF_subst_in_bg_subst_in_ctx | intros]; eauto.
replace ((v1, A) :: subst_in_ctx_LF v0 v Gamma) with
  (subst_in_ctx_LF v0 v ((v1, A)::Gamma)).
unfold open_LF. rewrite <- subst_t_comm_LF; try constructor; eauto.
apply types_renaming; eauto.
simpl; case_if; auto; repeat rewrite notin_union in H4;
rewrite notin_singleton in H4; destruct H4; destruct H5; elim H6; auto.
apply LF_to_Hyb_ctx_subst_t; auto.
intros. apply H2 with (v0:=v1)(v1:=v0)(v:=v); eauto; repeat case_if; auto.
rewrite notin_union in *; destruct H4; rewrite notin_singleton in *;
elim H5; auto.
unfold open_LF; rewrite subst_t_comm_LF; auto; constructor.
unfold open_t_Hyb; rewrite subst_t_Hyb_comm; auto; constructor.
(* appl *)
Admitted.

Definition subst_w_in_ctx_Hyb w1 w2 (Gamma: ctx_Hyb) :=
let w' :=  if eq_var_dec (fst_ Gamma) w2 then w1 else (fst_ Gamma)
in (w', snd_ Gamma).

Lemma subst_w_in_bg_Hyb_no_change:
forall G v1 v2,
  v2 \notin from_list (map fst_ G) ->
  G = map (subst_w_in_ctx_Hyb v1 v2) G.
unfold subst_w_in_ctx_Hyb in *;
induction G; intros; rew_map; auto;
destruct a; rew_map in *; simpl in *; case_if;
rewrite from_list_cons in H; rewrite notin_union in H; destruct H.
elim H; rewrite in_singleton; auto.
rewrite <- IHG; eauto.
Qed.

Lemma LF_to_Hyb_rel_rename_worlds:
forall Gamma M B G N w w'',
  LF_to_Hyb_rel Gamma M B G w N ->
  forall w' G' N' w0,
    w' \notin \{} ->
    G' = map (subst_w_in_ctx_Hyb w' w'') G ->
    N' = subst_w_Hyb (fwo w') (fwo w'') N ->
    (w0 = if (eq_var_dec w w'') then w' else w) ->
    LF_to_Hyb_rel Gamma M B G' w0 N'.
Admitted.

Lemma LF_to_Hyb_rel_lc_t:
forall Gamma M A G w N',
  LF_to_Hyb_rel Gamma M A G w N' ->
  lc_t_Hyb N'.
intros.
apply types_Hyb_lc_t_Hyb with (G:=G) (Gamma:=Gamma) (A:=A) (w:=w).
apply LF_to_Hyb_types in H; auto.
Qed.

Lemma LF_to_Hyb_rel_subst_t_rev:
forall N Gamma M v N' A B G w M',
  LF_to_Hyb_rel Gamma (subst_t_LF M v N) A G w N' ->
  LF_to_Hyb_rel Gamma M B G w M' ->
  exists N0,
    N' = subst_t_Hyb M' v N0.
induction N; intros; simpl in *; repeat case_if.
Admitted.

Lemma LF_to_Hyb_rel_te_vars:
forall N1 N2 Gamma A G w,
  LF_to_Hyb_rel Gamma N1 A G w N2 ->
  used_vars_te_LF N1 = free_vars_Hyb N2.
intros; apply R_te_vars; eapply LF_to_Hyb_rel_R; eauto.
Qed.

Lemma free_vars_Hyb_subst_t:
forall N C k,
  free_vars_Hyb ([C // bte k] N) = free_vars_Hyb N \/
  free_vars_Hyb ([C // bte k] N) = free_vars_Hyb C \u free_vars_Hyb N.
induction N; intros; simpl in *.
destruct v; case_if; simpl;
[right; rewrite union_empty_r | left | left ]; auto.
destruct IHN with C (S k); rewrite <- H; [left | right]; auto.
destruct IHN1 with C k; destruct IHN2 with C k; rewrite H; rewrite H0;
[left | right | right | right]; auto.
rewrite <- union_comm_assoc; auto.
rewrite union_assoc; auto.
rewrite <- union_comm_assoc.
rewrite <- union_assoc.
assert (forall N,
          free_vars_Hyb C \u free_vars_Hyb C \u N = free_vars_Hyb C \u N).
intros; rewrite union_assoc; rewrite union_same; auto.
rewrite H1; auto.
destruct IHN with C k; rewrite H; [left | right]; auto.
destruct IHN with C k; rewrite H; [left | right]; auto.
destruct IHN with C k; rewrite H; [left | right]; auto.
destruct IHN1 with C k; destruct IHN2 with C (S k); rewrite H; rewrite H0;
[left | right | right | right]; auto.
rewrite <- union_comm_assoc; auto.
rewrite union_assoc; auto.
rewrite <- union_comm_assoc.
rewrite <- union_assoc.
assert (forall N,
          free_vars_Hyb C \u free_vars_Hyb C \u N = free_vars_Hyb C \u N).
intros; rewrite union_assoc; rewrite union_same; auto.
rewrite H1; auto.
Qed.

Lemma free_vars_subset:
forall G w Gamma M A,
  G |= (w, Gamma) |- M ::: A ->
  forall x, x \in free_vars_Hyb M ->
      Mem x (concat (map (fun x => map fst_ (snd_ x)) ((w, Gamma)::G))).
intros G w Gamma M A H; induction H; intros; rew_map; rew_concat; simpl in *.
rewrite in_singleton in H; subst.
rewrite Mem_app_or_eq; left. induction Gamma0; rew_map; simpl in *.
rewrite Mem_nil_eq in HT; contradiction. destruct a; simpl in *.
rewrite Mem_cons_eq in *; destruct HT; [inversion H; subst | ];
[left | right]; eauto; eapply IHGamma0; auto. skip.
Admitted.

Lemma LF_to_Hyb_rel_total_L:
forall M Gamma A G' w,
  types_LF (map snd_ G') Gamma M A ->
  LF_to_Hyb_ctx (Gamma::(map snd_ G')) ((w, Gamma)::G') ->
  exists M',
    LF_to_Hyb_rel Gamma M A G' w M'.
intros; generalize dependent w;
remember (map snd_ G') as G;
generalize dependent G';
induction H; intros; subst.
(* hyp *)
exists (hyp_Hyb (fte v)); econstructor; eauto using types_LF.
(* lam *)
assert (exists v, v \notin L \u used_vars_te_LF M \u vars_from_G_Hyb G' \u
        from_list (map fst_ Gamma) \u used_vars_ctx_LF (Gamma::(map snd_ G')))
  as HF by apply Fresh; destruct HF;
destruct H0 with x G' w; auto; [eapply LF_to_Hyb_ctx_extend2_t; eauto | ].
(*
exists (lam_Hyb A x0); econstructor; eauto. econstructor; eauto.
intros; unfold open_LF in *; unfold open_t_Hyb in *.
assert (lc_t_Hyb x0).
  apply types_Hyb_lc_t_Hyb with (G:=G') (Gamma:=(x, A)::Gamma) (A:=B) (w:=w);
  apply LF_to_Hyb_types in H3; auto.
rewrite closed_subst_t_Hyb_bound with (n:=0); auto; try omega.
replace ((v0, A) :: Gamma) with (subst_in_ctx_LF v0 x ((x,A)::Gamma)).
replace (subst_t_LF (hyp_LF (fte v0)) (bte 0) M) with
   (subst_t_LF (hyp_LF (fte v0)) (fte x)
               (subst_t_LF (hyp_LF (fte x)) (bte 0) M)).
replace G' with (map (subst_in_ctx_Hyb v0 x) G').
replace x0 with
  ([hyp_Hyb (fte v0) // fte x] x0).
apply LF_to_Hyb_rel_rename_vars with ((x,A)::Gamma)
      (subst_t_LF (hyp_LF (fte x)) (bte 0) M) G' x0
      x v0; auto.
rewrite closed_subst_t_Hyb_free; auto.
(* x \notin FV x0 -- this may be tricky as x is created before x0;
also because x0 is in a relation with M ^t^ x, and FV x0 = FV (M ^t^ x).. *)
skip. (* !!!!! *)
rewrite <- subst_in_bg_Hyb_no_change; auto.
rewrite <- subst_t_neutral_free_LF; eauto.
simpl; case_if; rewrite subst_in_ctx_LF_no_change; auto.
*)
(* This is the non-cheating version:
It requires one more lemma then the one above: LF_to_Hyb_rel_subst_t_rev
*)
unfold open_LF in *;
assert (LF_to_Hyb_rel ((x, A) :: Gamma)
         (subst_t_LF (hyp_LF (fte x)) (bte 0) M) B G' w x0) by auto;
apply LF_to_Hyb_rel_subst_t_rev with (M:=hyp_LF (fte x)) (M':=hyp_Hyb (fte x))
                                                         (B:=A)
 in H3.
destruct H3; exists (lam_Hyb A x1);
apply lam_LF_Hyb with (L:=L)(G:=map snd_ G');
[ apply t_lam_LF with (L:=L) | |]; eauto;
intros; subst; unfold open_LF; unfold open_t_Hyb.
replace ((v0, A) :: Gamma) with (subst_in_ctx_LF v0 x ((x,A)::Gamma)).
replace (subst_t_LF (hyp_LF (fte v0)) (bte 0) M) with
   (subst_t_LF (hyp_LF (fte v0)) (fte x)
               (subst_t_LF (hyp_LF (fte x)) (bte 0) M)).
replace G' with (map (subst_in_ctx_Hyb v0 x) G').
replace ([hyp_Hyb (fte v0) // bte 0]x1) with
  ([hyp_Hyb (fte v0) // fte x] ([hyp_Hyb (fte x) // bte 0] x1)).
apply LF_to_Hyb_rel_rename_vars with ((x,A)::Gamma)
      (subst_t_LF (hyp_LF (fte x)) (bte 0) M) G' ([hyp_Hyb (fte x) // bte 0]x1)
      x v0; auto.
rewrite notin_union in H2; destruct H2; rewrite <- subst_t_Hyb_neutral_free;
auto. (* x \notin FV x1 -- this is tricky as x is created before x1 *)
assert (~ Mem x (concat (map (fun x => map fst_ (snd_ x))
                             ((w, Gamma)::G')))).
  rew_map; simpl; rew_concat; rewrite Mem_app_or_eq.
  repeat rewrite notin_union in H3; destruct H3; destruct H6; destruct H7.
  intro; destruct H9.
  elim H7; apply from_list_Mem; eauto.
  skip.
intro. apply free_vars_subset with G' w (Gamma) x1 B x in H7.
contradiction.
apply LF_to_Hyb_types in H4.

(* PROBLEM:
This does not type (it's open, d'uh..); for [hyp_Hyb (fte x) // bte 0]x1 version
we cannot cheat like this (b/c x actually is in the context variables)
Need alternatives :(
*)
(* This may be technical, but it should be doable with some extensions of set
to express FV N in relation to FV [M/k]N *) skip. (* !!!!! *)
rewrite <- subst_in_bg_Hyb_no_change; auto.
rewrite <- subst_t_neutral_free_LF; eauto.
simpl; case_if; rewrite subst_in_ctx_LF_no_change; auto.
apply hyp_LF_Hyb with (G:=map snd_ G').
constructor; auto; try apply Mem_here; apply ok_Bg_LF_fresh; auto.
apply LF_to_Hyb_ctx_extend2_t; auto.
(* appl *)
destruct IHtypes_LF1 with G' w; auto;
destruct IHtypes_LF2 with G' w; auto;
exists (appl_Hyb x x0); econstructor; eauto; econstructor; eauto.
(* box *)
remember (from_list (map fst_ (G' & (w, Gamma)))) as U.
assert (exists (w: var), w \notin U) by apply Fresh; destruct H1;
destruct IHtypes_LF with (G' & (w, Gamma)) x; auto;
[rew_map; auto | apply LF_to_Hyb_ctx_extend2_w; eauto | ].
assert (PPermut_LF (map snd_ G' & Gamma) (Gamma :: map snd_ G'))
  by PPermut_LF_simpl;
assert (PPermut_Hyb (G' & (w, Gamma)) ((w, Gamma) :: G'))
  by PPermut_Hyb_simpl;
rewrite H2; rewrite H3; auto.
assert (lc_w_Hyb x0).
  apply types_Hyb_lc_w_Hyb with (G:=G' & (w, Gamma)) (Gamma:=nil) (A:=A) (w:=x);
  apply LF_to_Hyb_types in H2; auto.
exists (box_Hyb x0); econstructor; eauto;
[econstructor; eauto | intros]; unfold open_w_Hyb.
assert (PPermut_Hyb (G' & (w, Gamma)) ((w, Gamma) :: G'))
  by PPermut_Hyb_simpl;
rewrite <- H5.
replace (G' & (w, Gamma)) with
  (map (subst_w_in_ctx_Hyb w0 x) (G' & (w, Gamma))).
replace ({{fwo w0 // bwo 0}}x0) with
  ({{fwo w0//fwo x}}{{fwo x // bwo 0}}x0).
apply LF_to_Hyb_rel_rename_worlds with
  (G' & (w, Gamma)) ({{fwo x // bwo 0}} x0) x x w0; eauto; try (case_if; auto).
rewrite closed_subst_w_Hyb_bound with (n:=0); auto; try omega.
(* Q: can I do the same cheat for lambda? (With not splitting x0) *)
rewrite subst_w_Hyb_neutral_free; auto.
(* Just as tricky as before, x is created before x0 *) skip.
rewrite <- subst_w_in_bg_Hyb_no_change; subst; auto.
(* unbox *)
destruct IHtypes_LF with G' w; auto;
exists (unbox_fetch_Hyb (fwo w) x); econstructor; eauto; constructor; auto.
(* unbox-fetch *)
assert (exists (G0: bg_Hyb), G = map snd_ G0) by skip. destruct H2 as (G0).
assert (exists w',
          PPermut_Hyb (G0 & (w', Gamma)) G'0) by skip. (* from H0 *)
destruct H3 as (w').
destruct IHtypes_LF with (G0 & (w, Gamma')) w'; auto.
rew_map; simpl; subst; auto.
subst. skip.
exists (unbox_fetch_Hyb (fwo w') x).
replace G'0 with ((w', Gamma) :: G0) by skip. (* lemma mentioned earlier *)
apply unbox_fetch_LF_Hyb with (G:=G); eauto. skip (* from ok + rel on ctxts *).
apply t_unbox_fetch_LF with (G:=G) (Gamma:=Gamma); auto. PPermut_LF_simpl.
skip. (* permuts *)
replace ((w, Gamma')::G0) with (G0 & (w, Gamma')) by skip. auto.
(* here *)
destruct IHtypes_LF with G' w; auto.
exists (get_here_Hyb (fwo w) x); econstructor; eauto; constructor; auto.
(* get-here *)
assert (exists (G0: bg_Hyb), G = map snd_ G0) by skip. destruct H2 as (G0).
assert (exists w',
          PPermut_Hyb (G0 & (w', Gamma)) G'0) by skip. (* from H0 *)
destruct H3 as (w').
destruct IHtypes_LF with (G0 & (w, Gamma')) w'; auto.
rew_map; simpl; subst; auto.
subst. skip.
exists (get_here_Hyb (fwo w') x).
replace G'0 with ((w', Gamma) :: G0) by skip. (* lemma mentioned earlier *)
apply get_here_LF_Hyb with (G:=G); eauto. skip (* from ok + rel on ctxts *).
apply t_get_here_LF with (G:=G) (Gamma:=Gamma); auto. PPermut_LF_simpl.
skip. (* permuts *)
replace ((w, Gamma')::G0) with (G0 & (w, Gamma')) by skip. auto.
(* letdia *)
assert (exists x, x \notin L) by apply Fresh; destruct H2.
destruct H0 with (((x,A)::nil) :: map snd_ G') x ((x, (x,A)::nil)::G') w; auto.
skip.
assert ( LF_to_Hyb_rel Gamma (open_LF N (hyp_LF (fte x))) B
         ((x, (x, A) :: nil) :: G') w x0) by auto.
skip. (*combination of lambda and box *)
(* letdia-get *)
skip. (* combin. of lambda, box and unbox *)
Qed.

Close Scope hybrid_is5_scope.
Close Scope permut_scope.
Close Scope is5_scope.
