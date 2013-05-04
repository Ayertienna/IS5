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

Lemma L_to_Hyb_subst_t:
forall M M' N N' G Gamma' G' Gamma w w' B A v,
  LF_to_Hyb_term_R Gamma N B G w N' ->
  LF_to_Hyb_term_R Gamma' M A G' w' M' ->
  (* inner subst *)
  ((w, Gamma) :: G ~=~ (w', (v, A) :: Gamma') :: G' ->
   LF_to_Hyb_term_R Gamma' (subst_t_LF M (fte v) N) B G w ([M'//(fte v)]N')) /\
  (* outer subst *) True.
Admitted.
(*
intros. generalize dependent N; generalize dependent N'.
remember  ((v, A1) :: Gamma) as Gamma';
generalize dependent Gamma;
generalize dependent v;
generalize dependent A1.
induction H; intros; simpl in *; subst.
inversion H; subst; repeat case_if.
inversion H2; subst.
rewrite Mem_cons_eq in H5; destruct H5.
inversion H4; subst; auto.
skip. (* Ok + H4 = contradiction *)
econstructor; eauto. constructor; eauto. skip. skip. skip. (*trivial *)
(* lam *)
econstructor; eauto.
replace (lam_LF A (subst_t_LF N (fte v) M)) with
(subst_t_LF N (fte v) (lam_LF A M)).
apply subst_t_LF_preserv_types_inner with (A:=A1). skip. eauto.
skip. simpl; auto. skip.
intros. unfold open_LF in *.
rewrite <- subst_t_comm_LF. unfold open_t_Hyb in *.
rewrite <- subst_t_Hyb_comm. apply H2 with (A2:=A1); eauto.
skip. (* permut *) skip. (* weakening *) skip. skip. skip. skip.
Admitted.
*)

Lemma L_to_Hyb_subst_t_inner:
forall M M' N N' G Gamma w B A v,
  LF_to_Hyb_term_R ((v, A)::Gamma) N B G w N' ->
  LF_to_Hyb_term_R Gamma M A G w M' ->
  LF_to_Hyb_term_R Gamma (subst_t_LF M (fte v) N) B G w ([M'//(fte v)]N').
intros; eapply L_to_Hyb_subst_t
        with (Gamma':=Gamma) (Gamma:=(v, A)::Gamma); eauto.
Qed.

(* Can it also preserve reductions? *)

Lemma L_to_Hyb_step:
forall M M' G' Gamma N w A,
  lc_w_Hyb N ->
  LF_to_Hyb_term_R Gamma M A G' w N -> step_LF M M' ->
  exists N', LF_to_Hyb_term_R Gamma M' A G' w N' /\
             step_Hyb (N, fwo w) (N', fwo w).
induction M; intros; inversion H1; subst.
(* appl_lam *)
clear IHM1 IHM2.
inversion H0; inversion H7; subst.
exists (M' ^t^ N2); split.
unfold open_t_Hyb in *; unfold open_LF in *.
assert (exists x, x \notin L \u used_vars_te_LF M \u free_vars_Hyb M')
  by apply Fresh; destruct H2.
rewrite subst_t_neutral_free_LF with (v:=x); auto.
rewrite subst_t_Hyb_neutral_free with (v:=x); auto.
apply L_to_Hyb_subst_t_inner with (A:=A1); eauto.
econstructor; auto.
skip. skip. skip. skip. (* lc * *)
(* appl *)
Admitted.

(*
(* Simpler relation that captures too much -- but preserves it all! *)

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

(* This simply states that LF_to_Hyb_term_R is one realisation of R *)
Lemma LF_to_Hyb_term_R_R:
forall M1 Gamma A G' w M2,
  LF_to_Hyb_term_R Gamma M1 A G' w M2 ->
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

(*****************************************************************************)
(* LF_to_Hyb_term_R is left-total for typing terms
I just want to "see what it takes" to proove this, not really make a full proof.
 *)

(* We can replace one variable with another in the environment and the term
 -- and the typing is intact *)
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

Lemma Mem_ctx_LF:
forall Gamma v v' v0 v1 A,
  Mem (v, A) Gamma ->
  (v' = if (eq_var_dec v v0) then v1 else v) ->
  Mem (v', A) (subst_in_ctx_LF v1 v0 Gamma).
induction Gamma; intros; [rewrite Mem_nil_eq in *; contradiction | ];
destruct a; rewrite Mem_cons_eq in *. simpl.
destruct H.
inversion H; subst; case_if; apply Mem_here.
repeat case_if; rewrite Mem_cons_eq; right; eapply IHGamma; eauto;
case_if; auto.
Qed.

Lemma types_renaming:
forall G Gamma M B v0 v,
  types_LF G Gamma M B ->
  types_LF (map (subst_in_ctx_LF v0 v) G)
     (subst_in_ctx_LF v0 v Gamma)
     (subst_t_LF (hyp_LF (fte v0)) (fte v) M) B.
intros; generalize dependent v; generalize dependent v0; induction H; intros.
Admitted.

Lemma LF_to_Hyb_term_R_rename_vars:
forall Gamma M B G w N v,
  LF_to_Hyb_term_R Gamma M B G w N ->
  forall v0 Gamma' G' M' N',
    v0 \notin \{} ->
    Gamma' = subst_in_ctx_LF v0 v Gamma ->
    G' = map (subst_in_ctx_Hyb v0 v) G ->
    M' = subst_t_LF (hyp_LF (fte v0)) (fte v) M ->
    N' = subst_t_Hyb (hyp_Hyb (fte v0)) (fte v) N ->
    LF_to_Hyb_term_R Gamma' M' B G' w N'.
Admitted.

Lemma subst_t_Hyb_neutral_bound:
forall (M : te_Hyb) x y k,
  lc_t_n_Hyb k M ->
  [hyp_Hyb (fte x)//fte y]M =
  [hyp_Hyb (fte x) // bte k]([hyp_Hyb (bte k) // fte y]M).
induction M; intros; simpl in *; repeat (case_if; simpl in * ); auto.
inversion H; omega.
inversion H; subst; rewrite IHM with (k:=S k); auto.
Admitted. (* This is not true in current implementation of substitution! *)

Lemma LF_to_Hyb_term_R_renaming:
forall G' Gamma x A B NtoX v0 w M,
lc_t_Hyb NtoX ->
x \notin from_list (map fst_ Gamma) \u
  vars_from_G_Hyb G'\u used_vars_te_LF M ->
LF_to_Hyb_term_R ((x, A) :: Gamma)
         (subst_t_LF (hyp_LF (fte x)) (bte 0) M) B G' w NtoX ->
LF_to_Hyb_term_R ((v0, A) :: Gamma)
                 (subst_t_LF (hyp_LF (fte v0)) (bte 0) M) B G' w
                 [hyp_Hyb (fte v0) // bte 0]([hyp_Hyb (bte 0) // fte x]NtoX).
intros.
apply LF_to_Hyb_term_R_rename_vars with (v:=x) (v0:=v0)
                                        (Gamma':=(v0,A)::Gamma)
                                        (G':=G')
(M':=subst_t_LF (hyp_LF (fte v0)) (bte 0) M)
(N':=[hyp_Hyb (fte v0) // bte 0]([hyp_Hyb (bte 0) // fte x]NtoX)) in H1;
auto.
simpl; case_if; rewrite subst_in_ctx_LF_no_change; auto.
rewrite <- subst_in_bg_Hyb_no_change; auto.
rewrite <- subst_t_neutral_free_LF; auto.
rewrite subst_t_Hyb_neutral_bound with (k:=0); auto.
Qed.

Lemma LF_to_Hyb_term_R_total_L:
forall M Gamma A G' w,
  types_LF (map snd_ G') Gamma M A ->
  LF_to_Hyb_ctx (Gamma::(map snd_ G')) ((w, Gamma)::G') ->
  exists M',
    LF_to_Hyb_term_R Gamma M A G' w M'.
intros; generalize dependent w;
remember (map snd_ G') as G;
generalize dependent G'.
induction H; intros; subst.
(* hyp *)
exists (hyp_Hyb (fte v)); econstructor; eauto using types_LF.
(* lam *)
assert (exists v, v \notin L \u used_vars_te_LF M \u vars_from_G_Hyb G' \u
        used_t_vars_Hyb ((w, Gamma) :: G') \u
        from_list (map fst_ Gamma) \u used_vars_ctx_LF (Gamma::(map snd_ G')))
  as HF by apply Fresh; destruct HF.
destruct H0 with x G' w as (NtoX); auto;
[eapply LF_to_Hyb_ctx_extend2_t; eauto | ].
exists (lam_Hyb A ([hyp_Hyb (bte 0) // fte x] NtoX));
apply lam_LF_Hyb with (G:=map snd_ G') (L:=L); eauto.
econstructor; eauto.
intros; unfold open_LF in *; unfold open_t_Hyb in *.
apply LF_to_Hyb_term_R_renaming.
skip. (* it is in relation, so it types, so it's lct, boooring *)
repeat rewrite notin_union in *; repeat split;
destruct H2; destruct H5; destruct H6; destruct H7; destruct H8;
auto.
auto.
(* appl *)
destruct IHtypes_LF1 with G' w; auto;
destruct IHtypes_LF2 with G' w; auto;
exists (appl_Hyb x x0); econstructor; eauto; econstructor; eauto.
(* box *)
remember (from_list (map fst_ (G' & (w, Gamma))) \u
                    used_w_vars_Hyb (G' & (w, Gamma))) as U.
assert (exists (w: var), w \notin U)
  by apply Fresh; destruct H1;
destruct IHtypes_LF with (G' & (w, Gamma)) x as (MtoX); auto;
[rew_map; auto | apply LF_to_Hyb_ctx_extend2_w; eauto | ].
assert (PPermut_LF (map snd_ G' & Gamma) (Gamma :: map snd_ G'))
  by PPermut_LF_simpl;
assert (PPermut_Hyb (G' & (w, Gamma)) ((w, Gamma) :: G'))
  by PPermut_Hyb_simpl;
rewrite H2; rewrite H3; eauto.
subst; auto.
assert (lc_w_Hyb MtoX).
  apply types_Hyb_lc_w_Hyb with (G:=G' & (w, Gamma)) (Gamma:=nil) (A:=A) (w:=x);
  apply LF_to_Hyb_types in H2; auto.
exists (box_Hyb ({{bwo 0 // fwo x}}MtoX)); econstructor; eauto;
[apply t_box_LF; eauto | intros]; unfold open_w_Hyb.
rewrite subst_w_Hyb_neutral_bound with (n:=0); try omega; auto.
(* this requires same approach as lambda, only with renaming of worlds *)
skip.
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
replace G'0 with ((w', Gamma) :: G0) by skip.
eapply unbox_fetch_LF_Hyb with (G:=G); eauto. skip (* from ok + rel on ctxts *).
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
replace G'0 with ((w', Gamma) :: G0) by skip.
eapply get_here_LF_Hyb with (G:=G); eauto. skip (* from ok + rel on ctxts *).
apply t_get_here_LF with (G:=G) (Gamma:=Gamma); auto. PPermut_LF_simpl.
skip. (* permuts *)
replace ((w, Gamma')::G0) with (G0 & (w, Gamma')) by skip. auto.
(* letdia *)
(* Combination of lambda and box *)
skip.
(* letdia-get *)
(* Combination of lambda and box *)
skip.
Admitted.
*)

Close Scope hybrid_is5_scope.
Close Scope permut_scope.
Close Scope is5_scope.
