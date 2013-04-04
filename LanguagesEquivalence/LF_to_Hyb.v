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
(* FIXME: There is no labelfree is5 scope *)
Open Scope hybrid_is5_scope.

Definition LF_to_Hyb_ctx (G: bg_LF) (G': bg_Hyb) :=
  map snd_ G' *=* G /\ ok_Hyb G' nil.

Lemma LF_to_Hyb_ctx_Ok:
forall G G',
  ok_Bg_LF G -> LF_to_Hyb_ctx G G' -> ok_Bg_Hyb G'.
Admitted.

Lemma LF_to_Hyb_ctx_extend_t:
forall G G' w Gamma v A,
LF_to_Hyb_ctx (((v,A)::Gamma)::G) ((w, (v,A)::Gamma)::G') ->
LF_to_Hyb_ctx (Gamma::G) ((w, Gamma)::G').
Admitted.

Lemma LF_to_Hyb_ctx_extend_w:
forall G G' w,
  LF_to_Hyb_ctx (nil::G) ((w, nil)::G') ->
  LF_to_Hyb_ctx G G'.
Admitted.

Add Morphism LF_to_Hyb_ctx: LF_to_Hyb_ctx_LF.
Admitted.

Fixpoint LF_to_Hyb_ctx_fun (G: bg_LF) (U: list var) :=
match G with
| nil => nil
| Gamma :: G' =>
  let w:= var_gen (from_list U) in
  (w, Gamma) :: LF_to_Hyb_ctx_fun G' (w::U)
end.

(* For each good context from LF there is a context from Hyb that extends it *)
(* Namely the one created in LF_to_Hyb_ctx_fun *)
Lemma LF_to_Hyb_ctx_Exists:
forall Gamma G,
  ok_Bg_LF (Gamma::G) ->
  exists w' G', LF_to_Hyb_ctx (Gamma::G) ((w', Gamma)::G').
Admitted.

Inductive LF_to_Hyb_rel: (* bg_LF  -> *) ctx_LF  -> te_LF  -> ty ->
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
    forall G Gamma Gamma' G' w w' M N A,
      w <> w' ->
      types_LF (Gamma'::G) Gamma (unbox_LF M) A ->
      LF_to_Hyb_ctx (Gamma::Gamma'::G) ((w, Gamma)::(w', Gamma')::G') ->
      LF_to_Hyb_rel Gamma' M ([*]A)
                    ((w, Gamma)::G') w' N ->
      LF_to_Hyb_rel Gamma (unbox_LF M) A
                    ((w', Gamma')::G') w (unbox_fetch_Hyb (fwo w') N)

| here_LF_Hyb:
    forall G Gamma G' w A M N,
      types_LF G Gamma (here_LF M) (<*>A) ->
      LF_to_Hyb_ctx (Gamma::G) ((w, Gamma)::G') ->
      LF_to_Hyb_rel Gamma M A G' w N ->
      LF_to_Hyb_rel Gamma (here_LF M) (<*>A)
                    G' w (get_here_Hyb (fwo w) N)

| get_here_LF_Hyb:
    forall G Gamma Gamma' G' w w' A M N,
      w <> w' ->
      types_LF (Gamma'::G) Gamma (here_LF M) (<*>A) ->
      LF_to_Hyb_ctx (Gamma::Gamma'::G) ((w, Gamma)::(w', Gamma')::G') ->
      LF_to_Hyb_rel Gamma' M A
                    ((w, Gamma)::G') w' N ->
      LF_to_Hyb_rel Gamma (here_LF M) (<*>A)
                    ((w', Gamma')::G') w (get_here_Hyb (fwo w') N)

(*Note: letdia is done without subst_t and subst_w, just to see
if this is better than with - as is done in lam and box *)
| letdia_LF_Hyb:
    forall Lt Lw G Gamma G' w A B M1 M2 N1 N2,
      types_LF G Gamma (letdia_LF M1 N1) B ->
      LF_to_Hyb_rel Gamma M1 (<*>A) G' w M2 ->
      (forall w'0 v', w'0 \notin Lw -> v' \notin Lt ->
                     LF_to_Hyb_rel Gamma (open_LF (hyp_LF (fte v')) N1) B
                                   ((w'0, (v', A) :: nil ) :: G') w
                                   ((N2 ^w^ fwo w'0 ) ^t^ hyp_Hyb (fte v'))) ->
      LF_to_Hyb_ctx (Gamma::G) ((w, Gamma)::G') ->
      LF_to_Hyb_rel Gamma (letdia_LF M1 N1) B G' w
                    (letdia_get_Hyb (fwo w) M2 N2)

| letdia_get_LF_Hyb:
    forall Lt Lw G Gamma Gamma' G' w w' A B M1 M2 N1 N2,
      types_LF (Gamma'::G) Gamma (letdia_LF M1 N1) B ->
      LF_to_Hyb_rel Gamma' M1 (<*>A)
                    ((w, Gamma)::G') w' M2 ->
      (forall w'0 v', w'0 \notin Lw -> v' \notin Lt ->
         LF_to_Hyb_rel Gamma (open_LF (hyp_LF (fte v')) N1) B
                       (((w'0, (v', A) :: nil ) :: (w', Gamma')::G'))
                       w ((N2 ^w^ fwo w'0 ) ^t^ hyp_Hyb (fte v'))) ->
      LF_to_Hyb_ctx (Gamma::Gamma'::G) ((w, Gamma)::(w', Gamma')::G') ->
      LF_to_Hyb_rel Gamma (letdia_LF M1 N1) B
                    ((w', Gamma')::G') w
                    (letdia_get_Hyb (fwo w') M2 N2)
.

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
inversion H0; subst.
apply t_unbox_fetch_Hyb with (G:=G') (Gamma:=Gamma').
assert ((w, Gamma) :: (w', Gamma') :: G' ~=~ (w', Gamma') :: G' & (w, Gamma))
  by PPermut_Hyb_simpl;
rewrite <- H3; eapply LF_to_Hyb_ctx_Ok ; eauto.
assert (G' & (w, Gamma) ~=~ (w, Gamma) :: G') by PPermut_Hyb_simpl;
rewrite H3; auto.
PPermut_Hyb_simpl.
apply t_unbox_fetch_Hyb with (G:=G') (Gamma:=Gamma').
assert ((w, Gamma) :: (w', Gamma') :: G' ~=~ (w', Gamma') :: G' & (w, Gamma))
  by PPermut_Hyb_simpl.
assert (PPermut_LF (Gamma0 :: G0 & Gamma) (Gamma :: Gamma' :: G)) by
(transitivity (G0 & Gamma0 & Gamma); [ | rewrite H7 ];
 rew_app; PPermut_LF_simpl).
rewrite H5 in Ok.
rewrite <- H3; eapply LF_to_Hyb_ctx_Ok ; eauto.
assert (G' & (w, Gamma) ~=~ (w, Gamma) :: G') by PPermut_Hyb_simpl;
rewrite H3; auto.
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
inversion H0; subst.
apply t_get_here_Hyb with (G:=G') (Gamma:=Gamma').
assert ((w, Gamma) :: (w', Gamma') :: G' ~=~ (w', Gamma') :: G' & (w, Gamma))
  by PPermut_Hyb_simpl;
rewrite <- H3; eapply LF_to_Hyb_ctx_Ok ; eauto.
assert (G' & (w, Gamma) ~=~ (w, Gamma) :: G') by PPermut_Hyb_simpl;
rewrite H3; auto.
PPermut_Hyb_simpl.
apply t_get_here_Hyb with (G:=G') (Gamma:=Gamma').
assert ((w, Gamma) :: (w', Gamma') :: G' ~=~ (w', Gamma') :: G' & (w, Gamma))
  by PPermut_Hyb_simpl.
assert (PPermut_LF (Gamma0 :: G0 & Gamma) (Gamma :: Gamma' :: G)) by
(transitivity (G0 & Gamma0 & Gamma); [ | rewrite H8 ];
 rew_app; PPermut_LF_simpl).
rewrite H4 in Ok.
rewrite <- H3; eapply LF_to_Hyb_ctx_Ok ; eauto.
assert (G' & (w, Gamma) ~=~ (w, Gamma) :: G') by PPermut_Hyb_simpl;
rewrite H3; auto.
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
inversion H; subst.
eapply t_letdia_get_Hyb with (G:=G') (Gamma:=Gamma').
assert ((w, Gamma) :: (w', Gamma') :: G' ~=~ (w', Gamma') :: G' & (w, Gamma))
  by PPermut_Hyb_simpl;
rewrite <- H4; eapply LF_to_Hyb_ctx_Ok ; eauto.
assert (G' & (w, Gamma) ~=~ (w, Gamma) :: G') by PPermut_Hyb_simpl;
rewrite H4; eauto.
intros;
assert ((w'0, (v', A) :: nil) :: (w', Gamma') :: G' ~=~
        (w'0, (v', A) :: nil) :: G' & (w', Gamma')) by PPermut_Hyb_simpl;
rewrite <- H6; eauto.
PPermut_Hyb_simpl.
eapply t_letdia_get_Hyb with (G:=G') (Gamma:=Gamma').
assert ((w, Gamma) :: (w', Gamma') :: G' ~=~ (w', Gamma') :: G' & (w, Gamma))
  by PPermut_Hyb_simpl.
assert (PPermut_LF (Gamma0 :: G0 & Gamma) (Gamma :: Gamma' :: G)) by
(transitivity (G0 & Gamma0 & Gamma); [ | rewrite H9 ];
 rew_app; PPermut_LF_simpl).
rewrite H5 in Ok.
rewrite <- H4; eapply LF_to_Hyb_ctx_Ok ; eauto.
assert (G' & (w, Gamma) ~=~ (w, Gamma) :: G') by PPermut_Hyb_simpl;
rewrite H4; eauto.
intros;
assert ((w'0, (v', A) :: nil) :: (w', Gamma') :: G' ~=~
        (w'0, (v', A) :: nil) :: G' & (w', Gamma')) by PPermut_Hyb_simpl;
rewrite <- H6; eauto.
PPermut_Hyb_simpl.
Qed.

Close Scope hybrid_is5_scope.
Close Scope permut_scope.
Close Scope is5_scope.
