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
  LF_to_Hyb_ctx (Gamma::G) ((w, Gamma)::G') ->
  LF_to_Hyb_ctx (((v,A)::Gamma)::G) ((w, (v,A)::Gamma)::G').
Admitted.

Lemma LF_to_Hyb_ctx_extend_w:
forall G G' w,
  LF_to_Hyb_ctx G G' ->
  LF_to_Hyb_ctx (nil::G) ((w, nil)::G').
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

Lemma LF_to_Hyb_ctx_Exists:
forall Gamma G,
  ok_Bg_LF (Gamma::G) ->
  exists w' G', LF_to_Hyb_ctx (Gamma::G) ((w', Gamma)::G').
Admitted.

Inductive LF_to_Hyb_rel: vwo -> te_LF -> te_Hyb ->
                         bg_LF -> ctx_LF -> Prop :=

| hyp_LF_Hyb:
    forall G Gamma w v A,
      types_LF G Gamma (hyp_LF v) A ->
      LF_to_Hyb_rel w (hyp_LF v) (hyp_Hyb v) G Gamma

| lam_LF_Hyb:
    forall L G Gamma w M A B N,
      types_LF G Gamma (lam_LF A M) (A ---> B) ->
      (forall v0, v0 \notin L ->
                  LF_to_Hyb_rel w
                    (open_LF M (hyp_LF (fte v0)))
                    (N ^t^ (hyp_Hyb (fte v0))) G ((v0,A)::Gamma)) ->
      LF_to_Hyb_rel w (lam_LF A M) (lam_Hyb A N) G Gamma

| appl_LF_Hyb:
    forall G Gamma w B M1 M2 N1 N2,
      types_LF G Gamma (appl_LF M1 N1) B ->
      LF_to_Hyb_rel w M1 M2 G Gamma ->
      LF_to_Hyb_rel w N1 N2 G Gamma ->
      LF_to_Hyb_rel w (appl_LF M1 N1) (appl_Hyb M2 N2) G Gamma

| box_LF_Hyb:
    forall L G Gamma w A M N,
      types_LF G Gamma (box_LF M) ([*]A) ->
      (forall w0, w0 \notin L ->
        LF_to_Hyb_rel (fwo w0) M (N ^w^ (fwo w0)) (G & Gamma) nil) ->
      LF_to_Hyb_rel w (box_LF M) (box_Hyb N) G Gamma

| unbox_LF_Hyb:
    forall G Gamma w A M N,
      types_LF G Gamma M ([*]A) ->
      LF_to_Hyb_rel w M N G Gamma ->
      LF_to_Hyb_rel w (unbox_LF M) (unbox_fetch_Hyb w N) G Gamma

| unbox_fetch_LF_Hyb:
    forall G Gamma Gamma' w w' A M N,
      w <> w' ->
      types_LF (Gamma::G) Gamma' M ([*]A) ->
      LF_to_Hyb_rel w' M N (Gamma::G) Gamma' ->
      LF_to_Hyb_rel w (unbox_LF M) (unbox_fetch_Hyb w' N) (Gamma'::G) Gamma
(*
| here_LF_Hyb:
    forall G Gamma w A M N,
      types_LF G Gamma (here_LF M) (<*>A) ->
      LF_to_Hyb_rel w M N ->
      LF_to_Hyb_rel w (here_LF M) (get_here_Hyb w N)

| get_here_LF_Hyb:
    forall G Gamma Gamma' w w' A M N,
      w <> w' ->
      types_LF (Gamma'::G) Gamma (here_LF M) (<*>A) ->
      LF_to_Hyb_rel w' M N ->
      LF_to_Hyb_rel w (here_LF M) (get_here_Hyb w' N)

| letdia_LF_Hyb:
    forall G Gamma w B M1 M2 N1 N2,
      types_LF G Gamma (letdia_LF M1 N1) B ->
      LF_to_Hyb_rel w M1 M2 ->
      LF_to_Hyb_rel w N1 N2 ->
      LF_to_Hyb_rel w (letdia_LF M1 N1) (letdia_get_Hyb w M2 N2)

| letdia_get_LF_Hyb:
    forall G Gamma Gamma' w w' B M1 M2 N1 N2,
      w <> w' ->
      types_LF (Gamma'::G) Gamma (letdia_LF M1 N1) B ->
      LF_to_Hyb_rel w' M1 M2 ->
      LF_to_Hyb_rel w N1 N2 ->
      LF_to_Hyb_rel w (letdia_LF M1 N1) (letdia_get_Hyb w' M2 N2)
*)
.

Lemma LF_to_Hyb_types:
forall M G Gamma A G' w M',
  types_LF G Gamma M A ->
  LF_to_Hyb_rel (fwo w) M M' G Gamma->
  LF_to_Hyb_ctx (Gamma::G) ((w, Gamma)::G') ->
  G' |= (w, Gamma) |- M' ::: A.
intros; generalize dependent G'; generalize dependent M';
generalize dependent w; induction H; intros.
(* hyp *)
inversion H0; subst;
constructor; [eapply LF_to_Hyb_ctx_Ok | ]; eauto.
(* lam *)
inversion H1; subst;
apply t_lam_Hyb with (L:=L \u L0);
[eapply LF_to_Hyb_ctx_Ok |
 intros; unfold open_t_Hyb in *; unfold open_LF in *]; eauto;
eapply H0; eauto;
apply LF_to_Hyb_ctx_extend_t; eauto.
(* appl *)
inversion H1; subst; econstructor;
[eapply LF_to_Hyb_ctx_Ok | |]; eauto.
(* box *)
inversion H0; subst;
assert (PPermut_Hyb (G' & (w, Gamma)) ((w, Gamma) :: G'))
  as Eq1 by PPermut_Hyb_simpl;
assert (PPermut_LF (G & Gamma) (Gamma :: G))
  as Eq2 by PPermut_LF_simpl;
econstructor; [rewrite Eq1; eapply LF_to_Hyb_ctx_Ok | ]; eauto;
[rewrite Eq2; auto | intros; unfold open_w_Hyb in *];
eapply IHtypes_LF; eauto;
eapply LF_to_Hyb_ctx_extend_w; rewrite Eq1; rewrite Eq2; eauto.
(* unbox *)
inversion H0; subst.
constructor; [eapply LF_to_Hyb_ctx_Ok | ]; eauto.
clear H5 H4 A0.

inversion H0; subst; [elim H3; auto | ].
destruct w'. skip.
assert (exists G0, G' ~=~ (v, Gamma') :: G0) by skip.
destruct H2 as (G'', H2); rewrite H2.
apply t_unbox_fetch_Hyb with (G:=G'') (Gamma:=Gamma').
skip.
eapply IHtypes_LF.
(* unbox_fetch *)
(* here *)
(* letdia *)

Admitted.

Lemma LF_to_Hyb_term:
forall G Gamma M A,
  types_LF G Gamma M A ->
  exists G' w M',
    LF_to_Hyb_typing G Gamma M G' (w, Gamma) M' A.
intros; induction H.
assert (ok_Bg_LF (Gamma::G)) by auto;
apply LF_to_Hyb_ctx_Exists in Ok; destruct Ok as (w', (G', Ok)).
exists G'; exists w'; exists (hyp_Hyb (fte v)).
constructor; destruct Ok; rew_map in *; simpl in *.
skip. constructor; auto.
Admitted.














Lemma LF_to_Hyb_typing:
forall M_LF G_LF Gamma_LF A M_Hyb w G_Hyb,
  types_LF G_LF Gamma_LF M_LF A ->
  LF_to_Hyb_term w True M_LF M_Hyb ->
  LF_to_Hyb_ctx (Gamma_LF :: G_LF) ((w, Gamma_LF)::G_Hyb) ->
  G_Hyb |= (w, Gamma_LF) |- M_Hyb ::: A.
intros; generalize dependent w; generalize dependent G_Hyb;
generalize dependent M_Hyb; induction H;
intros M_Hyb G_Hyb w T C; intros; inversion T; subst.
constructor; auto; eapply LF_to_Hyb_ctx_Ok; eauto.


Lemma LF_to_Hyb_steps:
forall M M' N,
  steps_LF M M' ->
  LF_to_Hyb_term M N ->
  exists N',
    steps_Hyb N N' /\ LF_to_Hyb_term M' N'.

Lemma LF_to_Hyb_left_total:
forall M, exists N,
  LF_to_Hyb_term M N.


Close Scope hybrid_is5_scope.
Close Scope permut_scope.
Close Scope is5_scope.
