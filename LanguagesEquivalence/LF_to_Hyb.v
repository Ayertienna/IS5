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

Lemma LF_to_Hyb_ctx_extend:
forall G G' w Gamma v A,
  LF_to_Hyb_ctx (Gamma::G) ((w, Gamma)::G') ->
  LF_to_Hyb_ctx (((v,A)::Gamma)::G) ((w, (v,A)::Gamma)::G').
Admitted.

Add Morphism LF_to_Hyb_ctx: LF_to_Hyb_ctx_LF.
Admitted.

Inductive LF_to_Hyb_term: var -> te_LF -> te_Hyb -> Prop :=
| hyp_LF_Hyb:
    forall v w, LF_to_Hyb_term w (hyp_LF v) (hyp_Hyb v)
| lam_LF_Hyb:
    forall L M N t w,
      (forall v0, v0 \notin L ->
                  LF_to_Hyb_term w
                    (open_LF M (hyp_LF (fte v0)))
                    (open_t_Hyb N (hyp_Hyb (fte v0)))) ->
      LF_to_Hyb_term w (lam_LF t M) (lam_Hyb t N)
| appl_LF_Hyb:
    forall M M' N N' w,
      LF_to_Hyb_term w M M' ->
      LF_to_Hyb_term w N N' ->
      LF_to_Hyb_term w (appl_LF M N) (appl_Hyb M' N')
| box_LF_Hyb:
    forall L M N w,
      (forall w0, w0 \notin L -> LF_to_Hyb_term w0 M
                                                (open_w_Hyb N (fwo w0))) ->
      LF_to_Hyb_term w (box_LF M) (box_Hyb N)
| unbox_LF_Hyb:
    forall M N w w',
      LF_to_Hyb_term w M N ->
      LF_to_Hyb_term w' (unbox_LF M) (unbox_fetch_Hyb (fwo w) N)
(*
| here_LF_Hyb:
    forall M N w w',
      LF_to_Hyb_term w M N ->
      LF_to_Hyb_term w' (here_LF M) (get_here_Hyb w N)
| letdia_LF_Hyb:
    forall M M' N N' w w',
      LF_to_Hyb_term w M M' ->
      LF_to_Hyb_term w' N N' ->
      LF_to_Hyb_term w' (letdia_LF M N) (letdia_get_Hyb w M' N')
*)
.

Lemma LF_to_Hyb_typing:
forall M0 G0 Gamma0 A,
  types_LF G0 Gamma0 M0 A ->
  forall M w G G0' G',
  PPermut_LF (Gamma0::G0) G0' ->
  PPermut_Hyb ((w, Gamma0)::G) G' ->
  LF_to_Hyb_ctx G0' G' ->
  LF_to_Hyb_term w M0 M ->
  G |= (w, Gamma0) |- M ::: A.
intros M0 G0 Gamma0 A H; induction H; subst;
intros M1 w G1 G1' G'' Perm1 Perm2 Ctx H2;
inversion H2; subst.
(* hyp *)
econstructor;
[apply LF_to_Hyb_ctx_Ok in Ctx | ]; auto;
[rewrite Perm2 | rewrite <- Perm1]; auto.
(* lam *)
apply t_lam_Hyb with (L:=L \u L0);
assert (LF_to_Hyb_ctx G1' G'') by auto;
apply LF_to_Hyb_ctx_Ok in Ctx; [rewrite Perm2 | rewrite <- Perm1 | |]; auto.
intros; auto; eapply H0 with (G0:=G1); eauto.
apply LF_to_Hyb_ctx_extend; rewrite Perm1; rewrite Perm2; auto.
rewrite <- Perm1; auto.
(* appl *)
apply t_appl_Hyb with (A:=A);
assert (LF_to_Hyb_ctx G1' G'') by auto;
apply LF_to_Hyb_ctx_Ok in Ctx; auto.
rewrite Perm2; auto. rewrite <- Perm1; auto.
eapply IHtypes_LF1; eauto.
rewrite <- Perm1; auto.
eapply IHtypes_LF2; eauto.
rewrite <- Perm1; auto.
(* box *)
apply t_box_Hyb with (L:=L).
apply LF_to_Hyb_ctx_Ok in Ctx; auto.
assert (G1 & (w, Gamma) ~=~ (w, Gamma) :: G1) by PPermut_Hyb_simpl;
rewrite H0; rewrite Perm2; auto.
assert (PPermut_LF (G & Gamma) (Gamma::G)) by PPermut_LF_simpl;
rewrite H0 in Ok; rewrite <- Perm1; auto.
intros; eapply IHtypes_LF; eauto.
skip. (* compatibility relation gives that from Ctx *)
(* unbox *)
destruct (eq_var_dec w0 w); subst.
(* = *)
constructor; [apply LF_to_Hyb_ctx_Ok in Ctx | eapply IHtypes_LF]; eauto.
rewrite Perm2; auto.
rewrite <- Perm1; auto.
(* <> *)
assert (exists G0, exists Gamma0, G1 ~=~ (w0, Gamma0)::G0).
skip.
destruct H0 as (G0, (Gamma0, H0)).
rewrite H0.
apply t_unbox_fetch_Hyb with (Gamma:=Gamma0) (G:=G0).
skip. (* permut *)
(* problem: we explicitely use Gamma in the assumptions, so it is required in
ihtypes :( *)
eapply IHtypes_LF.

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
