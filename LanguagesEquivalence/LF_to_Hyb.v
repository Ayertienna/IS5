Add LoadPath "..".
Add LoadPath "../LabelFree/SingleUnbox".
Add LoadPath "../Hybrid".

Require Import Shared.
Require Import LabelFree.
Require Import Hybrid.
Require Import Arith.
Require Import ListLib.

Open Scope is5_scope.
Open Scope permut_scope.
(* FIXME: There is no labelfree is5 scope *)
Open Scope hybrid_is5_scope.

Fixpoint LF_to_Hyb_ctx (G: bg_LF) (U: list var) : bg_Hyb :=
match G with
| nil => nil
| Gamma::G' =>
  let w := var_gen (from_list U) in
  (w, Gamma) :: (LF_to_Hyb_ctx G' (w::U))
end.

(* Alternative definition of context rewrite *)
Definition compatible_ctx (G: bg_LF) (G':bg_Hyb) :=
  map snd_ G' *=* G /\
  ok_Hyb G' nil.

Lemma LF_to_Hyb_ctx_Ok_simpl_worlds:
forall G U,
  ok_LF (concat G) U -> ok_Hyb (LF_to_Hyb_ctx G U) U.
induction G; simpl; intros; rew_concat in *; [constructor | ].
constructor.
apply notin_Mem; subst; apply var_gen_spec.
Admitted.

Lemma LF_to_Hyb_ctx_Ok_simpl_terms:
forall G U,
  ok_LF (concat G) U -> ok_Hyb (flat_map snd_ (LF_to_Hyb_ctx G U)) U.
Admitted.

Lemma LF_to_Hyb_ctx_Ok:
forall G,
  ok_Bg_LF G -> ok_Bg_Hyb (LF_to_Hyb_ctx G nil).
unfold ok_Bg_LF in *; intros; split.
eapply LF_to_Hyb_ctx_Ok_simpl_worlds; eauto.
eapply LF_to_Hyb_ctx_Ok_simpl_terms; eauto.
Qed.

Lemma compatible_ctx_Ok:
forall G G',
  ok_Bg_LF G -> compatible_ctx G G' -> ok_Bg_Hyb G'.
unfold compatible_ctx; intros; destruct H0; split; auto.
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
  forall M w G,
  compatible_ctx (Gamma0::G0) ((w, Gamma0) :: G) ->
  LF_to_Hyb_term w M0 M ->
  G |= (w, Gamma0) |- M ::: A.
intros M0 G0 Gamma0 A H. induction H; subst;
intros M1 w G1 Ctx H2;
inversion H2; subst.
(* hyp *)
econstructor.
apply compatible_ctx_Ok in Ctx; auto. auto.
(* lam *)
apply t_lam_Hyb with (L:=L \u L0).
apply compatible_ctx_Ok in Ctx; auto. intros; auto.
apply H0 with (G0:=G1); eauto.
skip. (* compatibility relation gives that from Ctx *)
(* appl *)
apply t_appl_Hyb with (A:=A).
apply compatible_ctx_Ok in Ctx; auto. auto. auto.
(* box *)
apply t_box_Hyb with (L:=L).
apply compatible_ctx_Ok in Ctx; auto.
assert (G1 & (w, Gamma) ~=~ (w, Gamma) :: G1) by PPermut_Hyb_simpl.
rewrite H0; auto.
assert (PPermut_LF (G & Gamma) (Gamma::G)) by PPermut_LF_simpl;
rewrite H0 in Ok; auto.
intros; eapply IHtypes_LF; eauto.
skip. (* compatibility relation gives that from Ctx *)
(* unbox *)
destruct (eq_var_dec w0 w); subst.
constructor; [apply compatible_ctx_Ok in Ctx | eapply IHtypes_LF]; eauto.
assert (exists G0, exists Gamma0, G1 ~=~ (w0, Gamma0)::G0).
skip.
destruct H0 as (G0, (Gamma0, H0)).
rewrite H0.
apply t_unbox_fetch_Hyb with (Gamma:=Gamma0) (G:=G0).
skip. (* permut *) eapply IHtypes_LF.

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
