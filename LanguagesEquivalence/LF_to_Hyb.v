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

Lemma LF_to_Hyb_ctx_Ok_simpl1:
forall G X U,
  ok_LF (X ++ concat G) U -> ok_Hyb (LF_to_Hyb_ctx G (map fst_ X ++ U)) U.
induction G; simpl; intros; rew_concat in *; [constructor | ].
constructor. apply notin_Mem; subst; apply var_gen_spec.
apply IHG with (X:=X++a); rew_app.
apply ok_LF_fresh_used; auto.
apply notin_Mem; rew_app.


Lemma LF_to_Hyb_ctx_Ok:
forall G,
  ok_Bg_LF G -> ok_Bg_Hyb (LF_to_Hyb_ctx G nil).
unfold ok_Bg_LF in *; intros;
eapply LF_to_Hyb_ctx_Ok_simpl; eauto.
Qed.

Inductive LF_to_Hyb_term: vwo -> te_LF -> te_Hyb -> Prop :=
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
      (forall w0, w0 \notin L -> LF_to_Hyb_term w0 M (open_w_Hyb N w0)) ->
      LF_to_Hyb_term w (box_LF M) (box_Hyb N)
| unbox_LF_Hyb:
    forall M N w w',
      LF_to_Hyb_term w M N ->
      LF_to_Hyb_term w' (unbox_LF M) (unbox_fetch_Hyb w N)
| here_LF_Hyb:
    forall M N w w',
      LF_to_Hyb_term w M N ->
      LF_to_Hyb_term w' (here_LF M) (get_here_Hyb w N)
| letdia_LF_Hyb:
    forall M M' N N' w w',
      LF_to_Hyb_term w M M' ->
      LF_to_Hyb_term w' N N' ->
      LF_to_Hyb_term w' (letdia_LF M N) (letdia_get_Hyb w M' N')
.

Lemma LF_to_Hyb_typing:
forall G0 Gamma0 M0 A G w M,
  LF_to_Hyb_ctx (Gamma0::G0) \{} = (w, Gamma0) :: G ->
  LF_to_Hyb_term (fwo w) M0 M ->
  types_LF G0 Gamma0 M0 A ->
  G |= (w, Gamma0) |- M ::: A.
intros; induction H1; inversion H0; subst.
constructor.

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
