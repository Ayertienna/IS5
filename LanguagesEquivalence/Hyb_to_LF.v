Add LoadPath "..".
Add LoadPath "../LabelFree/SingleUnbox".
Add LoadPath "../Hybrid".

Require Import Shared.
Require Import LabelFree.
Require Import Hybrid.
Require Import Arith.

Open Scope is5_scope.
Open Scope permut_scope.
(* FIXME: There is no labelfree is5 scope *)
Open Scope hybrid_is5_scope.

(* Context conversion *)

Definition Hyb_to_LF_ctx (G: bg_Hyb) (Ctx: ctx_Hyb) : (bg_LF * ctx_LF) :=
  (map snd_ G, snd_ Ctx).

(* Term conversion *)

Fixpoint Hyb_to_LF_term (M: te_Hyb) : te_LF :=
match M with
| hyp_Hyb v => hyp_LF v
| lam_Hyb A M => lam_LF A (Hyb_to_LF_term M)
| appl_Hyb M N => appl_LF (Hyb_to_LF_term M) (Hyb_to_LF_term N)
| box_Hyb M => box_LF (Hyb_to_LF_term M)
| unbox_fetch_Hyb w M => unbox_LF (Hyb_to_LF_term M)
| get_here_Hyb w M => here_LF (Hyb_to_LF_term M)
| letdia_get_Hyb w M N => letdia_LF (Hyb_to_LF_term M) (Hyb_to_LF_term N)
end.

Lemma ok_Hyb_to_LF_ctx_ok_LF:
forall G Gamma G' Gamma',
  ok_Bg_Hyb (Gamma :: G) ->
  Hyb_to_LF_ctx G Gamma = (G', Gamma') ->
  ok_Bg_LF (Gamma' :: G').
Admitted.
Hint Resolve ok_Hyb_to_LF_ctx_ok_LF.

Lemma ok_Hyb_to_LF_subst_t:
forall M N x,
  subst_t_LF (Hyb_to_LF_term M) x (Hyb_to_LF_term N) =
  Hyb_to_LF_term (subst_t_Hyb M x N).
induction N; intros; simpl in *;
try rewrite IHN || (rewrite IHN1; rewrite IHN2); auto;
repeat case_if; simpl; auto.
Qed.

Lemma Hyb_to_LF_typing:
forall G_Hyb Gamma_Hyb G_LF Gamma_LF M_Hyb A,
  Hyb_to_LF_ctx G_Hyb Gamma_Hyb = (G_LF, Gamma_LF) ->
  G_Hyb |= Gamma_Hyb |- M_Hyb ::: A ->
  types_LF G_LF Gamma_LF (Hyb_to_LF_term M_Hyb) A.
unfold Hyb_to_LF_ctx; intros; inversion H; subst; clear H; induction H0; simpl.
constructor; simpl; eauto.
apply t_lam_LF with (L:=L); intros; eauto; unfold open_LF in *;
replace (hyp_LF (fte v)) with (Hyb_to_LF_term (hyp_Hyb (fte v))) by
    (simpl; auto);
rewrite ok_Hyb_to_LF_subst_t;
apply H; auto.
econstructor; eauto.
Admitted.

Close Scope hybrid_is5_scope.
Close Scope permut_scope.
Close Scope is5_scope.
