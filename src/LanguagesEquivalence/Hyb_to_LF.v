Add LoadPath "..".
Add LoadPath "../LabelFree".
Add LoadPath "../Hybrid".

Require Import Shared.
Require Import LabelFree.
Require Import Hybrid.
Require Import Arith.
Require Import ListLib.

Open Scope is5_scope.
Open Scope permut_scope.
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
forall Gamma U,
  (@ok_Hyb ty Gamma U) -> ok_LF Gamma U.
induction Gamma; intros; try destruct a; constructor;
inversion H; subst; auto.
Qed.

Lemma ok_Bg_Hyb_to_LF_ctx_ok_Bg_LF:
forall G Gamma G' Gamma',
  ok_Bg_Hyb (Gamma :: G) ->
  Hyb_to_LF_ctx G Gamma = (G', Gamma') ->
  ok_Bg_LF (Gamma' :: G').
unfold ok_Bg_Hyb; unfold ok_Bg_LF; unfold Hyb_to_LF_ctx; intros;
apply ok_Hyb_to_LF_ctx_ok_LF; auto.
destruct Gamma; simpl in *; inversion H0; subst; rew_concat;
destruct H; rewrite flat_map_concat; auto.
Qed.
Hint Resolve ok_Bg_Hyb_to_LF_ctx_ok_Bg_LF.

Lemma Hyb_to_LF_term_subst_t:
forall M N x,
  subst_t_LF (Hyb_to_LF_term M) x (Hyb_to_LF_term N) =
  Hyb_to_LF_term (subst_t_Hyb M x N).
induction N; intros; simpl in *;
try rewrite IHN || (rewrite IHN1; rewrite IHN2); auto;
repeat case_if; simpl; auto.
Qed.

Lemma Hyb_to_LF_term_subst_w:
forall N w1 w2,
  Hyb_to_LF_term (subst_w_Hyb w1 w2 N) =
  Hyb_to_LF_term N.
induction N; intros; simpl in *;
try erewrite IHN || (erewrite IHN1; erewrite IHN2); eauto.
Qed.

Lemma map_snd_PPermut_LF_Hyb:
forall G G',
  PPermut_Hyb G G' ->
  PPermut_LF (map snd_ G) (map snd_ G').
intros; induction H; rew_map; simpl; auto.
transitivity (map snd_ G'); auto.
Qed.

Lemma Hyb_to_LF_typing:
forall G_Hyb Gamma_Hyb G_LF Gamma_LF M_Hyb A,
  Hyb_to_LF_ctx G_Hyb Gamma_Hyb = (G_LF, Gamma_LF) ->
  G_Hyb |= Gamma_Hyb |- M_Hyb ::: A ->
  types_LF G_LF Gamma_LF (Hyb_to_LF_term M_Hyb) A.
unfold Hyb_to_LF_ctx; intros; inversion H; subst; clear H; induction H0; simpl.
constructor; simpl; eauto.
econstructor; unfold open_LF in *; intros; eauto;
replace (hyp_LF (fte v)) with (Hyb_to_LF_term (hyp_Hyb (fte v))) by
    (simpl; auto);
rewrite Hyb_to_LF_term_subst_t; eauto.
econstructor; eauto.
econstructor.
assert (PPermut_LF (map snd_ G & Gamma) (Gamma :: map snd_ G))
  by PPermut_LF_simpl;
rewrite H0;
assert ((w, Gamma) :: G ~=~ G & (w, Gamma)) by PPermut_Hyb_simpl;
rewrite <- H1 in Ok_Bg; eauto.
unfold open_w_Hyb in *;
assert (exists w, w \notin L) by apply Fresh; destruct H0 as (w0);
assert (types_LF (map snd_ (G & (w, Gamma))) (snd_ (w0, nil))
       (Hyb_to_LF_term M) A)
by (rewrite <- Hyb_to_LF_term_subst_w with (w1:=fwo w0) (w2:=bwo 0);
    apply H; auto);
rew_map in *; simpl in *; auto.
constructor; eauto.
apply t_unbox_fetch_LF with (G:= map snd_ G) (Gamma:=Gamma).
apply ok_Bg_LF_PPermut with (G := Gamma' :: (map snd_ (G & (w, Gamma))));
[ | rew_map; simpl; rewrite map_snd_PPermut_LF_Hyb; auto];
apply ok_Bg_Hyb_to_LF_ctx_ok_Bg_LF with (G:=G & (w, Gamma))
                                          (Gamma:=(w', Gamma'));
simpl in *; auto; unfold Hyb_to_LF_ctx; simpl; auto.
rew_map in *; simpl in *; auto.
apply map_snd_PPermut_LF_Hyb in H; rewrite <- H; rew_map; simpl; auto.
econstructor; eauto.
apply t_get_here_LF with (G:= map snd_ G) (Gamma:=Gamma).
apply ok_Bg_LF_PPermut with (G := Gamma' :: (map snd_ (G & (w, Gamma))));
[ | rew_map; simpl; rewrite map_snd_PPermut_LF_Hyb; auto];
apply ok_Bg_Hyb_to_LF_ctx_ok_Bg_LF with (G:=G & (w, Gamma))
                                          (Gamma:=(w', Gamma'));
simpl in *; auto; unfold Hyb_to_LF_ctx; simpl; auto.
rew_map in *; simpl in *; auto.
apply map_snd_PPermut_LF_Hyb in H; rewrite <- H; rew_map; simpl; auto.
apply t_letdia_LF with (L:=L_t) (A:=A); eauto; intros; unfold open_LF in *.
unfold open_w_Hyb in *; unfold open_t_Hyb in *.
assert (exists w, w \notin L_w) by apply Fresh; destruct H3 as (w0).
rewrite <- Hyb_to_LF_term_subst_w with (w1:=fwo w0) (w2:=bwo 0).
replace (hyp_LF (fte v)) with (Hyb_to_LF_term (hyp_Hyb (fte v))) by
    (simpl; auto);
rewrite Hyb_to_LF_term_subst_t; eauto;
replace Gamma with (snd_ (w, Gamma)) by (simpl; auto);
rewrite <- H2; apply H; auto.
destruct Ctx' as (w', Gamma');
apply t_letdia_get_LF with (L:=L_t) (A:=A) (G:=map snd_ G) (Gamma:=Gamma).
apply ok_Bg_LF_PPermut with (G := Gamma' :: (map snd_ (G & (w, Gamma))));
[ | rew_map; simpl; rewrite map_snd_PPermut_LF_Hyb; auto];
apply ok_Bg_Hyb_to_LF_ctx_ok_Bg_LF with (G:=G & (w, Gamma))
                                          (Gamma:=(w', Gamma'));
simpl in *; auto; unfold Hyb_to_LF_ctx; simpl; auto.
rew_map in *; simpl in *; auto.
intros.
unfold open_LF in *; unfold open_w_Hyb in *; unfold open_t_Hyb in *.
assert (exists w, w \notin L_w) by apply Fresh; destruct H3 as (w0).
rewrite <- Hyb_to_LF_term_subst_w with (w1:=fwo w0) (w2:=bwo 0).
replace (hyp_LF (fte v)) with (Hyb_to_LF_term (hyp_Hyb (fte v))) by
    (simpl; auto).
rewrite Hyb_to_LF_term_subst_t; eauto.
replace Gamma with (snd_ (w, Gamma)) by (simpl; auto).
assert (types_LF
         (map snd_ ((w0, (v, A) :: nil) :: G & (w, Gamma)))
       (snd_ (w', Gamma'))
     (Hyb_to_LF_term [hyp_Hyb (fte v) // bte 0]({{fwo w0 // bwo 0}}N)) B).
apply H; eauto.
rew_map in *; simpl in *; auto.
apply map_snd_PPermut_LF_Hyb in H1; rewrite <- H1; rew_map; simpl; auto.
Qed.

Lemma Hyb_to_LF_lc_t:
forall M n,
  lc_t_n_Hyb n M -> lc_t_n_LF n (Hyb_to_LF_term M).
induction M; intros; simpl; inversion H; subst; constructor; auto.
Qed.
Hint Resolve Hyb_to_LF_lc_t.

Lemma Hyb_to_LF_value:
forall M, value_Hyb M -> value_LF (Hyb_to_LF_term M).
induction M; intros; inversion H; constructor; auto.
Qed.

Lemma Hyb_to_LF_step:
forall M N w,
  step_Hyb (M, w) (N, w) ->
  step_LF (Hyb_to_LF_term M) (Hyb_to_LF_term N).
induction M; intros; inversion H; subst;
unfold open_t_Hyb in *; unfold open_w_Hyb in *;
simpl; try rewrite <- Hyb_to_LF_term_subst_t;
try rewrite Hyb_to_LF_term_subst_w;
constructor;  unfold lc_t_Hyb in *; unfold lc_t_LF in *;
unfold lc_w_Hyb in *; eauto;
apply Hyb_to_LF_value; auto.
Qed.

Close Scope hybrid_is5_scope.
Close Scope permut_scope.
Close Scope is5_scope.
