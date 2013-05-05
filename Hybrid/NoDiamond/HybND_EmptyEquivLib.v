Add LoadPath "../..".
Require Import HybND_Shared.
Require Import LibList.
Require Import HybND_OkLib.
Require Import HybND_PPermutLib.
Require Import Relations.

Open Scope permut_scope.

(* emptyEquiv_Hyb = map (fun x => (x, nil)) (map fst G) *)
Fixpoint emptyEquiv_Hyb (G: bg_Hyb) : bg_Hyb :=
match G with
| nil => nil
| (w, a)::G => (w, nil) :: emptyEquiv_Hyb G
end.

Add Morphism emptyEquiv_Hyb : Permut_emptyEquiv_Hyb.
intros.
induction H; simpl in *; auto.
transitivity (emptyEquiv_Hyb G'); auto.
Qed.

Lemma emptyEquiv_Hyb_last_change:
forall G G' w C C',
  G  ~=~ G'& (w, C) ->
  emptyEquiv_Hyb G ~=~ emptyEquiv_Hyb (G' & (w, C')).
intros.
assert (G ~=~ (w, C) :: G') by (transitivity (G' & (w,C)); PPermut_Hyb_simpl).
assert (G' & (w, C') ~=~ (w, C') :: G') by PPermut_Hyb_simpl.
rewrite H0; rewrite H1; simpl; auto.
Qed.

Lemma emptyEquiv_Hyb_rewrite:
forall G H,
  emptyEquiv_Hyb (G++H) = emptyEquiv_Hyb G ++ emptyEquiv_Hyb H.
induction G; rew_app; intros; auto.
rew_app; destruct a; simpl; rew_app; rewrite IHG; auto.
Qed.

Lemma emptyEquiv_Hyb_rewrite_last:
forall G C,
  emptyEquiv_Hyb (G & C) = emptyEquiv_Hyb G ++ emptyEquiv_Hyb (C::nil).
intros; apply emptyEquiv_Hyb_rewrite.
Qed.

Lemma emptyEquiv_Hyb_Mem_nil:
forall G w C,
  Mem (w, C) (emptyEquiv_Hyb G) -> C = nil.
induction G; simpl; intros.
rewrite Mem_nil_eq in H; contradiction.
destruct a; simpl in *; rewrite Mem_cons_eq in H; destruct H.
inversion H; subst; auto.
apply IHG with (w:=w); auto.
Qed.

Lemma emptyEquiv_Hyb_permut_empty:
forall G G' w,
  G ~=~ emptyEquiv_Hyb G' ->
  forall C, Mem (w, C) G -> C = nil.
intros;
assert (G ~=~ emptyEquiv_Hyb G') by auto;
apply PPermut_Hyb_Mem with (w:=w) (X:=C) in H; auto;
destruct H as (C', (Ha, Hb)).
apply emptyEquiv_Hyb_Mem_nil in Hb; subst.
apply permut_nil_eq in Ha; auto.
Qed.

Lemma double_emptyEquiv_Hyb:
forall G,
 emptyEquiv_Hyb G = emptyEquiv_Hyb( emptyEquiv_Hyb G).
induction G; simpl; auto; destruct a;
simpl; rewrite <- IHG; auto.
Qed.

Lemma emptyEquiv_Hyb_permut_split_last:
forall G C H,
  G & C ~=~ emptyEquiv_Hyb H ->
  emptyEquiv_Hyb G = G.
induction G; intros; simpl in *; auto; destruct a; rew_app in *;
assert (l = nil) by
  (eapply emptyEquiv_Hyb_permut_empty; eauto; eapply Mem_here);
subst; assert (emptyEquiv_Hyb G = G).
  assert ((v, nil) :: G & C ~=~ emptyEquiv_Hyb H) by auto;
  apply PPermut_Hyb_split_head in H0; destruct H0 as (l', (hd, (tl, (Ha, Hb))));
  subst; apply permut_nil_eq in Ha; subst.
  rewrite Hb in H1.
  assert (G & C ~=~ hd ++ tl) by
    ( apply PPermut_Hyb_last_rev_simpl with (a:=(v,nil));
      transitivity ((v,nil)::G & C); [ | rewrite H1]; PPermut_Hyb_simpl).
  apply IHG with (C:=C) (H:=hd++tl).
  rewrite H0. apply PPermut_Hyb_last_rev_simpl with (a:=(v,nil));
  rew_app.
  assert (hd & (v, nil) ++ tl ~=~ hd ++ tl & (v, nil)) by PPermut_Hyb_simpl;
  rewrite <- H2.
  assert (emptyEquiv_Hyb (hd ++ tl)&(v, nil) ~=~
    emptyEquiv_Hyb (hd & (v, nil) ++ tl))
    by (repeat rewrite emptyEquiv_Hyb_rewrite; PPermut_Hyb_simpl).
  rewrite H3.
  rewrite <- Hb.
  rewrite <- double_emptyEquiv_Hyb; auto.
rewrite H1; auto.
Qed.

Lemma emptyEquiv_Hyb_ok_list:
forall G U,
  ok_Hyb G U ->
  ok_Hyb (emptyEquiv_Hyb G) U.
induction G; simpl; intros; auto; destruct a.
inversion H; subst; constructor; auto.
Qed.

Lemma emptyEquiv_Hyb_ok_var:
forall G U,
  ok_Hyb (flat_map snd G) U ->
  ok_Hyb (flat_map snd (emptyEquiv_Hyb G)) U.
induction G; simpl; intros; auto; destruct a;
simpl in *; apply IHG.
eapply ok_Hyb_split with (G1:=l); eauto.
Qed.

Lemma emptyEquiv_Hyb_ok_Bg_Hyb:
forall G,
  ok_Bg_Hyb G ->
  ok_Bg_Hyb (emptyEquiv_Hyb G).
induction G; simpl; intros; auto; destruct a.
unfold ok_Bg_Hyb in *;
destruct H; split; simpl in *.
inversion H; subst;
constructor; auto;
apply emptyEquiv_Hyb_ok_list; auto.
apply emptyEquiv_Hyb_ok_var.
apply ok_Hyb_split in H0; destruct H0; auto.
Qed.

Lemma emptyEquiv_Hyb_ok_list_part:
forall G G' U,
  ok_Hyb (G ++ G')  U ->
  ok_Hyb ((emptyEquiv_Hyb G) ++ G') U.
induction G; simpl; intros; auto; destruct a.
inversion H; rew_app in *; subst; constructor; auto.
Qed.

Lemma emptyEquiv_Hyb_ok_var_part:
forall G G' U,
  ok_Hyb (flat_map snd (G++G')) U ->
  ok_Hyb (flat_map snd ((emptyEquiv_Hyb G)++G')) U.
induction G; simpl; intros; auto; destruct a;
simpl in *; apply IHG.
eapply ok_Hyb_split with (G1:=l); rew_app in *; eauto.
Qed.

Lemma emptyEquiv_Hyb_ok_Bg_Hyb_part:
forall G G',
  ok_Bg_Hyb (G ++ G') ->
  ok_Bg_Hyb ((emptyEquiv_Hyb G) ++ G').
induction G; simpl; intros; auto; destruct a.
unfold ok_Bg_Hyb in *; rew_app in *;
destruct H; split; simpl in *; rew_app.
inversion H; subst;
constructor; auto;
apply emptyEquiv_Hyb_ok_list_part; auto.
apply emptyEquiv_Hyb_ok_var_part.
apply ok_Hyb_split in H0; destruct H0; auto.
Qed.