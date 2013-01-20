Add LoadPath "../..".
Require Export LF_PPermutLib.

Fixpoint emptyEquiv_LF (G: list (list (var * ty))) :=
match G with
| nil => nil
| a::G' => (@nil (var * ty)) :: emptyEquiv_LF G'
end.

Add Morphism emptyEquiv_LF : Permut_emptyEquiv.
intros.
induction H; simpl in *; auto.
transitivity (emptyEquiv_LF G'); auto.
Qed.

Lemma emptyEquiv_LF_Mem_nil:
forall G C,
  Mem C (emptyEquiv_LF G) -> C = nil.
induction G; simpl; intros.
rewrite Mem_nil_eq in H; contradiction.
simpl in *; rewrite Mem_cons_eq in H; destruct H; auto.
Qed.

Lemma emptyEquiv_LF_permut_empty:
forall G G',
  G ~=~ emptyEquiv_LF G' ->
  (forall C, Mem C G -> C = nil).
intros.
apply PPermut_LF_Mem with (G':=emptyEquiv_LF G') in H0; auto;
destruct H0 as (C0, (H0, H1)).
assert (C0 = nil).
  apply emptyEquiv_LF_Mem_nil with (G:=G'); auto.
subst. apply permut_nil_eq in H0; auto.
Qed.

Lemma double_emptyEquiv_LF:
forall G,
 emptyEquiv_LF G = emptyEquiv_LF (emptyEquiv_LF G).
induction G; simpl; auto; destruct a;
simpl; rewrite <- IHG; auto.
Qed.

Lemma emptyEquiv_LF_rewrite:
forall G H,
  emptyEquiv_LF (G++H) = emptyEquiv_LF G ++ emptyEquiv_LF H.
induction G; rew_app; intros; auto.
rew_app; simpl; rew_app; rewrite IHG; auto.
Qed.

Lemma emptyEquiv_LF_rewrite_last:
forall G C,
  emptyEquiv_LF (G & C) = emptyEquiv_LF G ++ emptyEquiv_LF (C::nil).
intros; apply emptyEquiv_LF_rewrite.
Qed.

Lemma emptyEquiv_LF_PPermut:
forall G Gamma G',
  G & Gamma ~=~ emptyEquiv_LF G' ->
  Gamma = nil.
intros.
assert (Mem Gamma (G & Gamma)).
rewrite Mem_app_or_eq; right; apply Mem_here.
apply emptyEquiv_LF_permut_empty with (G:=G & Gamma) (G':=G'); auto.
Qed.

Lemma emptyEquiv_LF_PPermut_eq:
forall G G',
  G ~=~ emptyEquiv_LF G' -> emptyEquiv_LF G = G.
induction G; intros; simpl in *; auto; rew_app in *.
assert (a = nil) by
  (eapply emptyEquiv_LF_permut_empty; eauto; eapply Mem_here);
subst; assert (emptyEquiv_LF G = G).
  assert (nil :: G ~=~ emptyEquiv_LF G') by auto;
  apply PPermut_LF_split_head in H0; destruct H0 as (l', (hd, (tl, (Ha, Hb))));
  subst; apply permut_nil_eq in Ha; subst.
  rewrite Hb in H.
  assert (G ~=~ hd ++ tl) by
    ( apply PPermut_LF_last_rev_simpl with (a:=nil);
      transitivity (nil::G); [ | rewrite H]; PPermut_LF_simpl).
  apply IHG with (G':=hd++tl).
  rewrite H0. apply PPermut_LF_last_rev_simpl with (a:=(nil));
  rew_app.
  assert (hd &  nil ++ tl ~=~ hd ++ tl &  nil) by PPermut_LF_simpl.
  rewrite <- H1.
  assert (emptyEquiv_LF (hd ++ tl)&(nil) ~=~ emptyEquiv_LF (hd & (nil) ++ tl)).
    (repeat rewrite emptyEquiv_LF_rewrite; PPermut_LF_simpl).
  rewrite H2.
  rewrite <- Hb.
  rewrite <- double_emptyEquiv_LF; auto.
rewrite H0; auto.
Qed.

Lemma PPermut_emptyEquiv_LF:
forall G G',
  G ~=~ G' -> emptyEquiv_LF G ~=~ emptyEquiv_LF G'.
intros; rewrite H; auto.
Qed.

Lemma emptyEquiv_LF_last_change:
forall G G' C C',
  G  ~=~ G'& C ->
  emptyEquiv_LF G ~=~ emptyEquiv_LF (G' & C').
intros; rewrite H; repeat rewrite emptyEquiv_LF_rewrite;
simpl; auto.
Qed.

Lemma emptyEquiv_LF_PPermut_equal:
forall G' G,
  G ~=~ emptyEquiv_LF G' -> G = emptyEquiv_LF G'.
induction G'; intros; simpl in *.
symmetry in H;
apply PPermut_LF_nil_impl in H; subst; auto.
destruct G.
apply PPermut_LF_nil_impl in H; inversion H.
assert (c = nil).
  apply emptyEquiv_LF_PPermut with (G:=G) (G':=nil::G');
  simpl; rewrite <- H; PPermut_LF_simpl.
subst.
assert (nil :: G ~=~ nil :: emptyEquiv_LF G') by auto.
apply PPermut_LF_split_head in H0.
destruct H0 as (l, (hd, (tl, (H0, H1)))).
apply permut_nil_eq in H0; subst.
assert (G = emptyEquiv_LF G').
apply IHG'. apply PPermut_LF_last_rev_simpl with (a:=nil).
transitivity (nil :: G). PPermut_LF_simpl.
rewrite H; PPermut_LF_simpl.
subst; auto.
Qed.
