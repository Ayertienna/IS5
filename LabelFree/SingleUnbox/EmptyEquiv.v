Add LoadPath "../..".
Require Export PPermutLib.

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