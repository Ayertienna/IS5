Require Import Shared.
Require Import LibList.
Require Import OkLib.
Require Import PPermutLib.
Require Import Relations.

Open Scope permut_scope.

(* emptyEquiv = map (fun x => (x, nil)) (map fst G) *)
Fixpoint emptyEquiv (G: Background_LF) : Background_LF :=
match G with
| nil => nil
| (w, a)::G => (w, nil) :: emptyEquiv G
end.

Add Morphism emptyEquiv : Permut_emptyEquiv.
intros.
induction H; simpl in *; auto.
transitivity (emptyEquiv G'); auto.
Qed.

Lemma emptyEquiv_last_change:
forall G G' w C C',
  G  ~=~ G'& (w, C) ->
  emptyEquiv G ~=~ emptyEquiv (G' & (w, C')).
intros.
assert (G ~=~ (w, C) :: G') by (transitivity (G' & (w,C)); PPermut_simpl).
assert (G' & (w, C') ~=~ (w, C') :: G') by PPermut_simpl.
rewrite H0; rewrite H1; simpl; auto.
Qed.

Lemma emptyEquiv_rewrite:
forall G H,
  emptyEquiv (G++H) = emptyEquiv G ++ emptyEquiv H.
induction G; rew_app; intros; auto.
rew_app; destruct a; simpl; rew_app; rewrite IHG; auto.
Qed.

Lemma emptyEquiv_rewrite_last:
forall G C,
  emptyEquiv (G & C) = emptyEquiv G ++ emptyEquiv (C::nil).
intros; apply emptyEquiv_rewrite.
Qed.

Lemma emptyEquiv_Mem_nil:
forall G w C,
  Mem (w, C) (emptyEquiv G) -> C = nil.
induction G; simpl; intros.
rewrite Mem_nil_eq in H; contradiction.
destruct a; simpl in *; rewrite Mem_cons_eq in H; destruct H.
inversion H; subst; auto.
apply IHG with (w:=w); auto.
Qed.

Lemma emptyEquiv_permut_empty:
forall G G' w,
  G ~=~ emptyEquiv G' ->
  forall C, Mem (w, C) G -> C = nil.
Admitted. (* !!! *)

Lemma double_emptyEquiv:
forall G,
 emptyEquiv G = emptyEquiv( emptyEquiv G).
induction G; simpl; auto; destruct a;
simpl; rewrite <- IHG; auto.
Qed.

Lemma emptyEquiv_permut_split_last:
forall G C H,
  G & C ~=~ emptyEquiv H ->
  emptyEquiv G = G.
Admitted.

Lemma emptyEquiv_ok_list:
forall G U,
  ok_LF G U ->
  ok_LF (emptyEquiv G) U.
induction G; simpl; intros; auto; destruct a.
inversion H; subst; constructor; auto.
Qed.

Lemma emptyEquiv_ok_var:
forall G U,
  ok_LF (flat_map snd G) U ->
  ok_LF (flat_map snd (emptyEquiv G)) U.
induction G; simpl; intros; auto; destruct a;
simpl in *; apply IHG.
eapply ok_LF_split with (G1:=l); eauto.
Qed.

Lemma emptyEquiv_ok_Bg:
forall G,
  ok_Bg G ->
  ok_Bg (emptyEquiv G).
induction G; simpl; intros; auto; destruct a.
unfold ok_Bg in *;
destruct H; split; simpl in *.
inversion H; subst;
constructor; auto;
apply emptyEquiv_ok_list; auto.
apply emptyEquiv_ok_var.
apply ok_LF_split in H0; destruct H0; auto.
Qed.