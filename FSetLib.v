(* Rename to fsetpermut or move to permutlib *)
Require Export PermutLib.

Open Scope permut_scope.

Definition fst_ {A} {B} (p: A * B) :=
  match p with
  | (x, y) => x
  end.

Definition snd_ {A} {B} (p:A * B) :=
  match p with
  | (x, y) => y
  end.

Lemma from_list_map:
forall A B (l: list (A * B)) l',
  l *=* l' ->
  from_list (map fst_ l) = from_list (map fst_ l').
intros A B; induction l; intros.
apply permut_nil_eq in H; subst; auto.
assert (a :: l *=* l') by auto;
apply permut_split_head in H; destruct H as (hd', (tl', H)); subst.
assert (from_list (map fst_ l) = from_list (map fst_ (hd' ++ tl'))).
  apply IHl; apply permut_cons_inv with (a:=a); rewrite H0; permut_simpl.
  destruct a; rew_map; simpl; rewrite from_list_cons; rewrite H.
  rewrite map_app; repeat rewrite from_list_app; rewrite from_list_cons.
  rewrite union_comm_assoc; auto.
Qed.

Lemma from_list_Mem:
forall A U (x:A), Mem x U <-> x \in from_list U.
intro A; induction U; split; intros.
rewrite Mem_nil_eq in H; contradiction.
rewrite from_list_nil in H; apply notin_empty in H; contradiction.
rewrite Mem_cons_eq in H; destruct H; subst; rewrite from_list_cons;
rewrite in_union.
  left; rewrite in_singleton; auto.
  right; eapply IHU; auto.
rewrite Mem_cons_eq; rewrite from_list_cons in H; rewrite in_union in H;
destruct H; subst.
  left; rewrite in_singleton in H; subst; auto.
  right; eapply IHU; auto.
Qed.
