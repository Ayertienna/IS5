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

(* Copied from standard list, but this one uses List from LibList *)
Definition flat_map {A}{B}(f:A -> list B) :=
  fix flat_map (l:list A) : list B :=
  match l with
    | nil => nil
    | x :: t => (f x) ++ (flat_map t)
  end.

Section FlatMapProp.

Variables A B: Type.
Variable f : A -> list B.

Lemma flat_map_nil :
  flat_map f nil = nil.
Proof. auto. Qed.

Lemma flat_map_cons : forall x l,
  flat_map f (x::l) = f x ++ flat_map f l.
Proof. auto. Qed.

Lemma flat_map_app : forall l1 l2,
  flat_map f (l1 ++ l2) = flat_map f l1 ++ flat_map f l2.
Proof.
induction l1; intros; rew_app; simpl; auto;
rewrite IHl1; rew_app; auto.
Qed.

Lemma flat_map_last : forall x l,
  flat_map f (l & x) = flat_map f l ++ f x.
Proof. intros; rewrite flat_map_app; simpl; rew_app; auto. Qed.

End FlatMapProp.

Hint Rewrite flat_map_nil flat_map_cons flat_map_app flat_map_last :
  rew_flat_map.

Tactic Notation "rew_flat_map" :=
  autorewrite with rew_flat_map rew_app.
Tactic Notation "rew_flat_map" "in" hyp(H) :=
  autorewrite with rew_flat_map rew_app in H.
Tactic Notation "rew_flat_map" "in" "*" :=
  autorewrite with rew_flat_map rew_app in *.

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

Lemma flat_map_snd_permut:
forall A B (G: list (A * list B)) G',
  G *=* G' ->
  flat_map snd_ G *=* flat_map snd_ G'.
induction G; intros; simpl in *.
apply permut_nil_eq in H; subst; simpl; auto.
destruct a; simpl in *; assert ((a,l)::G *=* G') as H0 by auto;
apply permut_split_head in H0; destruct H0 as (hd, (tl, H0)); subst;
rew_flat_map; simpl; permut_simpl; transitivity (flat_map snd_ (hd++tl));
[ apply IHG | rew_flat_map]; auto; apply permut_cons_inv with (a:=(a,l));
rewrite H; permut_simpl.
Qed.

Lemma flat_map_concat:
forall A B G, concat (map (@snd_ A (list B)) G) = flat_map snd_ G.
induction G; intros; try destruct a;
rew_map; rew_flat_map; simpl; rew_concat; try rewrite IHG; eauto.
Qed.
