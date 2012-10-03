Require Import Setoid.
Require Export Shared.
Require Export PermutLib.
Require Export PPermutLib.

Open Scope permut_scope.

(*** Definitions ***)

Set Implicit Arguments.

Section Definitions.

Variables A B : Type.

Inductive ok_LF: list (var * A) -> list var -> Prop :=
| ok_nil: forall U, ok_LF nil U
| ok_step: forall w C G U,
  ~ Mem w U -> ok_LF G (w::U) -> ok_LF ((w, C)::G) U
.

(* Copied from standard list, but this one uses List from LibList *)
Definition flat_map (f:A -> list B) :=
  fix flat_map (l:list A) : list B :=
  match l with
    | nil => nil
    | x :: t => (f x) ++ (flat_map t)
  end.

Section FlatMapProp.

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

End Definitions.

Definition fst_ {A} {B} (p: A * B) :=
  match p with
  | (x, y) => x
  end.

Definition snd_ {A} {B} (p:A * B) :=
  match p with
  | (x, y) => y
  end.

Hint Rewrite flat_map_nil flat_map_cons flat_map_app flat_map_last :
  rew_flat_map.

Tactic Notation "rew_flat_map" :=
  autorewrite with rew_flat_map rew_app.
Tactic Notation "rew_flat_map" "in" hyp(H) :=
  autorewrite with rew_flat_map rew_app in H.
Tactic Notation "rew_flat_map" "in" "*" :=
  autorewrite with rew_flat_map rew_app in *.

Definition ok_Bg (G: Background_LF) : Prop :=
ok_LF G nil  /\
ok_LF (flat_map snd_ G) nil.

Fixpoint used_t_vars (G: Background_LF) :=
match G with
| nil => from_list nil
| (w, Gamma) :: G => from_list (map fst_ Gamma) \u used_t_vars G
end.

Fixpoint used_w_vars (G: Background_LF) :=
match G with
| nil => from_list nil
| (w, Gamma) :: G => \{w} \u used_w_vars G
end.


(*** Lemmas ***)

Lemma flat_map_ppermut:
forall G G',
  G ~=~ G' -> flat_map snd_ G *=* flat_map snd_ G'.
induction G; intros.
apply PPermut_nil_impl in H; subst; auto.
assert (a::G ~=~ G') by auto;
destruct a; apply PPermut_split_head in H;
destruct H as (l', (hd, (tl, (Ha, Hb)))).
subst; simpl in *.
specialize IHG with (hd ++ tl).
rew_flat_map; simpl.
transitivity (l' ++ flat_map snd_ G); permut_simpl; auto.
transitivity (flat_map snd_ (hd++tl)).
apply IHG; apply PPermut_last_rev with (w:=v) (Gamma:=l) (Gamma':=l');
auto; transitivity ((v,l)::G); PPermut_simpl; rewrite H0; PPermut_simpl.
rew_flat_map; auto.
Qed.

(* used_*_vars *)

Lemma used_t_vars_app:
forall x y,
  used_t_vars (x ++ y) = used_t_vars x \u used_t_vars y.
induction x; intros.
rew_app; simpl; rewrite from_list_nil; rewrite union_empty_l; auto.
rew_app; destruct a; simpl; rewrite IHx; rewrite union_assoc; auto.
Qed.

Lemma used_w_vars_app:
forall x y,
  used_w_vars (x ++ y) = used_w_vars x \u used_w_vars y.
induction x; intros.
rew_app; simpl; rewrite from_list_nil; rewrite union_empty_l; auto.
rew_app; destruct a; simpl; rewrite IHx; rewrite union_assoc; auto.
Qed.

Lemma from_list_app:
forall A (l1: list A) l2,
  from_list (l1++l2) = from_list l1 \u from_list l2.
intro A; induction l1; intros.
rewrite from_list_nil; rewrite union_empty_l; auto.
rew_app; repeat rewrite from_list_cons; rewrite IHl1;
rewrite union_assoc; auto.
Qed.

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

Add Morphism used_t_vars: PPermut_used_t.
induction x; intros.
apply PPermut_nil_impl in H; subst; auto.
destruct a; simpl.
assert ((v, l) :: x ~=~ y) by auto.
apply PPermut_split_head in H;
destruct H as (l', (hd, (tl, (Ha, Hb)))).
subst.
assert (x & (v,l) ~=~  (hd ++ tl) & (v, l')).
  transitivity ((v,l)::x); [ | rewrite H0];
  PPermut_simpl.
apply PPermut_last_rev in H; auto.
rewrite IHx with (y:=hd ++ tl); auto.
repeat rewrite used_t_vars_app.
simpl; repeat rewrite <- union_assoc.
rewrite from_list_nil; rewrite union_empty_l.
assert (from_list (map fst_ l) = from_list (map fst_ l')).
  apply from_list_map; auto.
rewrite union_comm_assoc; rewrite H1; auto.
Qed.

Add Morphism used_w_vars: PPermut_used_w.
induction x; intros.
apply PPermut_nil_impl in H; subst; auto.
destruct a; simpl.
assert ((v, l) :: x ~=~ y) by auto.
apply PPermut_split_head in H;
destruct H as (l', (hd, (tl, (Ha, Hb)))).
subst.
assert (x & (v,l) ~=~  (hd ++ tl) & (v, l')).
  transitivity ((v,l)::x); [ | rewrite H0];
  PPermut_simpl.
apply PPermut_last_rev in H; auto.
rewrite IHx with (y:=hd ++ tl); auto.
repeat rewrite used_w_vars_app.
simpl; repeat rewrite <- union_assoc.
rewrite union_comm_assoc;
rewrite from_list_nil; rewrite union_empty_l.
auto.
Qed.


(* ok_LF for a generic type *)

Lemma ok_LF_used_permut:
forall A G U U',
  U *=* U' ->
  (@ok_LF A G U) ->
  (@ok_LF A G U').
induction G; intros; try constructor;
destruct a; inversion H0; subst;
constructor; [ intro | apply IHG with (U:=v::U)]; auto;
apply Mem_permut with (l':=U) in H1; [ elim H5 | symmetry]; auto.
Qed.

Lemma ok_LF_used_weakening:
forall A G x U,
  (@ok_LF A G (x::U)) ->
  (@ok_LF A G U).
induction G; intros; try constructor;
destruct a; inversion H; subst;
constructor.
intro; apply Mem_permut with (l':=U) in H0; auto; elim H4;
rewrite Mem_cons_eq; right; auto.
apply ok_LF_used_permut with (U' := (x::v::U)) in H5;
[ | permut_simpl]; apply IHG with (x:=x); auto.
Qed.

Lemma ok_LF_split:
forall A G1 G2 U,
  (@ok_LF A (G1++G2) U) ->
  ok_LF G1 U /\ ok_LF G2 U.
induction G1; intros; split; try destruct a; auto using ok_LF.
rew_app in *; inversion H; subst; constructor; auto;
eapply IHG1 with (G2:=G2); auto.
rew_app in *; inversion H; subst; eapply IHG1 with (G2:=G2); auto;
eapply ok_LF_used_weakening in H5; eauto.
Qed.


(* ok_LF for a specific type -- would be nice to make it more general btw *)

Add Morphism (@ok_LF (list (var*ty))) : ok_LF_PPermut_lst_var_ty.
intros x y H; induction H.
intros; tauto.
split; intros; inversion H1; subst; constructor; auto;
apply IHPPermut; auto.
split; intros; inversion H1; subst; inversion H7; subst;
constructor.
intro; elim H8; rewrite Mem_cons_eq; right; auto.
constructor.
  intro; rewrite Mem_cons_eq in H2; elim H6; destruct H2.
  subst; elim H8; rewrite Mem_cons_eq; left; auto. auto.
  apply ok_LF_used_permut with (U:=w'::w::y0); auto; permut_simpl.
intro; elim H8; rewrite Mem_cons_eq; right; auto.
constructor.
  intro; rewrite Mem_cons_eq in H2; elim H6; destruct H2.
  subst; elim H8; rewrite Mem_cons_eq; left; auto. auto.
  apply ok_LF_used_permut with (U:=w::w'::y0); auto; permut_simpl.
split; intros.
  apply IHPPermut2; apply IHPPermut1; auto.
  apply IHPPermut1; apply IHPPermut2; auto.
Qed.

Lemma ok_LF_PPermut_ty:
forall G G' U
  (H: G ~=~ G'),
  ok_LF (flat_map snd_ G) U <->
  ok_LF (flat_map snd_ G') U.
Admitted.

Lemma ok_LF_fresh_te_list:
forall G Gamma v A w U,
 ok_LF ((w, Gamma) :: G) U ->
 v \notin (used_t_vars ((w,Gamma)::G)) ->
 ok_LF ((w, (v,A)::Gamma) :: G) U.
intros; inversion H; subst; constructor; auto.
Qed.

Lemma ok_LF_fresh_te_ty:
forall U G Gamma v A w,
 ok_LF (flat_map snd_ ((w, Gamma) :: G)) U ->
 v \notin (used_t_vars ((w, Gamma)::G) \u from_list U) ->
 ok_LF (flat_map snd_ ((w, (v, A)::Gamma) :: G)) U.
Admitted. (* !!! *)

Lemma ok_LF_fresh_wo_list:
forall G w U,
 ok_LF G U ->
 w \notin (used_w_vars G)  \u from_list U ->
 ok_LF ((w, nil) :: G) U.
Admitted.

Lemma ok_LF_fresh_wo_ty:
forall G w U,
 ok_LF (flat_map snd_ G) U ->
 w \notin (used_w_vars G) \u from_list U ->
 ok_LF (flat_map snd_ ((w, nil) :: G)) U.
intros; inversion H; subst; simpl in *; rew_app in *; auto.
Qed.

Lemma ok_LF_fresh_wo_te_list:
forall U G v A w,
 ok_LF G U ->
 w \notin (used_w_vars G) \u from_list U ->
 v \notin (used_t_vars G) ->
 ok_LF ((w, (v,A)::nil) :: G) U.
intros; apply ok_LF_fresh_te_list;
[ apply ok_LF_fresh_wo_list | ]; auto.
simpl; rewrite map_nil; rewrite from_list_nil; rewrite union_empty_l; auto.
Qed.

Lemma ok_LF_fresh_wo_te_ty:
forall U G v A w,
 ok_LF (flat_map snd_ G) U ->
 w \notin (used_w_vars G) \u from_list U ->
 v \notin (used_t_vars G) \u from_list U ->
 ok_LF (flat_map snd_ ((w, (v,A) :: nil) :: G)) U.
intros; apply ok_LF_fresh_te_ty.
apply ok_LF_fresh_wo_ty; auto.
simpl; rewrite map_nil; rewrite from_list_nil; rewrite union_empty_l; auto.
Qed.

Lemma ok_LF_empty_first_list:
forall w G Gamma U,
  ok_LF ((w,Gamma) :: G) U ->
  ok_LF ((w, (@nil (prod var ty))) :: G) U.
intros; simpl in *; inversion H; subst; constructor; auto.
Qed.

Lemma ok_LF_empty_first_ty:
forall Gamma (w: var) G U,
  (@ok_LF ty (flat_map snd_ ((w,Gamma) :: G)) U) ->
  (@ok_LF ty (flat_map snd_ ((w, nil) :: G)) U).
induction Gamma; intros; simpl in *; auto; destruct a;
rew_app in H; inversion H; subst.
apply IHGamma; auto.
apply ok_LF_used_weakening with (x:=v); auto.
Qed.

(* ok_Bg *)

Add Morphism ok_Bg : ok_Bg_PPermut.
intros; unfold ok_Bg; split; intros;
destruct H0; split;
[ rewrite <- H | |
  rewrite H | eapply ok_LF_PPermut_ty; try symmetry ]; eauto.
assert (x ~=~y) by auto; eapply flat_map_ppermut in H; eapply ok_LF_PPermut_ty;
try symmetry; eauto.
assert (x ~=~ y) by auto; eapply flat_map_ppermut in H; eapply ok_LF_PPermut_ty;
eauto.
Qed.

Lemma ok_Bg_ppermut:
forall G G',
  G ~=~ G' ->
  ok_Bg G ->
  ok_Bg G'.
intros; rewrite <- H; auto.
Qed.

Lemma ok_Bg_permut:
forall G Ctx Ctx' w,
  Ctx *=* Ctx' ->
  ok_Bg ((w, Ctx) :: G) ->
  ok_Bg ((w, Ctx') :: G).
intros;
assert ((w, Ctx) :: G ~=~ (w, Ctx') :: G) by PPermut_simpl;
rewrite <- H1; auto.
Qed.

Lemma ok_Bg_permut_last:
forall G Ctx Ctx' w,
  Ctx *=* Ctx' ->
  ok_Bg (G ++ (w, Ctx) :: nil) ->
  ok_Bg (G ++ (w, Ctx') :: nil).
intros;
assert (G & (w, Ctx) ~=~ G & (w, Ctx')) by PPermut_simpl;
rewrite <- H1; auto.
Qed.

Lemma ok_Bg_fresh_te:
forall G Gamma v A w,
 ok_Bg ((w, Gamma) :: G) ->
 v \notin (used_t_vars ((w,Gamma)::G)) ->
 ok_Bg ((w, (v,A)::Gamma) :: G).
intros; unfold ok_Bg in *;  destruct H; split;
[ apply ok_LF_fresh_te_list |
  apply ok_LF_fresh_te_ty]; auto.
rewrite from_list_nil. rewrite notin_union; split; auto; rewrite notin_empty.
Qed.

Lemma ok_Bg_fresh_wo:
forall G w,
 ok_Bg G ->
 w \notin (used_w_vars G) ->
 ok_Bg ((w, nil) :: G).
intros; unfold ok_Bg in *;  destruct H; split;
[ eapply ok_LF_fresh_wo_list |
  eapply ok_LF_fresh_wo_ty]; eauto;
rewrite from_list_nil; rewrite union_empty_r; auto.
Qed.

Lemma ok_Bg_fresh_wo_te:
forall G w v A,
 ok_Bg G ->
 w \notin (used_w_vars G) ->
 v \notin (used_t_vars G) ->
 ok_Bg ((w, (v, A) :: nil) :: G).
intros; unfold ok_Bg in *;  destruct H; split;
[ apply ok_LF_fresh_wo_te_list |
  apply ok_LF_fresh_wo_te_ty]; eauto;
rewrite from_list_nil; rewrite union_empty_r; auto.
Qed.

Lemma ok_Bg_cons_last:
forall G a,
  ok_Bg (G & a) <-> ok_Bg (a :: G).
intros; assert (G & a ~=~ a :: G) by PPermut_simpl;
rewrite H; split; auto.
Qed.

Lemma ok_Bg_swap:
forall C C' G,
  ok_Bg (C :: G & C') ->
  ok_Bg (C' :: G & C).
intros; assert (C:: G & C' ~=~ C' :: G & C) by PPermut_simpl;
rewrite <- H0; auto.
Qed.

Hint Resolve ok_Bg_cons_last ok_Bg_swap.
Hint Resolve ok_Bg_permut_last: ok_bg_rew.
Hint Resolve ok_Bg_fresh_te ok_Bg_fresh_wo ok_Bg_fresh_wo_te.

Lemma ok_Bg_permut_first_tail:
forall G C C' w x A,
  ok_Bg ((w, C) :: G) ->
  C *=* (x,A)::C' ->
  ok_Bg ((w, C') :: G).
intros;
assert ((w,(x, A) :: C') :: G ~=~ (w, C) :: G) by PPermut_simpl;
rewrite <- H1 in H; unfold ok_Bg in *; destruct H; split; simpl in *.
inversion H; subst; constructor; auto.
rew_app in *; inversion H2; subst; simpl in *.
apply ok_LF_used_weakening with (x:=x); auto.
Qed.
Hint Resolve ok_Bg_permut_first_tail : ok_bg_rew.

Lemma ok_Bg_empty_first:
forall w G Gamma,
  ok_Bg ((w,Gamma) :: G) ->
  ok_Bg ((w, nil) :: G).
intros; unfold ok_Bg; destruct H; split;
[eapply ok_LF_empty_first_list |
 eapply ok_LF_empty_first_ty]; eauto.
Qed.

Hint Resolve ok_Bg_empty_first : ok_bg_rew.

Lemma ok_Bg_Mem_eq:
forall w C C' v A A0 G,
  ok_Bg ((w, C) :: G) ->
  C *=* (v, A) :: C' ->
  Mem (v, A0) C ->
  A0 = A.
intros; destruct (eq_ty_dec A0 A); auto;
assert (exists gh, exists gt, C' = gh & (v, A0) ++ gt) by
  ( apply permut_neq_split with (b := (v, A)) (l1 := C); auto;
    intro HH; inversion HH; subst; elim n; auto);
destruct H2 as (gh); destruct H2 as (gt); subst;
assert (C *=* (v, A) :: (v, A0) :: gh ++ gt) by (rewrite H0; permut_simpl);
unfold ok_Bg in *; destruct H.
assert (ok_LF (flat_map snd_ ((w, (v, A) :: (v, A0) :: gh ++ gt ) :: G )) nil)
by
  (apply ok_LF_PPermut_ty with (G := ((w, C) :: G)); [PPermut_simpl | auto]).
simpl in *. rew_app in *; inversion H4; subst.
inversion H10; subst;
elim H11; apply Mem_here.
Qed.

Lemma ok_Bg_Mem_contradict:
forall A A' w w' v C C' G G',
 ok_Bg ((w, C) :: G) ->
 Mem (v, A) C ->
 G ~=~ G' & (w', (v, A') :: C') ->
 False.
intros.
rewrite H1 in H.
apply permut_Mem_split_head with (l2 := C) in H0; auto;
destruct H0 as (gh); destruct H0 as (gt); subst.
assert ((w, gh & (v, A) ++ gt) :: G' & (w', (v, A') :: C') ~=~
        (w, (v, A) :: gh ++ gt) :: (w', (v, A') :: C') :: G') by
(PPermut_simpl; apply PPermut_skip; [permut_simpl | auto]).
rewrite H0 in H; unfold ok_Bg in H; destruct H.
rew_flat_map in *. simpl ok_LF in H2.
rew_app in *. inversion H2; subst.
assert (ok_LF ((v, A') :: C' ++ flat_map snd_ G') (v :: nil)).
  eapply ok_LF_split with (G1:=flat_map snd_ ((w, gh++gt)::nil)); simpl;
  rew_app; auto.
inversion H3; subst; elim H10; apply Mem_here.
Qed.

Lemma ok_Bg_permut_no_last:
forall G w C v A,
  ok_Bg (G & (w, (v,A) :: C)) ->
  ok_Bg (G & (w, C)).
Admitted. (* !!! *)

Lemma ok_Bg_permut_no_last_spec:
forall G w C C0 v A,
  ok_Bg (C0::G & (w, (v,A) :: C)) ->
  ok_Bg (C0::G & (w, C)).
intros;
assert (C0 :: G & (w, C)  ~=~ (C0 :: G) & (w, C)) by (rew_app; PPermut_simpl);
rewrite H0; eapply ok_Bg_permut_no_last; rew_app; eauto.
Qed.

Lemma ok_Bg_no_last:
forall G C,
  ok_Bg (G & C) -> ok_Bg G.
intros;
assert (G & C ~=~ (C :: nil) ++ G) by PPermut_simpl; rewrite H0 in H;
destruct H; split.
eapply ok_LF_split with (G1:=C::nil) (G2:=G); eauto.
destruct C; rew_app in *; simpl in *.
eapply ok_LF_split with (G1:=l) (G2:=flat_map snd_  G); auto.
Qed.
Hint Resolve ok_Bg_no_last.

Lemma ok_Bg_permut_no_last_spec2:
forall G w C C0 v A,
  ok_Bg (G & (w, (v,A) :: C) & C0) ->
  ok_Bg (G & (w, C) & C0).
intros.
assert (G & (w, C) & C0 ~=~ G & C0 & (w, C)) by PPermut_simpl;
rewrite H0;
apply ok_Bg_permut_no_last with (v:=v) (A:=A).
assert (G & C0 & (w, (v, A) :: C) ~=~ G & (w, (v, A) :: C) & C0)
  by PPermut_simpl;
rewrite H1; auto.
Qed.

Lemma ok_Bg_first_last_neq:
forall w w' C C' G,
  ok_Bg ((w, C) :: G & (w', C')) ->
  w <> w'.
intros.
assert ((w, C) :: G & (w', C') ~=~ (w, C) :: (w', C') :: G) by PPermut_simpl;
rewrite H0 in H;
destruct H; simpl in *. inversion H; subst; inversion H7; subst.
rewrite Mem_cons_eq in H8. rewrite Mem_nil_eq in H8. auto.
Qed.

Lemma ok_Bg_last_last2_neq:
forall w w' C C' G,
  ok_Bg (G & (w, C) & (w', C')) ->
  w <> w'.
intros;
assert (G & (w, C) & (w', C') ~=~ (w, C) :: (w', C') :: G) by PPermut_simpl;
rewrite H0 in H;
destruct H; simpl in *; inversion H; subst; inversion H7; subst.
rewrite Mem_cons_eq in H8. rewrite Mem_nil_eq in H8; auto.
Qed.

Lemma ok_Bg_swap_worlds:
forall G w w' C C',
  ok_Bg (G & (w, C) & (w', C')) ->
  ok_Bg (G & (w', C) & (w, C')).
intros.
assert (G & (w, C) & (w', C') ~=~ (w, C) :: (w', C') :: G) by PPermut_simpl.
rewrite H0 in H.
assert (G & (w', C) & (w, C') ~=~ (w', C) :: (w, C') :: G) by PPermut_simpl.
rewrite H1.
destruct H; split; simpl in *.
inversion H; subst; constructor. rewrite Mem_nil_eq; tauto.
inversion H8; subst; constructor.
rewrite Mem_cons_eq in *; intro; destruct H3; subst;
[ elim H9; left | rewrite Mem_nil_eq in H3 ]; auto.
apply ok_LF_used_permut with (U := w'::w::nil); [permut_simpl | ]; auto.
auto.
Qed.

Lemma ok_Bg_impl_ppermut:
forall G G' w C C',
  ok_Bg ((w, C) :: G) ->
  G & (w, C) ~=~ G' & (w, C') ->
  G ~=~ G' /\ C *=* C'.
Admitted.


(* FIXME: generalize all the ok_Bg_split* into :
   ok_Bg G <- ok_Bg reorder_G <- ok_Bg reorder_G' <- ok_Bg G':
   reorder X ~=~ X and all the singletons are in the front *)


Lemma ok_Bg_split1:
forall G w w' C C',
  ok_Bg ((w,C)::G & (w',C')) ->
  ok_Bg ((w, C ++ C') :: G).
intros.
assert ((w, C) :: G & (w', C') ~=~ (w,C) :: (w', C')::G) by PPermut_simpl.
rewrite H0 in H; destruct H; split; simpl in *.
inversion H; subst; inversion H7; subst; constructor; auto;
apply ok_LF_used_weakening with (x:=w'); auto.
rew_app; auto.
Qed.

Lemma ok_Bg_split2:
forall G w w' C C',
  ok_Bg ((w,C)::G & (w',C')) ->
  ok_Bg ((w', C' ++ C) :: G).
(*intros.
assert ((w, C) :: G & (w', C') ~=~ (w', C') :: (w, C)::G) by PPermut_simpl.
rewrite H0 in H; destruct H; split; simpl in *;
repeat case_if.
rewrite Mem_nil_eq in H2; auto.
apply ok_used_weakening with (x:=w); auto.
skip. (* this should be rew_app; auto *)
Qed. *) Admitted.

Lemma ok_Bg_split3:
forall G w w' w'' C C' C'',
  ok_Bg ((w,C)::G & (w',C') & (w'',C'')) ->
  ok_Bg ((w, C) :: G & (w', C' ++ C'')).
(*intros.
assert ((w, C) :: G & (w', C') & (w'',C'') ~=~
  (w, C) :: (w', C'):: (w'',C'') :: G) by PPermut_simpl.
assert ((w,C) :: G & (w', C'++C'') ~=~ (w,C) :: (w', C'++C'') :: G)
  by PPermut_simpl.
rewrite H0 in H; rewrite H1; destruct H; split; simpl in *;
repeat case_if.
apply ok_used_weakening with (x:=w''); auto.
skip. (* this should be rew_app; auto *)
Qed. *) Admitted.

Lemma ok_Bg_split4:
forall G w w' C C',
  ok_Bg (G & (w, C) & (w', C')) ->
  ok_Bg (G & (w', C' ++ C)).
(*intros.
assert (G & (w, C) & (w', C') ~=~
  (w, C) :: (w', C') :: G) by PPermut_simpl.
assert (G & (w', C'++C) ~=~ (w', C'++C) :: G)
  by PPermut_simpl.
rewrite H0 in H; rewrite H1; destruct H; split; simpl in *;
repeat case_if.
rewrite Mem_nil_eq in H3; auto.
apply ok_used_weakening with (x:=w);
apply ok_used_permut with (U:= w'::w::nil).
permut_simpl. auto.
skip. (* this should be rew_app; auto *)
Qed. *) Admitted.

Lemma ok_Bg_split5:
forall G w w' C C',
  ok_Bg (G & (w, C) & (w', C')) ->
  ok_Bg (G & (w, C ++ C')).
(* intros.
assert (G & (w, C) & (w', C') ~=~
  (w, C) :: (w', C') :: G) by PPermut_simpl.
assert (G & (w, C++C') ~=~ (w, C++C') :: G)
  by PPermut_simpl.
rewrite H0 in H; rewrite H1; destruct H; split; simpl in *;
repeat case_if.
apply ok_used_weakening with (x:=w'); auto.
skip. (* this should be rew_app; auto *)
Qed. *) Admitted.

Lemma ok_Bg_split6:
forall G w C C' C'' w' w'',
  ok_Bg (G & (w, C) & (w', C') & (w'', C'')) ->
  ok_Bg (G & (w, C ++ C') & (w'', C'')).
(*intros.
assert (G & (w,C) & (w', C') & (w'',C'') ~=~
  (w, C) :: (w', C'):: (w'',C'') :: G) by PPermut_simpl.
assert (G & (w, C++C') & (w'', C'') ~=~ (w, C ++ C') :: (w'', C'') :: G)
  by PPermut_simpl.
rewrite H0 in H; rewrite H1; destruct H; split; simpl in *;
repeat case_if.
rewrite Mem_cons_eq in H4;destruct H4; subst.
elim H6; rewrite Mem_cons_eq; right; apply Mem_here.
rewrite Mem_nil_eq in H4; auto.
apply ok_used_weakening with (x:=w');
apply ok_used_permut with (U:= w''::w'::w::nil).
  permut_simpl.
  auto.
skip. (* this should be rew_app; auto *)
Qed. *) Admitted.

(* This is actually false
Lemma ok_Bg_split7:
forall G w w' w'' C C' C'',
  ok_Bg ((w,C)::G & (w'',C'')) ->
  ok_Bg ((w, C ++ C'') :: G & (w', C')).
*)

Lemma ok_Bg_split8:
forall G G' w w' w'' C C' C'',
  ok_Bg (G ++ G' ++ (w, C) :: (w', C') :: (w'', C'') :: nil) ->
  ok_Bg (G ++ G' ++ (w', C') :: (w'', C'' ++ C)::nil) .
(*intros.
assert (G++G' ++ (w, C) :: (w', C') :: (w'',C'') :: nil ~=~
  (w, C) :: (w', C'):: (w'',C'') :: G ++ G') by PPermut_simpl.
assert (G ++ G' ++ (w', C') :: (w'', C'' ++ C) :: nil ~=~
  (w', C') :: (w'', C''++C) :: G ++ G')
  by PPermut_simpl.
rewrite H0 in H; rewrite H1; destruct H; split; simpl in *;
repeat case_if.
rewrite Mem_nil_eq in H3; auto.
rewrite Mem_cons_eq in H4; destruct H4; subst.
elim H7; rewrite Mem_cons_eq; left; auto.
rewrite Mem_nil_eq in H4; auto.
apply ok_used_weakening with (x:=w);
apply ok_used_permut with (U:=w'' :: w' :: w :: nil);
auto; permut_simpl.
skip. (* this should be rew_app; permut; auto *)
Qed. *) Admitted.

Lemma ok_Bg_split9:
forall G w w' w'' C C' C'',
  ok_Bg ((w,C)::G & (w',C') & (w'',C'')) ->
  ok_Bg ((w, C++C') :: G & (w'', C'')).
(*intros.
assert ((w, C) :: G & (w', C') & (w'',C'') ~=~
  (w, C) :: (w', C'):: (w'',C'') :: G) by PPermut_simpl.
assert ((w, C++C') :: G & (w'', C'')  ~=~
  (w, C++C') :: (w'', C'') :: G)
  by PPermut_simpl.
rewrite H0 in H; rewrite H1; destruct H; split; simpl in *;
repeat case_if.
rewrite Mem_cons_eq in H4; destruct H4; subst.
elim H6; rewrite Mem_cons_eq; right; apply Mem_here.
rewrite Mem_nil_eq in H4; auto.
apply ok_used_weakening with (x:=w');
apply ok_used_permut with (U:=w'' :: w' :: w :: nil);
auto; permut_simpl.
skip. (* this should be rew_app; permut; auto *)
Qed. *) Admitted.

Lemma ok_Bg_split10:
forall G G' w1 w2 w3 w4 c1 c2 c3 c4,
  ok_Bg (G ++ (w1, c1)::G' ++ (w2, c2) :: (w3, c3) :: (w4, c4) :: nil) ->
  ok_Bg (G ++ (w1, c1)::G' ++ (w2, c2 ++ c3) :: (w4, c4) :: nil).
(*intros.
assert (G ++ (w1,c1) :: G' ++ (w2, c2) :: (w3, c3) :: (w4,c4) :: nil ~=~
   (w1,c1) :: (w2, c2) :: (w3, c3) :: (w4,c4) :: G ++ G') by PPermut_simpl.
assert (G ++ (w1, c1) :: G' ++ (w2, c2 ++ c3) :: (w4, c4) :: nil~=~
   (w1,c1) :: (w2, c2 ++ c3) :: (w4,c4) :: G ++ G') by PPermut_simpl.
rewrite H0 in H; rewrite H1; destruct H; split; simpl in *;
repeat case_if.
rewrite Mem_cons_eq in H5. destruct H5; subst.
elim H7; rewrite Mem_cons_eq; right; apply Mem_here.
rewrite Mem_cons_eq in H5. destruct H5; subst.
elim H7; rewrite Mem_cons_eq; right;
rewrite Mem_cons_eq; right; apply Mem_here.
rewrite Mem_nil_eq in H5; auto.
apply ok_used_weakening with (x:=w3);
apply ok_used_permut with (U:=w4 :: w3 :: w2 :: w1 :: nil);
auto; permut_simpl.
skip. (* this should be rew_app; permut; auto *)
Qed. *) Admitted.

Hint Resolve ok_Bg_split1 ok_Bg_split2 ok_Bg_split3 ok_Bg_split4
  ok_Bg_split5 ok_Bg_split6 ok_Bg_split8
  ok_Bg_split9 ok_Bg_split10 : ok_bg_rew.
Hint Resolve ok_Bg_permut_no_last ok_Bg_permut_no_last_spec2
  ok_Bg_permut_no_last_spec ok_Bg_first_last_neq
  ok_Bg_last_last2_neq : ok_bg_rew.
Hint Resolve ok_Bg_swap_worlds.

Close Scope permut_scope.