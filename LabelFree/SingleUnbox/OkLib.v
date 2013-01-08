Add LoadPath "../..".
Require Export PPermutLib.
Require Export FSetLib.
Require Export EmptyEquiv.

Inductive ok_LF {A}: list (prod var A) -> list var -> Prop :=
| Ok_nil: forall U, ok_LF nil U
| Ok_step: forall G T w U,
  ~ Mem w U -> ok_LF G (w::U) -> ok_LF ((w, T)::G) U
.

Definition ok_Bg_LF (G: bg_LF) : Prop := ok_LF (concat G) nil.

Definition used_vars_ctx_LF (L: bg_LF) :=
  from_list (map fst_ (concat L)).

Lemma used_vars_app_LF:
forall x y,
  used_vars_ctx_LF (x ++ y) = used_vars_ctx_LF x \u used_vars_ctx_LF y.
induction x; intros; unfold used_vars_ctx_LF in *; rew_app; simpl.
rewrite from_list_nil; rewrite union_empty_l; auto.
rew_concat; rew_map; repeat rewrite from_list_app;
rewrite <- IHx; rew_concat; rew_map; rewrite from_list_app;
rewrite union_assoc; auto.
Qed.

Add Morphism used_vars_ctx_LF: PPermut_used_t.
induction x; intros.
apply PPermut_LF_nil_impl in H; subst; auto.
simpl; unfold used_vars_ctx_LF in *; simpl;
rew_concat; rew_map.
assert (a :: x ~=~ y) by auto.
apply PPermut_LF_split_head in H;
destruct H as (l', (hd, (tl, (Ha, Hb)))).
subst.
assert (x & a ~=~  (hd ++ tl) & l').
  transitivity (a::x); [ | rewrite H0];
  PPermut_LF_simpl.
apply PPermut_LF_last_rev in H; auto.
rew_concat; rew_map;
repeat rewrite from_list_app.
rewrite IHx with (y:=hd ++ tl); auto.
rew_concat; rew_map.
rewrite from_list_app.
rewrite <- union_comm_assoc.
assert (from_list (map fst_ a) = from_list (map fst_ l')).
  apply from_list_map; auto.
rewrite H1; auto.
Qed.

Lemma ok_LF_used_permut:
forall A G U U',
  U *=* U' ->
  (@ok_LF A G U) ->
  (@ok_LF A G U').
induction G; intros.
destruct U'; econstructor; eauto.
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
induction G1; intros; split; try destruct a; eauto using (@ok_LF A);
rew_app in *; inversion H; subst; try constructor; auto.
eapply IHG1 with (G2:=G2); auto.
rew_app in *; inversion H; subst; eapply IHG1 with (G2:=G2); auto;
eapply ok_LF_used_weakening in H5; eauto.
Qed.

Lemma ok_LF_permut:
forall A G G' U,
  (@ok_LF A G U) -> G *=* G' -> (@ok_LF A G' U).
intros A; induction G; intros.
apply permut_nil_eq in H0; subst; auto.
inversion H; subst.
assert ((w,T)::G *=* G') by auto.
apply permut_split_head in H0; destruct H0 as (hd, (tl, H0)); subst.
assert (G *=* hd ++ tl).
  apply permut_cons_inv with (a:=(w, T)); rewrite H1; permut_simpl.
specialize IHG with (G':=hd++tl) (U:=w::U).
apply IHG in H5; auto.
generalize dependent U. generalize dependent G.
induction hd; rew_app in *; intros.
constructor; auto.
destruct a; inversion H5; subst; constructor; auto.
  rewrite Mem_cons_eq in H8; intro; elim H8; right; auto.
  apply IHhd with (G:=hd++tl); try permut_simpl.
  intros; auto.
  rewrite Mem_cons_eq in H8; rewrite Mem_cons_eq; intro; elim H8;
  destruct H2; subst; [left | ]; auto; contradiction.
  apply ok_LF_used_permut with (U:=v::w::U); [permut_simpl | auto].
  constructor.
  rewrite Mem_cons_eq in H8; rewrite Mem_cons_eq; intro; elim H8;
  destruct H2; subst; [left | ]; auto; contradiction.
  apply ok_LF_used_permut with (U:=v::w::U); [permut_simpl | auto].
Qed.

Lemma ok_LF_PPermut:
forall U G G',
  ok_LF (concat G) U -> G ~=~ G' -> ok_LF (concat G') U.
intros;
apply PPermut_concat_permut in H0;
eapply ok_LF_permut; eauto.
Qed.

Lemma ok_Bg_LF_PPermut:
forall G G',
  ok_Bg_LF G -> G ~=~ G' -> ok_Bg_LF G'.
unfold ok_Bg_LF; intros; eapply ok_LF_PPermut; eauto.
Qed.

Lemma ok_LF_fresh_used:
forall A G x U,
  (@ok_LF A G U) ->
  ~ Mem x ((map fst_ G) ++ U) ->
  ok_LF G (x::U).
induction G; intros; rew_map in *.
constructor.
destruct a; simpl in *; constructor.
inversion H; subst.
rewrite Mem_cons_eq in *; rewrite Mem_app_or_eq in *; intro; elim H0;
destruct H1; subst. left; auto. contradiction.
inversion H; subst.
apply ok_LF_used_permut with (U:=x::v::U); try permut_simpl;
apply IHG; auto.
rewrite Mem_app_or_eq in *;
rewrite Mem_cons_eq in *;
rewrite Mem_app_or_eq in *; intro; elim H0; destruct H1; eauto.
destruct H1; eauto.
Qed.

Lemma ok_Bg_LF_fresh:
forall G Gamma x A,
  ok_Bg_LF (Gamma::G) ->
  x \notin (used_vars_ctx_LF (Gamma::G)) ->
  ok_Bg_LF (((x, A) :: Gamma)::G).
unfold ok_Bg_LF; intros; rew_concat;
constructor.
rewrite Mem_nil_eq; tauto.
replace (Gamma++concat G) with (concat (Gamma::G)) by
  (rew_concat; auto);
apply ok_LF_fresh_used; auto.
unfold used_vars_ctx_LF in *;
apply notin_Mem; rew_concat in *; rew_map in *; rewrite from_list_app in *.
rewrite notin_union in *; destruct H0; split; auto.
Qed.

Lemma ok_Bg_LF_nil:
forall G,
  ok_Bg_LF G ->
  ok_Bg_LF (nil::G).
intros; unfold ok_Bg_LF; rew_concat; rew_app; auto.
Qed.

Hint Resolve ok_Bg_LF_nil.

Lemma ok_Bg_LF_concat:
forall c1 c2 G0 G1 G2,
  c1::c2::G0 ~=~ G1 ->
  (c1++c2)::G0 ~=~ G2 ->
  (ok_Bg_LF G1 <-> ok_Bg_LF G2).
split; intros.
apply ok_Bg_LF_PPermut with (G:=(c1++c2)::G0); auto;
apply ok_Bg_LF_PPermut with (G':=c1::c2::G0) in H1; [ | symmetry]; auto;
unfold ok_Bg_LF in *; rew_concat in *; auto.
apply ok_Bg_LF_PPermut with (G':=(c1++c2)::G0) in H1; auto;
apply ok_Bg_LF_PPermut with (G:=c1::c2::G0); [ | symmetry]; auto;
unfold ok_Bg_LF in *; rew_concat in *; auto.
Qed.

Lemma ok_Bg_LF_empty:
forall G,
  ok_Bg_LF (emptyEquiv_LF G).
unfold ok_Bg_LF; induction G; simpl in *; rew_concat. constructor. auto.
Qed.

Add Morphism ok_Bg_LF: PPermut_ok_Bg_LF.
split; intros; eapply ok_Bg_LF_PPermut; eauto.
Qed.

Lemma ok_Bg_LF_empty_first:
forall G Gamma,
  ok_Bg_LF (Gamma :: G) ->
  ok_Bg_LF (nil :: G).
unfold ok_Bg_LF; intros; rew_concat in *.
apply ok_LF_split in H; destruct H; auto.
Qed.

Lemma ok_Bg_LF_weakening:
forall G Gamma,
  ok_Bg_LF (Gamma::G) -> ok_Bg_LF G.
unfold ok_Bg_LF; intros; rew_concat in *.
apply ok_LF_split in H; destruct H; auto.
Qed.

Lemma ok_Bg_LF_Mem_eq:
forall C C' v A A0 G,
  ok_Bg_LF (C :: G) ->
  C *=* (v, A) :: C' ->
  Mem (v, A0) C ->
  A0 = A.
intros; destruct (eq_ty_dec A0 A); auto.
assert (exists gh, exists gt, C' = gh & (v, A0) ++ gt) by
  ( apply permut_neq_split with (b := (v, A)) (l1 := C); auto;
    intro HH; inversion HH; subst; elim n; auto).
destruct H2 as (gh); destruct H2 as (gt); subst.
assert (C *=* (v, A) :: (v, A0) :: gh ++ gt) by (rewrite H0; permut_simpl).
unfold ok_Bg_LF in *.
assert (ok_LF (concat (((v, A) :: (v, A0) :: gh ++ gt ) :: G )) nil).
  apply ok_LF_PPermut with (G := ((C) :: G)). auto. PPermut_LF_simpl.
simpl in *. rew_concat in *; inversion H3; subst.
inversion H9; subst.
elim H10; apply Mem_here.
Qed.

Lemma ok_Bg_LF_permut_first_tail:
forall G C C' x A,
  ok_Bg_LF (C :: G) ->
  C *=* (x, A)::C' ->
  ok_Bg_LF (C' :: G).
intros;
assert (((x, A) :: C') :: G ~=~ (C) :: G) by PPermut_LF_simpl;
rewrite <- H1 in H; unfold ok_Bg_LF in *.
rew_concat in *; inversion H; subst.
apply ok_LF_used_weakening with (x:=x); auto.
Qed.

Lemma ok_Bg_LF_Mem_contradict:
forall A A' v C C' G G',
 ok_Bg_LF (C :: G) ->
 Mem (v, A) C ->
 G ~=~ G' & ((v, A') :: C') ->
 False.
intros.
rewrite H1 in H.
apply permut_Mem_split_head with (l2 := C) in H0; auto;
destruct H0 as (gh); destruct H0 as (gt); subst.
assert (( gh & (v, A) ++ gt) :: G' & ((v, A') :: C') ~=~
        ((v, A) :: gh ++ gt) :: ((v, A') :: C') :: G') by
(PPermut_LF_simpl; apply PPermut_LF_skip; [permut_simpl | auto]).
rewrite H0 in H; unfold ok_Bg_LF in H. rew_concat in *.
inversion H; subst.
assert (ok_LF ((v, A') :: C' ++ concat G') (v :: nil)).
  eapply ok_LF_split with (G1:=concat ((gh++gt)::nil)); simpl;
  rew_concat; auto.
inversion H2; subst. elim H9; apply Mem_here.
Qed.

Lemma ok_Bg_LF_permut_no_last:
forall G C v A,
  ok_Bg_LF (G & ((v,A) :: C)) ->
  ok_Bg_LF (G & C).
intros;
assert (G & (C) ~=~ (C) :: G) by PPermut_LF_simpl;
assert (G & ((v, A) :: C) ~=~ ((v,A) :: C) :: G) by PPermut_LF_simpl.
rewrite H1 in H. unfold ok_Bg_LF in H; rew_concat in *.
inversion H; subst. rewrite H0. unfold ok_Bg_LF; rew_concat.
apply ok_LF_used_weakening in H7;
auto.
Qed.

Lemma ok_Bg_LF_permut_no_last_spec:
forall G C C0 v A,
  ok_Bg_LF (C0::G & ((v,A) :: C)) ->
  ok_Bg_LF (C0::G & (C)).
intros;
assert (C0 :: G & (C)  ~=~ (C0 :: G) & (C)) by (rew_app; PPermut_LF_simpl).
rewrite H0; eapply ok_Bg_LF_permut_no_last; rew_app; eauto.
Qed.

Lemma ok_Bg_LF_emptyEquiv:
forall G,
  ok_Bg_LF (emptyEquiv_LF G).
induction G; simpl; auto; constructor.
Qed.

Lemma emptyEquiv_LF_ok_Bg_part:
forall G G',
  ok_Bg_LF (G ++ G') ->
  ok_Bg_LF ((emptyEquiv_LF G) ++ G').
induction G; simpl; intros; auto;
unfold ok_Bg_LF in *; rew_concat in *; simpl.
specialize IHG with (G':=a::G').
apply ok_LF_permut with (G':=concat(G ++ a :: G')) in H.
apply IHG in H. rew_concat in *.
apply ok_LF_permut with (G':=concat (a::(emptyEquiv_LF G)++G')) in H.
rew_concat in *.
assert (ok_Bg_LF (emptyEquiv_LF G ++ G')).
  eapply ok_Bg_LF_weakening with (Gamma:=a).
  unfold ok_Bg_LF; rew_concat; auto.
unfold ok_Bg_LF in *; rew_concat in *; auto.
rew_concat; permut_simpl.
rew_concat; permut_simpl.
Qed.
