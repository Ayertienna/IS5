Require Export PPermutLib.
Require Export FSetLib.

Inductive ok_LF {A}: list (prod var A) -> list var -> Prop :=
| Ok_nil: forall U, ok_LF nil U
| Ok_step: forall G T w U,
  ~ Mem w U -> ok_LF G (w::U) -> ok_LF ((w, T)::G) U
.

Definition ok_Bg (G: bg_LF) : Prop := ok_LF (concat G) nil.

Definition used_vars_ctx_LF (L: bg_LF) :=
  from_list (map fst_ (concat L)).

Lemma used_vars_app:
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
apply PPermut_nil_impl in H; subst; auto.
simpl; unfold used_vars_ctx_LF in *; simpl;
rew_concat; rew_map.
assert (a :: x ~=~ y) by auto.
apply PPermut_split_head in H;
destruct H as (l', (hd, (tl, (Ha, Hb)))).
subst.
assert (x & a ~=~  (hd ++ tl) & l').
  transitivity (a::x); [ | rewrite H0];
  PPermut_simpl.
apply PPermut_last_rev in H; auto.
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

Lemma ok_Bg_PPermut:
forall G G',
  ok_Bg G -> G ~=~ G' -> ok_Bg G'.
Admitted. (* This will be fun... it goes from ok_LF G U (for any U) but then..*)

Lemma ok_Bg_fresh:
forall G Gamma x A,
  ok_Bg (Gamma::G) ->
  x \notin (used_vars_ctx_LF (Gamma::G)) ->
  ok_Bg (((x, A) :: Gamma)::G).
Admitted.

Lemma ok_Bg_nil:
forall G,
  ok_Bg G ->
  ok_Bg (nil::G).
intros; unfold ok_Bg; rew_concat; rew_app; auto.
Qed.

Hint Resolve ok_Bg_nil.

Lemma ok_Bg_concat:
forall c1 c2 G0 G1 G2,
  c1::c2::G0 ~=~ G1 ->
  (c1++c2)::G0 ~=~ G2 ->
  ok_Bg G1 <-> ok_Bg G2.
Admitted.

Lemma ok_Bg_empty:
forall G,
  ok_Bg (emptyEquiv G).
Admitted.