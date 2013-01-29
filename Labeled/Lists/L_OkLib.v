Add LoadPath "../..".
Require Import L_Syntax.
Require Import PermutLib.
Require Import LibTactics. (* case_if *)

Open Scope permut_scope.

Fixpoint ok_Gamma_L (G: ctx_L) (Used: list var) : Prop :=
match G with
| nil => True
| (w, (v, A)) :: G' => ~ Mem v Used /\ ok_Gamma_L G' (v::Used)
end.

Fixpoint ok_Omega_L (L: list var) : Prop :=
match L with
| nil => True
| l :: L' => ~ Mem l L' /\ ok_Omega_L L'
end.

Lemma ok_Gamma_L_used_permut:
forall G U U',
  U *=* U' -> ok_Gamma_L G U -> ok_Gamma_L G U'.
induction G; intros.
destruct U'; econstructor; eauto.
destruct a; destruct p; simpl in *; destruct H0; split.
intro n; elim H0; apply Mem_permut with (l:=U'); [ symmetry | ]; auto.
eapply IHG; eauto.
Qed.

Lemma ok_Gamma_L_weakening_used:
forall G U u,
  ok_Gamma_L G (u::U) ->
  ok_Gamma_L G U.
induction G; intros; try constructor.
destruct a; destruct p; simpl in *; destruct H; split.
intro; elim H; rewrite Mem_cons_eq; right; auto.
apply ok_Gamma_L_used_permut with (U' := (u::v0::U)) in H0;
[ | permut_simpl]; apply IHG with (u:=u); auto.
Qed.

Lemma ok_Gamma_L_permut:
forall G1 G2 U,
  G1 *=* G2 -> ok_Gamma_L G1 U -> ok_Gamma_L G2 U.
induction G1; intros.
apply permut_nil_eq in H; subst; auto.
destruct a; destruct p; simpl in *; destruct H0.
assert ((v, (v0, t))::G1 *=* G2) by auto.
apply permut_split_head in H.
destruct H as (hd, (tl, H)).
assert (G1 *=* hd ++ tl).
  apply permut_cons_inv with (a:=(v, (v0, t))); rewrite H2; subst; permut_simpl.
specialize IHG1 with (G2:=hd++tl).
apply IHG1 in H1; auto.
subst; generalize dependent G1; generalize dependent U;
induction hd; intros; rew_app in *.
constructor; auto.
destruct a; destruct p; simpl in *; destruct H1; split.
intro; elim H; rewrite Mem_cons_eq; right; auto.
apply IHhd with (G1:=hd++tl); try permut_simpl.
intro n; elim H; rewrite Mem_cons_eq in n; destruct n; rewrite Mem_cons_eq;
[left; subst; auto | contradiction].
apply ok_Gamma_L_used_permut with (U:=v2::v0::U); [permut_simpl | auto].
intros; auto.
Qed.

Lemma ok_Omega_L_permut:
forall O1 O2,
  O1 *=* O2 -> ok_Omega_L O1 -> ok_Omega_L O2.
induction O1; intros.
apply permut_nil_eq in H; subst; auto.
simpl in *; destruct H0.
assert (a::O1 *=* O2) by auto.
apply permut_split_head in H.
destruct H as (hd, (tl, H)). subst.
assert (O1 *=* hd ++ tl).
  apply permut_cons_inv with (a:=a); rewrite H2; subst; permut_simpl.
specialize IHO1 with (O2:=hd++tl).
apply IHO1 in H1; auto.
subst; generalize dependent O1;
induction hd; intros; rew_app in *.
constructor; auto. intro n; apply Mem_permut with (l':= O1) in n;
[ contradiction | symmetry; auto].
simpl in *; destruct H1; split.
intro n; rewrite Mem_app_or_eq in n; destruct n.
elim H1; rewrite Mem_app_or_eq; left; auto.
rewrite Mem_cons_eq in H4; destruct H4; subst.
elim H0. apply Mem_permut with (l:=a::hd++tl).
symmetry; auto. rewrite Mem_cons_eq; left; auto.
elim H1; rewrite Mem_app_or_eq; right; auto.
apply IHhd with (O1:=hd++tl); try permut_simpl; auto.
intro n. elim H0. apply Mem_permut with (l:=a0::hd++tl).
symmetry; auto. rewrite Mem_cons_eq; right; auto.
Qed.

Definition ok_L Omega Gamma := ok_Omega_L Omega /\ ok_Gamma_L Gamma nil.

Lemma ok_L_permut:
forall O O' G G', O *=* O' -> G *=* G' -> ok_L O G -> ok_L O' G'.
intros; destruct H1; split;
[eapply ok_Omega_L_permut | eapply ok_Gamma_L_permut]; eauto.
Qed.

Lemma ok_Gamma_L_extend_fresh:
forall G U x w A,
  ok_Gamma_L G U ->
  x \notin used_vars_context_L G ->
  ~ Mem x U ->
  ok_Gamma_L ((w, (x, A))::G) U.
induction G; intros; simpl in *; split; auto;
destruct a; destruct p; destruct H; split.
rewrite Mem_cons_eq; intro n; destruct n; subst.
unfold used_vars_context_L in H0; rew_map in *; simpl in *;
rewrite from_list_cons in H0; rewrite notin_union in H0; destruct H0;
apply notin_singleton in H0; elim H0; auto.
contradiction.
apply ok_Gamma_L_used_permut with (U:=x::v0::U). permut_simpl.
apply IHG; auto.
unfold used_vars_context_L in *; rew_map in *; simpl in *;
rewrite from_list_cons in H0; rewrite notin_union in H0; destruct H0; auto.
rewrite Mem_cons_eq; intro n; destruct n; subst; try contradiction.
unfold used_vars_context_L in *; rew_map in *; simpl in *;
rewrite from_list_cons in H0; rewrite notin_union in H0; destruct H0;
apply notin_singleton in H0; elim H0; auto.
Qed.

Lemma ok_L_extend_fresh:
forall O G x w A,
  ok_L O G ->
  x \notin used_vars_context_L G ->
  ok_L O ((w, (x, A))::G).
unfold ok_L; intros; destruct H; split; auto.
apply ok_Gamma_L_extend_fresh; auto.
rewrite Mem_nil_eq; tauto.
Qed.

Lemma ok_L_Mem_contradiction:
forall w x A Gamma Omega B,
  Mem (w, (x, A)) Gamma ->
  ok_L Omega ((w, (x, B)) :: Gamma) ->
  False.
unfold ok_L; intros; simpl in *; destruct H0; destruct H1.
apply Mem_split in H; destruct H as (hd, (tl, H)); subst.
apply ok_Gamma_L_permut with (G2:=(w, (x,A))::hd++tl) in H2.
simpl in H2; destruct H2.
elim H; apply Mem_here.
permut_simpl.
Qed.

Lemma ok_L_smaller_Gamma:
forall O X w x a,
  ok_L O ((w, (x, a)) :: X)  ->
  ok_L O X.
unfold ok_L; intros; split; destruct H; auto.
simpl in *; destruct H0; apply ok_Gamma_L_weakening_used with (u:=x); auto.
Qed.

Lemma ok_L_smaller_Omega:
forall O X w,
  ok_L (w::O) X ->
  ok_L O X.
unfold ok_L; intros; split; destruct H; auto;
inversion H; auto.
Qed.

Lemma ok_L_Mem_contr:
forall X w x a U,
  ok_Gamma_L ((w, (x, a)) :: X) U  ->
  forall w' b, ~ Mem (w', (x, b)) X.
intros; intro n; simpl in *; destruct H.
apply Mem_split in n; destruct n as (hd, (tl, n)); subst.
apply ok_Gamma_L_permut with (G2:= (w', (x, b))::hd ++ tl) in H0;
[|permut_simpl]; simpl in *; destruct H0; elim H0; apply Mem_here.
Qed.

Fixpoint rename_context_L (w: var) (w': var) (C: ctx_L) :=
match C with
| nil => nil
| (w0, (x, A)) :: C'  =>
  let w1 := if (eq_var_dec w0 w) then w' else w0 in
    (w1, (x, A)) :: (rename_context_L w w' C')
end.

Lemma ok_Gamma_L_rename:
forall G U w w',
  ok_Gamma_L G U ->
  ok_Gamma_L (rename_context_L w w' G) U.
induction G; intros; simpl in *; auto;
destruct a; destruct p; simpl in *; destruct H; split; auto.
Qed.

Lemma ok_L_rename:
forall Omega Gamma w w',
  ok_L Omega Gamma ->
  ok_L Omega (rename_context_L w w' Gamma).
unfold ok_L; split; destruct H; auto;
apply ok_Gamma_L_rename; auto.
Qed.

Lemma Mem_rename_context_L:
forall Gamma x A w w' w0 w1,
  Mem (w, (x, A)) Gamma ->
  w' = (if (eq_var_dec w0 w) then w1 else w) ->
  Mem (w', (x, A)) (rename_context_L w0 w1 Gamma).
induction Gamma; intros; simpl in *; [| destruct a; destruct p].
rewrite Mem_nil_eq in H; tauto.
repeat case_if; subst;
rewrite Mem_cons_eq in H; rewrite Mem_cons_eq; destruct H.
  inversion H; subst; left; auto.
  right; apply IHGamma with (w:=w); auto; case_if; auto.
  inversion H; subst; elim H1; auto.
  right; apply IHGamma with (w:=w); auto; case_if; auto.
  inversion H; subst; elim H1; auto.
  right; apply IHGamma with (w:=w); auto; case_if; auto.
  inversion H; subst; left; auto.
  right; apply IHGamma with (w:=w); auto; case_if; auto.
Qed.