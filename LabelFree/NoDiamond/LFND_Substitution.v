Add LoadPath "../..".
Add LoadPath "..".
Require Import PermutLib.
Require Import LFND_Syntax.
Require Import Arith.
Require Export LibTactics. (* case_if *)

Open Scope permut_scope.

Reserved Notation " [ M // x ] N " (at level 5).

Fixpoint subst_t_LF M x N :=
match N with
| hyp_LF v => if (eq_vte_dec x v) then M else N
| lam_LF t N' => lam_LF t [M//shift_vte x]N'
| appl_LF N' N'' => appl_LF [M//x]N' [M//x]N''
| box_LF N' => box_LF [M//x]N'
| unbox_LF N' => unbox_LF [M//x]N'
end
where " [ M // x ] N " := (subst_t_LF M x N).

Definition open_LF (M: te_LF) (t: te_LF) := subst_t_LF t (bte 0) M.
Notation " M '^t^' t " := (open_LF M t) (at level 67).

Lemma closed_subst_t_free_LF:
forall M v0 N
  (H_lc: v0 \notin used_vars_te_LF N),
  [M // fte v0] N = N.
induction N; intros; simpl in *;
repeat case_if;
try (rewrite IHN || (rewrite IHN1; try rewrite IHN2); auto);
[ rewrite notin_singleton in H_lc; elim H_lc |
  destruct v]; auto.
Qed.

Lemma closed_subst_t_bound_LF:
forall N M v0 n
  (H_lc: lc_t_n_LF n N),
  v0 >= n -> [M // bte v0] N = N.
induction N; intros; simpl in *;
repeat case_if; inversion H_lc; subst;
try (erewrite IHN || (erewrite IHN1; try erewrite IHN2)); eauto.
assert (~(n = v0)) by omega;
apply gt_asym in H2; elim H2; omega.
omega.
Qed.

Lemma subst_t_comm_LF:
forall M v v' n N
  (Lc: lc_t_LF N),
  v <> v' ->
  [ N // fte v] ([ hyp_LF (fte v') // bte n] M) =
  [hyp_LF (fte v') // bte n] ([N // fte v] M).
induction M; intros; simpl;
[ repeat (case_if; simpl); auto;
  erewrite closed_subst_t_bound_LF; eauto; omega | | | | ];
try (rewrite IHM; auto);
try (rewrite IHM1; try rewrite IHM2; auto);
repeat (case_if; simpl); subst; simpl;
auto;
erewrite closed_subst_t_bound;
eauto;
replace n with (0+n) by omega;
apply closed_t_addition; auto.
Qed.

Lemma subst_t_neutral_free_LF:
forall M v n N
  (HT: v \notin used_vars_te_LF M),
  [ N // bte n] M = [N // fte v] [hyp_LF (fte v) // bte n] M.
induction M; intros; simpl in *;
try (erewrite IHM || (erewrite IHM1; try erewrite IHM2); eauto);
repeat (case_if; simpl); subst; auto;
assert (v0 <> v0) as Neq by eauto; elim Neq; auto.
Qed.

Lemma lc_t_subst_t_LF_bound:
forall M N n,
  lc_t_n_LF n N ->
  lc_t_n_LF (S n) M ->
  lc_t_n_LF n ([N//bte n] M).
induction M; intros; simpl in *; inversion H0; subst; repeat case_if;
try constructor; eauto.
assert (n <> v0) by (intro; subst; elim H1; auto); omega.
eapply IHM; auto; apply closed_t_succ_LF; auto.
Qed.

Lemma lc_t_subst_t_LF_free:
forall M N n v,
  lc_t_n_LF n N ->
  lc_t_n_LF n M ->
  lc_t_n_LF n ([N//fte v] M).
induction M; intros; simpl in *; inversion H0; subst; repeat case_if;
try constructor; eauto.
eapply IHM; eauto; apply closed_t_succ_LF; auto.
Qed.

Lemma lc_t_n_LF_subst_t:
forall N M n,
lc_t_n_LF n M ->
lc_t_n_LF n ([M // (bte n)] N) ->
lc_t_n_LF (S n) N.
induction N; intros; simpl in *; try destruct v; constructor;
repeat case_if; try inversion H1; subst; try omega;
inversion H0; subst; eauto.
apply IHN with (M:=M); eauto; apply closed_t_succ_LF; auto.
Qed.
