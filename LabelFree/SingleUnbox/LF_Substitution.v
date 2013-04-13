Add LoadPath "../..".
Require Import PermutLib.
Require Import LF_Syntax.
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
| here_LF N' => here_LF [M//x]N'
| letdia_LF N' N'' => letdia_LF [M//x]N' [M//shift_vte x]N''
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
omega. omega.
Qed.

Lemma subst_t_comm_LF:
forall M v v' n N
  (Lc: lc_t_LF N),
  v <> v' ->
  [ N // fte v] ([ hyp_LF (fte v') // bte n] M) =
  [hyp_LF (fte v') // bte n] ([N // fte v] M).
induction M; intros; simpl;
[ repeat (case_if; simpl); auto;
  erewrite closed_subst_t_bound_LF; eauto; omega | | | | | |];
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

Lemma subst_t_comm2_LF:
forall M v' m n N
  (Neq: m <> n)
  (Lc: lc_t_LF N),
  subst_t_LF N (bte m) (subst_t_LF (hyp_LF (fte v')) (bte n) M) =
  subst_t_LF (hyp_LF (fte v')) (bte n) (subst_t_LF N (bte m) M).
induction M; intros; subst; simpl;
repeat (case_if; subst; simpl); auto;
try rewrite IHM; eauto; try omega.
rewrite closed_subst_t_bound_LF with (n:=0); auto; omega.
rewrite IHM1; eauto; rewrite IHM2; eauto; omega.
rewrite IHM1; eauto; rewrite IHM2; eauto; omega.
Qed.
