Add LoadPath "../..".
Require Export L_Syntax.
Require Import Arith.
Require Import LibList.
Require Import LibTactics. (* case_if *)

(* Term variable substitution *)
Reserved Notation " [ M // x ] N " (at level 5).

Fixpoint subst_t_L M x N :=
match N with
| hyp_L v => if (eq_nat_dec x v) then M else N
| lam_L t N' => lam_L t [M//S x]N'
| appl_L N' N'' => appl_L [M//x]N' [M//x]N''
| box_L N' => box_L [M//x]N'
| unbox_L N' => unbox_L [M//x]N'
| get_L w N' => get_L w [M//x]N'
| letdia_L N' N'' => letdia_L [M//x]N' [M//S x]N''
| here_L N' => here_L [M//x]N'
| fetch_L w N' => fetch_L w [M//x]N'
end
where " [ M // x ] N " := (subst_t_L M x N) : labeled_is5_scope.

Open Scope labeled_is5_scope.

(* Substitute L[0] for n, L[1] for n+1,.. in M *)
Fixpoint subst_list_L L n N :=
match L with
| nil => N
| M :: L' => [M//n] (subst_list_L L' (S n) N)
end.

(* World variable substitution *)
Reserved Notation " {{ w1 // w2 }} N " (at level 5).

Fixpoint subst_w_L w1 w2 N :=
match N with
| hyp_L v => hyp_L v
| lam_L t N' => lam_L t {{w1//w2}}N'
| appl_L N' N'' => appl_L {{w1//w2}}N' {{w1//w2}}N''
| box_L N' => box_L {{shift_vwo w1 // shift_vwo w2}} N'
| unbox_L N' => unbox_L {{w1//w2}}N'
| get_L w N' => get_L (if eq_vwo_dec w w2 then w1 else w) {{w1//w2}}N'
| letdia_L N' N'' =>
  letdia_L {{w1 // w2}} N' {{shift_vwo w1 // shift_vwo w2}} N''
| here_L N' => here_L {{w1//w2}}N'
| fetch_L w N' => fetch_L (if eq_vwo_dec w w2 then w1 else w) {{w1//w2}}N'
end
where " {{ w1 // w2 }} N " := (subst_w_L w1 w2 N) : labeled_is5_scope.

Definition open_w_L M w := subst_w_L w (bwo 0) M.
Notation " M ^ w " := (open_w_L M w) : labeled_is5_scope.

Section Substitution_lemmas.

Lemma no_unbound_worlds_subst_w_L_id:
forall M w n
  (H_unbound: unbound_worlds_L n M = nil),
  {{w//bwo n}}M = M.
intros;
generalize dependent w;
generalize dependent n;
induction M; intros; simpl in *;
try (rewrite IHM); try auto.
(* appl *)
apply app_eq_nil in H_unbound;
destruct H_unbound;
rewrite IHM1; try rewrite IHM2; auto.
(* get *)
destruct (eq_vwo_dec v (bwo n));
[ subst; discriminate | reflexivity ];
try (destruct v; [discriminate | assumption]).
destruct v; [discriminate | assumption].
(* letdia *)
destruct w;
inversion H_unbound; auto;
apply app_eq_nil in H_unbound;
destruct H_unbound;
rewrite IHM1; try rewrite IHM2; auto.
(* fetch *)
destruct (eq_vwo_dec v (bwo n));
[ subst; discriminate | reflexivity ];
try (destruct w; [discriminate | assumption]).
destruct v; [discriminate | assumption].
Qed.

Lemma closed_w_L_subst_id:
forall M w n
  (HT: lc_w_n_L M n),
  {{w//bwo n}} M = M.
intros;
apply no_unbound_worlds_subst_w_L_id;
apply closed_no_unbound_worlds_L;
assumption.
Qed.

Lemma subst_order_irrelevant_L:
forall N M n m w
  (H_LC: lc_w_L M),
  {{w//bwo m}}([M//n]N) = [M//n]({{w//bwo m}}N).
unfold open_w_L; intro;
induction N; intros; simpl; try (rewrite IHN; auto).
(* hyp *)
destruct (eq_nat_dec n0 n);
simpl.
  apply closed_w_L_subst_id;
  replace m with (0+m) by auto;
  apply closed_w_addition_L; assumption.
  reflexivity.
(* appl *)
rewrite IHN1; try rewrite IHN2; auto.
(* letdia *)
destruct w; rewrite IHN1; try rewrite IHN2; auto.
Qed.

Lemma subst_w_L_comm:
forall M w w' w'' n
  (Neq: w'' <> w),
  {{fwo w'//fwo w''}}({{fwo w//bwo n}}M) =
  {{fwo w//bwo n}}({{fwo w'//fwo w''}}M).
induction M; intros; simpl; try (rewrite IHM; auto).
(* hyp *)
reflexivity.
(* appl *)
rewrite IHM1; try rewrite IHM2; auto.
(* get *)
repeat case_if; subst; auto.
(* letd *)
rewrite IHM1; try rewrite IHM2; auto.
(* fetch *)
repeat case_if; subst; auto.
Qed.

Lemma subst_id:
forall M w n
  (HT: fresh_world_L w M),
  {{bwo n//fwo w}}({{fwo w//bwo n}}M) = M.
unfold fresh_world_L;
intros; generalize dependent n;
induction M; intros; simpl in *;
try (rewrite IHM; auto).
(* hyp *)
reflexivity.
(* appl *)
apply notin_union in HT;
destruct HT;
rewrite IHM1; try rewrite IHM2; auto.
(* get *)
repeat case_if; subst; auto.
  subst; apply notin_union in HT; destruct HT;
  elim H; rewrite in_singleton; reflexivity.
destruct v; auto.
(* letdia *)
apply notin_union in HT;
destruct HT;
rewrite IHM1; try rewrite IHM2; auto.
(* fetch *)
repeat case_if; subst; auto.
  subst; apply notin_union in HT; destruct HT;
  elim H; rewrite in_singleton; reflexivity.
destruct v; auto.
Qed.

Lemma subst_neutral_L:
forall M w w' n
  (HT: lc_w_n_L M n),
  {{fwo w//bwo n}}({{bwo n//fwo w'}}M) = {{fwo w//fwo w'}}M.
intros; generalize dependent n;
induction M; intros; simpl;
inversion HT; subst;
try rewrite IHM;
try (rewrite IHM1; try rewrite IHM2);
auto;
repeat case_if; subst; auto.
Qed.

Lemma closed_step_opening_L:
forall M n w
  (HT: lc_w_n_L M (S n)),
  lc_w_n_L ({{fwo w//bwo n}}M) n.
intros; generalize dependent n; induction M;
intros; inversion HT; subst; simpl;
eauto using lc_w_n_L;
repeat case_if; subst; auto;
constructor; auto.
Qed.

End Substitution_lemmas.

Close Scope labeled_is5_scope.