Require Export LFSyntax.
Require Import LibLogic. (* If *)
Require Import LibList.
Require Import LibTactics. (* case_if *)

Global Reserved Notation " [ M // v ] N " (at level 5).
Global Reserved Notation " {{ w1 // w2 }} N " (at level 5).

(* Term substitution *)

Fixpoint subst_t (M0: te_LF) (v0: vte) (N0: te_LF) :=
match N0 with
| hyp_LF v => 
    if (eq_vte_dec v v0) then M0 else N0
| lam_LF A M => 
    lam_LF A ([M0 // shift_vte v0] M) 
| appl_LF M N => 
    appl_LF ([M0//v0]M) ([M0//v0]N)
| box_LF M => 
    box_LF ([M0//v0]M)
| unbox_fetch_LF w M =>
    unbox_fetch_LF w ([M0//v0]M)
| get_here_LF w M =>
    get_here_LF w ([M0//v0]M)
| letdia_get_LF w M N =>
    letdia_get_LF w ([M0//v0]M) ([M0//shift_vte v0]N)
end
where " [ M // v ] N " := (subst_t M v N) : label_free_is5_scope.

Definition open_var (M: te_LF) (t: te_LF) := subst_t t (bte 0) M.
Notation " M '^t^' t " := (open_var M t) (at level 5) : label_free_is5_scope.

Open Scope label_free_is5_scope.

(* Context substitution *)

Fixpoint subst_ctx (M0 : te_LF) (ctx1: vwo) (ctx2: vwo) := 
match M0 with 
| hyp_LF n => hyp_LF n
| lam_LF A M => lam_LF A ({{ctx1//ctx2}}M)
| appl_LF M N => appl_LF ({{ctx1//ctx2}}M) ({{ctx1//ctx2}}N)
| box_LF M =>  
  box_LF ({{ shift_vwo ctx1 // shift_vwo ctx2 }} M)
| unbox_fetch_LF w M =>
  let w' := If w = ctx2 then ctx1 else w in
    unbox_fetch_LF w' ({{ctx1//ctx2}} M)
| get_here_LF w M =>
  let w' := If w = ctx2 then ctx1 else w in
    get_here_LF w' ({{ctx1//ctx2}}M)
| letdia_get_LF w M N =>
  let w' := If w = ctx2 then ctx1 else w in
    letdia_get_LF w' ({{ctx1//ctx2}} M) ({{shift_vwo ctx1 // shift_vwo ctx2}} N)
end
where " {{ w1 // w2 }} M " := (subst_ctx M w1 w2) : label_free_is5_scope.

Definition open_ctx M ctx := subst_ctx M ctx (bwo 0).
Notation " M ^w^ w  " := (open_ctx M w) (at level 10) : label_free_is5_scope.


Section Lemmas.

Lemma subst_w_w:
forall M w,
  {{w // w}} M = M.
induction M; intros; simpl in *;
try (case_if; subst);
try (rewrite IHM);
try (rewrite IHM1; try rewrite IHM2; auto);
auto.
Qed.

Lemma no_unbound_vars_LF_subst_var_id:
forall N M n
  (H_unbound: unbound_vars n N = nil),
  [M//bte n] N = N.
induction N; intros; simpl in *;
try rewrite IHN; auto;
[ case_if; simpl in *; subst; auto | |];
apply app_eq_nil_inv in H_unbound;
destruct H_unbound;
rewrite IHN1;
try rewrite IHN2; eauto.
Qed.

Lemma no_unbound_worlds_LF_subst_ctx_id_bound:
forall M n w
  (H_unbound: unbound_worlds n M = nil),
  {{ w // bwo n }} M = M.
induction M; intros; simpl in *.
reflexivity.
rewrite IHM; auto.
rewrite IHM1; try rewrite IHM2; auto. 
apply app_eq_nil_inv in H_unbound; destruct H_unbound; auto.
apply app_eq_nil_inv in H_unbound; destruct H_unbound; auto.
rewrite IHM; auto.
case_if; subst.
  inversion H_unbound.
  rewrite IHM; auto; destruct v; try inversion H_unbound; auto.
case_if; subst.
  inversion H_unbound.
  rewrite IHM; auto; destruct v; try inversion H_unbound; auto.
case_if; subst.
  inversion H_unbound.
  rewrite IHM1; try rewrite IHM2; auto;
  destruct v. 
    inversion H_unbound.
    apply app_eq_nil_inv in H_unbound; destruct H_unbound; auto.
    inversion H_unbound.
    apply app_eq_nil_inv in H_unbound; destruct H_unbound; auto.
Qed.

Lemma no_unbound_worlds_LF_subst_ctx_id_free:
forall M w w'
  (H_free: w' \notin free_worlds_LF M),
  {{ w // fwo w' }} M = M.
induction M; intros; simpl in *.
reflexivity.
rewrite IHM; auto.
rewrite IHM1; try rewrite IHM2; auto.
rewrite IHM; auto.
case_if; subst.
  rewrite notin_union in H_free; 
  destruct H_free; rewrite notin_singleton in *;
  elim H; reflexivity.
  destruct v; rewrite IHM; auto.
  destruct v; rewrite IHM; auto.
case_if; try destruct v; subst.
  reflexivity.
  case_if. inversion H; subst.
  rewrite notin_union in H_free; 
  destruct H_free; rewrite notin_singleton in *;
  elim H0; reflexivity.
  auto.
case_if; try destruct v; subst.  
  rewrite notin_union in H_free; 
  destruct H_free; rewrite notin_singleton in *;
  elim H; reflexivity.
  rewrite IHM1; try rewrite IHM2; auto.
  rewrite IHM1; try rewrite IHM2; auto.
Qed.

Lemma closed_var_subst_var_id:
forall M n N
  (H_lc: lc_t_n_LF N n),
  [ M // bte n ] N = N.
intros;
apply no_unbound_vars_LF_subst_var_id;
apply closed_t_no_unbound_vars;
auto.
Qed.

Lemma closed_ctx_subst_ctx_id_free:
forall M w w'
  (H_lc: w' \notin free_worlds_LF M),
  {{w // fwo w'}} M  = M.
intros;
apply no_unbound_worlds_LF_subst_ctx_id_free;
auto.
Qed.

Lemma closed_ctx_subst_ctx_id_bound:
forall M w n
  (H_lc: lc_w_n_LF M n),
  {{w // bwo n}} M  = M.
intros;
apply no_unbound_worlds_LF_subst_ctx_id_bound;
apply closed_w_no_unbound_worlds;
auto.
Qed.

Lemma subst_ctx_comm:
forall M w w' w'' n
  (Neq: w'' <> w),
  {{fwo w'//fwo w''}}({{fwo w//bwo n}}M) = 
  {{fwo w//bwo n}}({{fwo w'//fwo w''}}M).
induction M; intros; simpl;
repeat case_if; subst; simpl;
try rewrite IHM;
try (rewrite IHM1; try rewrite IHM2);
auto.
Qed.

Lemma subst_var_comm:
forall M v v' n N
  (Neq: v <> v')
  (Lc: lc_t_LF N),
  [ N // fte v] ([ hyp_LF (fte v') // bte n] M) =
  [hyp_LF (fte v') // bte n] ([N // fte v] M).
induction M; intros; simpl;
try (rewrite IHM; auto);
try (rewrite IHM1; try rewrite IHM2; auto);
repeat (case_if; simpl); subst; simpl;
auto;
rewrite closed_var_subst_var_id;
auto;
replace n with (0+n) by omega;
apply closed_t_addition; auto.
Qed.

Lemma subst_ctx_id:
forall M w n
  (HT: w \notin free_worlds_LF M),
  {{bwo n//fwo w}}({{fwo w//bwo n}}M) = M.
induction M; intros; simpl in *.
reflexivity.
rewrite IHM; auto.
rewrite IHM1; try rewrite IHM2; auto.
rewrite IHM; auto.
repeat case_if; subst.
  rewrite IHM; auto.
  rewrite notin_union in HT; 
  destruct HT; rewrite notin_singleton in *;
  elim H; reflexivity.
  destruct v; rewrite IHM; auto.
repeat case_if; subst.
  rewrite IHM; auto.
  rewrite notin_union in HT; 
  destruct HT; rewrite notin_singleton in *;
  elim H; reflexivity.
  destruct v; rewrite IHM; auto.
repeat case_if; subst.
  rewrite IHM1; try rewrite IHM2; auto.
  rewrite notin_union in HT; 
  destruct HT; rewrite notin_singleton in *;
  elim H; reflexivity.
  destruct v; rewrite IHM1; try rewrite IHM2; auto.
Qed.

Lemma subst_ctx_neutral_free:
forall M w w' w0
  (HT: w0 \notin free_worlds_LF M),
  {{w//fwo w0}}({{fwo w0// w'}}M) = {{w//w'}}M.
induction M; intros; simpl in *.
reflexivity.
rewrite IHM; auto.
rewrite IHM1; try rewrite IHM2; auto.
rewrite IHM; auto.
repeat case_if; subst.
  destruct w'; rewrite IHM; auto.
  rewrite notin_union in HT; 
  destruct HT; rewrite notin_singleton in *;
  elim H; reflexivity.
  destruct v; rewrite IHM; auto.
repeat case_if; subst.
  destruct w'; rewrite IHM; auto.
  rewrite notin_union in HT; 
  destruct HT; rewrite notin_singleton in *;
  elim H; reflexivity.
  destruct v; rewrite IHM; auto.
repeat case_if; subst.
  destruct w'; rewrite IHM1; try rewrite IHM2; auto.
  rewrite notin_union in HT; 
  destruct HT; rewrite notin_singleton in *;
  elim H; reflexivity.
  destruct v; rewrite IHM1; try rewrite IHM2; auto.
Qed.

Lemma subst_var_neutral_free:
forall M v n N 
  (HT: v \notin free_vars_LF M),
  [ N // bte n] M = [N // fte v] [hyp_LF (fte v) // bte n] M.
induction M; intros; simpl in *;
try (rewrite notin_union in HT; destruct HT);
try erewrite IHM;
try (erewrite IHM1; try erewrite IHM2; eauto);
eauto;
case_if; simpl; case_if; auto;
subst; rewrite notin_singleton in HT; elim HT; auto.
Qed.

Lemma subst_ctx_neutral_bound:
forall M w w' n
  (HT: lc_w_n_LF M n),
  {{w//bwo n}}({{bwo n// w'}}M) = {{w//w'}}M.
induction M; intros; simpl in *;
try (destruct v); repeat case_if;
inversion HT; subst;
try rewrite IHM;
try (rewrite IHM1; try rewrite IHM2);
auto.
Qed.

Lemma closed_ctx_step_opening:
forall M n w
  (HT: lc_w_n_LF M (S n)),
  lc_w_n_LF ({{fwo w//bwo n}}M) n.
induction M; intros; inversion HT; subst;
simpl in *; eauto using lc_w_n_LF;
case_if; simpl; constructor; eauto.
Qed.

Lemma subst_order_irrelevant_bound:
forall N w M v m
  (HT_M: lc_w_LF M),
    [M // v ] ({{w // bwo m}} N)  = 
    {{w // bwo m}} ([M // v ] N). 
induction N; intros; simpl in *;
(* hyp *)
try (case_if;
  [ rewrite closed_ctx_subst_ctx_id_bound |
    simpl]; auto;
  replace m with (0+m) by omega;
  eapply closed_w_addition;
  auto);
unfold shift_vte in *;
unfold shift_vwo in *;
destruct v;
try destruct w;
try rewrite IHN;
try (rewrite IHN1; try rewrite IHN2);
auto.
Qed.

Lemma subst_order_irrelevant_free:
forall N w w' M v
  (HT_M: w' \notin (free_worlds_LF M)),
    [M // v ] ({{w // fwo w'}} N)  = 
    {{w // fwo w'}} ([M // v ] N). 
induction N; intros; simpl in *; unfold shift_vwo in *;
try ( (* hyp *)
  case_if;
  [ rewrite closed_ctx_subst_ctx_id_free |
    simpl]; auto;
  replace m with (0+m) by omega;
  eapply closed_w_addition;
  auto);
try destruct c; 
try destruct v;
try rewrite IHN;
try (rewrite IHN1; try rewrite IHN2);
auto.
Qed.

Lemma subst_var_preserv_free_worlds:
forall N v k w,
  w \notin free_worlds_LF N ->
  w \notin free_worlds_LF [ hyp_LF (fte v) // bte k ] N.
induction N; intros;
simpl in *;
repeat case_if;
try destruct v;
simpl;
auto.
Qed.

Lemma subst_world_preserv_free_vars:
forall N w w' v,
  v \notin free_vars_LF N ->
  v \notin free_vars_LF {{w // w'}} N.
induction N; intros;
simpl in *;
repeat case_if;
try destruct c;
simpl;
auto.
Qed.

End Lemmas.

Close Scope label_free_is5_scope.