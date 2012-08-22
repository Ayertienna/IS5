Require Export LFSyntax.
Require Export LibLogic. (* If *)
Require Export LibTactics. (* case_if *)

(* Notation for term substitution *)
Global Reserved Notation " [ M // v ] N " (at level 5).

(* Notation for world substitution *)
Global Reserved Notation " {{ w1 // w2 }} N " (at level 5).


(*** Definitions ***)


(*
Term substitution
  Simple term substitution, very similar to the one in simple lambda calculus.
*)
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


(*
Context substitution (or rather world substitution)
  Replaces one world with another. Since both of the worlds can be free or
  bound, we need to use shift operation on both sides for box and letdia cases.
*)
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


(* Opening is defined in terms of substitution *)

Definition open_var (M: te_LF) (t: te_LF) := subst_t t (bte 0) M.

Definition open_ctx M ctx := subst_ctx M ctx (bwo 0).

Notation " M '^t^' t " := (open_var M t) (at level 5) : label_free_is5_scope.
Notation " M ^w^ w  " := (open_ctx M w) (at level 10) : label_free_is5_scope.

Open Scope label_free_is5_scope.

(*
Property: term is locally closed
 This means that there are no bound variables.
*)

Inductive lc_w_LF : te_LF -> Prop :=
 | lcw_hyp_LF: forall v, lc_w_LF (hyp_LF v)
 | lcw_lam_LF: forall L t M,
     forall x, x \notin L -> lc_w_LF (M ^t^ (hyp_LF x)) ->
     lc_w_LF (lam_LF t M)
 | lcw_appl_LF: forall M N,
     lc_w_LF M -> lc_w_LF N ->
     lc_w_LF (appl_LF M N)
 | lcw_box_LF: forall M,
     lc_w_LF M ->
     lc_w_LF (box_LF M)
 | lcw_unbox_fetch_LF: forall M w,
     lc_w_LF M ->
     lc_w_LF (unbox_fetch_LF (fwo w) M)
 | lcw_get_here_LF: forall M w,
     lc_w_LF M ->
     lc_w_LF (get_here_LF (fwo w) M)
 | lcw_letdia_get_LF: forall L M N w,
     forall x, x \notin L -> lc_w_LF (N ^t^ (hyp_LF x)) -> lc_w_LF M ->
     lc_w_LF (letdia_get_LF (fwo w) M N)
.

Inductive lc_t_LF: te_LF -> Prop :=
| lct_hyp_LF: forall v, lc_t_LF (hyp_LF (fte v))
| lct_lam_LF: forall t M,
    lc_t_LF M ->
    lc_t_LF (lam_LF t M)
| lct_appl_LF: forall M N,
    lc_t_LF M -> lc_t_LF N ->
    lc_t_LF (appl_LF M N)
 | lct_box_LF: forall L M,
     forall w, w \notin L -> lc_t_LF (M ^w^ w) ->
     lc_t_LF (box_LF M)
 | lct_unbox_fetch_LF: forall M w,
     lc_t_LF M ->
     lc_t_LF (unbox_fetch_LF (fwo w) M)
 | lct_get_here_LF: forall M w,
     lc_t_LF M ->
     lc_t_LF (get_here_LF (fwo w) M)
 | lct_letdia_get_LF: forall L M N w,
     forall w', w' \notin L -> lc_t_LF (N ^w^ w') -> lc_t_LF M ->
     lc_t_LF (letdia_get_LF (fwo w) M N)
.


(*** Properties ***)


Lemma closed_var_subst_ctx:
forall M w w',
  lc_t_LF M = lc_t_LF ({{w //w'}} M).
Admitted.

Lemma closed_ctx_subst_var:
forall M N k
  (H: lc_w_LF N),
  lc_w_LF M = lc_w_LF ([N // k] M).
Admitted.

(*
Simplify substitution in special cases
  * when substitution is identity substitution
  * when the variable for which we try to substitute does not occur in the term
  * when term is closed and we try to substitute for bound variable
*)


(* We effectively make identity substitution *)

Lemma subst_w_id:
forall M w,
  {{w // w}} M = M.
induction M; intros; simpl in *;
repeat case_if; subst; auto;
rewrite IHM || (rewrite IHM1; try rewrite IHM2);
auto.
Qed.

Lemma subst_w_2_step_id:
forall M w n
  (HT: w \notin free_worlds_LF M),
  {{bwo n//fwo w}}({{fwo w//bwo n}}M) = M.
induction M; intros; simpl in *;
repeat case_if; subst; auto;
rewrite IHM || (rewrite IHM1; try rewrite IHM2);
try destruct v; auto;
assert (w <> w) as Neq by eauto; elim Neq; auto.
Qed.


(* There are no bound variables and we try to substitute for one *)

Lemma no_bound_vars_subst_t_id:
forall N M n
  (H_bound: bound_vars N = nil),
  [M//bte n] N = N.
induction N; intros; simpl in *;
repeat case_if; auto;
rewrite IHN || (rewrite IHN1; try rewrite IHN2); auto;
apply app_eq_nil_inv in H_bound;
destruct H_bound; auto.
Qed.

Lemma no_bound_worlds_subst_w_id:
forall M n w
  (H_bound: bound_worlds M = nil),
  {{ w // bwo n }} M = M.
induction M; intros; simpl in *;
repeat case_if; auto;
rewrite IHM || (rewrite IHM1; try rewrite IHM2); auto;
try (destruct v; subst);
(apply app_eq_nil_inv in H_bound; destruct H_bound) || auto;
discriminate || auto.
Qed.


(* Term is closed and we try to substitute for bound variable *)

Lemma closed_subst_t_id:
forall M n N
  (H_lc: lc_t_LF N),
  [ M // bte n ] N = N.
intros; apply no_bound_vars_subst_t_id.
induction N; simpl;
try destruct v; inversion H_lc; subst; eauto.
rewrite IHN1; try rewrite IHN2; simpl; auto.
apply IHN; unfold open_ctx in *; simpl; erewrite closed_var_subst_ctx; eauto.
rewrite IHN1; try rewrite IHN2; simpl; auto;
erewrite closed_var_subst_ctx; eauto.
Qed.

Lemma closed_subst_w_id:
forall M w n
  (H_lc: lc_w_LF M),
  {{w // bwo n}} M  = M.
intros;
apply no_bound_worlds_subst_w_id;
induction M; simpl;
try destruct v; inversion H_lc; subst; eauto.
apply IHM; unfold open_var in *; erewrite closed_ctx_subst_var;
eauto; constructor.
rewrite IHM1; try rewrite IHM2; simpl; auto.
rewrite IHM1; try rewrite IHM2; simpl; auto;
erewrite closed_ctx_subst_var; eauto; constructor.
Qed.


(* Free variable for which we substitute does not occur in the term *)
Lemma closed_subst_w_free:
forall M w w'
  (H_lc: w' \notin free_worlds_LF M),
  {{w // fwo w'}} M  = M.
induction M; intros; simpl in *;
repeat case_if; auto;
rewrite IHM || (rewrite IHM1; try rewrite IHM2); auto;
try (destruct v; subst); auto;
assert (w' <> w') as Neq by eauto; elim Neq; auto.
Qed.


(* Properties of substitution: commutativity *)

Lemma subst_w_comm:
forall M w w' w'' n
  (Neq: w'' <> w),
  {{fwo w'//fwo w''}}({{fwo w//bwo n}}M) =
  {{fwo w//bwo n}}({{fwo w'//fwo w''}}M).
induction M; intros; simpl;
repeat case_if; subst; simpl; auto;
rewrite IHM || (rewrite IHM1; try rewrite IHM2);
auto.
Qed.

Lemma subst_t_comm:
forall M v v' n N
  (Neq: v <> v')
  (Lc: lc_t_LF N),
  [ N // fte v] ([ hyp_LF (fte v') // bte n] M) =
  [hyp_LF (fte v') // bte n] ([N // fte v] M).
induction M; intros; simpl;
try (rewrite IHM || (rewrite IHM1; try rewrite IHM2); auto);
repeat (case_if; simpl); subst; simpl; auto;
rewrite closed_subst_t_id; auto.
Qed.


(* Properties of substitution: expansion with neutral element *)

Lemma subst_w_neutral_free:
forall M w w' w0
  (HT: w0 \notin free_worlds_LF M),
  {{w//fwo w0}}({{fwo w0// w'}}M) = {{w//w'}}M.
induction M; intros; simpl in *;
repeat case_if; subst; simpl; auto;
try destruct w; try destruct w'; try destruct v; subst;
rewrite IHM || (rewrite IHM1; try rewrite IHM2);
auto;
assert (w0 <> w0) as Neq by eauto; elim Neq; auto.
Qed.

Lemma subst_t_neutral_free:
forall M v n N
  (HT: v \notin free_vars_LF M),
  [ N // bte n] M = [N // fte v] [hyp_LF (fte v) // bte n] M.
induction M; intros; simpl in *;
try (erewrite IHM || (erewrite IHM1; try erewrite IHM2); eauto);
repeat (case_if; simpl); subst; auto;
assert (v0 <> v0) as Neq by eauto; elim Neq; auto.
Qed.

Lemma subst_w_neutral_bound:
forall M w w' n
  (HT: lc_w_LF M),
  {{w//bwo n}}({{bwo n// w'}}M) = {{w//w'}}M.
induction M; intros; simpl in *; auto;
inversion HT; repeat case_if; subst;
rewrite IHM || (rewrite IHM1; try rewrite IHM2); auto;
unfold open_var;
erewrite closed_ctx_subst_var; eauto; constructor.
Qed.


(* With two different types of substitution, the order does not matter *)

Lemma subst_order_irrelevant_bound:
forall N w M v m
  (HT_M: lc_w_LF M),
    [M // v ] ({{w // bwo m}} N)  =
    {{w // bwo m}} ([M // v ] N).
induction N; intros; simpl in *;
repeat case_if; simpl;
unfold shift_vte in *; unfold shift_vwo in *;
try destruct v; try destruct w; auto;
try rewrite IHN; try (rewrite IHN1; try rewrite IHN2);
auto; rewrite closed_subst_w_id; auto.
Qed.

Lemma subst_order_irrelevant_free:
forall N w w' M v
  (HT_M: w' \notin (free_worlds_LF M)),
    [M // v ] ({{w // fwo w'}} N)  =
    {{w // fwo w'}} ([M // v ] N).
induction N; intros; simpl in *;
repeat case_if; simpl;
unfold shift_vwo in *;
try destruct c; try destruct v; auto;
try rewrite IHN; try (rewrite IHN1; try rewrite IHN2);
auto; rewrite closed_subst_w_free; auto.
Qed.


(*
   Substitution of one type does not change the set of free variables
   of the other type.
*)

Lemma subst_var_preserv_free_worlds:
forall N v k w,
  w \notin free_worlds_LF N ->
  w \notin free_worlds_LF [ hyp_LF (fte v) // bte k ] N.
induction N; intros; simpl in *;
repeat case_if;try destruct v;
simpl; auto.
Qed.

Lemma subst_world_preserv_free_vars:
forall N w w' v,
  v \notin free_vars_LF N ->
  v \notin free_vars_LF {{w // w'}} N.
induction N; intros; simpl in *;
repeat case_if; try destruct c;
simpl; auto.
Qed.

Close Scope label_free_is5_scope.