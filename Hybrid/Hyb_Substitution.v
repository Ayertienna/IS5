Add LoadPath "..".
Require Export Hyb_Syntax.
Require Export LibTactics. (* case_if *)
Require Import Gt.


(* Notation for term substitution *)
Global Reserved Notation " [ M // v ] N " (at level 5).

(* Notation for world substitution *)
Global Reserved Notation " {{ w1 // w2 }} N " (at level 5).


(*** Definitions ***)


(*
Term substitution
  Simple term substitution, very similar to the one in simple lambda calculus.
  We assume here that the term M0 is locally closed, that is it does not
  require any shifts.
*)
Fixpoint subst_t_Hyb (M0: te_Hyb) (v0: vte) (N0: te_Hyb) :=
match N0 with
| hyp_Hyb v =>
    if (eq_vte_dec v v0) then M0 else N0
| lam_Hyb A M =>
    lam_Hyb A ([M0 // shift_vte v0] M)
| appl_Hyb M N =>
    appl_Hyb ([M0//v0]M) ([M0//v0]N)
| box_Hyb M =>
    box_Hyb ([M0//v0]M)
| unbox_fetch_Hyb w M =>
    unbox_fetch_Hyb w ([M0//v0]M)
| get_here_Hyb w M =>
    get_here_Hyb w ([M0//v0]M)
| letdia_get_Hyb w M N =>
    letdia_get_Hyb w ([M0//v0]M) ([M0//shift_vte v0]N)
end
where " [ M // v ] N " := (subst_t_Hyb M v N) : hybrid_is5_scope.


(*
World substitution
  Replaces one world with another. Since both of the worlds can be free or
  bound, we need to use shift operation on both sides for box and letdia cases.
*)
Fixpoint subst_w_Hyb (w1: vwo) (w2: vwo) (M0: te_Hyb) :=
match M0 with
| hyp_Hyb n => hyp_Hyb n
| lam_Hyb A M => lam_Hyb A ({{w1//w2}}M)
| appl_Hyb M N => appl_Hyb ({{w1//w2}}M) ({{w1//w2}}N)
| box_Hyb M =>
  box_Hyb ({{ shift_vwo w1 // shift_vwo w2 }} M)
| unbox_fetch_Hyb w M =>
  let w' := if (eq_vwo_dec w w2) then w1 else w in
    unbox_fetch_Hyb w' ({{w1//w2}} M)
| get_here_Hyb w M =>
  let w' := if (eq_vwo_dec w w2) then w1 else w in
    get_here_Hyb w' ({{w1//w2}}M)
| letdia_get_Hyb w M N =>
  let w' := if (eq_vwo_dec w w2) then w1 else w in
    letdia_get_Hyb w' ({{w1//w2}} M) ({{shift_vwo w1 // shift_vwo w2}} N)
end
where " {{ w1 // w2 }} M " := (subst_w_Hyb w1 w2 M) : hybrid_is5_scope.


(* Opening is defined in terms of substitution *)

Definition open_t_Hyb (M: te_Hyb) (t: te_Hyb) := subst_t_Hyb t (bte 0) M.

Definition open_w_Hyb M w := subst_w_Hyb w (bwo 0) M.

Notation " M '^t^' t " := (open_t_Hyb M t) (at level 67) : hybrid_is5_scope.
Notation " M ^w^ w  " := (open_w_Hyb M w) (at level 67) : hybrid_is5_scope.

Open Scope hybrid_is5_scope.


(*
List substitution
  Substituting a list of terms for bound variables in term, starting
  from a given index.
*)
Fixpoint list_t_subst_Hyb (L: list te_Hyb) (n: nat) (M: te_Hyb) :=
match L with
| nil => M
| t :: L' => [t // bte n] (list_t_subst_Hyb L' (S n) M)
end.



(*** Properties ***)


(*
Simplify substitution in special cases
  * when substitution is identity substitution
  * when the variable for which we try to substitute does not occur in the term
  * when term is closed and we try to substitute for bound variable
*)


Lemma subst_w_Hyb_id:
forall M w,
  {{w // w}} M = M.
induction M; intros; simpl in *;
repeat case_if; subst; auto;
rewrite IHM || (rewrite IHM1; try rewrite IHM2);
auto.
Qed.

Lemma subst_w_Hyb_2_step_id:
forall M w n
  (HT: w \notin free_worlds_Hyb M),
  {{bwo n//fwo w}}({{fwo w//bwo n}}M) = M.
induction M; intros; simpl in *;
repeat case_if; subst; auto;
rewrite IHM || (rewrite IHM1; try rewrite IHM2);
try destruct v; auto;
assert (w <> w) as Neq by eauto; elim Neq; auto.
Qed.


(* Free variable for which we substitute does not occur in the term *)

Lemma closed_subst_w_Hyb_free:
forall M w0 w
  (H_lc: w0 \notin free_worlds_Hyb M),
  {{ w // fwo w0}} M  = M.
induction M; intros; simpl in *;
repeat case_if; auto;
rewrite IHM || (rewrite IHM1; try rewrite IHM2); auto;
(rewrite notin_union in H_lc; rewrite notin_singleton in H_lc;
destruct H_lc as (Neq, H_lc); elim Neq) || destruct v; auto.
Qed.

Lemma closed_subst_t_Hyb_free:
forall M v0 N
  (H_lc: v0 \notin free_vars_Hyb N),
  [M // fte v0] N = N.
induction N; intros; simpl in *;
repeat case_if;
try (rewrite IHN || (rewrite IHN1; try rewrite IHN2); auto);
[ rewrite notin_singleton in H_lc; elim H_lc |
  destruct v]; auto.
Qed.


(* Term is closed and we try to substitute for bound variable *)


Lemma closed_subst_w_Hyb_bound:
forall M w0 w n
  (H_lc: lc_w_n_Hyb n M)
  (Gt: w0 >= n),
  {{ w // bwo w0}} M  = M.
induction M; intros; simpl in *;
repeat case_if; auto;
inversion H_lc; subst;
erewrite IHM || (erewrite IHM1; try erewrite IHM2); eauto;
omega.
Qed.

Lemma closed_subst_t_Hyb_bound:
forall N M v0 n
  (H_lc: lc_t_n_Hyb n N),
  v0 >= n -> [M // bte v0] N = N.
induction N; intros; simpl in *;
repeat case_if; inversion H_lc; subst;
try (erewrite IHN || (erewrite IHN1; try erewrite IHN2)); eauto.
assert (~(n = v0)) by omega;
apply gt_asym in H2; elim H2; omega.
omega. omega.
Qed.


(* Properties of substitution: commutativity *)

Lemma subst_w_Hyb_comm:
forall M w w' w'' n
  (Neq: w'' <> w),
  {{fwo w'//fwo w''}}({{fwo w//bwo n}}M) =
  {{fwo w//bwo n}}({{fwo w'//fwo w''}}M).
induction M; intros; simpl;
repeat case_if; subst; simpl; auto;
rewrite IHM || (rewrite IHM1; try rewrite IHM2);
auto.
Qed.

Lemma subst_t_Hyb_comm:
forall M v v' n N
  (Lc: lc_t_Hyb N),
  v <> v' ->
  [ N // fte v] ([ hyp_Hyb (fte v') // bte n] M) =
  [hyp_Hyb (fte v') // bte n] ([N // fte v] M).
induction M; intros; simpl;
[ repeat (case_if; simpl); auto;
  erewrite closed_subst_t_Hyb_bound; eauto; omega | | | | | |];
try (rewrite IHM; auto);
try (rewrite IHM1; try rewrite IHM2; auto);
repeat (case_if; simpl); subst; simpl;
auto;
erewrite closed_subst_t_Hyb_bound;
eauto;
replace n with (0+n) by omega;
apply closed_t_addition; auto.
Qed.


(* Properties of substitution: expansion with neutral element *)

Lemma subst_w_Hyb_neutral_free:
forall M w w' w0
  (HT: w0 \notin free_worlds_Hyb M),
  {{w//fwo w0}}({{fwo w0// w'}}M) = {{w//w'}}M.
induction M; intros; simpl in *;
repeat case_if; subst; simpl; auto;
try destruct w; try destruct w'; try destruct v; subst;
rewrite IHM || (rewrite IHM1; try rewrite IHM2);
auto;
assert (w0 <> w0) as Neq by eauto; elim Neq; auto.
Qed.

Lemma subst_t_Hyb_neutral_free:
forall M v n N
  (HT: v \notin free_vars_Hyb M),
  [ N // bte n] M = [N // fte v] [hyp_Hyb (fte v) // bte n] M.
induction M; intros; simpl in *;
try (erewrite IHM || (erewrite IHM1; try erewrite IHM2); eauto);
repeat (case_if; simpl); subst; auto;
assert (v0 <> v0) as Neq by eauto; elim Neq; auto.
Qed.

Lemma subst_w_Hyb_neutral_bound:
forall M n
  (HT: lc_w_n_Hyb n M),
  forall m w w',
    m >= n -> {{w//bwo m}}({{bwo m// w'}}M) = {{w//w'}}M.
intros M n HT; induction HT; intros; simpl in *; auto.
rewrite IHHT; auto.
rewrite IHHT1; try rewrite IHHT2; auto.
destruct w; destruct w'; simpl; try rewrite IHHT; auto; omega.
repeat case_if; rewrite IHHT; auto.
repeat case_if; rewrite IHHT; auto; inversion H1; subst; omega.
repeat case_if; rewrite IHHT; auto.
repeat case_if; rewrite IHHT; auto; inversion H1; subst; omega.
repeat case_if; rewrite IHHT1; try rewrite IHHT2; auto; omega.
repeat case_if; rewrite IHHT1; try rewrite IHHT2; auto; try omega;
inversion H1; subst; omega.
Qed.

(* With two different types of substitution, the order does not matter *)

Lemma subst_Hyb_order_irrelevant_bound:
forall N w M v m
  (HT_M: lc_w_Hyb M),
    [M // v ] ({{w // bwo m}} N)  =
    {{w // bwo m}} ([M // v ] N).
induction N; intros; simpl in *;
repeat case_if; simpl;
unfold shift_vte in *; unfold shift_vwo in *;
try destruct v; try destruct w; auto;
try rewrite IHN; try (rewrite IHN1; try rewrite IHN2);
auto; erewrite closed_subst_w_Hyb_bound; eauto; omega.
Qed.

Lemma subst_Hyb_order_irrelevant_free:
forall N w w' M v
  (HT_M: w' \notin (free_worlds_Hyb M)),
    [M // v ] ({{w // fwo w'}} N)  =
    {{w // fwo w'}} ([M // v ] N).
induction N; intros; simpl in *;
repeat case_if; simpl;
unfold shift_vwo in *;
try destruct c; try destruct v; auto;
try rewrite IHN; try (rewrite IHN1; try rewrite IHN2);
auto; rewrite closed_subst_w_Hyb_free; auto.
Qed.


(*
   Substitution of one type does not change the set of free variables
   of the other type.
*)

Lemma subst_t_Hyb_preserv_free_worlds:
forall N v k w,
  w \notin free_worlds_Hyb N ->
  w \notin free_worlds_Hyb [ hyp_Hyb (fte v) // bte k ] N.
induction N; intros; simpl in *;
repeat case_if;try destruct v;
simpl; auto.
Qed.

Lemma subst_w_Hyb_preserv_free_vars:
forall N w w' v,
  v \notin free_vars_Hyb N ->
  v \notin free_vars_Hyb {{w // w'}} N.
induction N; intros; simpl in *;
repeat case_if; try destruct c;
simpl; auto.
Qed.

Close Scope hybrid_is5_scope.