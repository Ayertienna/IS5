Require Export Shared.
Require Export PermutLib.

(*** Definitions ***)

(*
Terms in label-free IS5 system:
  * hypothesis
  * lambda expression
  * application
  * box expression
  * unpacking box (possibly in a different world)
  * diamond expression (possibly in a different world)
  * using diamond expression (possibly the diamond itself is from a
  different world)
*)
Inductive te_LF :=
| hyp_LF: vte -> te_LF
| lam_LF: ty -> te_LF -> te_LF
| appl_LF: te_LF -> te_LF -> te_LF
| box_LF: te_LF -> te_LF
| unbox_fetch_LF: vwo -> te_LF -> te_LF
| get_here_LF: vwo -> te_LF -> te_LF
| letdia_get_LF: vwo -> te_LF -> te_LF -> te_LF
.


(* Calculate set of free worlds used in term M *)
Fixpoint free_worlds_LF (M: te_LF) : fset var :=
match M with
| hyp_LF _ => \{}
| lam_LF _ M => free_worlds_LF M
| appl_LF M N => free_worlds_LF M \u free_worlds_LF N
| box_LF M => free_worlds_LF M
| unbox_fetch_LF (fwo w) M => \{w} \u free_worlds_LF M
| unbox_fetch_LF _ M => free_worlds_LF M
| get_here_LF (fwo w) M => \{w} \u free_worlds_LF M
| get_here_LF _ M => free_worlds_LF M
| letdia_get_LF (fwo w) M N => \{w} \u free_worlds_LF M \u free_worlds_LF N
| letdia_get_LF _ M N => free_worlds_LF M \u free_worlds_LF N
end.

(* Calculate set of free variables used in term M *)
Fixpoint free_vars_LF (M: te_LF) : fset var :=
match M with
| hyp_LF (fte v) => \{v}
| hyp_LF (bte _) => \{}
| lam_LF _ M => free_vars_LF M
| appl_LF M N => free_vars_LF M \u free_vars_LF N
| box_LF M => free_vars_LF M
| unbox_fetch_LF _ M => free_vars_LF M
| get_here_LF _ M => free_vars_LF M
| letdia_get_LF _ M N => free_vars_LF M \u free_vars_LF N
end.


(*
Property: term is locally closed
 This means that there are no bound variables.
*)

Inductive lc_t_n_LF : nat -> te_LF -> Prop :=
 | lct_hyp_LF: forall v n, lc_t_n_LF n (hyp_LF (fte v))
 | lct_lam_LF: forall M t n,
     lc_t_n_LF (S n) M ->
     lc_t_n_LF n (lam_LF t M)
 | lct_appl_LF: forall M N n,
     lc_t_n_LF n M -> lc_t_n_LF n N ->
     lc_t_n_LF n (appl_LF M N)
 | lct_box_LF: forall M n,
     lc_t_n_LF n M ->
     lc_t_n_LF n (box_LF M)
 | lct_unbox_fetch_LF: forall M w n,
     lc_t_n_LF n M ->
     lc_t_n_LF n (unbox_fetch_LF (fwo w) M)
 | lct_get_here_LF: forall M w n,
     lc_t_n_LF n M ->
     lc_t_n_LF n (get_here_LF (fwo w) M)
 | lct_letdia_get_LF: forall M N w n,
     lc_t_n_LF (S n) N ->
     lc_t_n_LF n M ->
     lc_t_n_LF n (letdia_get_LF (fwo w) M N)
.

Definition lc_t_LF M := lc_t_n_LF 0 M.


Inductive lc_w_n_LF: nat -> te_LF -> Prop :=
| lcw_hyp_LF: forall v n, lc_w_n_LF n (hyp_LF (fte v))
| lcw_lam_LF: forall t M n,
    lc_w_n_LF n M ->
    lc_w_n_LF n (lam_LF t M)
| lcw_appl_LF: forall M N n,
    lc_w_n_LF n M -> lc_w_n_LF n N ->
    lc_w_n_LF n (appl_LF M N)
| lcw_box_LF: forall M n,
    lc_w_n_LF (S n) M ->
    lc_w_n_LF n (box_LF M)
| lcw_unbox_fetch_LF: forall M w n,
    lc_w_n_LF n M ->
    lc_w_n_LF n (unbox_fetch_LF (fwo w) M)
| lcw_get_here_LF: forall M w n,
    lc_w_n_LF n M ->
    lc_w_n_LF n (get_here_LF (fwo w) M)
| lcw_letdia_get_LF: forall M N w n,
    lc_w_n_LF (S n) N ->
    lc_w_n_LF n M ->
    lc_w_n_LF n (letdia_get_LF (fwo w) M N)
.

Definition lc_w_LF M := lc_w_n_LF 0 M.


(*** Properties ***)


(* For each pair of contexts, they are either equivalent or not. *)
Theorem permut_context_LF_dec:
forall (c1 c2: Context_LF),
  {  permut (snd c1) (snd c2) /\ (fst c1) = (fst c2)} +
  { ~permut (snd c1) (snd c2) \/ (fst c1) <> (fst c2)}.
intros; destruct c1 as (w, a); destruct c2 as (w', a');
destruct (eq_var_dec w w'); subst; simpl;
destruct (permut_dec (var * ty) a a'); simpl;
auto; intros;
repeat decide equality;
apply eq_var_dec.
Qed.


(* Propagation of lc_*_n_LF property *)

Lemma closed_w_succ:
forall M n,
  lc_w_n_LF n M -> lc_w_n_LF (S n) M.
intros; generalize dependent n;
induction M; intros; inversion H; subst;
eauto using lc_w_n_LF.
Qed.

Lemma closed_t_succ:
forall M n,
  lc_t_n_LF n M -> lc_t_n_LF (S n) M.
intros; generalize dependent n;
induction M; intros; inversion H; subst;
eauto using lc_t_n_LF.
Qed.


Lemma closed_w_addition:
forall M n m,
  lc_w_n_LF n M -> lc_w_n_LF (n + m) M.
intros; induction m;
[ replace (n+0) with n by auto |
  replace (n+ S m) with (S (n+m)) by auto] ;
try apply closed_w_succ;
assumption.
Qed.

Lemma closed_t_addition:
forall M n m,
  lc_t_n_LF n M -> lc_t_n_LF (n + m) M.
intros; induction m;
[ replace (n+0) with n by auto |
  replace (n + S m) with (S (n+m)) by auto] ;
try apply closed_t_succ;
assumption.
Qed.