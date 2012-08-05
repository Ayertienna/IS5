Require Export Shared.
Require Import LibList.
Require Import LibListSorted.

Inductive te_LF :=
| hyp_LF: vte -> te_LF
| lam_LF: ty -> te_LF -> te_LF
| appl_LF: te_LF -> te_LF -> te_LF
| box_LF: te_LF -> te_LF
| unbox_fetch_LF: vwo -> te_LF -> te_LF
| get_here_LF: vwo -> te_LF -> te_LF
| letdia_get_LF: vwo -> te_LF -> te_LF -> te_LF
.


(* FIXME: is this going to give us trouble? I.e., should we proove this? *)
Axiom permut_dec:
forall (a: list (var * ty)) a',
  { permut a a' } + { ~permut a a' }.


Theorem permut_context_LF_dec:
forall (c1 c2: Context_LF),
  { permut (snd c1) (snd c2) /\ (fst c1) = (fst c2)} + 
  { ~permut (snd c1) (snd c2) \/ (fst c1) <> (fst c2)}.
intros; destruct c1 as (w, a); destruct c2 as (w', a');
destruct (eq_var_dec w w'); subst; simpl;
destruct (permut_dec a a'); simpl;
auto.
Qed.


(* When a term is context-wise locally closed at level n *)
Inductive lc_w_n_LF : te_LF -> nat -> Prop :=
 | lcw_hyp_LF: forall v n, lc_w_n_LF (hyp_LF v) n
 | lcw_lam_LF: forall t M n,
     lc_w_n_LF M n ->
     lc_w_n_LF (lam_LF t M) n
 | lcw_appl_LF: forall M N n,
     lc_w_n_LF M n -> lc_w_n_LF N n ->
     lc_w_n_LF (appl_LF M N) n
 | lcw_box_LF: forall M n,
     lc_w_n_LF M (S n) ->
     lc_w_n_LF (box_LF M) n
 | lcw_unbox_fetch_LF: forall M n w,
     lc_w_n_LF M n ->
     lc_w_n_LF (unbox_fetch_LF (fwo w) M) n
 | lcw_get_here_LF: forall M n w ,
     lc_w_n_LF M n ->
     lc_w_n_LF (get_here_LF (fwo w) M) n
 | lcw_letdia_get_LF: forall M N n w,
     lc_w_n_LF N (S n) -> lc_w_n_LF M n ->
     lc_w_n_LF (letdia_get_LF (fwo w) M N) n
.
Definition lc_w_LF (t:te_LF) : Prop := lc_w_n_LF t 0.


(* When a term is term-wise locally closed at level n *)
Inductive lc_t_n_LF: te_LF -> nat -> Prop :=
| lct_hyp_LF: forall v n, lc_t_n_LF (hyp_LF (fte v)) n
| lct_lam_LF: forall t M n, 
    lc_t_n_LF M (S n) ->
    lc_t_n_LF (lam_LF t M) n
| lct_appl_LF: forall M N n,
    lc_t_n_LF M n -> lc_t_n_LF N n ->
    lc_t_n_LF (appl_LF M N) n
 | lct_box_LF: forall M n,
     lc_t_n_LF M n ->
     lc_t_n_LF (box_LF M) n
 | lct_unbox_fetch_LF: forall M n w,
     lc_t_n_LF M n ->
     lc_t_n_LF (unbox_fetch_LF (fwo w) M) n
 | lct_get_here_LF: forall M n w ,
     lc_t_n_LF M n ->
     lc_t_n_LF (get_here_LF (fwo w) M) n
 | lct_letdia_get_LF: forall M N n w,
     lc_t_n_LF N n -> lc_t_n_LF M n ->
     lc_t_n_LF (letdia_get_LF (fwo w) M N) n
.
Definition lc_t_LF (t:te_LF) : Prop := lc_t_n_LF t 0.


(* Calculate list of free worlds used in term M *)
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


(* Calculate list of unbound worlds of level above n *)
Fixpoint unbound_worlds (n:nat) (M:te_LF):=
match M with
| hyp_LF n => nil
| lam_LF t M => unbound_worlds n M
| appl_LF M N => unbound_worlds n M ++ unbound_worlds n N
| box_LF M => unbound_worlds (S n) M
| unbox_fetch_LF (bwo w) M => w :: unbound_worlds n M
| unbox_fetch_LF (fwo w) M => unbound_worlds n M
| get_here_LF (bwo w) M => w :: unbound_worlds n M
| get_here_LF (fwo w) M => unbound_worlds n M
| letdia_get_LF (bwo w) M N =>
  w :: unbound_worlds n M ++ unbound_worlds (S n) N
| letdia_get_LF (fwo w) M N => unbound_worlds n M ++ unbound_worlds (S n) N
end.


(* Calculate list of free variables used in term M *)
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


(* Calculate list of unbound variables of level above n *)
Fixpoint unbound_vars (n:nat) (M:te_LF):=
match M with
| hyp_LF (bte n) => n::nil
| hyp_LF (fte n) => nil 
| lam_LF t M => unbound_vars (S n) M
| appl_LF M N => unbound_vars n M ++ unbound_vars n N
| box_LF M => unbound_vars n M
| unbox_fetch_LF _ M => unbound_vars n M
| get_here_LF _ M => unbound_vars n M
| letdia_get_LF _ M N => unbound_vars n M ++ unbound_vars (S n) N
end.


Section Lemmas.


Lemma closed_w_succ:
forall M n,
  lc_w_n_LF M n -> lc_w_n_LF M (S n).
intros; generalize dependent n;
induction M; intros; inversion H; subst;
eauto using lc_w_n_LF.
Qed.

Lemma closed_w_addition:
forall M n m,
  lc_w_n_LF M n -> lc_w_n_LF M (n + m).
intros; induction m;
[ replace (n+0) with n by auto |
  replace (n+ S m) with (S (n+m)) by auto] ;
try apply closed_w_succ;
assumption.
Qed.

Lemma closed_w_no_unbound_worlds:
forall M n,
  lc_w_n_LF M n -> unbound_worlds n M = nil.
intros;
generalize dependent n;
induction M; intros; simpl in *;
inversion H; subst; eauto;
rewrite IHM1; try rewrite IHM2; auto.
Qed.

Lemma closed_t_succ:
forall M n,
  lc_t_n_LF M n -> lc_t_n_LF M (S n).
intros; generalize dependent n;
induction M; intros; inversion H; subst;
eauto using lc_t_n_LF.
Qed.

Lemma closed_t_addition:
forall M n m,
  lc_t_n_LF M n -> lc_t_n_LF M (n + m).
intros; induction m;
[ replace (n+0) with n by auto |
  replace (n + S m) with (S (n+m)) by auto] ;
try apply closed_t_succ;
assumption.
Qed.

Lemma closed_t_no_unbound_vars:
forall M n,
  lc_t_n_LF M n -> unbound_vars n M = nil.
intros;
generalize dependent n;
induction M; intros; simpl in *;
inversion H; subst; eauto;
rewrite IHM1; try rewrite IHM2; auto;
apply closed_t_succ; assumption.
Qed.

End Lemmas.

