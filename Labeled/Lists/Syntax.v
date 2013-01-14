(* Labeled using lists *)
Add LoadPath "../..".

Require Export Shared.
Require Export LibList.

Definition worlds_L := list var.

Inductive te_L :=
| hyp_L: vte -> te_L
| lam_L: ty -> te_L -> te_L
| appl_L: te_L -> te_L -> te_L
| box_L: te_L -> te_L
| unbox_L: te_L -> te_L
| get_L: vwo -> te_L -> te_L
| letd_L: te_L -> te_L -> te_L
| here_L: te_L -> te_L
| fetch_L: vwo -> te_L -> te_L
.

Inductive lc_t_n_L : nat -> te_L -> Prop :=
 | lct_hyp_fte_L: forall v n, lc_t_n_L n (hyp_L (fte v))
 | lct_hyp_bte_L: forall v n, n > v -> lc_t_n_L n (hyp_L (bte v))
 | lct_lam_L: forall t M n,
     lc_t_n_L (S n) M ->
     lc_t_n_L n (lam_L t M)
 | lct_appl_L: forall M N n,
     lc_t_n_L n M -> lc_t_n_L n N ->
     lc_t_n_L n (appl_L M N)
 | lct_box_L: forall M n,
     lc_t_n_L n M ->
     lc_t_n_L n (box_L M)
 | lct_unbox_L: forall M n,
     lc_t_n_L n M ->
     lc_t_n_L n (unbox_L M)
 | lct_fetch_L: forall M w n,
     lc_t_n_L n M ->
     lc_t_n_L n (fetch_L w M)
 | lct_here_L: forall M n,
     lc_t_n_L n M ->
     lc_t_n_L n (here_L M)
 | lct_get_L: forall M w n,
     lc_t_n_L n M ->
     lc_t_n_L n (get_L w M)
 | lct_letd_L: forall M N n,
     lc_t_n_L (S n) N -> lc_t_n_L n M ->
     lc_t_n_L n (letd_L M N)
.

Inductive lc_w_n_L: nat -> te_L -> Prop :=
| lcw_hyp_L: forall v n, lc_w_n_L n (hyp_L v)
| lcw_lam_L: forall t M n,
    lc_w_n_L n M ->
    lc_w_n_L n (lam_L t M)
| lcw_appl_L: forall M N n,
    lc_w_n_L n M -> lc_w_n_L n N ->
    lc_w_n_L n (appl_L M N)
| lcw_box_L: forall M n,
    lc_w_n_L (S n) M ->
    lc_w_n_L n (box_L M)
| lcw_unbox_L: forall M n,
    lc_w_n_L n M ->
    lc_w_n_L n (unbox_L M)
| lcw_fetch_L: forall M w n,
    lc_w_n_L n M ->
    lc_w_n_L n (fetch_L (fwo w) M)
| lcw_here_L: forall M n,
    lc_w_n_L n M ->
    lc_w_n_L n (here_L M)
| lcw_get_L: forall M w n,
    lc_w_n_L n M ->
    lc_w_n_L n (get_L (fwo w) M)
| lcw_letd_L: forall M N n,
    lc_w_n_L (S n) N -> lc_w_n_L n M ->
    lc_w_n_L n (letd_L M N)
.

Definition lc_w_L w := lc_w_n_L 0 w.
Definition lc_t_L t := lc_t_n_L 0 t.

Fixpoint used_vars_term_L (M: te_L) :=
match M with
| hyp_L (bte _) => \{}
| hyp_L (fte w) => \{w}
| lam_L A M => used_vars_term_L M
| appl_L M N => used_vars_term_L M \u used_vars_term_L N
| box_L M => used_vars_term_L M
| unbox_L M => used_vars_term_L M
| here_L M => used_vars_term_L M
| letd_L M N => used_vars_term_L M \u used_vars_term_L N
| get_L w M => used_vars_term_L M
| fetch_L w M => used_vars_term_L M
end.

Fixpoint used_worlds_term_L (M: te_L) :=
match M with
| hyp_L _ => \{}
| lam_L A M => used_worlds_term_L M
| appl_L M N => used_worlds_term_L M \u used_worlds_term_L N
| box_L M => used_worlds_term_L M
| unbox_L M => used_worlds_term_L M
| here_L M => used_worlds_term_L M
| letd_L M N => used_worlds_term_L M \u used_worlds_term_L N
| get_L (fwo w) M => \{w} \u used_worlds_term_L M
| get_L (bwo _) M => used_worlds_term_L M
| fetch_L (fwo w) M => \{w} \u used_worlds_term_L M
| fetch_L (bwo _) M => used_worlds_term_L M
end.

Definition used_vars_context_L (Gamma: ctx_L) : fset var :=
  from_list (map (fun x => fst (snd x)) Gamma).

Lemma closed_w_succ_L:
forall M n,
  lc_w_n_L n M -> lc_w_n_L (S n) M.
intros; generalize dependent n;
induction M; intros; inversion H; subst;
eauto using lc_w_n_L.
Qed.

Lemma closed_t_succ_L:
forall M n,
  lc_t_n_L n M -> lc_t_n_L (S n) M.
intros; generalize dependent n;
induction M; intros; inversion H; subst;
eauto using lc_t_n_L.
Qed.

Lemma closed_w_addition_L:
forall M n m,
  lc_w_n_L n M -> lc_w_n_L (n + m) M.
intros; induction m;
[ replace (n+0) with n by auto |
  replace (n+ S m) with (S (n+m)) by auto] ;
try apply closed_w_succ_L;
assumption.
Qed.

Lemma closed_t_addition_L:
forall M n m,
  lc_t_n_L n M -> lc_t_n_L (n + m) M.
intros; induction m;
[ replace (n+0) with n by auto |
  replace (n + S m) with (S (n+m)) by auto] ;
try apply closed_t_succ_L;
assumption.
Qed.