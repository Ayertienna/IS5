Add LoadPath "../../..".
Require Export LFND_Shared.

Inductive vctx_LF :=
| bctx: nat -> vctx_LF
| cctx: ctx_LF -> vctx_LF
.

Inductive te_LF :=
| hyp_LF: vte -> te_LF
| lam_LF: ty -> te_LF -> te_LF
| appl_LF: te_LF -> te_LF -> te_LF
| box_LF: te_LF -> te_LF
| unbox_LF: te_LF -> te_LF
.

Inductive lc_t_n_LF : nat -> te_LF -> Prop :=
 | lc_t_hyp_bte_LF: forall v n, n > v -> lc_t_n_LF n (hyp_LF (bte v))
 | lc_t_hyp_fte_LF: forall v n, lc_t_n_LF n (hyp_LF (fte v))
 | lc_t_lam_LF: forall M t n,
     lc_t_n_LF (S n) M ->
     lc_t_n_LF n (lam_LF t M)
 | lc_t_appl_LF: forall M N n,
     lc_t_n_LF n M -> lc_t_n_LF n N ->
     lc_t_n_LF n (appl_LF M N)
 | lc_t_box_LF: forall M n,
     lc_t_n_LF n M ->
     lc_t_n_LF n (box_LF M)
 | lc_t_unbox_LF: forall M n,
     lc_t_n_LF n M ->
     lc_t_n_LF n (unbox_LF M)
.

Definition lc_t_LF := lc_t_n_LF 0.

Fixpoint used_vars_te_LF (M: te_LF) : fset var :=
match M with
| hyp_LF (fte v) => \{v}
| hyp_LF (bte _) => \{}
| lam_LF _ M => used_vars_te_LF M
| appl_LF M N => used_vars_te_LF M \u used_vars_te_LF N
| box_LF M => used_vars_te_LF M
| unbox_LF M => used_vars_te_LF M
end.
