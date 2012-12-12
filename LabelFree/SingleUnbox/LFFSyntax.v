Require Export Shared.

Inductive vctx :=
| bctx: nat -> vctx
| cctx: ctx_LF -> vctx
.

Inductive te_LF :=
| hyp_LF: vte -> te_LF
| lam_LF: ty -> te_LF -> te_LF
| appl_LF: te_LF -> te_LF -> te_LF
| box_LF: te_LF -> te_LF
| unbox_LF: te_LF -> te_LF
| here_LF: te_LF -> te_LF
| letdia_LF: te_LF -> te_LF -> te_LF
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
 | lc_t_here_LF: forall M n,
     lc_t_n_LF n M ->
     lc_t_n_LF n (here_LF M)
 | lc_t_letdia_LF: forall M N n,
     lc_t_n_LF (S n) N -> lc_t_n_LF n M ->
     lc_t_n_LF n (letdia_LF M N)
.

Definition lc_t_LF := lc_t_n_LF 0.
