Require Export Shared.
Require Import Arith.
Require Import LibFset.
Require Import LibList.
Require Import PermutLib.

Open Scope is5_scope. Open Scope permut_scope.

Inductive te_LF :=
| hyp_LF: vte -> te_LF
| lam_LF: ty -> te_LF -> te_LF
| appl_LF: te_LF -> te_LF -> te_LF
| box_LF: te_LF -> te_LF
| unbox_LF: te_LF -> te_LF
| unbox_fetch_LF: te_LF -> te_LF
| here_LF: te_LF -> te_LF
| get_here_LF: te_LF -> te_LF
| letdia_LF: te_LF -> te_LF -> te_LF
| letdia_get_LF: te_LF -> te_LF -> te_LF
.

Inductive lc_n_LF : nat -> te_LF -> Prop :=
 | lc_hyp_bte_LF: forall v n, n > v -> lc_n_LF n (hyp_LF (bte v))
 | lc_hyp_fte_LF: forall v n, lc_n_LF n (hyp_LF (fte v))
 | lc_lam_LF: forall M t n,
     lc_n_LF (S n) M ->
     lc_n_LF n (lam_LF t M)
 | lc_appl_LF: forall M N n,
     lc_n_LF n M -> lc_n_LF n N ->
     lc_n_LF n (appl_LF M N)
 | lc_box_LF: forall M n,
     lc_n_LF n M ->
     lc_n_LF n (box_LF M)
 | lc_unbox_LF: forall M n,
     lc_n_LF n M ->
     lc_n_LF n (unbox_LF M)
 | lc_unbox_fetch_LF: forall M n,
     lc_n_LF n M ->
     lc_n_LF n (unbox_fetch_LF M)
 | lc_here_LF: forall M n,
     lc_n_LF n M ->
     lc_n_LF n (here_LF M)
 | lc_get_here_LF: forall M n,
     lc_n_LF n M ->
     lc_n_LF n (get_here_LF M)
 | lc_letdia_LF: forall M N n,
     lc_n_LF (S n) N -> lc_n_LF n M ->
     lc_n_LF n (letdia_LF M N)
 | lc_letdia_get_LF: forall M N n,
     lc_n_LF (S n) N -> lc_n_LF n M ->
     lc_n_LF n (letdia_get_LF M N)
.

Definition lc_LF := lc_n_LF 0.
