Require Export LLSyntax.
Require Export LibLogic.
Require Export LibTactics.

(* Notation for term substitution *)
Global Reserved Notation " [ M // v ] N " (at level 5).

(* Notation for world substitution *)
Global Reserved Notation " {{ w1 // w2 }} N " (at level 5).

Fixpoint subst_t (M0: te_L) (v0: vte) (N0: te_L) :=
match N0 with
| hyp_L v =>
    if (eq_vte_dec v v0) then M0 else N0
| lam_L A M =>
    lam_L A ([M0 // shift_vte v0] M)
| appl_L M N =>
    appl_L ([M0//v0]M) ([M0//v0]N)
| box_L M =>
    box_L ([M0//v0]M)
| unbox_L M =>
    unbox_L ([M0//v0]M)
| fetch_L w M =>
    fetch_L w ([M0//v0]M)
| get_L w M =>
    get_L w ([M0//v0]M)
| here_L M =>
    here_L ([M0//v0]M)
| letd_L M N =>
    letd_L ([M0//v0]M) ([M0//shift_vte v0]N)
end
where " [ M // v ] N " := (subst_t M v N) : labeled_is5_scope.

Fixpoint subst_w (M0: te_L) (w1: vwo) (w2: vwo) :=
match M0 with
| hyp_L n => hyp_L n
| lam_L A M => lam_L A ({{w1//w2}}M)
| appl_L M N => appl_L ({{w1//w2}}M) ({{w1//w2}}N)
| box_L M => box_L ({{ shift_vwo w1 // shift_vwo w2 }} M)
| unbox_L M => unbox_L ({{w1//w2}}M)
| fetch_L w3 M =>
  let w' := If w3 = w2 then w1 else w3 in
    fetch_L w' ({{w1//w2}} M)
| get_L w3 M =>
  let w' := If w3 = w2 then w1 else w3 in
    get_L w' ({{w1//w2}}M)
| here_L M => here_L ({{w1//w2}}M)
| letd_L M N =>
    letd_L ({{w1//w2}} M) ({{shift_vwo w1 // shift_vwo w2}} N)
end
where " {{ w1 // w2 }} M " := (subst_w M w1 w2) : labeled_is5_scope.

Definition open_t (M: te_L) (t: te_L) := subst_t t (bte 0) M.

Definition open_w M w := subst_w M w (bwo 0).

Notation " M '^t^' t " := (open_t M t) (at level 5) : labeled_is5_scope.
Notation " M ^w^ w  " := (open_w M w) (at level 10) : labeled_is5_scope.

Open Scope labeled_is5_scope.

Inductive lc_t_L : te_L -> Prop :=
 | lct_hyp_L: forall v, lc_t_L (hyp_L (fte v))
 | lct_lam_L: forall L t M,
     forall x, x \notin L -> lc_t_L (M ^t^ (hyp_L (fte x))) ->
     lc_t_L (lam_L t M)
 | lct_appl_L: forall M N,
     lc_t_L M -> lc_t_L N ->
     lc_t_L (appl_L M N)
 | lct_box_L: forall M,
     lc_t_L M ->
     lc_t_L (box_L M)
 | lct_unbox_L: forall M,
     lc_t_L M ->
     lc_t_L (unbox_L M)
 | lct_fetch_L: forall M w,
     lc_t_L M ->
     lc_t_L (fetch_L w M)
 | lct_here_L: forall M,
     lc_t_L M ->
     lc_t_L (here_L M)
 | lct_get_L: forall M w,
     lc_t_L M ->
     lc_t_L (get_L (fwo w) M)
 | lct_letd_L: forall L M N,
     (forall x, x \notin L -> lc_t_L (N ^t^ (hyp_L (fte x)))) ->
     lc_t_L M ->
     lc_t_L (letd_L M N)
.

Inductive lc_w_L: te_L -> Prop :=
| lcw_hyp_L: forall v, lc_w_L (hyp_L (fte v))
| lcw_lam_L: forall t M,
    lc_w_L M ->
    lc_w_L (lam_L t M)
| lcw_appl_L: forall M N,
    lc_w_L M -> lc_w_L N ->
    lc_w_L (appl_L M N)
| lcw_box_L: forall L M,
    forall w, w \notin L -> lc_w_L (M ^w^ (fwo w)) ->
    lc_w_L (box_L M)
| lcw_unbox_L: forall M,
    lc_w_L M ->
    lc_w_L (unbox_L M)
| lcw_fetch_L: forall M w,
    lc_w_L M ->
    lc_w_L (fetch_L (fwo w) M)
| lcw_here_L: forall M,
    lc_w_L M ->
    lc_w_L (here_L M)
| lcw_get_L: forall M w,
    lc_w_L M ->
    lc_w_L (get_L (fwo w) M)
| lcw_letd_L: forall L M N,
    (forall w', w' \notin L -> lc_w_L (N ^w^ (fwo w'))) -> lc_w_L M ->
    lc_w_L (letd_L M N)
.
