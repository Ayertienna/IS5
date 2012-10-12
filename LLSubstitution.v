Require Export LLSyntax.

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
  let w' := if (eq_vwo_dec w3 w2) then w1 else w3 in
    fetch_L w' ({{w1//w2}} M)
| get_L w3 M =>
  let w' := if (eq_vwo_dec w3 w2) then w1 else w3 in
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
