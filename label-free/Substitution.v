Require Export Syntax.
Require Import Metatheory.
Require Import Arith.
Require Import List.

Open Scope label_free_is5_scope.

Global Reserved Notation " [ M // v ] N " (at level 5).
Global Reserved Notation " {{ w1 // w2 }} N " (at level 5).

(* Term substitution *)

Fixpoint subst_t (M0: te_LF) (v0: var_LF) (N0: te_LF) :=
match N0 with
| hyp_LF v => 
    if (eq_var_LF_dec v v0) then M0 else N0
| lam_LF A M => 
    lam_LF A ([M0 // var_succ v0] M) 
| appl_LF M N => 
    appl_LF ([M0//v0]M) ([M0//v0]N)
| box_LF M => 
    box_LF ([M0//v0]M)
| unbox_fetch_LF w M =>
    unbox_fetch_LF w ([M0//v0]M)
| get_here_LF w M =>
    get_here_LF w ([M0//v0]M)
| letdia_get_LF w M N =>
    letdia_get_LF w ([M0//v0]M) ([M0//var_succ v0]N)
end
where " [ M // v ] N " := (subst_t M v N) : label_free_is5_scope.

Definition open_var (M: te_LF) (t: te_LF) := subst_t t (bvar 0) M.
Notation " M '^t^' t " := (open_var M t) (at level 5) : label_free_is5_scope.


(* Context substitution *)

Fixpoint subst_ctx (M0 : te_LF) (ctx1: ctx_LF) (ctx2: ctx_LF) := 
match M0 with 
| hyp_LF n => hyp_LF n
| lam_LF A M => lam_LF A ({{ctx1//ctx2}}M)
| appl_LF M N => appl_LF ({{ctx1//ctx2}}M) ({{ctx1//ctx2}}N)
| box_LF M =>  
  box_LF ({{ ctx_succ ctx1 // ctx_succ ctx2 }} M)
| unbox_fetch_LF w M =>
  let w' := If w = ctx2 then ctx1 else w in
    unbox_fetch_LF w' ({{ctx1//ctx2}} M)
| get_here_LF w M =>
  let w' := If w = ctx2 then ctx1 else w in
    get_here_LF w' ({{ctx1//ctx2}}M)
| letdia_get_LF w M N =>
  let w' := If w = ctx2 then ctx1 else w in
    letdia_get_LF w' ({{ctx1//ctx2}} M) ({{ctx_succ ctx1 // ctx_succ ctx2}} N)
end
where " {{ w1 // w2 }} M " := (subst_ctx M w1 w2) : label_free_is5_scope.

Definition open_ctx M ctx := subst_ctx M ctx (bctx 0).
Notation " M ^w^ w  " := (open_ctx M w) (at level 10) : label_free_is5_scope.


Section Lemmas.

Lemma no_unbound_worlds_LF_subst_ctx_id:
forall M n w
  (H_unbound: unbound_worlds n M = nil),
  {{ w // bctx n }} M = M.
Admitted.

Lemma closed_ctx_subst_ctx_id:
forall M w n
  (H_lc: lc_w_n_LF M n),
  {{w // bctx n}} M  = M.
Admitted.

Lemma subst_ctx_comm:
forall M w w' w'' n
  (Neq: w'' <> w),
  {{fctx w'//fctx w''}}({{fctx w//bctx n}}M) = 
  {{fctx w//bctx n}}({{fctx w'//fctx w''}}M).
Admitted.

Lemma subst_ctx_id:
forall M w n
  (HT: w \notin free_worlds_LF M),
  {{bctx n//fctx w}}({{fctx w//bctx n}}M) = M.
Admitted.

Lemma subst_ctx_neutral_free:
forall M w w' w0
  (HT: w0 \notin free_worlds_LF M),
  {{w//fctx w0}}({{fctx w0// w'}}M) = {{w//w'}}M.
Admitted.

Lemma subst_ctx_neutral_bound:
forall M w w' n
  (HT: lc_w_n_LF M n),
  {{w//bctx n}}({{bctx n// w'}}M) = {{w//w'}}M.
Admitted.

Lemma closed_ctx_step_opening:
forall M n w
  (HT: lc_w_n_LF M (S n)),
  lc_w_n_LF ({{fctx w//bctx n}}M) n.
Admitted.


Lemma subst_order_irrelevant:
forall N w M v m
  (HT_M: lc_w_LF M),
    [M // v ] ({{w // bctx m}} N)  = 
    {{w // bctx m}} ([M // v ] N). 
Admitted.

End Lemmas.

Close Scope label_free_is5_scope.