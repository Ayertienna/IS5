Require Export Syntax.
Require Import Arith.
Require Import List.

Open Scope label_free_is5_scope.

Reserved Notation " {{ ctx1 // ctx2 }} Gamma " (at level 5).

Fixpoint subst_ctx (M0 : te_LF) (ctx1: ctx_LF) (ctx2: ctx_LF) :=
match M0 with 
| hyp_LF n => hyp_LF n
| lam_LF A M =>lam_LF A {{ctx1 // ctx2}} M
| appl_LF M N => appl_LF {{ctx1 // ctx2}}M {{ctx1 // ctx2}}N
| box_LF M => 
  match ctx1, ctx2 with
    | bctx c1, bctx c2 => box_LF {{bctx (S c1) // bctx (S c2)}} M
    | bctx c1, fctx c2 => box_LF {{bctx (S c1) // ctx2}} M
    | fctx c1, bctx c2 => box_LF {{ctx1 // bctx (S c2)}} M
    | fctx c1, fctx c2 => box_LF {{ctx1 // ctx2}} M
  end
| unbox_LF M => unbox_LF {{ctx1 // ctx2}} M
| unbox_fetch_LF ctx M =>
  let ctx' := if eq_ctx_LF_dec ctx ctx2 then ctx1 else ctx in
  unbox_fetch_LF ctx' {{ctx1 // ctx2}} M
| here_LF M => here_LF {{ctx1 // ctx2}} M
| get_here_LF ctx M =>
  let ctx' := if eq_ctx_LF_dec ctx ctx2 then ctx1 else ctx in
  get_here_LF ctx' {{ctx1 // ctx2}}M
| letdia_LF M N =>
  match ctx1, ctx2 with
    | bctx c1, bctx c2 => letdia_LF {{ctx1 // ctx2}}M {{bctx (S c1) // bctx (S c2)}}N
    | bctx c1, fctx c2 => letdia_LF {{ctx1 // ctx2}}M {{bctx (S c1) // ctx2}}N
    | fctx c1, bctx c2 => letdia_LF {{ctx1 // ctx2}}M {{ctx1 // bctx (S c2)}}N
    | fctx c1, fctx c2 => letdia_LF {{ctx1 // ctx2}}M {{ctx1 // ctx2}}N
  end
| letdia_get_LF ctx M N =>
  let ctx' := if eq_ctx_LF_dec ctx ctx2 then ctx1 else ctx in
  match ctx1, ctx2 with
    | bctx c1, bctx c2 => letdia_get_LF ctx' {{ctx1 // ctx2}}M {{bctx (S c1) // bctx (S c2)}}N
    | bctx c1, fctx c2 => letdia_get_LF ctx' {{ctx1 // ctx2}}M {{bctx (S c1) // ctx2}}N
    | fctx c1, bctx c2 => letdia_get_LF ctx' {{ctx1 // ctx2}}M {{ctx1 // bctx (S c2)}}N
    | fctx c1, fctx c2 => letdia_get_LF ctx' {{ctx1 // ctx2}}M {{ctx1 // ctx2}}N
  end
end
where " {{ c1 // c2 }} M " := (subst_ctx M c1 c2) : label_free_is5_scope.

Definition open_ctx M c := subst_ctx M c (bctx 0). 
Notation " M ^^ Gamma " := (open_ctx M Gamma) (at level 5) : label_free_is5_scope.

(* TODO: this may be too little - we may need "outer" substitution with context switch 
         and in that case when moving between contexts we will use "outer" substitution
         to find the next occ. of "our" context *)
Reserved Notation " [ M // n ] N " (at level 5).

Fixpoint subst_LF (M: te_LF) (n: nat) (N: te_LF) : te_LF :=
match N with
| hyp_LF n' => if eq_nat_dec n n' then M else N
| lam_LF A N' => lam_LF A [M//S n] N'
| appl_LF N1 N2 => appl_LF ([M // n] N1) ([M // n] N2)
| box_LF N' => box_LF ([M // n] N')
| unbox_LF N' => unbox_LF ([M // n] N')
| unbox_fetch_LF Ctx N' => N
| here_LF N' => here_LF ([M // n] N')
| get_here_LF Ctx N' => N
| letdia_LF N1 N2 => letdia_LF ([M // n] N1) ([M // S n ] N2)
| letdia_get_LF Ctx N1 N2 => N
end
where " [ M // n ] N " := (subst_LF M n N) : label_free_is5_scope.

Fixpoint subst_list L n N :=
match L with
| nil => N
| M :: L' => [ M // n ] (subst_list L' (S n) N)
end.

Close Scope label_free_is5_scope.