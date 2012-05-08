Require Export Syntax.
Require Import Arith.
Require Import List.

Open Scope label_free_is5_scope.

Reserved Notation " [ M // x  | CtxSubst ] [ N | CtxCurr ] " (at level 5).

(* "outer" substitution - current context is not the one in which we want to substitute *)
Fixpoint find_subst (M: te_LF) (n: nat) (N: te_LF) (CtxSubst: Context_LF) (CtxCurr: Context_LF) {struct N} : te_LF :=
match N with
| hyp_LF n' => N
| lam_LF A N' => lam_LF A (find_subst M n N' CtxSubst (A::CtxCurr))
| appl_LF N1 N2 => 
  appl_LF (find_subst M n N1 CtxSubst CtxCurr) (find_subst M n N2 CtxSubst CtxCurr)
(* unsure  - maybe skip the matching? *)
| box_LF N' => 
  match (eq_context_LF_dec CtxSubst nil) with
    | left _ => box_LF (inner_subst M n N' nil)
    | right _ => box_LF (find_subst M n N' CtxSubst nil) 
  end
| unbox_LF N' => unbox_LF (find_subst M n N' CtxSubst CtxCurr)
| unbox_fetch_LF N' CtxSwitch => 
  match (eq_context_LF_dec CtxSubst CtxSwitch) with
    | left _ => unbox_fetch_LF (inner_subst M n N' CtxSwitch) CtxSwitch
    | right _ => unbox_fetch_LF (find_subst M n N' CtxSubst CtxSwitch) CtxSwitch
  end
| here_LF N' => here_LF (find_subst M n N' CtxSubst CtxCurr)
| get_here_LF N' CtxSwitch => 
  match (eq_context_LF_dec CtxSubst CtxSwitch) with
    | left _ => get_here_LF (inner_subst M n N' CtxSwitch) CtxSwitch
    | right _ => get_here_LF (find_subst M n N' CtxSubst CtxSwitch) CtxSwitch
  end
| letdia_LF N1 N2 => 
  letdia_LF (find_subst M n N1 CtxSubst CtxCurr) (find_subst M n N2 CtxSubst CtxCurr)
| letdia_get_LF N1 N2 CtxSwitch => 
  match (eq_context_LF_dec CtxSubst CtxSwitch) with
    | left _ => letdia_get_LF (inner_subst M n N1 CtxSwitch) 
                              (find_subst M n N2 CtxSubst CtxCurr) CtxSwitch
    | right _ => letdia_get_LF (find_subst M n N1 CtxSubst CtxSwitch) 
                               (find_subst M n N2 CtxSubst CtxCurr) CtxSwitch
  end
end
with
(* "inner" substitution - the usual substitution; when we change context, we go back to 
   "outer" *)
inner_subst (M: te_LF) (n: nat) (N: te_LF) (CtxCurr: Context_LF) {struct N} : te_LF :=
match N with
| hyp_LF n' => if (eq_nat_dec n n') then M else N
| lam_LF A N' => lam_LF A (inner_subst M (S n) N' (A::CtxCurr))
| appl_LF N1 N2 => appl_LF (inner_subst M n N1 CtxCurr) (inner_subst M n N2 CtxCurr)
| box_LF N' => box_LF (find_subst M n N' CtxCurr nil)
| unbox_LF N' => unbox_LF (inner_subst M n N' CtxCurr)
| unbox_fetch_LF N' CtxSwitch => 
  unbox_fetch_LF (find_subst M n N' CtxCurr CtxSwitch) CtxSwitch
| here_LF N' => here_LF (inner_subst M n N' CtxCurr)
| get_here_LF N' CtxSwitch => get_here_LF (find_subst M n N' CtxCurr CtxSwitch) CtxSwitch
| letdia_LF N1 N2 => letdia_LF (inner_subst M n N1 CtxCurr) (inner_subst M n N2 CtxCurr)
| letdia_get_LF N1 N2 CtxSwitch => 
  letdia_get_LF (find_subst M n N1 CtxCurr CtxSwitch)
                (inner_subst M n N2 CtxCurr) CtxSwitch 
end.

Definition subst_LF (M:te_LF) (n:nat) (Delta: Context_LF) 
                  (N:te_LF) (Gamma: Context_LF): te_LF := 
match (eq_context_LF_dec Delta Gamma) with
| left _ => inner_subst M n N Gamma
| right _ => find_subst M n N Gamma Delta
end.

Notation " [ M // x | Delta ] [ N | Gamma ] " := (subst_LF M x Delta N Gamma) : label_free_is5_scope.


(* Substitute L[0] for n, L[1] for n+1,.. in M *)
(* unsure - maybe we should allow each substitution to have a different CtxSubst? *) 
Fixpoint subst_list L n N CtxSubst CtxCurr :=
match L with
| nil => N
| M :: L' => [ M // n | CtxSubst] [(subst_list L' (S n) N CtxSubst CtxCurr) | CtxCurr]
end.

Close Scope label_free_is5_scope.