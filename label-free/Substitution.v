Require Export Syntax.
Require Import Arith.
Require Import List.

Open Scope label_free_is5_scope.

Reserved Notation " [ M // x ] N " (at level 5).

Fixpoint subst_LF (M:te_LF) (n:nat) (N:te_LF) : te_LF :=
match N with
| hyp_LF n' => if (eq_nat_dec n n') then M else N
| lam_LF A N' => lam_LF A ([M // S n]N')
| appl_LF N1 N2 => appl_LF ([M//n]N1) ([M//n]N2)
| box_LF N' => box_LF [M//n]N'
| unbox_LF N' => unbox_LF [M//n]N'
| unbox_fetch_LF N'=> unbox_fetch_LF [M//n]N'
| here_LF N' => here_LF [M//n]N'
| get_here_LF N' => get_here_LF [M//n]N'
| letdia_LF N1 N2 => letdia_LF [M//n]N1 [M//S n]N2
| letdia_get_LF N1 N2 => letdia_get_LF [M//n]N1 [M//S n]N2
end
where " [ M // x ] N " := (subst_LF M x N) : label_free_is5_scope.

(* Substitute L[0] for n, L[1] for n+1,.. in M *)
Fixpoint subst_list L n N :=
match L with
| nil => N
| M :: L' => [M//n] (subst_list L' (S n) N)
end.

Close Scope label_free_is5_scope.