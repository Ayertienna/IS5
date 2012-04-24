Require Export Syntax.
Require Import Arith.
Require Import List.
Open Scope is5_scope.

Reserved Notation " [ M // x ] N " (at level 5).

Fixpoint subst (M:te) (n:nat) (N:te) : te :=
match N with
| hyp n' => if (eq_nat_dec n n') then M else N
| lam A N' => lam A ([M // S n]N')
| appl N1 N2 => appl ([M//n]N1) ([M//n]N2)
| box N' => box [M//n]N'
| unbox N' => unbox [M//n]N'
| unbox_fetch N'=> unbox_fetch [M//n]N'
| here N' => here [M//n]N'
| get_here N' => get_here [M//n]N'
| letdia N1 N2 => letdia [M//n]N1 [M//S n]N2
| letdia_get N1 N2 => letdia_get [M//n]N1 [M//S n]N2
end
where " [ M // x ] N " := (subst M x N) : is5_scope.

(* Substitute L[0] for n, L[1] for n+1,.. in M *)
Fixpoint subst_list L n N :=
match L with
| nil => N
| M :: L' => [M//n] (subst_list L' (S n) N)
end.


Close Scope is5_scope.