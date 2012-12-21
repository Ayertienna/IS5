Require Import PermutLib.
Require Import LFFSyntax.
Require Import Arith.

Open Scope permut_scope.

Reserved Notation " [ M // x ] N " (at level 5).

Fixpoint subst_t_LF M x N :=
match N with
| hyp_LF v => if (eq_vte_dec x v) then M else N
| lam_LF t N' => lam_LF t [M//shift_vte x]N'
| appl_LF N' N'' => appl_LF [M//x]N' [M//x]N''
| box_LF N' => box_LF [M//x]N'
| unbox_LF N' => unbox_LF [M//x]N'
| here_LF N' => here_LF [M//x]N'
| letdia_LF N' N'' => letdia_LF [M//x]N' [M//shift_vte x]N''
end
where " [ M // x ] N " := (subst_t_LF M x N).

Definition open_LF (M: te_LF) (t: te_LF) := subst_t_LF t (bte 0) M.
Notation " M '^t^' t " := (open_LF M t) (at level 67).
