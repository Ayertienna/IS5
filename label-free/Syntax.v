(* Types are exactly the same and should be shared between two languages *)
Inductive ty_LF :=
| tvar_LF: ty_LF
| tarrow_LF: ty_LF -> ty_LF -> ty_LF
| tbox_LF: ty_LF -> ty_LF
| tdia_LF: ty_LF -> ty_LF
.

(* So are notations *)
Notation " A '--->' B " := (tarrow_LF A B) (at level 30, right associativity) : label_free_is5_scope.
Notation " '[*]' A " := (tbox_LF A) (at level 30) : label_free_is5_scope.
Notation " '<*>' A " := (tdia_LF A) (at level 30) : label_free_is5_scope.

Open Scope label_free_is5_scope.

Inductive te_LF :=
| hyp_LF: nat -> te_LF
| lam_LF: ty_LF -> te_LF -> te_LF
| appl_LF: te_LF -> te_LF -> te_LF
| box_LF: te_LF -> te_LF
| unbox_LF: te_LF -> te_LF
| unbox_fetch_LF: te_LF -> te_LF
| here_LF: te_LF -> te_LF
| get_here_LF: te_LF -> te_LF
| letdia_LF: te_LF -> te_LF -> te_LF
| letdia_get_LF: te_LF -> te_LF -> te_LF
.

Close Scope label_free_is5_scope.
