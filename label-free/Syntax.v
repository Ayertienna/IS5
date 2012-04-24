(* Types are exactly the same and should be shared between two languages *)
Inductive ty :=
| tvar: ty
| tarrow: ty -> ty -> ty
| tbox: ty -> ty
| tdia: ty -> ty
.

(* So are notations *)
Notation " A '--->' B " := (tarrow A B) (at level 30, right associativity) : is5_scope.
Notation " '[*]' A " := (tbox A) (at level 30) : is5_scope.
Notation " '<*>' A " := (tdia A) (at level 30) : is5_scope.

(* TODO: we'll need separate scopes for labeled and label-free version *)
Open Scope is5_scope.

Inductive te :=
| hyp: nat -> te
| lam: ty -> te -> te
| appl: te -> te -> te
| box: te -> te
| unbox: te -> te
| unbox_fetch: te -> te
| here: te -> te
| get_here: te -> te
| letdia: te -> te -> te
| letdia_get: te -> te -> te
.

Close Scope is5_scope.
