(* Labeled using lists *)
Require Export Shared.
Require Export LibList.

Definition worlds_L := list var.

Inductive te_L :=
| hyp_L: vte -> te_L
| lam_L: ty -> te_L -> te_L
| appl_L: te_L -> te_L -> te_L
| box_L: te_L -> te_L
| unbox_L: te_L -> te_L
| get_L: vwo -> te_L -> te_L
| letd_L: te_L -> te_L -> te_L
| here_L: te_L -> te_L
| fetch_L: vwo -> te_L -> te_L
.
