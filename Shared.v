Require Import Metatheory.

(* Definitions *)

(* 
Types in IS5 system:
   * base type
   * arrow type for functions
   * box type for universally true terms
   * diamond type for existentially true terms
*)
Inductive ty :=
| tvar: ty
| tarrow: ty -> ty -> ty
| tbox: ty -> ty
| tdia: ty -> ty
.
Notation " A '--->' B " := (tarrow A B) 
  (at level 30, right associativity) : is5_scope.
Notation " '[*]' A " := (tbox A) 
  (at level 30) : is5_scope.
Notation " '<*>' A " := (tdia A) 
  (at level 30) : is5_scope.

(*
Variables for worlds - bound and free
*)
Inductive vwo := 
| bwo: nat -> vwo
| fwo: var -> vwo
.

(*
Variables for terms - bound and free
*)
Inductive vte :=
| bte: nat -> vte
| fte: var -> vte
.

(* Properties *)

(* Decidability *)

Theorem eq_ty_dec:
forall a b: ty, {a = b} + {a <> b}.
  decide equality. 
Qed.

(* 
Decidability for var is not expressed in the library, so we need to
assume is manually.
*)
Axiom eq_var_dec:
  forall v1 v2: var, {v1 = v2} + {v1 <> v2}.

Theorem eq_vwo_dec:
forall w1 w2: vwo, {w1 = w2} + {w1 <> w2}.
  decide equality.
  decide equality.
  apply eq_var_dec.
Qed.

Theorem eq_vte_dec:
forall v1 v2: vte, {v1 = v2} + {v1 <> v2}.
  decide equality.
  decide equality.
  apply eq_var_dec.
Qed.

(* Free variable extraction *)

Definition var_from_vwo (w: vwo) :=
match w with
| fwo w0 => \{w0}
| bwo _ => \{}
end.

Definition var_from_vte (v: vte) :=
match v with
| fte v0 => \{v0}
| bte _ => \{}
end.

(* Shared definitions *)

Definition Context_LF := prod var (list (prod var ty)).
Definition Background_LF := list Context_LF.

