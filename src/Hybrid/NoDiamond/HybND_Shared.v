Require Export Utf8.
Require Export LibVar.
Require Export LibListSorted.


(*** Definitions ***)

(*
Types in IS5 system:
  * base type
  * arrow type for functions
  * box type for universally true terms (= in all the worlds)
  * diamond type for existentially true terms (= in some of the worlds)
*)
Inductive ty :=
| tvar: ty
| tarrow: ty -> ty -> ty
| tbox: ty -> ty
.
Notation " A '--->' B " := (tarrow A B)
  (at level 30, right associativity) : is5_scope.
Notation " '[*]' A " := (tbox A)
  (at level 30) : is5_scope.

(*
Variables for worlds - bound and free
  We are using locally nameless representation for world variables.
*)
Inductive vwo :=
| bwo: nat -> vwo
| fwo: var -> vwo
.

(*
Variables for terms - bound and free
  We are using locally nameless representation for term variables.
*)
Inductive vte :=
| bte: nat -> vte
| fte: var -> vte
.


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


(* "shift by one" for bound variable *)

Definition shift_vwo (w: vwo) : vwo :=
match w with
  | fwo _ => w
  | bwo n => bwo (S n)
end.

Definition shift_vte (v: vte) : vte :=
match v with
| fte _ => v
| bte n => bte (S n)
end.


(*** Properties ***)


(* Decidability *)

(*
Decidability for var is not expressed in the library, so we need to
add an axiom for it.
*)
Axiom eq_var_dec:
  forall v1 v2: var, {v1 = v2} + {v1 <> v2}.

Theorem eq_ty_dec:
forall a b: ty, {a = b} + {a <> b}.
  decide equality.
Qed.

Theorem eq_vwo_dec:
forall w1 w2: vwo, {w1 = w2} + {w1 <> w2}.
  decide equality;
  [ decide equality |
    apply eq_var_dec].
Qed.

Theorem eq_vte_dec:
forall v1 v2: vte, {v1 = v2} + {v1 <> v2}.
  decide equality;
  [ decide equality |
    apply eq_var_dec].
Qed.

(* Generating new variable produces fresh variable *)
Lemma generate_fresh:
forall L w
  (HIn: w \in L),
  var_gen L <> w.
intros;
intro; subst;
absurd (var_gen L \in L);
[apply var_gen_spec | assumption].
Qed.

(* For every set of variables, we can generate a variable that is
   not within that set *)
Lemma Fresh:
forall (L: fset var), exists w0, w0 \notin L.
intro;
exists (var_gen L);
apply var_gen_spec.
Qed.


(*** Shared definitions ***)

(* Background and context for hybrid language *)
Definition ctx_Hyb := prod var (list (prod var ty)).
Definition bg_Hyb := list ctx_Hyb.

(* Context for labeled language *)
Definition ctx_L := list (prod var (prod var ty)).

(* Background and context for label-free language *)
Definition ctx_LF := list (var * ty).
Definition bg_LF := list ctx_LF.