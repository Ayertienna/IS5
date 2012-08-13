Require Export Utf8.

(* Package not included in standard Coq builds, needs to be downloaded from
   http://www.chargueraud.org/softs/ln/ *)
Require Export LibVar.

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

(*** Properties ***)


(* Decidability *)

(* 
Decidability for var is not expressed in the library, so we need to
assume is manually.
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


(* Calculate shift by one for variable *)

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


(*** Shared definitions ***)

(* Potentially removable once we have generic libraries *)

Definition Context_LF := prod var (list (prod var ty)).
Definition Background_LF := list Context_LF.
