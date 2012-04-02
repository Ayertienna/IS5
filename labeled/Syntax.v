(* Metatheory package by Arthur Chargueraud, http://www.chargueraud.org/softs/ln/ *)
Require Export Metatheory.
Require Export Arith.
Require Export List.

Inductive ty :=
| tvar: ty
| tarrow: ty -> ty -> ty
| tbox: ty -> ty
| tdia: ty -> ty
.

Notation " A '--->' B " := (tarrow A B) (at level 30, right associativity) : is5_scope.
Notation " '[*]' A " := (tbox A) (at level 30) : is5_scope.
Notation " '<*>' A " := (tdia A) (at level 30) : is5_scope.

Open Scope is5_scope.

(* We use var from Metatheory package to represent free worlds *)
Inductive wo := 
| bwo: nat -> wo
| fwo: var -> wo
.

(* vars = fset var *)
Definition worlds := vars.

Axiom eq_var_dec:
  forall v1 v2: var, {v1 = v2} + {v1 <> v2}.

Theorem eq_wo_dec:
  forall w1 w2: wo, {w1 = w2} + {w1 <> w2}.
  decide equality.
    decide equality.
    apply eq_var_dec.
Qed.

Inductive te :=
| hyp: nat -> te
| lam: ty -> te -> te
| appl: te -> te -> te
| box: te -> te
| unbox: te -> te
| get: wo -> te -> te
| letd: te -> te -> te
| here: te -> te
| fetch: wo -> te -> te
.

(* Calculate list of free worlds used in term M *)
Fixpoint free_worlds (M: te) : fset var :=
match M with
| hyp _ => \{}
| lam _ M => free_worlds M
| appl M N => free_worlds M \u free_worlds N
| box M => free_worlds M
| unbox M => free_worlds M
| here M => free_worlds M
| letd M N => free_worlds M \u free_worlds N
| fetch (fwo w) M => \{w} \u free_worlds M
| fetch _ M => free_worlds M
| get (fwo w) M => \{w} \u free_worlds M
| get _ M => free_worlds M
end.

Definition fresh_world (w: var) (M: te) := w \notin (free_worlds M).

(* When a term is locally closed at level n *)
Inductive lc_w_n : te -> nat -> Prop :=
 | lcw_hyp: forall x n, lc_w_n (hyp x) n
 | lcw_lam: forall t M n, lc_w_n M n -> lc_w_n (lam t M) n
 | lcw_appl: forall M N n, lc_w_n M n -> lc_w_n N n -> lc_w_n (appl M N) n
 | lcw_box: forall M n, lc_w_n M (S n) -> lc_w_n (box M) n
 | lcw_unbox: forall M n, lc_w_n M n -> lc_w_n (unbox M) n
 | lcw_get: forall w M n, lc_w_n M n -> lc_w_n (get (fwo w) M) n
 | lcw_letd: forall M N n, lc_w_n N (S n) -> lc_w_n M n -> lc_w_n (letd M N) n
 | lcw_here: forall M n, lc_w_n M n -> lc_w_n (here M) n
 | lcw_fetch: forall w M n, lc_w_n M n -> lc_w_n (fetch (fwo w) M) n
.

(* Calculate list of unbound worlds of level above n *)
Fixpoint unbound_worlds (n:nat) (M:te) : list nat :=
match M with
| hyp n => nil
| lam t M => unbound_worlds n M
| appl M N => unbound_worlds n M ++ unbound_worlds n N
| box M => unbound_worlds (S n) M
| unbox M => unbound_worlds n M
| here M => unbound_worlds n M
| letd M N => unbound_worlds n M ++ unbound_worlds (S n) N
| fetch (bwo w) M => w :: unbound_worlds n M
| fetch (fwo w) M => unbound_worlds n M
| get (bwo w) M => w :: unbound_worlds n M
| get (fwo w) M => unbound_worlds n M
end.

Definition lc_w (t:te) : Prop := lc_w_n t 0.

Section Lemmas.

Lemma closed_w_succ:
forall M n,
  lc_w_n M n -> lc_w_n M (S n).
intros; generalize dependent n;
induction M; intros; inversion H; subst;
eauto using lc_w_n.
Qed.

Lemma closed_w_addition:
forall M n m,
  lc_w_n M n -> lc_w_n M (n + m).
intros; induction m.
replace (n+0) with n by auto; assumption.
replace (n+ S m) with (S (n+m)) by auto;
apply closed_w_succ; assumption.
Qed.


Lemma closed_no_unbound_worlds:
forall M n,
  lc_w_n M n -> unbound_worlds n M = nil.
intros.
generalize dependent n.
induction M; intros; simpl in *.
reflexivity.
apply IHM; inversion H; subst; assumption.
inversion H; subst;
rewrite IHM1; try rewrite IHM2; auto.
apply IHM; inversion H; subst; assumption.
apply IHM; inversion H; subst; assumption.
destruct w.
  inversion H; subst.
  apply IHM; inversion H; subst; assumption.
rewrite IHM1; try rewrite IHM2; inversion H; subst; auto.
apply IHM; inversion H; subst; assumption.
destruct w.
  inversion H; subst.
  apply IHM; inversion H; subst; assumption.
Qed.

End Lemmas.

Close Scope is5_scope.