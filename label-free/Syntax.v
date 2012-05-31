Require Import Metatheory.
Require Import List.

Inductive ty_LF :=
| tvar_LF: ty_LF
| tarrow_LF: ty_LF -> ty_LF -> ty_LF
| tbox_LF: ty_LF -> ty_LF
| tdia_LF: ty_LF -> ty_LF
.

Notation " A '--->' B " := (tarrow_LF A B) (at level 30, right associativity) : label_free_is5_scope.
Notation " '[*]' A " := (tbox_LF A) (at level 30) : label_free_is5_scope.
Notation " '<*>' A " := (tdia_LF A) (at level 30) : label_free_is5_scope.

Open Scope label_free_is5_scope.

Definition Context_LF := prod var (list ty_LF).
Definition Background_LF := list Context_LF.

Inductive ctx_LF :=
| bctx: nat -> ctx_LF
| fctx: var -> ctx_LF.


Inductive te_LF :=
| hyp_LF: nat -> te_LF
| lam_LF: ty_LF -> te_LF -> te_LF
| appl_LF: te_LF -> te_LF -> te_LF
| box_LF: te_LF -> te_LF
| unbox_fetch_LF: ctx_LF -> te_LF -> te_LF
| get_here_LF: ctx_LF -> te_LF -> te_LF
| letdia_get_LF: ctx_LF -> te_LF -> te_LF -> te_LF
.

Axiom eq_var_LF_dec:
  forall v1 v2: var, {v1 = v2} + {v1 <> v2}.

Theorem eq_context_LF_dec:
forall c1 c2: Context_LF, {c1 = c2} + {c1 <> c2}.
intros.
decide equality.
decide equality.
decide equality.
apply eq_var_LF_dec.
Qed.

Theorem eq_ctx_LF_dec:
forall c1 c2: ctx_LF, {c1 = c2} + {c1 <> c2}.
intros.
decide equality.
decide equality.
apply eq_var_LF_dec. 
Qed.

(* When a term is locally closed at level n *)
Inductive lc_w_n_LF : te_LF -> nat -> Prop :=
 | lcw_hyp_LF: forall x n, lc_w_n_LF (hyp_LF x) n
 | lcw_lam_LF: forall t M n, 
     lc_w_n_LF M n -> 
     lc_w_n_LF (lam_LF t M) n
 | lcw_appl_LF: forall M N n, 
     lc_w_n_LF M n -> lc_w_n_LF N n -> 
     lc_w_n_LF (appl_LF M N) n
 | lcw_box_LF: forall M n, 
     lc_w_n_LF M (S n) -> 
     lc_w_n_LF (box_LF M) n
 | lcw_unbox_fetch_LF: forall M n w, 
     lc_w_n_LF M n -> 
     lc_w_n_LF (unbox_fetch_LF (fctx w) M) n
 | lcw_get_here_LF: forall M n w , 
     lc_w_n_LF M n -> 
     lc_w_n_LF (get_here_LF (fctx w) M) n
 | lcw_letdia_get_LF: forall M N n w, 
     lc_w_n_LF N (S n) -> lc_w_n_LF M n -> 
     lc_w_n_LF (letdia_get_LF (fctx w) M N) n
.

Definition lc_w_LF (t:te_LF) : Prop := lc_w_n_LF t 0.

(* Calculate list of free worlds used in term M *)
Fixpoint free_worlds_LF (M: te_LF) : fset var :=
match M with
| hyp_LF _ => \{}
| lam_LF _ M => free_worlds_LF M
| appl_LF M N => free_worlds_LF M \u free_worlds_LF N
| box_LF M => free_worlds_LF M
| unbox_fetch_LF (fctx w) M => \{w} \u free_worlds_LF M
| unbox_fetch_LF _ M => free_worlds_LF M
| get_here_LF (fctx w) M => \{w} \u free_worlds_LF M
| get_here_LF _ M => free_worlds_LF M
| letdia_get_LF (fctx w) M N => \{w} \u free_worlds_LF M \u free_worlds_LF N
| letdia_get_LF _ M N => free_worlds_LF M \u free_worlds_LF N
end.

Section Lemmas.

Lemma closed_w_succ:
forall M n,
  lc_w_n_LF M n -> lc_w_n_LF M (S n).
intros; generalize dependent n;
induction M; intros; inversion H; subst;
eauto using lc_w_n_LF.
Qed.

End Lemmas.

Close Scope label_free_is5_scope.
