Require Import Metatheory.

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
| unbox_LF: te_LF -> te_LF
| unbox_fetch_LF: ctx_LF -> te_LF -> te_LF
| here_LF: te_LF -> te_LF
| get_here_LF: ctx_LF -> te_LF -> te_LF
| letdia_LF: te_LF -> te_LF -> te_LF
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

Theorem eq_ty_LF_dec:
forall t1 t2: ty_LF, {t1 = t2} + {t1 <> t2}.
intros; decide equality.
Qed.

Theorem eq_te_LF_dec:
forall t1 t2: te_LF, {t1 = t2} + {t1 <> t2}.
intros; decide equality.
decide equality.
decide equality.
apply eq_ctx_LF_dec.
apply eq_ctx_LF_dec.
apply eq_ctx_LF_dec.
Qed.

Close Scope label_free_is5_scope.
