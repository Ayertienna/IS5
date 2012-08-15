Require Export Shared.
Require Export LibList.


(*** Definitions ***)

(*
Terms in label-free IS5 system:
  * hypothesis
  * lambda expression
  * application
  * box expression
  * unpacking box (possibly in a different world)
  * diamond expression (possibly in a different world)
  * using diamond expression (possibly diamond is from a different world)
*)
Inductive te_LF :=
| hyp_LF: vte -> te_LF
| lam_LF: ty -> te_LF -> te_LF
| appl_LF: te_LF -> te_LF -> te_LF
| box_LF: te_LF -> te_LF
| unbox_fetch_LF: vwo -> te_LF -> te_LF
| get_here_LF: vwo -> te_LF -> te_LF
| letdia_get_LF: vwo -> te_LF -> te_LF -> te_LF
.


(*
Property: term is locally closed
 This means that there are no bound variables.
*)

Inductive lc_w_LF : te_LF -> Prop :=
 | lcw_hyp_LF: forall v, lc_w_LF (hyp_LF v)
 | lcw_lam_LF: forall t M,
     lc_w_LF M ->
     lc_w_LF (lam_LF t M)
 | lcw_appl_LF: forall M N,
     lc_w_LF M -> lc_w_LF N ->
     lc_w_LF (appl_LF M N)
 | lcw_box_LF: forall M,
     lc_w_LF M ->
     lc_w_LF (box_LF M)
 | lcw_unbox_fetch_LF: forall M w,
     lc_w_LF M ->
     lc_w_LF (unbox_fetch_LF (fwo w) M)
 | lcw_get_here_LF: forall M w,
     lc_w_LF M ->
     lc_w_LF (get_here_LF (fwo w) M)
 | lcw_letdia_get_LF: forall M N w,
     lc_w_LF N -> lc_w_LF M ->
     lc_w_LF (letdia_get_LF (fwo w) M N)
.

Inductive lc_t_LF: te_LF -> Prop :=
| lct_hyp_LF: forall v, lc_t_LF (hyp_LF (fte v))
| lct_lam_LF: forall t M,
    lc_t_LF M ->
    lc_t_LF (lam_LF t M)
| lct_appl_LF: forall M N,
    lc_t_LF M -> lc_t_LF N ->
    lc_t_LF (appl_LF M N)
 | lct_box_LF: forall M,
     lc_t_LF M ->
     lc_t_LF (box_LF M)
 | lct_unbox_fetch_LF: forall M w,
     lc_t_LF M ->
     lc_t_LF (unbox_fetch_LF (fwo w) M)
 | lct_get_here_LF: forall M w,
     lc_t_LF M ->
     lc_t_LF (get_here_LF (fwo w) M)
 | lct_letdia_get_LF: forall M N w,
     lc_t_LF N -> lc_t_LF M ->
     lc_t_LF (letdia_get_LF (fwo w) M N)
.

(* Calculate list of free worlds used in term M *)
Fixpoint free_worlds_LF (M: te_LF) : fset var :=
match M with
| hyp_LF _ => \{}
| lam_LF _ M => free_worlds_LF M
| appl_LF M N => free_worlds_LF M \u free_worlds_LF N
| box_LF M => free_worlds_LF M
| unbox_fetch_LF (fwo w) M => \{w} \u free_worlds_LF M
| unbox_fetch_LF _ M => free_worlds_LF M
| get_here_LF (fwo w) M => \{w} \u free_worlds_LF M
| get_here_LF _ M => free_worlds_LF M
| letdia_get_LF (fwo w) M N => \{w} \u free_worlds_LF M \u free_worlds_LF N
| letdia_get_LF _ M N => free_worlds_LF M \u free_worlds_LF N
end.

(* Calculate list of free variables used in term M *)
Fixpoint free_vars_LF (M: te_LF) : fset var :=
match M with
| hyp_LF (fte v) => \{v}
| hyp_LF (bte _) => \{}
| lam_LF _ M => free_vars_LF M
| appl_LF M N => free_vars_LF M \u free_vars_LF N
| box_LF M => free_vars_LF M
| unbox_fetch_LF _ M => free_vars_LF M
| get_here_LF _ M => free_vars_LF M
| letdia_get_LF _ M N => free_vars_LF M \u free_vars_LF N
end.

(* Calculate list of bound worlds in the term *)
Fixpoint bound_worlds (M: te_LF) :=
match M with
| hyp_LF n => nil
| lam_LF t M => bound_worlds M
| appl_LF M N => bound_worlds M ++ bound_worlds N
| box_LF M => bound_worlds M
| unbox_fetch_LF (bwo w) M => w :: bound_worlds M
| unbox_fetch_LF (fwo w) M => bound_worlds M
| get_here_LF (bwo w) M => w :: bound_worlds M
| get_here_LF (fwo w) M => bound_worlds M
| letdia_get_LF (bwo w) M N => w :: bound_worlds M ++ bound_worlds N
| letdia_get_LF (fwo w) M N => bound_worlds M ++ bound_worlds N
end.

(* Calculate list of bound variables of level above n *)
Fixpoint bound_vars (M: te_LF) :=
match M with
| hyp_LF (bte n) => n::nil
| hyp_LF (fte n) => nil
| lam_LF t M => bound_vars M
| appl_LF M N => bound_vars M ++ bound_vars N
| box_LF M => bound_vars M
| unbox_fetch_LF _ M => bound_vars M
| get_here_LF _ M => bound_vars M
| letdia_get_LF _ M N => bound_vars M ++ bound_vars N
end.


(*** Properties ***)


(* For each pair of contexts, they are either equivalent or not. *)
Theorem permut_context_LF_dec:
forall (c1 c2: Context_LF),
  {  permut (snd c1) (snd c2) /\ (fst c1) = (fst c2)} +
  { ~permut (snd c1) (snd c2) \/ (fst c1) <> (fst c2)}.
intros; destruct c1 as (w, a); destruct c2 as (w', a');
destruct (eq_var_dec w w'); subst; simpl;
destruct (permut_dec a a'); simpl;
auto.
Qed.


(* If term is closed at some level, it does not contain bound variables*)

Lemma closed_w_no_bound_worlds:
forall M,
  lc_w_LF M -> bound_worlds M = nil.
intros;
induction M; intros; simpl in *;
inversion H; subst; eauto;
erewrite IHM1; try erewrite IHM2; eauto.
Qed.

Lemma closed_t_no_bound_vars:
forall M,
  lc_t_LF M -> bound_vars M = nil.
intros;
induction M; intros; simpl in *;
inversion H; subst; eauto;
erewrite IHM1; try erewrite IHM2; eauto;
apply closed_t_succ; assumption.
Qed.
