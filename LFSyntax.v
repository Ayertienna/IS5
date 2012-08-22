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


(* Calculate set of free worlds used in term M *)
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

(* Calculate set of free variables used in term M *)
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
