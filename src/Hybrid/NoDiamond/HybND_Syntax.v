Add LoadPath "../..".
Require Export HybND_Shared.
Require Export PermutLib.

(*** Definitions ***)

(*
Terms in label-free IS5 system:
  * hypothesis
  * lambda expression
  * application
  * box expression
  * unpacking box (possibly in a different world)
  * diamond expression (possibly in a different world)
  * using diamond expression (possibly the diamond itself is from a
  different world)
*)
Inductive te_Hyb :=
| hyp_Hyb: vte -> te_Hyb
| lam_Hyb: ty -> te_Hyb -> te_Hyb
| appl_Hyb: te_Hyb -> te_Hyb -> te_Hyb
| box_Hyb: te_Hyb -> te_Hyb
| unbox_fetch_Hyb: vwo -> te_Hyb -> te_Hyb
.


(* Calculate set of free worlds used in term M *)
Fixpoint free_worlds_Hyb (M: te_Hyb) : fset var :=
match M with
| hyp_Hyb _ => \{}
| lam_Hyb _ M => free_worlds_Hyb M
| appl_Hyb M N => free_worlds_Hyb M \u free_worlds_Hyb N
| box_Hyb M => free_worlds_Hyb M
| unbox_fetch_Hyb (fwo w) M => \{w} \u free_worlds_Hyb M
| unbox_fetch_Hyb _ M => free_worlds_Hyb M
end.

(* Calculate set of free variables used in term M *)
Fixpoint free_vars_Hyb (M: te_Hyb) : fset var :=
match M with
| hyp_Hyb (fte v) => \{v}
| hyp_Hyb (bte _) => \{}
| lam_Hyb _ M => free_vars_Hyb M
| appl_Hyb M N => free_vars_Hyb M \u free_vars_Hyb N
| box_Hyb M => free_vars_Hyb M
| unbox_fetch_Hyb _ M => free_vars_Hyb M
end.


(*
Property: term is locally closed
 This means that there are no bound variables.
*)

Inductive lc_t_n_Hyb : nat -> te_Hyb -> Prop :=
 | lct_hyp_bte_Hyb: forall v n, n > v -> lc_t_n_Hyb n (hyp_Hyb (bte v))
 | lct_hyp_fte_Hyb: forall v n, lc_t_n_Hyb n (hyp_Hyb (fte v))
 | lct_lam_Hyb: forall M t n,
     lc_t_n_Hyb (S n) M ->
     lc_t_n_Hyb n (lam_Hyb t M)
 | lct_appl_Hyb: forall M N n,
     lc_t_n_Hyb n M -> lc_t_n_Hyb n N ->
     lc_t_n_Hyb n (appl_Hyb M N)
 | lct_box_Hyb: forall M n,
     lc_t_n_Hyb n M ->
     lc_t_n_Hyb n (box_Hyb M)
 | lct_unbox_fetch_Hyb: forall M w n,
     lc_t_n_Hyb n M ->
     lc_t_n_Hyb n (unbox_fetch_Hyb w M)
.

Definition lc_t_Hyb M := lc_t_n_Hyb 0 M.


Inductive lc_w_n_Hyb: nat -> te_Hyb -> Prop :=
| lcw_hyp_Hyb: forall v n, lc_w_n_Hyb n (hyp_Hyb v)
| lcw_lam_Hyb: forall t M n,
    lc_w_n_Hyb n M ->
    lc_w_n_Hyb n (lam_Hyb t M)
| lcw_appl_Hyb: forall M N n,
    lc_w_n_Hyb n M -> lc_w_n_Hyb n N ->
    lc_w_n_Hyb n (appl_Hyb M N)
| lcw_box_Hyb: forall M n,
    lc_w_n_Hyb (S n) M ->
    lc_w_n_Hyb n (box_Hyb M)
| lcw_unbox_fetch_fwo_Hyb: forall M w n,
    lc_w_n_Hyb n M ->
    lc_w_n_Hyb n (unbox_fetch_Hyb (fwo w) M)
| lcw_unbox_fetch_bwo_Hyb: forall M n m,
    lc_w_n_Hyb n M -> n > m ->
    lc_w_n_Hyb n (unbox_fetch_Hyb (bwo m) M)
.

Definition lc_w_Hyb M := lc_w_n_Hyb 0 M.


(*** Properties ***)


(* For each pair of contexts, they are either equivalent or not. *)
Theorem permut_context_Hyb_dec:
forall (c1 c2: ctx_Hyb),
    permut (snd c1) (snd c2) /\ (fst c1) = (fst c2) \/
   ~permut (snd c1) (snd c2) \/ (fst c1) <> (fst c2).
intros; destruct c1 as (w, a); destruct c2 as (w', a');
destruct (eq_var_dec w w'); subst; simpl;
destruct (permut_Dec (var * ty) a a'); simpl;
auto; intros;
repeat decide equality;
apply eq_var_dec.
Qed.


(* Propagation of lc_*_n_Hyb property *)

Lemma closed_w_succ:
forall M n,
  lc_w_n_Hyb n M -> lc_w_n_Hyb (S n) M.
intros; generalize dependent n;
induction M; intros; inversion H; subst;
eauto using lc_w_n_Hyb.
constructor; [ | omega]; eauto.
Qed.

Lemma closed_t_succ:
forall M n,
  lc_t_n_Hyb n M -> lc_t_n_Hyb (S n) M.
intros; generalize dependent n;
induction M; intros; inversion H; subst;
eauto using lc_t_n_Hyb.
Qed.

Lemma closed_w_addition:
forall M n m,
  lc_w_n_Hyb n M -> lc_w_n_Hyb (n + m) M.
intros; induction m;
[ replace (n+0) with n by auto |
  replace (n+ S m) with (S (n+m)) by auto] ;
try apply closed_w_succ;
assumption.
Qed.

Lemma closed_t_addition:
forall M n m,
  lc_t_n_Hyb n M -> lc_t_n_Hyb (n + m) M.
intros; induction m;
[ replace (n+0) with n by auto |
  replace (n + S m) with (S (n+m)) by auto] ;
try apply closed_t_succ;
assumption.
Qed.