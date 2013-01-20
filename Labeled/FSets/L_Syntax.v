Add LoadPath "../..".
Require Export Shared.
Require Import Arith.
Require Import List.

(* vars = fset var *)
Definition worlds_L := vars.

Inductive te_L :=
| hyp_L: nat -> te_L
| lam_L: ty -> te_L -> te_L
| appl_L: te_L -> te_L -> te_L
| box_L: te_L -> te_L
| unbox_L: te_L -> te_L
| get_L: vwo -> te_L -> te_L
| letdia_L: te_L -> te_L -> te_L
| here_L: te_L -> te_L
| fetch_L: vwo -> te_L -> te_L
.

(* Calculate list of free worlds used in term M *)
Fixpoint free_worlds_L (M: te_L) : fset var :=
match M with
| hyp_L _ => \{}
| lam_L _ M => free_worlds_L M
| appl_L M N => free_worlds_L M \u free_worlds_L N
| box_L M => free_worlds_L M
| unbox_L M => free_worlds_L M
| here_L M => free_worlds_L M
| letdia_L M N => free_worlds_L M \u free_worlds_L N
| fetch_L (fwo w) M => \{w} \u free_worlds_L M
| fetch_L _ M => free_worlds_L M
| get_L (fwo w) M => \{w} \u free_worlds_L M
| get_L _ M => free_worlds_L M
end.

Definition fresh_world_L (w: var) (M: te_L) := w \notin (free_worlds_L M).

(* When a term is locally closed at level n *)
Inductive lc_w_n_L : te_L -> nat -> Prop :=
 | lcw_hyp: forall x n, lc_w_n_L (hyp_L x) n
 | lcw_lam: forall t M n, lc_w_n_L M n -> lc_w_n_L (lam_L t M) n
 | lcw_appl: forall M N n,
   lc_w_n_L M n -> lc_w_n_L N n -> lc_w_n_L (appl_L M N) n
 | lcw_box: forall M n, lc_w_n_L M (S n) -> lc_w_n_L (box_L M) n
 | lcw_unbox: forall M n, lc_w_n_L M n -> lc_w_n_L (unbox_L M) n
 | lcw_get: forall w M n, lc_w_n_L M n -> lc_w_n_L (get_L (fwo w) M) n
 | lcw_letdia: forall M N n, lc_w_n_L N (S n) -> lc_w_n_L M n ->
   lc_w_n_L (letdia_L M N) n
 | lcw_here: forall M n, lc_w_n_L M n -> lc_w_n_L (here_L M) n
 | lcw_fetch: forall w M n, lc_w_n_L M n -> lc_w_n_L (fetch_L (fwo w) M) n
.

(* Calculate list of unbound worlds of level above n *)
Fixpoint unbound_worlds_L (n:nat) (M:te_L) : list nat :=
match M with
| hyp_L n => nil
| lam_L t M => unbound_worlds_L n M
| appl_L M N => unbound_worlds_L n M ++ unbound_worlds_L n N
| box_L M => unbound_worlds_L (S n) M
| unbox_L M => unbound_worlds_L n M
| here_L M => unbound_worlds_L n M
| letdia_L M N => unbound_worlds_L n M ++ unbound_worlds_L (S n) N
| fetch_L (bwo w) M => w :: unbound_worlds_L n M
| fetch_L (fwo w) M => unbound_worlds_L n M
| get_L (bwo w) M => w :: unbound_worlds_L n M
| get_L (fwo w) M => unbound_worlds_L n M
end.

Definition lc_w_L (t:te_L) : Prop := lc_w_n_L t 0.

Section Lemmas.

Lemma closed_w_succ_L:
forall M n,
  lc_w_n_L M n -> lc_w_n_L M (S n).
intros; generalize dependent n;
induction M; intros; inversion H; subst;
eauto using lc_w_n_L.
Qed.

Lemma closed_w_addition_L:
forall M n m,
  lc_w_n_L M n -> lc_w_n_L M (n + m).
intros; induction m.
replace (n+0) with n by auto; assumption.
replace (n+ S m) with (S (n+m)) by auto;
apply closed_w_succ_L; assumption.
Qed.

Lemma closed_no_unbound_worlds_L:
forall M n,
  lc_w_n_L M n -> unbound_worlds_L n M = nil.
intros;
generalize dependent n;
induction M; intros; simpl in *;
try (reflexivity);
try (apply IHM; inversion H; subst; assumption);
try (inversion H; subst; rewrite IHM1; try rewrite IHM2; auto);
try (destruct v; [ | apply IHM]; inversion H; subst; auto).
Qed.

End Lemmas.