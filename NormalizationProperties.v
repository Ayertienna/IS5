Add LoadPath "./labeled" as Labeled.
Require Import Labeled.
Require Import Metatheory.
Require Import List.
Require Import Relations.

Open Scope labeled_is5_scope.

Definition normal_form (M: te_L) := value_L M.

Inductive neutral: te_L -> Prop := 
| nHyp: forall n, neutral (hyp_L n)
| nAppl: forall M N, neutral (appl_L M N)
| nUnbox: forall M, neutral (unbox_L M)
| nHere: forall M, neutral M -> neutral (here_L M) 
| nLetd: forall M N, neutral (letd_L M N)
| nFetch: forall w M, neutral (fetch_L w M)
| nGet: forall w M, neutral (get_L w M)
.

Lemma neutral_or_value:
forall M,
  neutral M \/ value_L M.
induction M; intros.
left; constructor.
right; constructor.
left; constructor.
right; constructor.
left; constructor.
left; constructor.
left; constructor.
destruct IHM; [left | right]; constructor; auto.
left; constructor.
Qed.

(*
Lemma neutral_not_value:
forall M,
  neutral M -> ~value_L M.
induction M; intros; intro;
try inversion H0; 
try inversion H;
auto;
subst;
apply IHM in HT; auto.
Qed.
*)

Lemma value_no_step:
forall M,
  value_L M ->
  forall N w, ~ (M, w) |-> (N, w).
induction M;
intros;
intro;
try inversion H;
inversion H0;
subst;
apply IHM with (N:=N') (w:=w) in HT;
contradiction.
Qed.

(*
Lemma neutral_step:
forall M Omega A
  (H_lc: lc_w M)
  (HN: neutral M),
  forall w,
    Omega; nil |- M ::: A @ w ->
      exists N,  (M, fwo w) |-> (N, fwo w).
intros;
assert ( value_L M \/ exists N, (M, fwo w) |-> (N, fwo w) ) by (eapply Progress; eauto);
apply neutral_not_value in HN;
destruct H0;
[ contradiction | auto].
Qed.
*)

(* We want to have the property that term that has a type is strongly normalizing *)
Inductive strong_norm: te_L -> var -> Prop :=
| val_SN: forall M w, value_L M -> strong_norm M w
| step_SN: forall M w, 
             (forall N, (M, fwo w) |-> (N, fwo w) -> strong_norm N w) -> 
             strong_norm M w.

Lemma alt_strong_norm:
forall M w,
  strong_norm M w <->
  forall N, (M, fwo w) |->* (N, fwo w) -> strong_norm N w.
split.
(* -> *)
intros;
remember (M, fwo w) as M0;
remember (N, fwo w) as N0;
generalize dependent w;
generalize dependent M;
generalize dependent N;
induction H0; intros; subst.
inversion HeqN0; subst; auto.
destruct y;
assert (w0 = fwo w) by
  (inversion H; subst; reflexivity);
subst;
apply IHclos_refl_trans_1n with (M:=t);
try reflexivity;
inversion H1; subst.
apply value_no_step in H; auto; contradiction.
apply H2; auto.
(* <- *)
intros;
apply H;
constructor.
Qed.

Lemma strong_norm_appl:
forall M N w,
  lc_w (appl_L M N) ->
  strong_norm (appl_L M N) w ->
  strong_norm M w.
intros;
remember (appl_L M N) as T;
generalize dependent M;
generalize dependent N;
induction H0; intros; subst;
[ inversion H0 |
  assert (neutral M0 \/ value_L M0) by apply neutral_or_value];
destruct H2;
[ inversion H; subst |
  constructor; auto];
apply step_SN; intros;
apply H1 with (N0:=appl_L N0 N) (N:=N);
constructor; auto;
apply closed_step_propag with (M:=M0) (w:=w); auto.
Qed.

Definition strong_norm_n (M: te_L) (w: var) (n: nat):=
  forall N m,
    value_L N ->
    steps_n_L m M (fwo w) N (fwo w) ->
    m <= n.

Lemma strong_norm_multistep:
forall (M: te_L) (w: var),
  strong_norm M w <->
  (forall n N, steps_n_L n M (fwo w) N (fwo w) -> strong_norm N w).
intros; split; intros.
(* -> *)
remember (fwo w) as w0;
generalize dependent w;
induction H0; intros;
auto; subst;
apply IHsteps_n_L; auto; subst;
inversion H1; subst.
apply value_no_step with (w:=fwo w1) (N:=N) in H2;
auto;
contradiction.
apply H2; auto.
(* <- *)
assert (neutral M \/ value_L M) by apply neutral_or_value.
destruct H0.
apply step_SN; intros;
apply H with (n:=1); econstructor; eauto; constructor.
constructor; auto.
Qed.

Fixpoint Reducible (M: te_L) (A: ty_L) (w: var):=
match A with 
| tvar_L => strong_norm M w
| tarrow_L A1 A2 =>
  forall N
    (H_lc_N: lc_w N)
    (HR: Reducible N A1 w),
    Reducible (appl_L M N) A2 w
| tbox_L A1 => False
| tdia_L A1 => False
end.

(* CR 2 base *)
Theorem head_expansion:
forall w A M M'
  (HRed: Reducible M A w)
  (H_lc: lc_w M)
  (HStep: (M, fwo w) |-> (M', fwo w)),
  Reducible M' A w.
induction A; intros; simpl in *; intros.
(* base type *)
inversion HRed; subst.
apply value_no_step with (N:=M')(w:=fwo w) in H; contradiction.
apply H; auto.
(* arrow type *)
apply IHA2 with (M:=appl_L M N); auto;
constructor; auto.
(* box type *)
auto.
(* dia type *)  
auto.
Qed.

(* CR1 + CR3 *)
Theorem reducibility_props:
forall A M w
  (H_lc: lc_w M),
  (Reducible M A w -> strong_norm M w)
  /\
  ( neutral M -> 
   (forall M', (M, fwo w) |-> (M', fwo w) -> Reducible M' A w) ->
   Reducible M A w).
induction A; intros; split; simpl in *.
(* base type *)
auto.
intros;
apply step_SN; auto.
(* arrow type *)
intros.
(* Create variable of type A1 *)
assert (exists Omega x, Omega; (A1, fwo w) :: nil |- hyp_L x ::: A1 @ w).
exists \{w}; exists 0; constructor; auto; rewrite in_singleton; reflexivity.
destruct H0 as (Omega'); destruct H0 as (x).
(* Use it to prove strong_norm (appl_L M (hyp_L x)) *)
assert (neutral (hyp_L x)) by constructor.
assert (strong_norm (hyp_L x) w).
  apply step_SN; intros; inversion H2.
assert (Reducible (hyp_L x) A1 w).
  apply IHA1; auto.
  constructor.
  intros; inversion H3.
assert (Reducible (appl_L M (hyp_L x)) A2 w).
apply H; auto; constructor.
assert (strong_norm (appl_L M (hyp_L x)) w).
eapply IHA2; eauto.
constructor; auto; constructor.
(* From strong_norm (appl_L M (hyp_L x)) w deduce strong_norm M w *)
apply strong_norm_appl with (N:=hyp_L x); auto; constructor; auto;
constructor.
intros;
apply IHA2; try constructor; auto;
intros;
inversion H1; subst;
inversion H;
apply H0; auto.
(* box type *)
intro; contradiction.
skip. (* not finished *)
(* dia type *)
intro; contradiction.
skip. (* not finished *)
Qed.

Theorem types_reducible:
forall Omega M A w,
  lc_w M ->
  Omega; nil |- M ::: A @ w ->
    Reducible M A w.
Admitted.

Theorem strong_normalization_theorem:
forall Omega M A w,
  lc_w M ->
  Omega; nil |- M ::: A @ w ->
    strong_norm M w.
intros;
apply types_reducible in H0; auto;
eapply reducibility_props; eauto.
Qed.