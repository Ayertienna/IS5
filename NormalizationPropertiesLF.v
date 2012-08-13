Require Import LabelFree.
Require Import LibTactics.
Require Import LibList.
Require Import Relations.
Require Import Arith.

Require Import OkLib.
Require Import PPermutLib.

Open Scope is5_scope.
Open Scope label_free_is5_scope.

Definition normal_form (M: te_LF) := value_LF M.

Inductive neutral_LF: te_LF -> Prop := 
| nHyp: forall n, neutral_LF (hyp_LF n)
| nAppl: forall M N, neutral_LF (appl_LF M N)
| nUnbox: forall M w, neutral_LF (unbox_fetch_LF w M)
| nHere: forall M w, neutral_LF M -> neutral_LF (get_here_LF w M) 
| nLetd: forall M w N, neutral_LF (letdia_get_LF w M N)
.

Lemma value_no_step:
forall M,
  value_LF M ->
  forall N w, ~ (M, w) |-> (N, w).
induction M;
intros;
intro;
try inversion H;
inversion H0;
subst;
apply IHM with (N:=M') (w:=v) in H2;
contradiction.
Qed.

Inductive strong_norm: te_LF -> var -> Prop :=
| val_SN: forall M, value_LF M -> forall w, strong_norm M w
| step_SN: forall M w, 
             (forall N, (M, fwo w) |-> (N, fwo w) -> strong_norm N w) -> 
             strong_norm M w.

Fixpoint Reducible (M: te_LF) (A: ty) (w: var):=
match A with 
| tvar => strong_norm M w
| tarrow A1 A2 =>
  forall N
    (H_lc_N: lc_w_LF N)
    (H_lc_N': lc_t_LF N)
    (HR: Reducible N A1 w),
    Reducible (appl_LF M N) A2 w
| tbox A1 => 
  forall w', Reducible (unbox_fetch_LF (fwo w) M) A1 w'
| tdia A1 => False
end.

Lemma strong_norm_appl:
forall M N w,
  lc_w_LF (appl_LF M N) ->
  lc_t_LF (appl_LF M N) ->
  strong_norm (appl_LF M N) w ->
  strong_norm M w.
Admitted.

Lemma strong_norm_box:
forall M w w',
  lc_w_LF (unbox_fetch_LF (fwo w) M) ->
  lc_t_LF (unbox_fetch_LF (fwo w) M) ->  
  strong_norm (unbox_fetch_LF (fwo w) M) w' ->
  strong_norm M w'.
Admitted.

(* CR 2 base *)
Theorem property_2:
forall A w M M'
  (HRed: Reducible M A w)
  (H_lc_w: lc_w_LF M)
  (H_lc_t: lc_t_LF M)
  (HStep: (M, fwo w) |-> (M', fwo w)),
  Reducible M' A w.
induction A; intros; simpl in *; intros.
(* base type *)
inversion HRed; subst.
apply value_no_step with (N:=M')(w:=fwo w) in H; contradiction.
apply H; auto.
(* arrow type *)
apply IHA2 with (M:=appl_LF M N); auto;
constructor; auto.
(* box type *)
apply IHA with (M:=unbox_fetch_LF (fwo w) M);
try constructor; eauto. 
(* dia type *)  
auto.
Qed.

(* CR1 + CR3 *)
Theorem reducibility_props:
forall A M w 
  (H_lc_w: lc_w_LF M)
  (H_lc_t: lc_t_LF M),
  (Reducible M A w -> strong_norm M w)
  /\
  ( neutral_LF M -> (forall M', (M, fwo w) |-> (M', fwo w) -> Reducible M' A w) ->
   Reducible M A w).
induction A; intros; split; simpl in *.
(* base type *)
auto.
intros;
apply step_SN; auto.
(* arrow type *)
intros.
(* Create variable of type A1 *)
assert (forall x, nil |= (w, (x, A1) :: nil) |- hyp_LF (fte x) ::: A1). 
intros; constructor.
unfold ok_Bg; split; simpl; rewrite Mem_nil_eq; case_if; auto.
apply Mem_here.
assert (forall x, neutral_LF (hyp_LF x)) by (intros; constructor).
assert (forall x, strong_norm (hyp_LF x) w).
  intros; apply step_SN; intros; inversion H2.
assert (forall x, Reducible (hyp_LF (fte x)) A1 w).
  intros; apply IHA1; auto.
  constructor. constructor.
  intros; inversion H3.
assert (forall x, Reducible (appl_LF M (hyp_LF (fte x))) A2 w).
intros. apply H; auto; constructor.
assert (forall x, strong_norm (appl_LF M (hyp_LF (fte x))) w).
intros; eapply IHA2; eauto.
constructor; auto; constructor.
constructor; auto; constructor.
(* From strong_norm (appl_L M (hyp_L x)) w deduce strong_norm M w *)
eapply strong_norm_appl; auto; constructor; auto;
constructor.
intros;
apply IHA2; try constructor; auto;
intros;
inversion H1; subst;
inversion H;
apply H0; auto.
(* box type *)
intros.
eapply strong_norm_box.
constructor; auto.
constructor; auto.
apply IHA; [constructor | constructor | ]; auto. 
intros. 
apply IHA;
try constructor; auto;
intros;
inversion H1; subst; [inversion H | ];
apply H0; auto.
(* dia type *)
skip. (* not finished *)
skip. (* not finished *)
Admitted.

Lemma property_1:
forall A M w
  (H_lc: lc_w_LF M)
  (H_lc': lc_t_LF M),
  Reducible M A w -> strong_norm M w.
intros; eapply reducibility_props; eauto.
Qed.

Lemma property_3:
forall A M w
  (H_lc: lc_w_LF M)
  (H_lc': lc_t_LF M),
  neutral_LF M -> 
  (forall M', (M, fwo w) |-> (M', fwo w) -> 
    Reducible M' A w) ->
   Reducible M A w.
intros; eapply reducibility_props; eauto.
Qed.