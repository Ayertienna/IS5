Add LoadPath "..".
Add LoadPath "../LabelFree/SingleUnbox".
Require Import Shared.
Require Import LabelFree.

Open Scope is5_scope.
Open Scope permut_scope.

Fixpoint NoDiamond_LF (M0:te_LF) :=
match M0 with
| hyp_LF v => True
| lam_LF A M => NoDiamond_LF M
| appl_LF M N => NoDiamond_LF M /\ NoDiamond_LF N
| box_LF M => NoDiamond_LF M
| unbox_LF M => NoDiamond_LF M
| here_LF M => False
| letdia_LF M N => False
end.

Definition normal_form (M: te_LF) := value_LF M.

Inductive neutral_LF: te_LF -> Prop :=
| nHyp: forall n, neutral_LF (hyp_LF n)
| nAppl: forall M N, neutral_LF (appl_LF M N)
| nUnbox: forall M, neutral_LF (unbox_LF M)
| nHere: forall M, neutral_LF M -> neutral_LF (here_LF M)
| nLetd: forall M N, neutral_LF (letdia_LF M N)
.

Lemma value_no_step:
forall M,
  value_LF M ->
  forall N , ~ M |-> N.
induction M; intros; intro;
try inversion H; inversion H0; subst;
eapply IHM; eauto.
Qed.

Lemma neutral_or_value:
forall M,
  neutral_LF M \/ value_LF M.
induction M; intros;
try (destruct IHM; [left | right]; constructor; auto);
try (left; constructor);
right;
constructor.
Qed.

Inductive SN: te_LF -> Prop :=
| val_SN: forall M, value_LF M -> SN M
| step_SN: forall M,
             (forall N, M |-> N -> SN N) ->
             SN M.

Fixpoint Red (M: te_LF) (A: ty):=
match A with
| tvar => SN M
| tarrow A1 A2 =>
  forall N
    (H_lc_N: lc_t_LF N)
    (HR: Red N A1),
    Red (appl_LF M N) A2
| tbox A1 => Red (unbox_LF M) A1
| tdia A1 => False
end.

Lemma lc_t_step_LF:
forall M N,
  lc_t_LF M ->
  M |-> N ->
  lc_t_LF N.
Admitted. (* simple, been done *)

Lemma SN_appl:
forall M N,
  lc_t_LF (appl_LF M N) ->
  SN (appl_LF M N) ->
  SN M.
intros;
remember (appl_LF M N) as T;
generalize dependent M;
generalize dependent N;
induction H0; intros; subst;
[ inversion H0 |
  assert (neutral_LF M0 \/ value_LF M0) by apply neutral_or_value];
destruct H2;
[ inversion H; subst |
  constructor; auto];
apply step_SN; intros;
apply H1 with (N0:=appl_LF N0 N) (N:=N).
constructor; eauto.
apply lc_t_step_LF with (M:=appl_LF M0 N); auto; constructor; auto.
auto.
Qed.

Lemma SN_box:
forall M,
  lc_t_LF (unbox_LF M) ->
  SN (unbox_LF M) ->
  SN M.
intros; remember (unbox_LF M) as T;
generalize dependent M;
induction H0; intros; subst;
[ inversion H0 |
  assert (neutral_LF M0 \/ value_LF M0) by apply neutral_or_value];
destruct H2; [ inversion H; subst | constructor; auto];
apply step_SN; intros;
apply H1 with (N := unbox_LF N).
constructor; inversion H; auto.
apply lc_t_step_LF with (M:=unbox_LF M0); auto; constructor; auto.
auto.
Qed.

(* CR 2 base *)
Theorem property_2:
forall A M M'
  (HRed: Red M A)
  (H_lc_t: lc_t_LF M)
  (HStep: M |-> M'),
  Red M' A.
induction A; intros; simpl in *; intros.
(* base type *)
inversion HRed; subst;
[apply value_no_step with (N:=M') in H; contradiction | apply H; auto].
(* arrow type *)
apply IHA2 with (M:=appl_LF M N); auto; constructor; auto.
(* box type *)
apply IHA with (M:=unbox_LF M); auto; constructor; eauto.
(* dia type - we ommit it *)
auto.
Qed.

(* CR1 + CR3 *)
Theorem reducibility_props:
forall A M
  (H_lc_t: lc_t_LF M),
  (Red M A -> SN M)
  /\
  (neutral_LF M -> (forall M', M |-> M' -> Red M' A) -> Red M A).
assert (exists (x:var), x \notin \{}) as nn by apply Fresh; destruct nn; auto;
induction A; intros; split; simpl in *.
(* base type *)
auto.
intros; apply step_SN; auto.
(* arrow type *)
intros.
(* Create variable of type A1 *)
assert (forall x, nil |= (x, A1) :: nil |- hyp_LF (fte x) ::: A1).
intros; constructor.
unfold ok_Bg_LF; rew_concat; constructor;
[rewrite Mem_nil_eq | constructor]; auto.
apply Mem_here.
assert (forall x, neutral_LF (hyp_LF x)) by (intros; constructor).
assert (forall x, SN (hyp_LF x))
  by (intros; apply step_SN; intros; inversion H3).
assert (forall x, Red (hyp_LF (fte x)) A1).
  intros; apply IHA1; auto.
  constructor.
  intros; inversion H4.
assert (forall x, Red (appl_LF M (hyp_LF (fte x))) A2).
intros. apply H0; auto; constructor.
assert (forall x, SN (appl_LF M (hyp_LF (fte x)))).
intros; eapply IHA2; eauto.
constructor; auto; constructor.
(* From strong_norm (appl_L M (hyp_L x)) w deduce strong_norm M w *)
eapply SN_appl; auto; constructor; auto; constructor.
intros; apply IHA2; try constructor; auto; intros; simpl in *;
inversion H2; subst; inversion H0; apply H1; auto.
(* box type *)
intros; apply SN_box.
constructor; auto.
apply IHA; [constructor | ]; auto.
intros; apply IHA; try constructor; auto; intros;
inversion H2; subst; [inversion H0 | ]; apply H1; auto.
(* dia type *)
intro; contradiction.
skip. (* Create a sublanguage? Or add NoDiamond M = True? *)
Grab Existential Variables.
auto.
Qed.

Lemma property_1:
forall A M
  (H_lc: lc_t_LF M),
  Red M A -> SN M.
intros; eapply reducibility_props; eauto.
Qed.

Lemma property_3:
forall A M
  (H_lc: lc_t_LF M),
  neutral_LF M ->
  (forall M', M |-> M' ->
    Red M' A) ->
   Red M A.
intros; eapply reducibility_props; eauto.
Qed.

(************************** DONE UNTIL HERE **********************************)
(*
Goal: substitute elements of L for term variables.
*)
Fixpoint subst_list n L N :=
match L with
| (t :: L') => [t // bte n] (subst_list (S n) L' N)
| nil => N
end.

Fixpoint subst_typing G (w: var) (L: list te_LF) (D: list (var * ty)) : Prop :=
match L, D with
| nil, nil => True
| M::L', (v, A)::D' => emptyEquiv G |= (w, nil) |- M ::: A /\
  (subst_typing G w L' D')
| _, _ => False
end.


(*
Goal: We have a list of terms and their corresponding types;
we want to express that terms are reducible at their respecive types.
*)
Fixpoint red_list (w: var) (L: list te_LF) (G: list (var * ty)) :=
match L, G with
| nil, nil => True
| M :: D', (v, A):: Gamma' => Reducible M A w /\ red_list w D' Gamma'
| _, _ => False
end.

Lemma reducible_abstraction:
forall A w N B
  (lc_N: lc_w_LF (lam_LF A N))
  (lc_N': lc_t_LF (lam_LF A N))
  (HT: forall M,
    lc_w_LF M -> lc_t_LF M ->
    Reducible M A w ->
    Reducible ([M// bte 0] N) B w),
  Reducible (lam_LF A N) (A ---> B) w.
simpl; intros;
apply property_3;
repeat constructor; auto.
inversion lc_N; auto.
intros; inversion H; subst.
unfold open_var; apply HT; auto.
inversion HT0.
Qed.

Lemma reducible_box:
forall L A w M
  (lc_M: lc_t_LF M)
  (lc_M': forall x, x \notin L -> lc_w_LF (M ^w^ (fwo x)))
  (HT: forall w',
    Reducible (M ^w^ (fwo w')) A w'),
  Reducible (box_LF M) ([*]A) w.
simpl; intros;
apply property_3;
repeat constructor; auto.
assert (exists w: var, w \notin L) as H1 by apply Fresh;
destruct H1 as (w0);
apply lcw_box_LF with (L:=L) (w:=w0); auto.
intros; inversion H; subst.
unfold open_var; apply HT; auto.
inversion HT0.
Qed.

(* Extra substitution properties - FIXME: move *)
Lemma subst_list_lam:
forall D X A M,
  subst_list X D (lam_LF A M) = lam_LF A (subst_list (S X) D M).
Admitted.

Lemma subst_list_appl:
forall D X M N,
  subst_list X D (appl_LF M N) = appl_LF (subst_list X D M) (subst_list X D N).
Admitted.

Lemma subst_list_box:
forall D n M,
  subst_list n D (box_LF M) = box_LF (subst_list n D M).
Admitted.

Lemma subst_list_unbox:
forall D w n M,
  subst_list n D (unbox_fetch_LF w M) = unbox_fetch_LF w (subst_list n D M).
Admitted.

Lemma subst_list_get:
forall D n M w ,
  subst_list n D (get_here_LF w M) = get_here_LF w (subst_list n D M).
Admitted.

Lemma subst_list_letd:
forall D n M N w,
  subst_list n D (letdia_get_LF w M N) =
  letdia_get_LF w (subst_list n D M) (subst_list (S n) D M).
Admitted.

Lemma lc_w_subst_list:
forall D k M,
  (forall N, In N D -> lc_w_LF N) ->
  lc_w_LF M ->
  lc_w_LF (subst_list k D M).
Admitted.

Lemma lc_t_subst_list:
forall D k M,
  (forall N, In N D -> lc_t_LF N) ->
  lc_t_LF M ->
  lc_t_LF (subst_list k D M).
Admitted.

Lemma subst_list_lc_t_LF:
forall M D l,
  lc_t_LF M ->
  subst_list l D M = M.
Admitted.

Lemma subst_list_subst_w:
forall w k D l M,
  (forall N, In N D -> lc_w_LF N) ->
  {{fwo w // bwo k}} (subst_list l D M) = subst_list l D ({{fwo w // bwo k}} M).
Admitted.

Lemma subst_list_hyp:
forall G Gamma D n A w M,
  G |= (w, Gamma) |- hyp_LF (bte n) ::: A ->
  nth_error D n = Some M ->
  subst_list 0 D (hyp_LF (bte n)) = M.
Admitted.





Theorem subst_types_reducible:
forall M w G Gamma A D
  (H_lc: lc_w_LF M)
  (H_lc': lc_t_LF M)
  (H_lc_D: forall N, In N D -> lc_w_LF N)
  (H_lc_D': forall N, In N D -> lc_t_LF N)
  (HT: G |= (w, Gamma) |- M ::: A)
  (HRed: red_list w D Gamma),
  Reducible (subst_list 0 D M) A w.
induction M; intros.
(* hyp *)
destruct v.
assert (exists M, nth_error D n = Some M) by skip. (* need a lemma *)
destruct H.
rewrite subst_list_hyp with (G:=G) (Gamma:=Gamma) (A:=A) (w:=w) (M:=x); auto.
skip. (* from HRed *)
rewrite subst_list_lc_t_LF; [apply property_3 | ]; constructor || intros;
inversion H.
(* lam *)
rewrite subst_list_lam; inversion HT; subst; simpl; intros.
apply property_3.
skip. skip. (* fairly obvious *)
constructor. intros.
inversion H; subst.
unfold open_var in *.
replace ([N // bte 0](subst_list 1 D M)) with ((subst_list 0 (N::D) M)) by
   (simpl; auto).
eapply IHM.
inversion H_lc; auto.
inversion H_lc'; subst.






.






















intros; generalize dependent D;
remember (w, Gamma) as Ctx;
generalize dependent w; generalize dependent Gamma;
induction HT; intros;
simpl in *; destruct H_lc;
inversion HeqCtx; subst.
(* hyp *)
rewrite subst_list_lc_t_LF; [ | constructor]; simpl;
apply property_3; try constructor; auto;
intros; inversion H1.
(* lam *)
intros; rewrite subst_list_lam;
apply property_3;
repeat constructor; auto.
inversion H0; subst;
apply lc_w_subst_list; auto.
inversion H1; subst;
apply lct_lam_LF with (L:=L0) (x:=x); auto;
unfold open_var in *.
skip. (* Needs a lemma, but is obvious *)
simpl in *; intros; inversion H2; subst.
unfold open_var in *.
replace ([N // bte 0](subst_list 1 D M)) with (subst_list 0 (N::D) M)
 by (simpl; auto).
eapply H.
inversion H_lc; subst; auto.
intros. simpl in H0; destruct H0; subst; auto.
simpl.
split; auto.

inversion HRed0.
