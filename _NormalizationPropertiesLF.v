Require Import LabelFree.
Require Import OkLib.
Require Import EmptyEquivLib.

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

Lemma neutral_or_value:
forall M,
  neutral_LF M \/ value_LF M.
induction M; intros;
try (destruct IHM; [left | right]; constructor; auto);
try (left; constructor);
right;
constructor.
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

Lemma lc_w_step:
forall M N w,
  lc_w_LF M ->
  (M, w) |-> (N, w) ->
  lc_w_LF N.
induction M; intros; inversion H0; subst;
unfold open_var in *; unfold open_ctx in *.
erewrite <- closed_ctx_subst_var; eauto.
constructor; eauto.
inversion H; subst; inversion H3; subst.
Admitted.

Lemma lc_t_step:
forall M N w,
  lc_t_LF M ->
  (M, w) |-> (N, w) ->
  lc_t_LF N.
Admitted.

Lemma strong_norm_appl:
forall M N w,
  lc_w_LF (appl_LF M N) ->
  lc_t_LF (appl_LF M N) ->
  strong_norm (appl_LF M N) w ->
  strong_norm M w.
intros;
remember (appl_LF M N) as T;
generalize dependent M;
generalize dependent N;
induction H1; intros; subst;
[ inversion H1 |
  assert (neutral_LF M0 \/ value_LF M0) by apply neutral_or_value];
destruct H3;
[ inversion H; subst |
  constructor; auto];
apply step_SN; intros;
apply H2 with (N0:=appl_LF N0 N) (N:=N);
constructor; auto;
inversion H; subst;
inversion H0; subst;
auto;
[ eapply lc_w_step in H6 |
  eapply lc_t_step in H11]; eauto.
Qed.

Lemma strong_norm_box:
forall M w w',
  lc_w_LF (unbox_fetch_LF (fwo w) M) ->
  lc_t_LF (unbox_fetch_LF (fwo w) M) ->
  strong_norm (unbox_fetch_LF (fwo w) M) w' ->
  strong_norm M w'.
intros; remember (unbox_fetch_LF (fwo w) M) as T;
generalize dependent M;
generalize dependent w.
induction H1; intros; subst;
[ inversion H1 |
  assert (neutral_LF M0 \/ value_LF M0) by apply neutral_or_value];
destruct H3.
apply step_SN; intros.
apply H2 with (N := unbox_fetch_LF (fwo w0) N) (w0:=w).
econstructor; auto.
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
  ( neutral_LF M -> (forall M', (M, fwo w) |->
                                (M', fwo w) -> Reducible M' A w) ->
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
