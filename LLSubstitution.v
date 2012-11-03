Require Export LLSyntax.
Require Import LLOkLib.
Require Import LibTactics.
Require Import Arith.

(* Notation for term substitution *)
Global Reserved Notation " [ M // v ] N " (at level 5).

(* Notation for world substitution *)
Global Reserved Notation " {{ w1 // w2 }} N " (at level 5).

Fixpoint subst_t_L (M0: te_L) (v0: vte) (N0: te_L) :=
match N0 with
| hyp_L v =>
    if (eq_vte_dec v v0) then M0 else N0
| lam_L A M =>
    lam_L A ([M0 // shift_vte v0] M)
| appl_L M N =>
    appl_L ([M0//v0]M) ([M0//v0]N)
| box_L M =>
    box_L ([M0//v0]M)
| unbox_L M =>
    unbox_L ([M0//v0]M)
| fetch_L w M =>
    fetch_L w ([M0//v0]M)
| get_L w M =>
    get_L w ([M0//v0]M)
| here_L M =>
    here_L ([M0//v0]M)
| letd_L M N =>
    letd_L ([M0//v0]M) ([M0//shift_vte v0]N)
end
where " [ M // v ] N " := (subst_t_L M v N) : labeled_is5_scope.

Fixpoint subst_w_L (M0: te_L) (w1: vwo) (w2: vwo) :=
match M0 with
| hyp_L n => hyp_L n
| lam_L A M => lam_L A ({{w1//w2}}M)
| appl_L M N => appl_L ({{w1//w2}}M) ({{w1//w2}}N)
| box_L M => box_L ({{ shift_vwo w1 // shift_vwo w2 }} M)
| unbox_L M => unbox_L ({{w1//w2}}M)
| fetch_L w3 M =>
  let w' := if (eq_vwo_dec w3 w2) then w1 else w3 in
    fetch_L w' ({{w1//w2}} M)
| get_L w3 M =>
  let w' := if (eq_vwo_dec w3 w2) then w1 else w3 in
    get_L w' ({{w1//w2}}M)
| here_L M => here_L ({{w1//w2}}M)
| letd_L M N =>
    letd_L ({{w1//w2}} M) ({{shift_vwo w1 // shift_vwo w2}} N)
end
where " {{ w1 // w2 }} M " := (subst_w_L M w1 w2) : labeled_is5_scope.

Definition open_t_L (M: te_L) (t: te_L) := subst_t_L t (bte 0) M.

Definition open_w_L M w := subst_w_L M w (bwo 0).

Notation " M '^t^' t " := (open_t_L M t) (at level 67) : labeled_is5_scope.
Notation " M '^w^' w  " := (open_w_L M w) (at level 67) : labeled_is5_scope.

Open Scope labeled_is5_scope.

Lemma subst_t_neutral_free:
forall M N n w,
  w \notin used_vars_term_L M ->
  [N // bte n] M = [N // fte w] ([hyp_L (fte w) // bte n] M).
induction M; intros; simpl in *;
try (erewrite IHM || (erewrite IHM1; try erewrite IHM2); eauto);
repeat (case_if; simpl); subst; auto;
rewrite notin_singleton in H; elim H; auto.
Qed.

Lemma subst_w_neutral_free:
forall M w w' w_f,
  w_f \notin used_worlds_term_L M ->
  {{w // w'}} M = {{w // fwo w_f}} ({{ fwo w_f // w'}}  M).
induction M; intros; simpl in *; repeat case_if;
try destruct w; try destruct w'; try destruct v; subst;
try (erewrite IHM || erewrite IHM1; try erewrite IHM2; eauto); eauto;
rewrite notin_union in H; destruct H; eauto;
rewrite notin_singleton in H; elim H; auto.
Qed.

Lemma closed_subst_w_free:
forall M w0 w,
  w0 \notin used_worlds_term_L M ->
  {{w // fwo w0}} M = M.
induction M; intros; simpl in *;
repeat case_if; auto;
rewrite IHM || (rewrite IHM1; try rewrite IHM2); auto;
(rewrite notin_union in H; rewrite notin_singleton in H;
destruct H as (Neq, H); elim Neq; auto) || destruct v; auto.
Qed.

Lemma closed_subst_w_bound:
forall M w0 w n
  (H_lc: lc_w_n_L n M),
  {{ w // bwo w0}} M  = M.
induction M; intros; simpl in *;
repeat case_if; auto;
inversion H_lc; subst;
erewrite IHM || (erewrite IHM1; try erewrite IHM2); eauto.
Qed.

Lemma closed_subst_t_bound:
forall N M v0 n,
  lc_t_n_L n N ->
  v0 >= n -> [M // bte v0] N = N.
induction N; intros; simpl in *;
repeat case_if; inversion H; subst;
try (erewrite IHN || (erewrite IHN1; try erewrite IHN2)); eauto.
assert (~(n = v0)) by omega;
apply gt_asym in H3; elim H3; omega.
omega. omega.
Qed.

Lemma subst_order_irrelevant_free:
forall M w0 w1 x N,
  w1 \notin used_worlds_term_L N ->
  {{ w0 // fwo w1 }} ([ N // x ] M) = [ N // x ] ({{ w0 // fwo w1 }} M).
induction M; intros; simpl in *; repeat case_if; simpl; unfold shift_vwo in *;
try (rewrite IHM || (rewrite IHM1; try rewrite IHM2; auto)); auto;
rewrite closed_subst_w_free; auto.
Qed.

Lemma subst_order_irrelevant_bound:
forall M w0 w1 x N,
  lc_w_L N ->
  {{ w0 // bwo w1 }} ([ N // x ] M) = [ N // x ] ({{ w0 // bwo w1 }} M).
induction M; intros; simpl in *; repeat case_if; simpl;
unfold shift_vte in *; unfold shift_vwo in *; auto;
try destruct v; try destruct w; auto;
try (rewrite IHM || (rewrite IHM1; try rewrite IHM2; auto));
auto; erewrite closed_subst_w_bound; eauto.
Qed.

Lemma lc_t_subst:
forall M N k,
  lc_t_n_L (S k) M ->
  lc_t_n_L 0 N ->
  lc_t_n_L k [N // bte k] M.
induction M; intros; simpl in *; repeat case_if;
try (constructor;
  (eapply IHM || (try eapply IHM1; try eapply IHM2; eauto));
  inversion H; subst; eauto).
replace k with (0+k) by omega;
eapply closed_t_addition; auto.
destruct v; constructor; inversion H; subst;
eapply gt_S in H4; destruct H4; auto; subst; elim H1; auto.
Qed.

Lemma lc_w_subst:
forall M w k,
  lc_w_n_L (S k) M ->
  lc_w_n_L k {{w // bwo k}} M.
induction M; intros; simpl in *; repeat case_if;
try (try destruct w; econstructor;
  (eapply IHM || (try eapply IHM1; try eapply IHM2; eauto));
  inversion H; subst; eauto);
try inversion H; subst;
constructor; eapply IHM; auto.
Qed.

Lemma subst_t_comm:
forall M v v' n N
  (Neq: v <> v')
  (Lc: lc_t_L N),
  [ N // fte v] ([ hyp_L (fte v') // bte n] M) =
  [hyp_L (fte v') // bte n] ([N // fte v] M).
induction M; intros; simpl;
[ repeat (case_if; simpl); auto;
  erewrite closed_subst_t_bound; eauto; omega | | | | | | | | ];
try (rewrite IHM; auto);
try (rewrite IHM1; try rewrite IHM2; auto);
repeat (case_if; simpl); subst; simpl;
auto;
erewrite closed_subst_t_bound;
eauto;
replace n with (0+n) by omega;
apply closed_t_addition; auto.
Qed.

Lemma subst_w_comm:
forall M w w' w'' n,
  w'' <> w ->
  {{fwo w' // fwo w''}} ({{fwo w // bwo n}} M) =
  {{ fwo w // bwo n}} ( {{fwo w' // fwo w''}}M).
induction M; intros; simpl;
repeat case_if; subst; simpl; auto;
rewrite IHM || (rewrite IHM1; try rewrite IHM2);
auto.
Qed.

Lemma rename_w_same:
forall M w,
  {{ fwo w // fwo w }} M = M.
induction M; intros; simpl in *; repeat case_if;
try rewrite IHM; try rewrite IHM1; try rewrite IHM2; auto.
Qed.
