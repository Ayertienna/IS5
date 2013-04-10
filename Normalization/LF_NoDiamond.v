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

Lemma closed_t_succ_LF:
forall M n,
  lc_t_n_LF n M -> lc_t_n_LF (S n) M.
intros; generalize dependent n;
induction M; intros; inversion H; subst;
eauto using lc_t_n_LF.
Qed.

Lemma lc_t_subst_t_LF_bound:
forall M N n,
  lc_t_n_LF n N ->
  lc_t_n_LF (S n) M ->
  lc_t_n_LF n ([N//bte n] M).
induction M; intros; simpl in *; inversion H0; subst; repeat case_if;
try constructor; eauto.
assert (n <> v0) by (intro; subst; elim H1; auto); omega.
eapply IHM; auto; apply closed_t_succ_LF; auto.
eapply IHM2; auto; apply closed_t_succ_LF; auto.
Qed.

Lemma lc_t_subst_t_LF_free:
forall M N n v,
  lc_t_n_LF n N ->
  lc_t_n_LF n M ->
  lc_t_n_LF n ([N//fte v] M).
induction M; intros; simpl in *; inversion H0; subst; repeat case_if;
try constructor; eauto.
eapply IHM; eauto; apply closed_t_succ_LF; auto.
eapply IHM2; eauto; apply closed_t_succ_LF; auto.
Qed.

Lemma lc_t_step_LF:
forall M N,
  lc_t_LF M ->
  M |-> N ->
  lc_t_LF N.
induction M; intros; inversion H0; inversion H; subst; try constructor; eauto.
apply lc_t_subst_t_LF_bound; auto.
eapply IHM1; eauto.
eapply IHM; eauto.
eapply IHM; eauto.
unfold open_LF; apply lc_t_subst_t_LF_bound; auto.
eapply IHM1; eauto.
Qed.

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

(* FIXME: diamond type needs to be removed *)
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

Lemma reducible_abstraction:
forall A N B
  (lc_N: lc_t_LF (lam_LF A N))
  (HT: forall M,
    lc_t_LF M ->
    Red M A ->
    Red ([M// bte 0] N) B),
  Red (lam_LF A N) (A ---> B).
simpl; intros;
apply property_3;
repeat constructor; auto.
inversion lc_N; auto.
intros; inversion H; subst.
apply HT; auto.
inversion H5.
Qed.

Lemma reducible_box:
forall A M
  (lc_M: lc_t_LF M)
  (HT: Red M A),
  Red (box_LF M) ([*]A).
simpl; intros;
apply property_3;
repeat constructor; auto.
intros; inversion H; subst; auto.
inversion H2.
Qed.

(************************* WORKING UNTILL HERE ********************************)
(* Idea: gather all free variables from a term,
         substitute them with reducible terms of appropriate type
         conclude that the resulting term is reducible *)

Fixpoint subst_free_vars (D: list (var*ty)) L N :=
match D, L with
| nil, _ => N
| _, nil => N
| (v, _ )::V', l::L' => [l // fte v] (subst_free_vars V' L' N)
end.

Fixpoint subst_typing (G: bg_LF) (L: list te_LF) (D: list (var * ty)) :=
match L, D with
| nil, nil => True
| M::L', (v, A) :: D' =>
  emptyEquiv_LF G |= nil |- M ::: A /\ (subst_typing G L' D')
| _, _ => False
end.

Fixpoint red_list (L: list te_LF) (D: list (var * ty)) :=
match L, D with
| nil, nil => True
| M :: L', (v, A):: D' => Red M A /\ red_list L' D'
| _, _ => False
end.

Fixpoint no_rep_var (D: list (var * ty)) (U: list var) :=
match D with
| nil => True
| (v, _ ):: D' =>
  (~Mem v U) /\ (no_rep_var D' (v::U))
end.

Lemma no_rep_var_weakening:
forall D U v,
  no_rep_var D (v::U) -> no_rep_var D U.
Admitted.

Lemma no_rep_var_not_Mem:
forall D U,
  no_rep_var D U ->
  forall v, Mem v U -> ~Mem v (map fst_ D).
Admitted.

Lemma subst_free_vars_notin:
forall D G L,
  red_list L D ->
  no_rep_var D nil ->
  subst_typing G L D ->
  forall v,
    ~ Mem v (map fst_ D) ->
    subst_free_vars D L (hyp_LF (fte v)) = hyp_LF (fte v).
induction D; intros; simpl in *; auto; destruct a; rew_map in *; simpl in *;
rewrite Mem_cons_eq in *; destruct L; inversion H1; subst;
try contradiction.
simpl in *; destruct H; destruct H0;
rewrite IHD with (G:=G); simpl; eauto.
case_if; auto; inversion H7; subst; elim H2; left; auto.
apply no_rep_var_weakening in H6; auto.
Qed.

Lemma subst_free_vars_hyp_Red:
forall D G L,
  red_list L D ->
  no_rep_var D nil ->
  subst_typing G L D ->
  forall v A,
    Mem (v, A) D ->
    Red (subst_free_vars D L (hyp_LF (fte v))) A.
induction D; intros.
rewrite Mem_nil_eq in H2; contradiction.
destruct a; simpl in *; destruct L; inversion H1; subst; try contradiction.
rewrite Mem_cons_eq in H2; destruct H2.
inversion H2; subst; simpl in *; destruct H; destruct H0.
(* here *)
rewrite subst_free_vars_notin with (G:=G); eauto.
simpl; case_if; auto.
apply no_rep_var_weakening in H6; auto.
eapply no_rep_var_not_Mem; eauto; apply Mem_here.
(* step *)
simpl in *; destruct H; destruct H0.
rewrite closed_subst_t_free_LF; [eapply IHD | ]; simpl; eauto.
apply no_rep_var_weakening in H6; auto.
skip. (* !!!! *)
Qed.

Lemma subst_free_vars_lam:
forall D L A M,
  subst_free_vars D L (lam_LF A M) = lam_LF A (subst_free_vars D L M).
induction D; intros; simpl in *; eauto;
destruct a; destruct L; auto; rewrite IHD; simpl; auto.
Qed.

Lemma subst_free_vars_appl:
forall D L M N,
  subst_free_vars D L (appl_LF M N) =
  appl_LF (subst_free_vars D L M) (subst_free_vars D L N).
induction D; intros; simpl in *; eauto;
destruct a; destruct L; auto; rewrite IHD; simpl; auto.
Qed.

Lemma subst_free_vars_box:
forall D L M,
  subst_free_vars D L (box_LF M) = box_LF (subst_free_vars D L M).
induction D; intros; simpl in *; eauto;
destruct a; destruct L; auto; rewrite IHD; simpl; auto.
Qed.

Lemma subst_free_vars_unbox:
forall D L M,
  subst_free_vars D L (unbox_LF M) = unbox_LF (subst_free_vars D L M).
induction D; intros; simpl in *; eauto;
destruct a; destruct L; auto; rewrite IHD; simpl; auto.
Qed.

Lemma subst_free_vars_here:
forall D L M,
  subst_free_vars D L (here_LF M) = here_LF (subst_free_vars D L M).
induction D; intros; simpl in *; eauto;
destruct a; destruct L; auto; rewrite IHD; simpl; auto.
Qed.

Lemma subst_free_vars_letdia:
forall D L M N,
  subst_free_vars D L (letdia_LF M N) =
  letdia_LF (subst_free_vars D L M) (subst_free_vars D L N) .
induction D; intros; simpl in *; eauto;
destruct a; destruct L; auto; rewrite IHD; simpl; auto.
Qed.

Lemma lc_t_subst_free_vars:
forall L D k M,
  (forall N, Mem N L -> lc_t_LF N) ->
  lc_t_n_LF k M ->
  lc_t_n_LF k (subst_free_vars D L M).
Admitted.

Theorem subst_types_reducible:
forall M G Gamma A L
  (H_lc: lc_t_LF M)
  (H_lc_D: forall N, Mem N L -> lc_t_LF N)
  (HT: G |= Gamma |- M ::: A)
  (HRed: red_list L (concat (Gamma::G)))
  (HRedType: subst_typing G L (concat (Gamma :: G))),
  Red (subst_free_vars (concat (Gamma::G)) L M) A.
intros; generalize dependent L.
induction HT; intros; simpl in *; inversion H_lc; subst; rew_app in *.
(* hyp *)
apply subst_free_vars_hyp_Red with (G:=G); auto.
skip. (* from Ok *)
rew_concat; rewrite Mem_app_or_eq; left; auto.
(* lam *)
intros; rewrite subst_free_vars_lam; apply property_3;
repeat constructor; auto.
skip. (* !!! *)
intros; inversion H1; subst.
assert (exists x, x\notin L) by apply Fresh. destruct H2.
specialize H0 with x L0; apply H0 with (L:=L0) in H2;
unfold open_LF in *.
destruct L0; simpl in *.
destruct (concat (Gamma::G)); simpl.
replace ([N // bte 0](subst_list 1 D M)) with (subst_list 0 (N::D) M)
 by (simpl; auto).
eapply H0.
inversion H_lc; subst; auto.
intros. simpl in H0; destruct H0; subst; auto.
simpl.
split; auto.

inversion HRed0.

Theorem Termination_LF:
forall M G A,
  emptyEquiv_LF G |= nil |- M ::: A ->
  exists N, value N /\ (steps_LF M N).