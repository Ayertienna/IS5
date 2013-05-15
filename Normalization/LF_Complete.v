Add LoadPath "..".
Add LoadPath "../LabelFree".
Require Import Shared.
Require Import LabelFree.

Open Scope is5_scope.
Open Scope permut_scope.

Lemma closed_t_succ_LF:
forall M n,
  lc_t_n_LF n M -> lc_t_n_LF (S n) M.
intros; generalize dependent n;
induction M; intros; inversion H; subst;
eauto using lc_t_n_LF.
Qed.

Lemma closed_t_addition_LF:
forall M n m,
  lc_t_n_LF n M -> lc_t_n_LF (n + m) M.
intros; induction m;
[ replace (n+0) with n by auto |
  replace (n + S m) with (S (n+m)) by auto] ;
try apply closed_t_succ_LF;
assumption.
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

Lemma lc_t_step_LF:
forall M N,
  lc_t_LF M ->
  M |-> N ->
  lc_t_LF N.
induction M; intros; inversion H0; inversion H; subst; try constructor; eauto;
unfold open_LF in *.
apply lc_t_subst_t_LF_bound; auto.
eapply IHM1; eauto.
eapply IHM; eauto.
eapply IHM; eauto.
apply lc_t_subst_t_LF_bound; auto.
eapply IHM1; eauto.
Qed.

Lemma lc_t_steps_LF:
forall M N, lc_t_LF M -> steps_LF M N -> lc_t_LF N.
intros; induction H0.
apply lc_t_step_LF in H0; auto.
apply IHsteps_LF; apply lc_t_step_LF in H0; auto.
Qed.

Definition normal_form (M: te_LF) := value_LF M.

Inductive neutral_LF: te_LF -> Prop :=
| nHyp: forall n A, neutral_LF (hyp_LF A n)
| nAppl: forall M N, neutral_LF (appl_LF M N)
| nUnbox: forall M, neutral_LF (unbox_LF M)
| nHere: forall M, neutral_LF M -> neutral_LF (here_LF M)
| nLetd: forall M N A, neutral_LF (letdia_LF A M N)
.

Lemma value_no_step_LF:
forall M,
  value_LF M ->
  forall N , ~ M |-> N.
induction M; intros; intro;
try inversion H; inversion H0; subst; try inversion H2;
eapply IHM; eauto.
Qed.

Lemma neutral_or_value_LF:
forall M,
  neutral_LF M \/ value_LF M.
induction M; intros;
try (destruct IHM; [left | right]; constructor; auto);
try (left; constructor);
right;
constructor.
Qed.

Lemma neutral_not_value:
forall M,
  neutral_LF M -> ~ value_LF M.
induction M; intros; intro; try inversion H0; subst; inversion H; subst;
apply IHM in H3; contradiction.
Qed.

Fixpoint find_var (L: list (var * ty * te_LF)) (x:var) :
                     option (var * ty * te_LF) :=
match L with
| nil => None
| (v, A, M) :: L' =>
  if (eq_var_dec x v) then Some (v, A, M) else find_var L' x
end.

Lemma Mem_find_var:
  forall L v,
    Mem v (map fst_ (map fst_ L)) ->
    exists A M, find_var L v = Some (v, A, M).
induction L; intros; [ rewrite Mem_nil_eq in *; contradiction | ];
destruct a; destruct p; rew_map in *; simpl in *.
subst; rewrite Mem_cons_eq in H.
destruct (eq_var_dec v v0).
subst; simpl; exists t0 t; auto.
destruct H; try contradiction; apply IHL; auto.
Qed.

Lemma NotMem_find_var:
  forall L v,
    ~Mem v (map fst_ (map fst_ L)) ->
    find_var L v = None.
induction L; intros; simpl in *; auto;
destruct a; destruct p; rew_map in *; simpl in *;
case_if.
elim H; apply Mem_here.
apply IHL; intro; elim H;
rewrite Mem_cons_eq; right; auto.
Qed.

Lemma find_var_Mem:
forall L v A M,
  find_var L v = Some (v, A, M) -> Mem (v, A, M) L.
induction L; intros; [inversion H; subst | ].
destruct a; destruct p; simpl in *; case_if.
inversion H; subst; apply Mem_here.
rewrite Mem_cons_eq; right; apply IHL; auto.
Qed.

Fixpoint OkL (L: list (var * ty * te_LF)) U :=
match L with
| nil => True
| (v, A, M) :: L' => ~ Mem v U /\ OkL L' (v::U)
end.

Lemma OkL_permut:
forall L U1 U2,
  U1 *=* U2 ->
  OkL L U1 -> OkL L U2.
induction L; intros; [constructor | destruct a; destruct p];
inversion H0; subst; constructor.
intro; elim H1; apply Mem_permut with (l:=U2); [symmetry | ]; auto.
apply IHL with (U1:=v::U1); auto.
Qed.

Lemma OkL_weaken:
forall L U w,
  OkL L (w::U) -> OkL L U.
induction L; intros; simpl in *; auto; destruct a; destruct p; destruct H;
split.
intro; elim H; rewrite Mem_cons_eq; right; auto.
apply IHL with w. apply OkL_permut with (U1:=v::w::U); auto; permut_simpl.
Qed.

Lemma OkL_used_notin:
forall L U x A M,
  OkL L U ->
  Mem x U ->
  ~ Mem (x, A, M) L.
induction L; intros.
rewrite Mem_nil_eq; tauto.
intro; destruct a; destruct p; rewrite Mem_cons_eq in *; inversion H; subst;
destruct H1.
inversion H1; subst; contradiction.
specialize IHL with U x A M.
apply OkL_weaken in H3; apply IHL in H3; auto.
Qed.

Lemma OkL_fresh:
forall L x U,
  OkL L U->
  x \notin from_list (map fst_ (map fst_ L)) \u from_list U ->
  OkL L (x::U).
induction L; intros; [constructor | destruct a; destruct p];
simpl in *; destruct H; split.
intro; elim H; rewrite Mem_cons_eq in *; destruct H2; subst; auto;
repeat rewrite notin_union in *; destruct H0; destruct H0;
rew_map; simpl; rewrite from_list_cons; rewrite in_union; left;
rewrite in_singleton; auto.
apply OkL_permut with (U1:=x::v::U); [permut_simpl | apply IHL]; auto.
rew_map in *; simpl in *;
repeat rewrite from_list_cons in *; repeat rewrite notin_union in *;
simpl in *; destruct H0; destruct H0; split; auto.
Qed.

Lemma Mem_find_var_type:
  forall L v A,
    OkL L nil ->
    Mem (v, A) (map fst_ L) ->
    {M | find_var L v = Some (v, A, M)}.
induction L; intros; [ rewrite Mem_nil_eq in *; contradiction | ];
destruct a; destruct p; rew_map in *; simpl in *; destruct H.
subst; apply Mem_cons_spec in H0.
case_if.
destruct H0.
inversion e; subst; exists t; auto.
destruct IHL with v0 A; auto.
apply OkL_weaken in H1; auto.
apply find_var_Mem in e.
apply OkL_used_notin with (x:=v0) (A:=A) (M:=x) in H1; [ | apply Mem_here];
contradiction.
destruct H0; [inversion e; subst; elim H2; auto | ].
apply IHL; auto; apply OkL_weaken in H1; auto.
intros; decide equality. apply eq_ty_dec. apply eq_var_dec.
Qed.

Fixpoint SL (L: list (var * ty * te_LF)) M :=
match M with
| hyp_LF A (bte v) => M
| hyp_LF A (fte v) =>
  let x := find_var L v in
  match x with
    | Some (v, A, M) => M
    | None => hyp_LF A (fte v)
  end
| lam_LF A M => lam_LF A (SL L M)
| appl_LF M N => appl_LF (SL L M) (SL L N)
| box_LF M => box_LF (SL L M)
| unbox_LF M => unbox_LF (SL L M)
| here_LF M => here_LF (SL L M)
| letdia_LF A M N => letdia_LF A (SL L M) (SL L N)
end.

Lemma lc_SL:
forall M L n,
  lc_t_n_LF n M ->
  (forall a b c, Mem (a,b,c) L -> lc_t_LF c) ->
  lc_t_n_LF n (SL L M).
induction M; intros; simpl in *;
try (inversion H; subst; constructor; eapply IHM; eauto).
destruct v; inversion H; subst;
[constructor; auto | ];
destruct (Mem_dec var (map fst_ (map fst_ L)) v);
[apply eq_var_dec | apply Mem_find_var in m; destruct m; destruct H1 | ].
rewrite H1; replace n with (0+n) by omega;
apply closed_t_addition_LF; apply H0 with v x; apply find_var_Mem; auto.
rewrite NotMem_find_var; auto.
inversion H; subst; constructor; [apply IHM1 | apply IHM2]; auto.
inversion H; subst; constructor; [eapply IHM2 | apply IHM1]; auto.
Qed.

Lemma eq_te_LF_dec:
forall (M1: te_LF) (M2: te_LF),
  {M1 = M2} + {M1 <> M2}.
decide equality.
apply eq_vte_dec.
apply eq_ty_dec.
apply eq_ty_dec.
apply eq_ty_dec.
Qed.

Lemma SL_bte_subst:
forall L0 M x k A,
  ~ Mem x (map fst_ (map fst_ L0)) ->
  (forall v a m, Mem (v, a, m) L0 -> lc_t_LF m) ->
  [hyp_LF A (fte x) // bte k](SL L0 M) =
  SL L0 [hyp_LF A (fte x) // bte k]M.
induction M; intros; simpl in *;
try rewrite IHM || (rewrite IHM1; try rewrite IHM2); auto.
case_if; simpl.
case_if. rewrite NotMem_find_var; auto.
destruct v; simpl; repeat case_if; auto.
destruct (Mem_dec var (map fst_ (map fst_ L0)) v);
try apply eq_var_dec; [ | rewrite NotMem_find_var]; auto;
simpl; repeat case_if; auto.
apply Mem_find_var in m; destruct m as (a, (b, m)); rewrite m; simpl.
rewrite closed_subst_t_bound_LF with (n:=0); auto; try omega;
apply H0 with v a; apply find_var_Mem; auto.
Qed.

Fixpoint FV_L (L: list (var * ty * te_LF)) :=
match L with
| nil => \{}
| (v, A, M) :: L' => used_vars_te_LF M \u FV_L L'
end.

Lemma notin_FV_notin_elem:
forall x L,
  x \notin FV_L L ->
  forall a b c, Mem (a,b,c) L -> x \notin used_vars_te_LF c.
induction L; intros; simpl in *.
rewrite Mem_nil_eq in *; contradiction.
rewrite Mem_cons_eq in H0; destruct H0; [inversion H0; subst | ].
rewrite notin_union in H; destruct H; auto.
destruct a; destruct p; rewrite notin_union in H; destruct H;
apply IHL with (a:=a0) (b:=b); auto.
Qed.

Lemma SL_extend:
forall M L0 x A N,
  x \notin FV_L L0 ->
  ~Mem x (map fst_ (map fst_ L0)) ->
  SL ((x, A, N) :: L0) M =
  [N // fte x](SL L0 M).
induction M; intros; simpl in *;
try rewrite IHM || (rewrite IHM1; try rewrite IHM2); auto.
destruct v; simpl; repeat case_if; auto.
rewrite NotMem_find_var; auto; simpl; case_if; auto.
destruct (Mem_dec var (map fst_ (map fst_ L0)) v);
try apply eq_var_dec; [ | rewrite NotMem_find_var]; auto;
simpl; repeat case_if; auto.
apply Mem_find_var in m; destruct m as (a, (b, m)); rewrite m; simpl.
rewrite closed_subst_t_free_LF; auto.
apply notin_FV_notin_elem with L0 v a; eauto.
apply find_var_Mem; eauto.
Qed.

Require Export Relations.

Definition multisteps := clos_refl_trans_1n _ step_LF.

Notation " M |->* N " := (multisteps M N) (at level 70).

Inductive WT: te_LF -> Prop :=
| val_WT: forall V, value_LF V -> WT V
| step_WT: forall M, (exists V, value_LF V /\ steps_LF M V) -> WT M
.

Lemma lc_t_starsteps_LF:
forall M N,
 lc_t_LF M -> M |->* N -> lc_t_LF N.
intros.
induction H0; auto.
apply IHclos_refl_trans_1n; apply lc_t_step_LF in H0; auto.
Qed.

Hint Resolve lc_t_step_LF lc_t_steps_LF lc_t_starsteps_LF.

Lemma steps_star:
forall M M',
  steps_LF M M' -> M |->* M'.
intros. induction H; unfold multisteps in *.
apply clos_rt1n_step; auto.
Admitted.

Lemma WTWT':
forall M,
WT M <->  (exists V, value_LF V /\ M |->* V).
split; intros.
induction H.
  exists V; split; eauto; apply rt1n_refl.
  destruct H as (V, (H, H1)); exists V; split; auto.
Admitted.

Lemma step_LF_unique:
forall M N N',
  M |-> N ->
  M |-> N' ->
  N = N'.
intros; generalize dependent N'; induction H; intros.
inversion H1; subst; auto; inversion H7.
inversion H0; subst; auto; inversion H3.
inversion H2; subst; auto; inversion H9; subst;
apply value_no_step_LF in H5; auto; contradiction.
inversion H2; subst; [inversion H1 | ]; rewrite IHstep_LF with M'0; auto.
inversion H1; subst; [inversion H0 | ]; rewrite IHstep_LF with M'0; auto.
inversion H1; subst; rewrite IHstep_LF with M'0; auto.
inversion H2; subst.
  inversion H1; subst; apply value_no_step_LF in H5; auto; contradiction.
  rewrite IHstep_LF with M'0; auto.
Qed.

Theorem WT_step:
forall M M',
  WT M ->
  M |-> M' ->
  WT M'.
intros; inversion H; subst.
apply value_no_step_LF with (N:=M') in H1; contradiction.
destruct H1 as (V, (H1, H2)).
inversion H2; subst.
apply step_LF_unique with (N':=V) in H0; subst; auto; constructor; auto.
apply step_WT; exists V; split; auto.
apply step_LF_unique with (N':=M'0) in H0; subst; auto.
Qed.

Lemma WT_step_back:
forall M N,
  WT N ->
  M |-> N ->
  WT M.
intros; inversion H; subst.
apply step_WT; exists N; split; auto; constructor; auto.
destruct H1 as (V, (H1, H2)); apply step_WT; exists V; split; auto.
apply multi_step_LF with (M':=N); auto.
Qed.

Lemma WT_steps:
forall M N,
  steps_LF M N ->
  WT M -> WT N.
intros; induction H; apply WT_step in H; auto.
Qed.

Lemma WT_steps_back:
forall M N,
  steps_LF M N ->
  WT N -> WT M.
intros; induction H; apply WT_step_back in H; auto.
Qed.

(*
Lemma here_val:
forall M V,
  value_LF V -> steps_LF (here_LF M) V ->
  exists M', V = here_LF M'.
intros; remember (here_LF M) as M0; generalize dependent M.
induction H0; intros; subst.
inversion H0; subst. eexists; eauto.
inversion H0; subst.
apply IHsteps_LF with (M:=M'0); auto.
Qed.

Lemma WT_here:
forall M,
  lc_t_LF M ->
  (WT M <-> WT (here_LF M)).
split.
intros; inversion H0; subst.
constructor; constructor; auto.
destruct H1 as (V, (H1, H2)).
apply step_WT; exists (here_LF V); split.
constructor; auto.
induction H2; intros; subst.
  constructor; constructor; auto.
  apply multi_step_LF with (here_LF M').
    constructor; auto.
    apply IHsteps_LF; auto.
    apply lc_t_step_LF in H2; auto.
    apply WT_step in H2; auto.
Admitted.
*)

(*
intros. remember (here_LF M) as T; generalize dependent M.
induction H0; intros; subst.
inversion H; constructor; subst; auto.
destruct H as (V, (H, H1)).
assert ( steps_LF (here_LF M0) V) by auto.
apply here_val in H1; auto; destruct H1; subst.
apply step_WT; exists x; split; inversion H; subst; auto.
remember (here_LF M0) as hm; remember (here_LF x) as hx; generalize dependent x;
generalize dependent M0; induction H2; intros; subst.
inversion H0; subst; constructor; auto.
inversion H0; subst.
apply multi_step_LF with M'0; auto. apply IHsteps_LF; auto.
apply lc_t_step_LF in H6; auto.
Qed.
*)

Hint Resolve WT_step.

Inductive ContDia :=
| IdD: ty -> ContDia
| ConsD: ContDia -> te_LF -> ty -> ty -> ContDia
.

Fixpoint ContDiaAppl (K: ContDia) (M: te_LF) : te_LF :=
match K with
| IdD A => M
| ConsD K' N A B => ContDiaAppl K' (letdia_LF A (here_LF M) N)
end.

Inductive ContDiaLC: ContDia -> Prop :=
| ContDLC_nil: forall A, ContDiaLC (IdD A)
| ContDLC_step: forall K N A B,
                 ContDiaLC K -> lc_t_n_LF 1 N -> ContDiaLC (ConsD K N A B)
.

Inductive ContApp :=
| IdA: ty -> ContApp
| LConsA: ContApp -> te_LF -> ty -> ty -> ContApp (* K' M *)
| RConsA: ty -> te_LF -> ContApp -> ty -> ContApp (*  (\T.M) K' *).

Fixpoint ContAppAppl (K: ContApp) (M : te_LF) : te_LF :=
match K with
| IdA A => M
| LConsA K' N A B => ContAppAppl K' (appl_LF M N)
| RConsA A N K' B => ContAppAppl K' (appl_LF (lam_LF A N)  M)
end.

Inductive ContAppLC: ContApp -> Prop :=
| ContALC_nil: forall A, ContAppLC (IdA A)
| ContALC_stepL: forall K N A B,
                 ContAppLC K -> lc_t_LF N -> ContAppLC (LConsA K N A B)
| ContALC_stepR: forall K N A B,
                 ContAppLC K -> lc_t_LF N -> ContAppLC (RConsA A N K B)
.

Lemma WT_KAppl_step:
forall K M M',
  lc_t_LF M ->
  ContAppLC K ->
  WT (ContAppAppl K M') -> steps_LF M  |-> M' -> WT (ContAppAppl K M).
induction K; intros; simpl in *.
apply WT_step_back in H2; auto.
inversion H0; subst; apply IHK with (M':=appl_LF M' t); auto;
repeat constructor; auto.
inversion H0; subst; apply IHK with (M':=appl_LF M' t); auto;
repeat constructor; auto.
Abort.


(*
Lemma Step_KApplStep:
forall K M M',
  ContLC K ->
  lc_t_LF M ->
  M |-> M' ->
  ContAppl K M |-> ContAppl K M'.
induction K; intros; simpl in *.
auto.
inversion H; subst.
assert (letdia_LF t0 (here_LF M) t |-> (letdia_LF t0 (here_LF M') t)).
   constructor; auto; constructor; auto.
apply IHK in H2; auto.
constructor; auto; constructor; auto.
inversion H; subst.
assert (appl_LF M t |-> appl_LF M' t).
   constructor; auto; constructor; auto.
apply IHK in H2; auto.
constructor; auto; constructor; auto.
Qed.

Lemma steps_KApplSteps:
forall K M M',
  ContLC K ->
  lc_t_LF M ->
  steps_LF M M' ->
  steps_LF (ContAppl K M) (ContAppl K M').
intros; generalize dependent K; induction H1; intros.
constructor; apply Step_KApplStep; auto.
apply multi_step_LF with (M':=(ContAppl K M')).
apply Step_KApplStep; auto.
apply IHsteps_LF; auto. apply lc_t_step_LF in H; auto.
Qed.
*)
(*
Lemma neutral_ContAppl:
forall K M,
  neutral_LF M ->
  neutral_LF (ContAppl K M).
induction K; intros; simpl in *.
auto.
apply IHK; constructor; constructor.
apply IHK; constructor; constructor.
Qed.

Lemma neutral_not_value_LF:
forall M,
  neutral_LF M -> ~value_LF M.
induction M; intros; intro; inversion H0; auto; subst; inversion H; subst.
apply IHM in H3; contradiction.
Qed.
*)
(*
Lemma value_ContAppl:
forall K M,
  value_LF (ContAppl K M) ->
  value_LF M /\ exists A, K = IdK A.
induction K; intros; simpl in *.
inversion H; subst; split; auto; eexists; auto.
assert (neutral_LF (ContAppl K (here_LF (letdia_LF t0 M t)))).
apply neutral_ContAppl; constructor; constructor.
Admitted.

apply neutral_not_value_LF in H0; contradiction.
assert (neutral_LF (ContAppl K (here_LF (appl_LF M t)))).
apply neutral_ContAppl; constructor; constructor.
apply neutral_not_value_LF in H0; contradiction.
Qed.
*)

Definition ContDiaRed K K' :=
  forall M, (ContDiaAppl K M) |-> (ContDiaAppl K' M).

Definition ContAppRed K K' :=
  forall M, (ContAppAppl K M) |-> (ContAppAppl K' M).

Definition WTCont K M := WT (ContAppl K (M)).

Fixpoint Red (M: te_LF) (A: ty) : Prop :=
let RedCont K A :=
    (forall V, Red V A -> lc_t_LF V ->
               WT (ContAppl K (V))) in
match A with
| tvar => WT M
| tarrow A1 A2 =>
  WT M /\
  forall N,
    lc_t_LF N ->
    Red N A1 ->
    forall K,
      ContLC K ->
      RedCont K A2 ->
      WT (ContDiaAppl (ContAppAppl K (appl_LF M N)
| tbox A1 => WT M /\
             forall K,
               ContLC K ->
               RedCont K A1 ->
               WTCont K (unbox_LF M)
| tdia A1 =>
  forall K,
    ContLC K ->
    RedCont K A1 ->
    WT (ContAppl K M)
end.

Definition RedCont K A:=
    (forall V, Red V A -> lc_t_LF V ->
               WT (ContAppl K (V))).

(* CR 2 *)
Theorem property_2:
forall A M M'
  (HRed: Red M A)
  (H_lc_t: lc_t_LF M)
  (HStep: M |-> M'),
  Red M' A.
Admitted.
(*
induction A; intros; simpl in *; intros.
(* base type *)
eauto.
(* arrow type *)
destruct HRed; split; eauto; intros.
assert (exists (x: var), x \notin \{}) by apply Fresh; destruct H3.
inversion H; subst.
apply value_no_step_LF in HStep; eauto; contradiction.
[specialize HStep with (fwo x);
  apply value_no_step with (N:=M') (w:=fwo x) in H0; contradiction |
apply H0; auto].
(*
apply WT_step with (M:=ContAppl K (here_LF (appl_LF M N))).
apply H0; auto.
apply Step_KApplStep; auto.
constructor; constructor; auto.
constructor; constructor; auto.
*)
(* box type *)
destruct HRed; split; eauto; intros.
apply WT_step with (M:=ContAppl K (here_LF (unbox_LF M))).
apply H0; auto.
apply Step_KApplStep; auto.
constructor; constructor; auto.
constructor; constructor; auto.
(* dia type *)
specialize HRed with K; assert (ContLC K) by auto;
apply HRed in H; auto; inversion H; subst.
apply value_ContAppl in H2; destruct H2; destruct H3; subst; simpl in *;
apply value_no_step_LF in HStep; auto; contradiction.
assert (ContAppl K M |-> ContAppl K M') by (apply Step_KApplStep; auto);
destruct H2 as (V, (H2, H5)); eauto.
Qed.
*)
(*
Lemma head_expansion_star:
forall A M M'
  (HRed: Red M A)
  (H_lc_t: lc_t_LF M)
  (HStep: M |->* M'),
  Red M' A.
intros; induction HStep; [ assumption | ];
apply IHHStep;
[apply property_2 with x | apply lc_t_step_LF with x]; auto.
Qed.
*)

Lemma property_2_steps:
forall A M M'
  (HRed: Red M A)
  (H_lc_t: lc_t_LF M)
  (HStep: steps_LF M M'),
  Red M' A.
Admitted.

Lemma property_3:
forall A M M'
  (H_lc: lc_t_LF M),
  M |-> M' ->
  Red M' A ->
  Red M A.
Admitted.
(*
assert (exists (x:var), x \notin \{}) as nn by apply Fresh; destruct nn; auto;
induction A; intros; simpl in *; try split; eauto.
apply WT_step_back in H0; auto.
apply WT_step_back in H0; auto; destruct H1; auto.
destruct H1.
intros. apply IHA2 with (appl_LF M' N); try constructor; auto; intros; simpl in *.
apply WT_step_back in H0; auto; destruct H1; auto.
destruct H1. apply IHA with (unbox_LF M'); auto; constructor; auto.
intros.
apply WT_step_back with (N:=ContAppl K M').
apply H1; auto. apply Step_KApplStep; auto.
Qed.
*)

Lemma property3_steps:
forall A M M'
  (H_lc: lc_t_LF M),
  steps_LF M M' ->
  Red M' A ->
  Red M A.
Admitted.

Lemma property_1:
forall A M
  (H_lc_t: lc_t_LF M),
  Red M A -> WT M.
induction A; intros; auto.
destruct H; auto.
destruct H; auto. simpl in H.
assert (WT (ContAppl (IdK A) M)). apply H.
constructor. intros. simpl; apply IHA; auto.
simpl in H0; auto.
Qed.

(*
Lemma lc_ContAppl:
forall K M,
  ContLC K-> lc_t_LF M -> lc_t_LF (ContAppl K M).
induction K; intros; simpl in *.
auto.
inversion H; subst.
apply IHK with (M:=here_LF (letdia_LF t0 M t)) in H3; auto.
Admitted.

constructor; auto. constructor; auto.
inversion H; subst.
apply IHK with (M:=here_LF (appl_LF M t)) in H3; auto.
constructor; auto. constructor; auto.
Qed.
*)
(*
Lemma Red_here:
forall M A, lc_t_LF M -> Red M A -> Red (here_LF M) (<*>A).
simpl; intros; apply H2; auto.
Qed.
*)
(*
Lemma Red_here:
forall M A, lc_t_LF M -> Red M A -> Red (here_LF M) (<*>A).
simpl; intros. apply H2; auto.
Qed.*)

(*
Lemma RedCont_cons:
forall K N B A C,
  ContLC K ->
  lc_t_n_LF 1 N ->
  RedCont K B ->
  (forall P, lc_t_LF P -> Red P C -> Red ([P // bte 0]N) B) ->
  RedCont (ConsK K N A B) C.
unfold RedCont; intros. simpl.
assert (WT V).
  apply property_1 with C; auto.
inversion H5; subst.
apply H1.
Focus 2. repeat constructor; auto.
apply property_3 with (M':=[V//bte 0] N).
repeat constructor; auto.
constructor.
constructor; auto.
apply H2; auto.
destruct H6 as (V', (H6, H7)).
apply WT_steps with (M:=ContAppl K (here_LF (letdia_LF A (here_LF V') N))).
apply steps_KApplSteps; auto.
repeat constructor; auto. apply lc_t_steps_LF with (n:=0) in H7; auto.
skip. (* from H7 *)
apply H1.
Focus 2. repeat constructor; auto. apply lc_t_steps_LF with (n:=0) in H7; auto.
apply property_3 with (M':=[V'//bte 0] N).
repeat constructor; auto. apply lc_t_steps_LF with (n:=0) in H7; auto.
constructor.
constructor; auto. apply lc_t_steps_LF with (n:=0) in H7; auto.
apply H2; auto. apply lc_t_steps_LF with (n:=0) in H7; auto.
apply property_2_steps with (M:=V); auto.
Qed.
*)

Lemma steps_val_here:
forall M V,
  steps_LF (here_LF M) V ->
  value_LF V ->
  exists M0, V = here_LF M0.
intros; remember (here_LF M) as M1;
generalize dependent M; induction H; intros; subst.
inversion H; subst; eexists; eauto.
inversion H; subst.
destruct IHsteps_LF with M'0; auto; subst; eexists; eauto.
Qed.

Lemma steps_letdia:
forall M M', steps_LF M M' ->
forall A N, lc_t_LF M -> lc_t_n_LF 1 N ->
            steps_LF (letdia_LF A M N) (letdia_LF A M' N).
intros M M' H; induction H; intros; simpl in *.
constructor; constructor; auto.
apply multi_step_LF with (M':=letdia_LF A M' N); auto.
constructor; auto. apply IHsteps_LF; auto. apply lc_t_step_LF in H; auto.
Qed.

Lemma steps_here:
forall M M', steps_LF M M' -> lc_t_LF M -> steps_LF (here_LF M) (here_LF M').
intros; induction H; simpl in *.
repeat constructor; auto.
apply multi_step_LF with (M':=here_LF M').
repeat constructor; auto.
apply IHsteps_LF; apply lc_t_step_LF in H; auto.
Qed.

Lemma steps_appl:
forall M M' N,
  steps_LF M M' -> lc_t_LF M -> lc_t_LF N ->
  steps_LF (appl_LF M N) (appl_LF M' N).
Admitted.

Lemma steps_unbox:
forall M M',
  steps_LF M M' -> lc_t_LF M ->
  steps_LF (unbox_LF M) (unbox_LF M').
Admitted.

(*
Lemma Lemma_6:
forall M,
  lc_t_LF M -> WT M ->
  forall N K A, lc_t_n_LF 1 N -> ContLC K ->
  WT (ContAppl K (here_LF (N ^t^ M))) ->
  WT (ContAppl K (here_LF (letdia_LF A (here_LF M) N))).
intros M LC H; induction H; intros.
apply WT_step_back with (N:=ContAppl K (here_LF (N ^t^ V))); auto.
apply Step_KApplStep; auto.
repeat constructor; auto.
repeat constructor; auto.
destruct H as (V, (H, H3)).
apply WT_steps_back
with (N:=(ContAppl K (here_LF (letdia_LF A (here_LF V) N)))).
apply steps_KApplSteps; auto.
repeat constructor; auto.
apply steps_here; auto.
apply steps_letdia; auto.
apply steps_here; auto. constructor; auto.
repeat constructor; auto.
apply WT_step_back with (N:=ContAppl K (here_LF (N ^t^ V))).
Focus 2.
apply Step_KApplStep; auto.
repeat constructor; auto; eapply lc_t_steps_LF in H3; eauto.
repeat constructor; auto.
apply lc_t_steps_LF with (n:=0) in H3; auto.
apply lc_t_steps_LF with (n:=0) in H3; auto.
Admitted.

Lemma Lemma_7:
forall K M A N B,
  lc_t_n_LF 1 N -> lc_t_LF M ->
  Red M (<*>A) ->
  (forall P, Red P A -> Red (N ^t^ P) B) ->
  RedCont K B ->
  ContLC K ->
  WT (ContAppl K (here_LF (letdia_LF A M N))).
intros; simpl in *; unfold RedCont in *.
assert (RedCont (ConsK K N A B) A); unfold RedCont; intros.
simpl.
apply Lemma_6; auto.
apply property_1 in H5; auto.
apply H3. apply H2; auto. unfold open_LF; apply lc_t_subst_t_LF_bound; auto.
unfold RedCont in *. simpl in *.
Admitted.
*)

Lemma Red_SL_hyp:
forall L G Gamma v A,
  OkL L nil ->
  concat (Gamma::G) *=* map fst_ L ->
  (forall a b c, Mem (a, b, c) L -> Red c b) ->
  G |= Gamma |- hyp_LF A (fte v) ::: A ->
  Red (SL L (hyp_LF A (fte v))) A.
intros.
inversion H2; subst.
assert (Mem (v, A) (map fst_ L)).
  apply Mem_permut with (l:=concat (Gamma::G)); auto.
  rew_concat; rewrite Mem_app_or_eq; left; auto.
apply Mem_find_var_type in H3; auto. destruct H3.
simpl; rewrite e; apply H1 with v.
apply find_var_Mem; auto.
Qed.

(*
Lemma WT_letdia:
forall M N A ,
  WT (letdia_LF A M N) -> WT M.
intros; remember (letdia_LF A M N) as M'.
generalize dependent M; generalize dependent N; generalize dependent A.
induction H; intros; subst; [ inversion H | ].
destruct H as (V, (H, H0)).
remember (letdia_LF A M0 N) as M'.
generalize dependent M0; generalize dependent N; generalize dependent A.
induction H0; intros; subst.
inversion H0; subst. rewrite <- WT_here; auto. constructor; auto.
inversion H.
inversion H0; subst. rewrite <- WT_here; auto. constructor; auto.
apply WT_step_back with (N:=M'0); auto.
apply IHsteps_LF with A N; auto.
Qed.

Lemma WT_crazyletdia:
forall A M, lc_t_LF M ->
(WT (letdia_LF A (here_LF M) (here_LF (hyp_LF (bte 0)))) <-> WT M).
split.
intros. apply WT_here; auto. apply WT_letdia in H0; auto.
intros.
inversion H0; subst.
apply WT_step_back with (N:=(here_LF (hyp_LF (bte 0)))^t^ M).
unfold open_LF in *; simpl in *; case_if; rewrite <- WT_here; auto.
constructor; auto; repeat constructor; auto.
destruct H1 as (V, (H1, H2)).
apply WT_steps_back with
(N:=letdia_LF A (here_LF V) (here_LF (hyp_LF (bte 0)))).
Focus 2.
apply WT_step_back with (N:=(here_LF (hyp_LF (bte 0))) ^t^ V).
unfold open_LF; simpl; case_if; rewrite <- WT_here.
  constructor; auto.
  apply lc_t_steps_LF with (n:=0) in H2; auto.
  constructor; auto.
  apply lc_t_steps_LF with (n:=0) in H2; auto.
  repeat constructor; auto.
apply steps_letdia. apply steps_here; auto.
constructor; auto. repeat constructor; omega.
Qed.
*)

(*
Lemma WT_subst_val:
forall M N v,
lc_t_LF M -> lc_t_LF N ->
value_LF N -> WT M -> WT [M // v]N.
intros. generalize dependent M;
generalize dependent v;
induction H1; intros; simpl.
constructor; constructor; auto.
constructor; constructor; auto.
inversion H0; subst;
rewrite <- WT_here; auto.
inversion H0; subst.
destruct v. destruct n.
apply lc_t_subst_t_LF_bound; auto;
apply closed_t_succ_LF; auto.
rewrite closed_subst_t_bound_LF with (n:=0); auto; omega.
apply lc_t_subst_t_LF_free; auto.
Qed.
*)
(*
Lemma value_red:
forall G Gamma V A,
  value_LF V ->
  G |= Gamma |- V ::: A ->
                Red V A.
Abort.
*)
Lemma WT_K_step:
forall K M M',
  lc_t_LF M ->
  ContLC K ->
  WT (ContAppl K M') -> M |-> M' -> WT (ContAppl K M).
induction K; intros; simpl in *.
apply WT_step_back in H2; auto.
inversion H0; subst; apply IHK with (M':=letdia_LF t0 (here_LF M') t); auto;
repeat constructor; auto.
inversion H0; subst; apply IHK with (M':=appl_LF M' t); auto;
repeat constructor; auto.
Abort.

Theorem main_theorem:
forall G Gamma M A,
  lc_t_LF M ->
  G |= Gamma |- M ::: A ->
 forall L,
    OkL L nil ->
    concat(Gamma::G) *=* map fst_ L ->
    (forall a b c, Mem (a,b,c) L -> lc_t_LF c) ->
    (forall a b c, Mem (a,b,c) L -> Red c b) ->
    forall K,
      ContLC K ->
      RedCont K A ->
      WT (ContAppl K (SL L M)).
intros G Gamma M A LC HT;
induction HT;
intros; simpl in *.
(* hyp *)
assert (lc_t_LF (SL L (hyp_LF A (fte v)))) by
  (apply lc_SL; auto; constructor);
simpl in *;
remember (match find_var L v with
           | Some (_, _, M) => M
           | None => hyp_LF A (fte v)
           end) as M';
apply H5; subst; auto; apply Red_SL_hyp with G Gamma; auto; constructor; auto.
(* lam *)
inversion LC; subst; unfold RedCont in *; unfold WTCont;
apply H6. simpl. intros; split. repeat constructor. intros.
 intros; simpl; [split | constructor; apply lc_SL]; auto;
[repeat constructor | intros].
apply WT_step_back with (N:=ContAppl K0 (((SL L0 M) ^t^ N)));
[ unfold open_LF in *;
  assert (exists x, x \notin L \u used_vars_te_LF (SL L0 M) \u FV_L L0
       \u  from_list (map fst_ (map fst_ L0))  \u from_list nil)
  as HF by apply Fresh; destruct HF | ].
rewrite subst_t_neutral_free_LF with (v:=x) (A:=A); auto.
  rewrite SL_bte_subst; auto. rewrite <- SL_extend with (A:=A); auto.
  apply H0; auto.
  apply lc_t_subst_t_LF_bound.
    constructor. inversion LC; auto.
  constructor; [ rewrite Mem_nil_eq | apply OkL_fresh]; auto.
  rew_map in *; simpl; rewrite <-  H2; rew_concat; auto.
  intros; rewrite Mem_cons_eq in *; destruct H13; eauto;
  inversion H13; subst; auto.
  intros; rewrite Mem_cons_eq in *; destruct H13; eauto;
  inversion H13; subst; auto.
  apply notin_Mem; auto. apply notin_Mem; auto.

repeat constructor; auto; apply lc_SL; auto.
constructor.
repeat constructor; auto; apply lc_SL; auto.
auto.
(* appl *)
inversion LC; subst;
assert (WT (ContAppl (ApplK K (SL L N) A B) (SL L M)));
[ | simpl]; auto; apply IHHT1; auto;
[constructor; auto; apply lc_SL; auto | ];
unfold RedCont in *; intros.
simpl.
 simpl; intros; destruct H5.
skip. (* RedCont strikes again *)
simpl in H5. auto.

(* box *)
unfold RedCont in *; inversion LC; subst;
apply H4; [ | constructor; apply lc_SL; auto];
split; [ repeat constructor | intros].
apply WT_step_back with (N:=ContAppl K0 ((SL L M))).
apply IHHT; auto.
rew_map in *; simpl; rewrite <-  H0; rew_concat; auto.
apply Step_KApplStep; auto.
repeat constructor; apply lc_SL; auto.
constructor. repeat constructor; apply lc_SL; auto.
Focus 4.
(* box *)
unfold RedCont in *; inversion LC; subst;
apply H4; [ | constructor; apply lc_SL; auto];
split; [ repeat constructor | intros].
apply WT_step_back with (N:=ContAppl K0 ((SL L M))).
apply IHHT; auto.
rew_map in *; simpl; rewrite <-  H0; rew_concat; auto.
apply Step_KApplStep; auto.
repeat constructor; apply lc_SL; auto.
constructor. repeat constructor; apply lc_SL; auto.
Focus 4.
(* get-here *)
inversion LC; subst.
assert (WT (ContAppl (ConsK K (here_LF (hyp_LF (bte 0))) A A) (SL L M))).
apply IHHT; auto.
rew_map in *; simpl; rewrite <-  H1; rew_concat; auto. permut_simpl.
replace (Gamma ++ concat G) with (concat (Gamma::G)) by (rew_concat; auto).
apply PPermut_concat_permut; rewrite <- H; PPermut_LF_simpl.
constructor; auto; repeat constructor; auto.
skip. (* RedCont *)
simpl in H6.
assert (WT (SL L M)).
  assert (WT (ContAppl (IdK A) (SL L M))).
  apply IHHT; auto.
  rew_map in *; simpl; rewrite <-  H1; rew_concat; auto. permut_simpl.
  replace (Gamma ++ concat G) with (concat (Gamma::G)) by (rew_concat; auto).
  apply PPermut_concat_permut; rewrite <- H; PPermut_LF_simpl.
  constructor. unfold RedCont; intros; simpl.
                                 apply property_1 in H7; auto.
  auto.
assert (exists V, value_LF V /\ (SL L M) |->* V) by skip.
destruct H9 as (V, (H9, H10)).
apply WT_steps_back with (ContAppl K ((here_LF (hyp_LF (bte 0))) ^t^ V)).
apply steps_KApplSteps; auto. repeat constructor; apply lc_SL; auto.
unfold open_LF; simpl; case_if. apply steps_here. skip. apply lc_SL; auto.
apply WT_step with (M:=(ContAppl K
            (letdia_LF A (here_LF V) (here_LF (hyp_LF (bte 0)))))).
apply WT_steps with ((ContAppl K
            (letdia_LF A (here_LF (SL L M)) (here_LF (hyp_LF (bte 0)))))).
apply steps_KApplSteps; auto. repeat constructor; auto; apply lc_SL; auto.
apply steps_letdia. apply steps_here. skip. apply lc_SL. auto. auto.
constructor; apply lc_SL; auto. repeat constructor; auto. auto.
apply Step_KApplStep; auto. repeat constructor; auto. skip.
constructor; auto. skip. repeat constructor; auto.
Focus 4.
(* letdia-get *)
assert (exists x, x \notin L \u used_vars_te_LF (SL L0 M) \u FV_L L0
       \u  from_list (map fst_ (map fst_ L0))  \u from_list nil \u
       used_vars_te_LF (SL L0 N)) by apply Fresh;
destruct H7; inversion LC; subst.
assert (WT (SL L0 M)).
  assert (WT (ContAppl (IdK A) ((SL L0 M)))).
  apply IHHT; auto.
  rewrite <-  H2; apply PPermut_concat_permut. rewrite <- H0; PPermut_LF_simpl.
  constructor. unfold RedCont; intros.
  simpl. apply property_1 in H8; auto.
  auto.
  simpl in H8; auto.
assert (exists V, SL L0 M |->* V /\ value_LF V). skip.
destruct H9 as (V, (H9, H10)).
assert (exists V', V = here_LF V') by skip. destruct H12 as (V', H12).
subst.
assert (WT (ContAppl K ( (letdia_LF A (here_LF V') (SL L0 N))))).
Focus 2.
apply WT_steps_back
with (N:= (ContAppl K ( (letdia_LF A (here_LF V') (SL L0 N))))).
apply steps_KApplSteps; auto.
repeat constructor; apply lc_SL; auto.
apply steps_letdia. skip. (* H9 *)
apply lc_SL; auto. apply lc_SL; auto.
auto.
apply WT_step_back with (N:=(ContAppl K (((SL L0 N)^t^ V')))).
Focus 2.
apply Step_KApplStep; auto.
repeat constructor; auto. apply lc_SL; auto.
skip. (* lc_t_steps_LF in H8; auto *)
constructor. skip. apply lc_SL; auto. inversion H10; auto.
unfold open_LF in *.
rewrite subst_t_neutral_free_LF with (v:=x); auto.
rewrite SL_bte_subst; [ | apply notin_Mem |]; eauto.
rewrite <- SL_extend with (A:=A); auto.
Focus 2. apply notin_Mem; auto.

apply H; auto.
apply lc_t_subst_t_LF_bound; auto; constructor.
constructor. rewrite Mem_nil_eq; auto. apply OkL_fresh; auto.
rew_map in *; simpl; rewrite <-  H2; rew_concat; auto. permut_simpl.
apply PPermut_concat_permut in H0; rewrite <- H0; rew_concat; permut_simpl.
intros; rewrite Mem_cons_eq in *; destruct H12; eauto;
inversion H12; subst; auto. skip.
intros; rewrite Mem_cons_eq in *; destruct H12; eauto;
inversion H12; subst; auto.
inversion H10; constructor; auto.
(* appl *)
(* unbox *)

inversion LC; subst.
assert (WT (SL L M)).
assert (WT (ContAppl (IdK ([*]A)) ((SL L M)))).
  apply IHHT; auto. constructor.
  unfold RedCont; intros; simpl in *;
  destruct H5; auto.
simpl in H5; auto.

remember (unbox_LF (hyp_LF (bte 0))) as N.
assert (WT (ContAppl (ConsK K N ([*]A) A) ((SL L M)))).
apply IHHT; auto. constructor; auto; subst; constructor; constructor; omega.
skip. (* RedCont *)

assert (exists V, SL L M |->* V) by skip.
destruct H8 as (V, H8).
assert (exists M0, V = box_LF (SL L M0)) by skip.
destruct H9 as (M0, H9).
simpl in H6.

apply WT_steps with (N:=ContAppl K (letdia_LF ([*]A)
  (here_LF (box_LF (SL L M0))) N)) in H6.
subst.
apply WT_step with (M':=ContAppl K
 ((unbox_LF (hyp_LF (bte 0))) ^t^ (box_LF (SL L M0)))) in H6.
unfold open_LF in *; simpl in *; case_if.

apply WT_steps_back with
(N:=ContAppl K ((unbox_LF (box_LF (SL L M0))))).
apply steps_KApplSteps; auto. repeat constructor; apply lc_SL; auto.
apply steps_unbox. skip.
apply lc_SL; auto.
auto.

apply Step_KApplStep; auto.
repeat constructor. skip.
constructor. skip. repeat constructor; auto.
constructor.
apply steps_KApplSteps; auto.
subst; repeat constructor; auto; apply lc_SL; auto.
apply steps_letdia. apply steps_here. subst. skip.
apply lc_SL; auto. constructor; apply lc_SL; auto.
subst; repeat constructor; omega.
(* unbox-fetch *)
skip. (* once unbox is done, no need to copy-paste more than once *)
Qed.

Lemma lc_t_n_LF_subst_t:
forall N M n,
lc_t_n_LF n M ->
lc_t_n_LF n (subst_t_LF M (bte n) N) ->
lc_t_n_LF (S n) N.
induction N; intros; simpl in *; try destruct v; constructor;
repeat case_if; try inversion H1; subst; try omega;
inversion H0; subst; eauto.
apply IHN with (M:=M); eauto; apply closed_t_succ_LF; auto.
apply IHN2 with (M:=M); eauto; apply closed_t_succ_LF; auto.
Qed.

Lemma types_LF_lc_t_LF:
forall G Gamma M A,
  G |= Gamma |- M ::: A -> lc_t_LF M.
intros; induction H; constructor; try apply IHHT;
unfold open_LF in *; auto.
assert (exists x, x \notin L) by apply Fresh; destruct H1;
assert (x \notin L) by auto;
specialize H0 with x; apply H0 in H1;
apply lc_t_n_LF_subst_t in H0; auto; constructor.
assert (exists x, x \notin L) by apply Fresh; destruct H1;
assert (x \notin L) by auto;
specialize H0 with (((x, A) :: nil) :: G) x; apply H0 in H1;
apply lc_t_n_LF_subst_t in H0; auto; constructor.
assert (exists x, x \notin L) by apply Fresh; destruct H2;
assert (x \notin L) by auto;
specialize H0 with x; apply H0 in H2;
apply lc_t_n_LF_subst_t in H2; auto; constructor.
Qed.

Lemma SL_nil:
forall M,
  SL nil M = M.
induction M; intros; simpl; try destruct v;
try rewrite IHM || (rewrite IHM1; try rewrite IHM2); eauto.
Qed.

Theorem WT_Lang:
forall G M A,
  emptyEquiv_LF G |= nil |- M ::: A ->
  WT M.
intros.
assert (lc_t_LF M).
  apply types_LF_lc_t_LF in H; auto.
assert (WT (ContAppl (IdK A) M)).
apply main_theorem with (L:=nil) (K:=IdK A) in H; auto.
rewrite SL_nil in H; auto.
constructor.
rew_concat; rew_map; clear M A H H0;
induction G; simpl; rew_concat; auto.
intros; rewrite Mem_nil_eq in *; contradiction.
intros; rewrite Mem_nil_eq in *; contradiction.
constructor.
unfold RedCont; intros; simpl.
apply property_1 in H1; auto.
simpl in H1; auto.
Qed.