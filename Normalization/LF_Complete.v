Add LoadPath "..".
Add LoadPath "../LabelFree/SingleUnbox".
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
induction M; intros; inversion H0; inversion H; subst; try constructor; eauto.
apply lc_t_subst_t_LF_bound; auto.
eapply IHM1; eauto.
eapply IHM; eauto.
eapply IHM; eauto.
(*constructor; auto. *)
unfold open_LF; apply lc_t_subst_t_LF_bound; auto.
eapply IHM1; eauto.
(* constructor; auto. apply closed_t_succ_LF; auto. *)
Qed.

Definition normal_form (M: te_LF) := value_LF M.

Inductive neutral_LF: te_LF -> Prop :=
| nHyp: forall n, neutral_LF (hyp_LF n)
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

Require Export Relations.
Definition multisteps := clos_refl_trans_1n _ step_LF.
Notation " M |->* N " := (multisteps M N) (at level 70).


Definition WT' (M: te_LF) :=
  exists V, value_LF V /\ M |->* V.

(* FIXME: WT' would be more elegant *)
Inductive WT: te_LF -> Prop :=
| val_WT: forall V, value_LF V -> WT V
| step_WT: forall M, (exists V, value_LF V /\ steps_LF M V) -> WT M
.

Lemma step_LF_unique:
forall M N1 N2,
  M |-> N1 ->
  M |-> N2 ->
  N1 = N2.
induction M; intros; inversion H; inversion H0; subst; auto.
inversion H6; subst; auto.
inversion H11.
inversion H6.
specialize IHM1 with M' M'0; rewrite IHM1; auto.
inversion H4; subst; auto.
inversion H6.
inversion H3.
specialize IHM with M' M'0; rewrite IHM; auto.
specialize IHM with M' M'0; rewrite IHM; auto.
inversion H9; subst; auto.
inversion H14; subst. apply value_no_step_LF in H3; auto; contradiction.
inversion H7; subst. apply value_no_step_LF in H3; auto; contradiction.
specialize IHM1 with M' M'0; rewrite IHM1; auto.
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
apply step_LF_unique with (N1:=V) in H0; subst; auto. constructor; auto.
apply step_WT; exists V; split; auto.
apply step_LF_unique with (N1:=M'0) in H0; subst; auto.
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

Hint Resolve WT_step.

Inductive Cont :=
| IdK: ty -> Cont
| ConsK: Cont -> te_LF -> ty -> ty -> Cont
.

(* continuation - type it takes (without <*>) - type it returns *)
Inductive ContTyping: Cont -> ty -> ty -> Prop:=
| IdKT: forall A, ContTyping (IdK A) A A
| ConsKT:
    forall K B C,
      ContTyping K B C ->
      forall N A,
        ContTyping (ConsK K N A B) A C
.

Fixpoint ContAppl (K: Cont) (M: te_LF) : te_LF :=
match K with
| IdK A => here_LF M
| ConsK K' N A B => ContAppl K' (here_LF (letdia_LF A M N))
end.

Inductive ContLC: Cont -> Prop :=
| ContLC_nil: forall A, ContLC (IdK A)
| ContLC_step: forall K N A B,
                 ContLC K -> lc_t_n_LF 1 N -> ContLC (ConsK K N A B)
.

Lemma Step_KApplStep:
forall K M M',
  ContLC K ->
  lc_t_LF M ->
  M |-> M' ->
  ContAppl K M |-> ContAppl K M'.
induction K; intros; simpl in *.
constructor; auto.
inversion H; subst.
assert (here_LF (letdia_LF t0 M t) |-> here_LF (letdia_LF t0 M' t)).
   constructor; auto; constructor; auto.
apply IHK in H2; auto.
constructor; auto; constructor; auto.
Qed.

Lemma neutral_ContAppl:
forall K M,
  neutral_LF M ->
  neutral_LF (ContAppl K M).
induction K; intros; simpl in *.
constructor; auto.
apply IHK; constructor; constructor.
Qed.

Lemma neutral_not_value_LF:
forall M,
  neutral_LF M -> ~value_LF M.
induction M; intros; intro; inversion H0; auto; subst; inversion H; subst.
apply IHM in H3; contradiction.
Qed.

Lemma value_ContAppl:
forall K M,
  value_LF (ContAppl K M) ->
  value_LF M /\ exists A, K = IdK A.
induction K; intros; simpl in *.
inversion H; subst; split; auto; eexists; auto.
assert (neutral_LF (ContAppl K (here_LF (letdia_LF t0 M t)))).
apply neutral_ContAppl; constructor; constructor.
apply neutral_not_value_LF in H0; contradiction.
Qed.

Fixpoint Red (M: te_LF) (A: ty) : Prop :=
let RedCont K A :=
    (forall V, Red V A -> lc_t_LF V ->
               WT (ContAppl K (here_LF V))) in
match A with
| tvar => WT M
| tarrow A1 A2 =>
  WT M /\
  forall N
         (H_lc: lc_t_LF N)
         (HRed: Red N A1),
    forall K,
      ContLC K ->
      RedCont K A2 ->
    WT (ContAppl K (here_LF (appl_LF M N)))

| tbox A1 => WT M /\
             forall K,
               ContLC K ->
               RedCont K A1 ->
               WT (ContAppl K (here_LF (unbox_LF M)))
| tdia A1 =>
  forall K,
    ContLC K ->
    RedCont K A1 ->
    WT (ContAppl K M)
end.

Definition RedCont K A:=
    (forall V, Red V A -> lc_t_LF V ->
               WT (ContAppl K (here_LF V))).

(* CR 2: head expansion *)
Theorem property_2:
forall A M M'
  (HRed: Red M A)
  (H_lc_t: lc_t_LF M)
  (HStep: M |-> M'),
  Red M' A.
induction A; intros; simpl in *; intros.
(* base type *)
eauto.
(* arrow type *)
destruct HRed; split; eauto; intros.
apply WT_step with (M:=ContAppl K (here_LF (appl_LF M N))).
apply H0; auto.
apply Step_KApplStep; auto.
constructor; constructor; auto.
constructor; constructor; auto.
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

Lemma lc_ContAppl:
forall K M,
  ContLC K-> lc_t_LF M -> lc_t_LF (ContAppl K M).
induction K; intros; simpl in *.
constructor; auto.
inversion H; subst.
apply IHK with (M:=here_LF(letdia_LF t0 M t)) in H3; auto.
constructor; auto. constructor; auto.
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
| hyp_LF (bte v) => M
| hyp_LF (fte v) =>
  let x := find_var L v in
  match x with
    | Some (v, A, M) => M
    | None => hyp_LF (fte v)
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

Lemma SL_hyp:
forall L G Gamma v A,
  OkL L nil ->
  concat (Gamma::G) *=* map fst_ L ->
  (forall a b c, Mem (a, b, c) L -> Red c b) ->
  G |= Gamma |- hyp_LF (fte v) ::: A ->
  Red (SL L (hyp_LF (fte v))) A.
intros; inversion H2; subst.
assert (Mem (v, A) (map fst_ L)).
  apply Mem_permut with (l:=concat (Gamma::G)); auto.
  rew_concat; rewrite Mem_app_or_eq; left; auto.
apply Mem_find_var_type in H3; auto. destruct H3.
simpl; rewrite e; apply H1 with v.
apply find_var_Mem; auto.
Qed.

Lemma eq_te_LF_dec:
forall (M1: te_LF) (M2: te_LF),
  {M1 = M2} + {M1 <> M2}.
decide equality.
apply eq_vte_dec.
apply eq_ty_dec.
apply eq_ty_dec.
Qed.

Lemma SL_bte_subst:
forall L0 M x k,
  ~ Mem x (map fst_ (map fst_ L0)) ->
  (forall v a m, Mem (v, a, m) L0 -> lc_t_LF m) ->
  [hyp_LF (fte x) // bte k](SL L0 M) =
  SL L0 [hyp_LF (fte x) // bte k]M.
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

Lemma property_1:
forall A M
  (H_lc_t: lc_t_LF M),
  Red M A -> WT M.
induction A; intros; simpl in *; auto.
destruct H; auto.
destruct H; auto.
assert (WT (ContAppl (IdK A) M)).
apply H.
constructor.
intros; simpl in *. rewrite <- WT_here. rewrite <- WT_here; auto.
constructor; auto.
simpl in H0. apply WT_here in H0; auto.
Qed.

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
    WT (ContAppl K (here_LF (SL L M))).
intros G Gamma M A LC HT.
induction HT; unfold RedCont in *;
intros; simpl in *.
(* hyp *)
assert (lc_t_LF (SL L (hyp_LF (fte v)))) by
  (apply lc_SL; auto; constructor);
simpl in *;
remember (match find_var L v with
           | Some (_, _, M) => M
           | None => hyp_LF (fte v)
           end) as M';
assert (Red M' A)
  by (subst; apply SL_hyp with G Gamma; auto; constructor; auto);
apply H5; auto.
(* lam *)
apply H6; auto; [split | inversion LC; constructor; apply lc_SL; auto];
[repeat constructor | intros];
apply WT_step_back with (N:=ContAppl K0 (here_LF ((SL L0 M) ^t^ N))).
unfold open_LF in *;
assert (exists x, x \notin L \u used_vars_te_LF (SL L0 M) \u FV_L L0
       \u  from_list (map fst_ (map fst_ L0))  \u from_list nil)
  by apply Fresh; destruct H9;
rewrite subst_t_neutral_free_LF with (v:=x); auto;
replace (here_LF [N // fte x]([hyp_LF (fte x) // bte 0](SL L0 M))) with
(here_LF (SL ((x, A, N) :: L0) ([hyp_LF (fte x) // bte 0]M))).
apply H0; auto.
apply lc_t_subst_t_LF_bound.
 constructor. inversion LC; auto.
constructor; [ rewrite Mem_nil_eq | apply OkL_fresh]; auto.
rew_map in *; simpl; rewrite <-  H2; rew_concat; auto.
intros; rewrite Mem_cons_eq in *; destruct H10.
inversion H10; subst; auto.
apply H3 with a b; auto.
intros; apply Mem_cons_spec in H10. destruct H10.
inversion e; subst; auto.
apply H4 with a; auto.
intros; destruct k; destruct p; destruct k'; destruct p; decide equality.
apply eq_te_LF_dec. destruct p; destruct a0; decide equality.
apply eq_ty_dec. apply eq_var_dec.
rewrite SL_bte_subst; auto. rewrite SL_extend; auto.
apply notin_Mem; auto.
apply notin_Mem; auto.
apply Step_KApplStep; auto.
repeat constructor; auto; apply lc_SL; auto. inversion LC; auto.
constructor. repeat constructor; auto; inversion LC; apply lc_SL; auto.
constructor. apply lc_SL; inversion LC; auto. auto.
Focus 2.
(* box *)
inversion LC; subst;
apply H4; [ | constructor; apply lc_SL; auto];
split; [ repeat constructor | intros].
apply WT_step_back with (N:=ContAppl K0 (here_LF (SL L M))).
apply IHHT; auto.
rew_map in *; simpl; rewrite <-  H0; rew_concat; auto.
apply Step_KApplStep; auto.
repeat constructor; apply lc_SL; auto.
constructor. repeat constructor; apply lc_SL; auto.
constructor; apply lc_SL; auto.
Focus 4.
apply H4; [ intros | inversion LC; constructor; apply lc_SL; auto].
apply IHHT; inversion LC; auto.
Focus 4.
apply H5; [ intros | inversion LC; constructor; apply lc_SL; auto].
apply IHHT; inversion LC; subst; auto.
rew_map in *; simpl; rewrite <-  H1; rew_concat; auto. permut_simpl.
replace (Gamma ++ concat G) with (concat (Gamma::G)) by (rew_concat; auto).
apply PPermut_concat_permut; rewrite <- H; PPermut_LF_simpl.
Focus 4.
replace (ContAppl K (here_LF (letdia_LF A (SL L0 M) (SL L0 N)))) with
(ContAppl (ConsK K (SL L0 N) A B) (SL L0 M)).
Focus 2. simpl; auto.
apply WT_here. skip.
assert (WT (here_LF (ContAppl (ConsK K (SL L0 N) A B) (SL L0 M))) <->
WT ((ContAppl (ConsK K (SL L0 N) A B) (here_LF (SL L0 M))))).
skip.
inversion LC; subst; apply H6; apply IHHT; auto.
constructor; auto; apply lc_SL; auto.
intros.
assert (WT (here_LF (ContAppl (ConsK K (SL L0 N) A B) V)) <->
WT ((ContAppl (ConsK K (SL L0 N) A B) (here_LF V)))).
skip.
apply H9. rewrite <- WT_here. simpl.
simpl.


Focus 2.
inversion LC; subst.
assert (WT (ContAppl K (here_LF (SL L M)))).
apply IHHT; auto; intros; destruct H5.
assert (WT (ContAppl K (here_LF (unbox_LF V)))).
apply H8; auto.
skip.
<


inversion LC; subst.









remember (here_LF (appl_LF (SL L M) (SL L N))) as HMN.
generalize dependent M;
generalize dependent N;
generalize dependent L;
generalize dependent A;
generalize dependent B.
induction K; intros.
subst.
assert (WT (ContAppl (IdK (A ---> B)) (here_LF (SL L M)))).
apply IHHT1; auto; intros. destruct H4.
simpl. apply WT_here. constructor; auto.
simpl. apply WT_here; auto.
simpl in *.
apply WT_here. repeat constructor; apply lc_SL; auto.
apply WT_here. repeat constructor; apply lc_SL; auto.
skip.
simpl.
assert (WT (ContAppl (IdK A) (here_LF (SL L N)))).
apply IHHT2; auto; intros.
simpl. apply WT_here. constructor; auto.
apply WT_here; auto. apply property_1 in H5; auto.
assert (WT (ContAppl K (here_LF (SL L M)))).
apply IHHT1; auto; intros. destruct H6.

simpl. apply WT_here. constructor; auto.
simpl. apply WT_here; auto.


assert (Red (SL L M) (A ---> B)).
simpl in *; split.
apply WT_here_back. apply lc_SL; auto.
apply WT_here_back. constructor; apply lc_SL; auto.
auto.
intros.

assert (WT (ContAppl (IdK (A ---> B)) (here_LF (SL L M)))).
apply IHHT1; auto.
constructor. auto.
intros. simpl.
destruct H6.
Lemma WT_expand:
forall M A,
  lc_t_LF M ->
  WT M ->
  WT (letdia_LF A (here_LF M) (hyp_LF (bte 0))).
intros. inversion H0; subst; apply step_WT.
exists ((hyp_LF (bte 0)) ^t^ M); split;
[unfold open_LF; simpl; case_if; auto | constructor].
constructor; auto. constructor; omega.
destruct H1; destruct H1; exists x; split; auto.
assert (steps_LF (letdia_LF A (here_LF M) (hyp_LF (bte 0)))
                 (letdia_LF A (here_LF x) (hyp_LF (bte 0)))).
remember (here_LF M) as y.
remember (here_LF x) as x'.
remember (hyp_LF (bte 0)) as z.
induction H2.
constructor; constructor; auto.
subst; constructor; auto.
subst; constructor; omega.
subst; constructor; auto. skip.
skip.
Qed.
simpl.
apply WT_expand with (A:=A ---> B) in H6.
replace (appl_LF (SL L M) (SL L N)) with (SL L (appl_LF M N)) by (simpl; auto).

assert (WT (ContAppl (IdK (A ---> B)) (here_LF (SL L M)))).
apply IHHT1 with (A ---> B); auto. constructor.
intros; destruct H6; simpl.
apply WT_here. constructor; auto. apply WT_here; auto.

apply H6; auto; [ | inversion LC; subst; constructor; apply lc_SL; auto];
split; [constructor; constructor | intros].

(* appl *)
(* box *)
(* unbox *)
(* here *)
(* get_here *)
(* letdia *)
(* letdia_get *)



























































Focus 9.
apply step_WT; intros.

simpl in *.
(* here (letdia x = m in n ) -> letdia x = m in here n*)
(* letdia y = (letdia x = m in n ) in p - > letdia x =m in letdia y= here n in p *)

(*
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
induction M; intros; inversion H0; inversion H; subst; try constructor; eauto.
apply lc_t_subst_t_LF_bound; auto.
eapply IHM1; eauto.
eapply IHM; eauto.
eapply IHM; eauto.
unfold open_LF; apply lc_t_subst_t_LF_bound; auto.
eapply IHM1; eauto.
Qed.

Lemma WT_appl:
forall M N,
  lc_t_LF (appl_LF M N) ->
  WT (appl_LF M N) ->
  WT M.
intros;
remember (appl_LF M N) as T;
generalize dependent M;
generalize dependent N;
induction H0; intros; subst;
[ inversion H0 |
  assert (neutral_LF M0 \/ value_LF M0) by apply neutral_or_value_LF];
destruct H2;
[ inversion H; subst |
  constructor; auto];
apply step_WT; intros;
apply H1 with (N0:=appl_LF N0 N) (N:=N).
constructor; eauto.
apply lc_t_step_LF with (M:=appl_LF M0 N); auto; constructor; auto.
auto.
Qed.

Lemma WT_box:
forall M,
  lc_t_LF (unbox_LF M) ->
  WT (unbox_LF M) ->
  WT M.
intros; remember (unbox_LF M) as T;
generalize dependent M;
induction H0; intros; subst;
[ inversion H0 |
  assert (neutral_LF M0 \/ value_LF M0) by apply neutral_or_value_LF];
destruct H2; [ inversion H; subst | constructor; auto];
apply step_WT; intros;
apply H1 with (N := unbox_LF N).
constructor; inversion H; auto.
apply lc_t_step_LF with (M:=unbox_LF M0); auto; constructor; auto.
auto.
Qed.

Lemma WT_here:
forall M,
  lc_t_LF (here_LF M) ->
  WT (here_LF M) ->
  WT M.
intros;
remember (here_LF M) as T;
generalize dependent M;
induction H0; intros; subst.
inversion H0; subst; constructor; auto.
assert (neutral_LF M0 \/ value_LF M0) by apply neutral_or_value_LF.
destruct H2;
[ inversion H; subst |
  constructor; auto].
apply step_WT; intros;
apply H1 with (N:=here_LF N).
constructor; eauto.
apply lc_t_step_LF with (M:=here_LF M0); auto; constructor; auto.
auto.
Qed.

Theorem WT_step:
forall M M',
  WT M ->
  M |-> M' ->
  WT M'.
intros; inversion H; subst.
apply value_no_step_LF with (N:=M') in H1; contradiction.
apply H1; auto.
Qed.

Lemma Step_KApplStep:
forall K M M',
  ContLC K ->
  lc_t_LF M ->
  M |-> M' ->
  ContAppl K M |-> ContAppl K M'.
induction K; intros; simpl in *.
constructor; auto.
inversion H; subst.
assert ((letdia_LF M (here_LF t)) |-> (letdia_LF M' (here_LF t))).
   constructor; auto; constructor; auto.
apply IHK in H2; auto.
constructor; auto; constructor; auto.
Qed.

(* CR 2 *)
Theorem property_2:
forall A M M'
  (HRed: Red M A)
  (H_lc_t: lc_t_LF M)
  (HStep: M |-> M'),
  Red M' A.
induction A; intros; simpl in *; intros.
(* base type *)
inversion HRed; subst;
[apply value_no_step_LF with (N:=M') in H; contradiction | apply H; auto].
(* arrow type *)
apply IHA2 with (M:=appl_LF M N); auto.
constructor; auto.
constructor; auto.
(* box type *)
apply IHA with (M:=unbox_LF M); auto; constructor; eauto.
(* dia type *)
specialize HRed with K B.
assert (ContLC K) by auto;
apply HRed in H; auto.
apply WT_step with (M:=ContAppl K M); auto.
apply Step_KApplStep; auto.
Qed.

Lemma WT_N_WT_here:
forall N,
  WT N -> WT (here_LF N).
intros; induction H; subst.
constructor; constructor; auto.
apply step_WT; intros.
inversion H1; subst.
apply H0 in H4; auto.
Qed.

Lemma lc_ContAppl:
forall K M,
  ContLC K-> lc_t_LF M -> lc_t_LF (ContAppl K M).
induction K; intros; simpl in *.
constructor; auto.
inversion H; subst.
apply IHK with (M:=(letdia_LF M (here_LF t))) in H3; auto;
constructor; auto; constructor; auto.
Qed.

Lemma neutral_ContAppl:
forall K M,
  neutral_LF M ->
  neutral_LF (ContAppl K M).
induction K; intros; simpl in *.
constructor; auto.
apply IHK; constructor; constructor.
Qed.

Lemma neutral_not_value:
forall M,
  neutral_LF M -> ~ value_LF M.
induction M; intros; intro; try inversion H0; subst; inversion H; subst.
apply IHM in H3; contradiction.
Qed.

Lemma step_neutral_ContAppl:
forall K M N,
  neutral_LF M ->
  ContAppl K M |-> N ->
  (exists M', N = ContAppl K M' /\ M |-> M').
induction K; intros; simpl in *.
inversion H0; subst; eexists; split; eauto.
destruct IHK with (M:=(letdia_LF M (here_LF t))) (N:=N).
constructor; constructor.
auto.
destruct H1.
inversion H2; subst.
inversion H; subst; apply neutral_not_value in H3; contradiction.
eexists; split; eauto.
Qed.

(* CR1 + CR3 *)
Theorem reducibility_props:
forall A M
  (H_lc_t: lc_t_LF M),
  (Red M A -> WT M)
  /\
  (neutral_LF M -> (forall M', M |-> M' -> Red M' A) -> Red M A).
assert (exists (x:var), x \notin \{}) as nn by apply Fresh; destruct nn; auto;
induction A; intros; split; simpl in *.
(* base type *)
auto.
intros; apply step_WT; auto.
(* arrow type *)
intros.
(* Create variable of type A1 *)
assert (forall x, nil |= (x, A1) :: nil |- hyp_LF (fte x) ::: A1).
intros; constructor.
unfold ok_Bg_LF; rew_concat; constructor;
[rewrite Mem_nil_eq | constructor]; auto.
apply Mem_here.
assert (forall x, neutral_LF (hyp_LF x)) by (intros; constructor).
assert (forall x, WT (hyp_LF x))
  by (intros; apply step_WT; intros; inversion H3).
assert (forall x, Red (hyp_LF (fte x)) A1).
  intros; apply IHA1; auto.
  constructor.
  intros; inversion H4.
assert (forall x, Red (appl_LF M (hyp_LF (fte x))) A2).
intros; eapply H0; auto; constructor.
assert (forall x, WT (appl_LF M (hyp_LF (fte x)))).
intros; eapply IHA2; eauto; constructor; auto; constructor.
(* From strong_norm (appl_L M (hyp_L x)) w deduce strong_norm M w *)
eapply WT_appl; auto; constructor; auto; constructor.
intros; apply IHA2; try constructor; auto; intros; simpl in *.
inversion H2; subst; inversion H0; eapply H1; eauto.
(* box type *)
intros; apply WT_box.
constructor; auto.
apply IHA; [constructor | ]; auto.
intros; apply IHA; try constructor; auto; intros;
inversion H2; subst; [inversion H0 | ]; apply H1; auto.
(* dia type *)
intros.
assert (WT (ContAppl (IdK A) M)).
apply H0 with (B:=A).
constructor.
constructor.
intros. simpl.
apply IHA in H2.
apply WT_N_WT_here; apply WT_N_WT_here; destruct H2; auto.
simpl in H1.
apply WT_here.
constructor; auto.
auto.
intros.
apply step_WT; intros; apply step_neutral_ContAppl in H5; auto;
destruct H5; destruct H5;
subst; apply H1 with B; auto.
Grab Existential Variables.
auto.
Qed.

Lemma property_1:
forall A M
  (H_lc: lc_t_LF M),
  Red M A -> WT M.
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

Fixpoint find_var (L: list (var * ty * te_LF)) (x:var) :
                     option (var * ty * te_LF) :=
match L with
| nil => None
| (v, A, M) :: L' =>
  if (eq_var_dec x v) then Some (v, A, M) else find_var L' x
end.

Fixpoint SL (L: list (var * ty * te_LF)) M :=
match M with
| hyp_LF (bte v) => M
| hyp_LF (fte v) =>
  let x := find_var L v in
  match x with
    | Some (v, A, M) => M
    | None => hyp_LF (fte v)
  end
| lam_LF A M => lam_LF A (SL L M)
| appl_LF M N => appl_LF (SL L M) (SL L N)
| box_LF M => box_LF (SL L M)
| unbox_LF M => unbox_LF (SL L M)
| here_LF M => here_LF (SL L M)
| letdia_LF M N => letdia_LF (SL L M) (SL L N)
end.

Lemma Mem_concat_mem_elem:
forall G (e:var*ty),
  Mem e (concat G) ->
  exists (l: ctx_LF), Mem l G /\ Mem e l.
induction G; intros; rew_concat in *.
rewrite Mem_nil_eq in H; contradiction.
rewrite Mem_app_or_eq in H; destruct H.
exists a; split; auto; apply Mem_here.
destruct (IHG e); auto; destruct H0; exists x; split; auto.
rewrite Mem_cons_eq; right; auto.
Qed.

Lemma ok_LF_Mem_Mem_eq':
  forall (G : ctx_LF)(v : var) (A B : ty),
    ok_LF G nil  ->
    Mem (v, A) G -> Mem (v,B) G ->
    A = B.
induction G; intros.
rewrite Mem_nil_eq in H0; contradiction.
rewrite Mem_cons_eq in *; destruct H0; destruct H1; subst.
inversion H1; subst; auto.
inversion H; subst; apply Mem_split in H1; destruct H1 as (hd, (tl, H1));
assert (hd & (v, B) ++ tl *=* (v, B) :: hd ++ tl) by permut_simpl;
rewrite H1 in H6; apply ok_LF_permut with (G':= (v, B) :: hd ++ tl) in H6;
auto; inversion H6; subst; elim H8; apply Mem_here.
inversion H; subst; apply Mem_split in H0; destruct H0 as (hd, (tl, H0));
assert (hd & (v, A) ++ tl *=* (v, A) :: hd ++ tl) by permut_simpl;
rewrite H0 in H6; apply ok_LF_permut with (G':= (v, A) :: hd ++ tl) in H6;
auto; inversion H6; subst; elim H8; apply Mem_here.
eapply IHG; eauto.
inversion H; subst; eapply ok_LF_used_weakening; eauto.
Qed.

Lemma SL_hyp:
forall L G Gamma v A,
  concat (Gamma::G) *=* map fst_ L ->
  (forall a b c, Mem (a, b, c) L -> Red c b) ->
  G |= Gamma |- hyp_LF (fte v) ::: A ->
  Red (SL L (hyp_LF (fte v))) A.
induction L; intros; rew_map in *.
symmetry in H; apply permut_nil_eq in H; rew_concat in *;
symmetry in H; apply nil_eq_app_inv in H; destruct H; subst;
inversion H1; subst; rewrite Mem_nil_eq in *; contradiction.
destruct a; destruct p; inversion H1; subst; simpl in *.
case_if.
assert (A = t0).
unfold ok_Bg_LF in *.
apply ok_LF_Mem_Mem_eq' with (concat (Gamma::G)) v0; auto;
[rew_concat; rewrite Mem_app_or_eq; left; auto | ].
apply Mem_permut with (l:=(v0,t0) :: map fst_ L); [symmetry; auto |
apply Mem_here].
subst; apply H0 with v0; apply Mem_here.
assert (concat (Gamma :: G) *=* (v0, t0) :: map fst_ L) by auto;
symmetry in H; apply permut_split_head in H;
destruct H as (hd, (tl, H)).
destruct Mem_concat_mem_elem with (e:=(v0, t0)) (G:=Gamma::G).
apply Mem_permut with (l:=(v0,t0) :: map fst_ L); [symmetry; auto |];
apply Mem_here. destruct H4.
apply Mem_split in H4.
apply Mem_split in H6.
destruct H6 as (l0, (l1,H6)).
destruct H4 as (G0, (G1, H4)); subst.
destruct G0; rew_app in *.
inversion H4; subst. apply IHL with G1 (l0++l1).
rew_concat in *.
apply permut_cons_inv with (a:=(v0,t0)).
rewrite <- H3. permut_simpl.
intros; apply H0 with a; rewrite Mem_cons_eq; right; auto.
constructor.
eapply ok_Bg_LF_permut_first_tail in Ok; eauto; permut_simpl.
rewrite Mem_app_or_eq in *; destruct H5; auto; rewrite Mem_cons_eq in *;
destruct H5; auto; inversion H5; subst; elim H2; auto.
inversion H4; subst.
apply IHL with (G0 ++ (l0 ++ l1) :: G1) c.
rew_concat in *. apply permut_cons_inv with (a:=(v0,t0)).
rewrite <- H3. permut_simpl.
intros; apply H0 with a; rewrite Mem_cons_eq; right; auto.
constructor; auto.
assert (c :: G0 ++ (l0 ++ (v0, t0) :: l1) :: G1 ~=~
        ((l0++(v0, t0) :: l1) :: c :: G0 ++ G1)).
PPermut_LF_simpl; constructor; auto; permut_simpl.
rewrite H6 in Ok.
eapply ok_Bg_LF_permut_first_tail with (x:=v0)(A:=t0) (C':=l0++l1)in Ok; eauto.
Focus 2. permut_simpl.
apply ok_Bg_LF_PPermut with (G:=(l0 ++ l1) :: c :: G0 ++ G1); auto;
PPermut_LF_simpl.
Qed.

Lemma closed_t_succ:
forall M n,
  lc_t_n_LF n M -> lc_t_n_LF (S n) M.
intros; generalize dependent n;
induction M; intros; inversion H; subst;
eauto using lc_t_n_LF.
Qed.

Lemma closed_t_addition:
forall M n m,
  lc_t_n_LF n M -> lc_t_n_LF (n + m) M.
intros; induction m;
[ replace (n+0) with n by auto |
  replace (n + S m) with (S (n+m)) by auto] ;
try apply closed_t_succ;
assumption.
Qed.

Lemma SL_nil:
forall M,
  SL nil M = M.
induction M; intros; simpl in *;
try erewrite IHM || (erewrite IHM1; erewrite IHM2); eauto.
destruct v; auto.
Qed.

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

Lemma lc_SL:
forall M L n,
  lc_t_n_LF n M ->
  (forall a b c, Mem (a,b,c) L -> lc_t_LF c) ->
  lc_t_n_LF n (SL L M).
induction M; intros; simpl in *;
try (inversion H; subst; constructor; eapply IHM; eauto).
destruct v; inversion H; subst.
constructor; auto.
destruct (Mem_dec var (map fst_ (map fst_ L)) v). apply eq_var_dec.
apply Mem_find_var in m; destruct m; destruct H1.
rewrite H1. replace n with (0+n) by omega.
apply closed_t_addition; apply H0 with v x. apply find_var_Mem; auto.
rewrite NotMem_find_var; auto.
inversion H; subst; constructor; [apply IHM1 | apply IHM2]; auto.
inversion H; subst; constructor; [eapply IHM2 | apply IHM1]; auto.
Qed.

Lemma SL_bte_subst:
forall L0 M x k,
  ~ Mem x (map fst_ (map fst_ L0)) ->
  (forall v a m, Mem (v, a, m) L0 -> lc_t_LF m) ->
  [hyp_LF (fte x) // bte k](SL L0 M) =
  SL L0 [hyp_LF (fte x) // bte k]M.
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

Lemma Red_appl:
forall M N A B,
lc_t_LF (appl_LF M N) -> Red M (A ---> B) -> Red N A -> Red (appl_LF M N) B.
intros; simpl in *; apply H0; inversion H; auto.
Qed.

Lemma Red_unbo:
forall M A,
Red M ([*]A) -> Red (unbox_LF M) A.
intros; simpl in *; auto.
Qed.

Lemma Red_here:
forall N A,
lc_t_LF N -> Red N A -> Red (here_LF N) (<*>A).
intros; simpl in *; intros; apply H3; auto.
Qed.

Lemma WT_letdia:
forall K M N,
  WT M ->
  WT (ContAppl K ([M // bte 0]N)) ->
  WT (ContAppl K (here_LF (letdia_LF (here_LF M) N))).
Admitted.

Theorem main_theorem:
forall G Gamma M A,
  lc_t_LF M ->
  G |= Gamma |- M ::: A ->
 forall L,
    concat(Gamma::G) *=* map fst_ L ->
    (forall a b c, Mem (a,b,c) L -> lc_t_LF c) ->
    (forall a b c, Mem (a,b,c) L -> Red c b) ->
  forall K B,
    ContTyping K A B ->
    RedCont K A B ->
    WT (ContAppl K (here_LF (SL L M))).
intros G Gamma M A LC HT; induction HT; unfold RedCont in *;
intros.
(* hyp *)
assert (lc_t_LF (SL L (hyp_LF (fte v)))) by
  (apply lc_SL; auto; constructor);
simpl in *;
remember (match find_var L v with
           | Some (_, _, M) => M
           | None => hyp_LF (fte v)
           end) as M';
assert (Red M' A) by
(subst; apply SL_hyp with G Gamma; auto; constructor; auto);
apply H4 with (V:=M') in H3; auto.
Focus 8.
simpl.
replace (ContAppl K (here_LF (letdia_LF (SL L0 M) (SL L0 N)))) with
 (ContAppl (ConsK K (SL L0 N) A B) (SL L0 M)) by (simpl; auto).
remember (ConsK K (SL L0 N) A B) as K'.

(* lam *)
unfold open_LF in *.
assert (exists x, x \notin L \u used_vars_te_LF (SL L0 M) \u
       from_list (map fst_ (map fst_ L0)) \u FV_L L0) by apply Fresh;
destruct H6.
assert (WT (ContAppl K (here_LF (SL L0 [hyp_LF (fte x) // bte 0]M)))).
apply H0 with B0; eauto.
apply lc_t_subst_t_LF_bound; [constructor | inversion LC]; auto.
rewrite <- H1.

specialize H0 with x L K B0.
apply H5; auto; [ | apply lc_SL; auto].
simpl in *; intros; unfold open_LF in *;
assert (exists x, x \notin L \u used_vars_te_LF (SL L0 M) \u
       from_list (map fst_ (map fst_ L0)) \u FV_L L0) by apply Fresh;
destruct H6; simpl in *; intros; apply property_3.
constructor; auto; constructor; apply lc_SL; auto; inversion LC; auto.
constructor.
intros; inversion H7; subst; [ | inversion H13];
rewrite subst_t_neutral_free_LF with (v:=x); auto.
replace ([N // fte x]([hyp_LF (fte x) // bte 0](SL L0 M))) with
  (SL ((x, A, N)::L0) [hyp_LF (fte x) // bte 0]M).

(*apply H5; auto.
rewrite SL_bte_subst; auto; [ | apply notin_Mem; auto].
rewrite SL_extend; auto; apply notin_Mem; auto.
(* appl *)
simpl in *; inversion LC; subst; apply IHHT1; auto; apply lc_SL; auto.
(* box *)
simpl in *; inversion LC; subst; apply property_3.
constructor; constructor; apply lc_SL; auto.
constructor.
intros; inversion H2; subst.
apply IHHT; auto; rew_concat in *; rewrite <- H; permut_simpl.
inversion H6.
(* unbox *)
simpl in *;
inversion LC; subst; apply IHHT; auto.
(* unbox-fetch *)
simpl in *;
inversion LC; subst; apply IHHT; auto;
rewrite <- H0; apply PPermut_concat_permut; rewrite <- H; PPermut_LF_simpl.
(* here *)
inversion LC; subst; simpl in *; intros.
apply H5; [ | apply lc_SL]; auto.
(* get-here *)
inversion LC; subst; simpl in *; intros.
apply H6; [ | apply lc_SL]; auto.
apply IHHT; auto.
rewrite <- H0.
apply PPermut_concat_permut; rewrite <- H; PPermut_LF_simpl.
(* letdia *)
unfold open_LF in *; simpl; inversion LC; subst.
apply reducible_letdia with A.
apply IHHT; auto.
intros.
assert (exists x, x\notin L) by apply Fresh.
destruct H4.
rewrite subst_t_neutral_free_LF with (v:=x); auto.
replace ([P // fte x]([hyp_LF (fte x) // bte 0](SL L0 N))) with
  (SL ((x, A, P)::L0) [hyp_LF (fte x) // bte 0]N).
apply H with (G':=((x,A)::nil)::G); auto.
skip. rew_map; rewrite <- H0; rew_concat; simpl; permut_simpl.
skip. skip.
rewrite SL_bte_subst; auto; [ | apply notin_Mem; auto].
rewrite SL_extend; auto.
skip. skip. skip. skip.
rewrite

Admitted.

Lemma less_trivial_2:
forall G Gamma M A,
  lc_t_LF M ->
  G |= Gamma |- M ::: A ->
  Red M A ->
  forall K B,
    ContTyping K A B ->
    WT (ContAppl K (here_LF M)).
Admitted.

Lemma non_trivial:
forall G Gamma M A,
  lc_t_LF M ->
  G |= Gamma |- M ::: A ->
  forall K B,
    ContTyping K A B ->
    WT (ContAppl K (here_LF M)).
Admitted.
*)

(* Theorem:
forall G Gamma M A,
  lc_t_LF M ->
  G |= Gamma |- M ::: A ->
  forall K B, ContTyping K A B -> WT (ContAppl K (here_LF M)).
intros G Gamma M A LC HT; induction HT; intros.
*)

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

Theorem WT_Lang:
forall G M A,
  emptyEquiv_LF G |= nil |- M ::: A ->
  WT M.
intros.
assert (lc_t_LF M).
  apply types_LF_lc_t_LF in H; auto.
assert (WT (ContAppl (IdK A) (here_LF M))).
apply less_trivial_1 with (L:=nil) (K:=IdK A) (B:=A) in H; auto.
rewrite SL_nil in H; auto.
rew_concat; rew_map; clear M A H H0;
induction G; simpl; rew_concat; auto.
intros; rewrite Mem_nil_eq in *; contradiction.
intros; rewrite Mem_nil_eq in *; contradiction.
constructor.
unfold RedCont; intros; simpl.
repeat apply WT_N_WT_here; apply property_1 with (A:=A); auto.
simpl in H1; apply WT_here; [constructor |]; auto; apply WT_here; auto;
constructor; constructor; auto.
Qed.
*)