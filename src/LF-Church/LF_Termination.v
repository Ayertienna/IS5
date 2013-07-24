Add LoadPath "..".
Add LoadPath "../..".
Require Import Shared.
Require Import LF_Semantics.

Open Scope is5_scope.
Open Scope permut_scope.

(* Find a variable in a list of potential substitutions *)
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

(* A list of potential substitutions contains no repetitions *)

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

(* Simultaneous substitution *)

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
| letdia_LF t M N => letdia_LF t (SL L M) (SL L N)
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

(* Termination *)

Definition WT M : Type := (* sigT (fun V => prod (value_LF V) (M |->* V)). *)
  { V | prod (value_LF V)  (M |->* V) }.
(*
Inductive WT: te_LF -> Type :=
| val_WT: forall V, value_LF V -> WT V
| step_WT: forall M,  sigT (fun V => prod (value_LF V) (steps_LF M V)) -> WT M
.
*)
Check WT.
Hint Resolve lc_t_step_LF lc_t_steps_LF.

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

Lemma steps_LF_val:
forall V V', 
  value_LF V ->
  V |->* V' ->
  V' = V.
intros. induction H0. auto.
apply value_no_step_LF in H0; auto; contradiction.
Qed.

Lemma steps_LF_val_steps:
forall M V,
  M |->* V -> value_LF V ->
  forall N,
    M |->* N ->
    N |->* V.
intros.
induction H1. auto.
destruct H. apply value_no_step_LF in H1; auto; contradiction.
apply step_LF_unique with (N:=y) in H; auto; subst.
apply IHclos_refl_trans_1n. auto.
Qed.

Theorem WT_step:
forall M M',
  WT M ->
  M |-> M' ->
  WT M'.
intros. unfold WT in *. 
destruct X as (V, X). exists V. destruct X as (Val, HT); split; auto.
induction HT.
  apply value_no_step_LF with (N:=M') in Val; contradiction.
apply step_LF_unique with (N:=M') in H0; subst; auto.
Qed.

Lemma WT_step_back:
forall M N,
  WT N ->
  M |-> N ->
  WT M.
intros. destruct X as (V, X); exists V; destruct X as (Val, HT); split; auto.
induction HT. econstructor; eauto. constructor.
constructor 2 with (y:=x); auto. constructor 2 with (y:=y); auto.
Qed.

Lemma WT_steps:
forall M N,
  M |->* N ->
  WT M -> WT N.
intros; destruct X as (V, (Val, HT)); exists V; split; auto;
apply steps_LF_val_steps with (M:=M); auto.
Qed.

Import Setoid.

Lemma WT_steps_back:
forall M N,
  M |->* N ->
  WT N -> WT M.
intros; destruct X as (V, (Val, HT)); exists V; split; auto.
transitivity N; auto.
Qed.

Lemma here_val:
forall M V,
  value_LF V -> steps_LF (here_LF M) V ->
  exists M', V = here_LF M'.
intros; remember (here_LF M) as M0; generalize dependent M.
induction H0; intros; subst.
eexists; eauto.
inversion H0; subst.
apply IHclos_refl_trans_1n with (M:=M'); auto.
Qed.

Lemma WT_here:
forall M,
  lc_t_LF M ->
  WT M ->
  WT (here_LF M).
intros. destruct X as (V, (Val, H1)).
exists (here_LF V); split; [constructor; auto | ].
induction H1. 
  constructor.
  constructor 2 with (here_LF y).
    constructor; auto.
    apply IHclos_refl_trans_1n; auto.
    apply lc_t_step_LF in H0; auto.
Qed.

Hint Resolve WT_step.

Inductive Cont :=
| IdK: ty -> Cont
| ConsU: Cont -> ty -> Cont
| ConsD: Cont -> ty -> te_LF -> ty -> ty -> Cont
| ConsA: Cont -> te_LF -> ty -> ty -> Cont
.

Fixpoint ContAppl (K: Cont) (M: te_LF) : te_LF :=
match K with
| IdK A => M
| ConsU K' A => ContAppl K' (unbox_LF M)
| ConsD K' t N A B => ContAppl K' (letdia_LF t M N)
| ConsA K' N A B => ContAppl K' (appl_LF M N)
end.

Notation " K '@' M " := (ContAppl K M) (at level 65).

Inductive ContLC: Cont -> Prop :=
| ContId_lc: forall A, ContLC (IdK A)
| ContU_lc: forall K A, ContLC K -> ContLC (ConsU K A)
| ContD_lc: forall K t N A B,
                 ContLC K -> lc_t_n_LF 1 N -> ContLC (ConsD K t N A B)
| ContA_lc: forall K N A B,
                 ContLC K -> lc_t_LF N -> ContLC (ConsA K N A B)
.

Definition WTC K := forall M, WT (K@M).

Lemma Step_KApplStep:
forall K M M',
  ContLC K ->
  lc_t_LF M ->
  M |-> M' ->
  K @ M |-> K @ M'.
induction K; intros; simpl in *; auto.
inversion H; subst;
assert (unbox_LF M |-> unbox_LF M')
   by (repeat constructor; auto);
apply IHK in H2; auto; constructor; auto.
inversion H; subst;
assert (letdia_LF t M t0 |-> letdia_LF t M' t0)
   by (repeat constructor; auto);
apply IHK in H2; auto; constructor; auto.
inversion H; subst;
assert (appl_LF M t |-> appl_LF M' t)
   by (repeat constructor; auto);
apply IHK in H2; auto; constructor; auto.
Qed.

Lemma steps_KApplSteps:
forall K M M',
  ContLC K ->
  lc_t_LF M ->
  M |->* M' ->
  (K @ M) |->* (K @ M').
intros; generalize dependent K; induction H1; intros.
constructor; apply Step_KApplStep; auto.
constructor 2 with (K @ y).
apply Step_KApplStep; auto.
apply IHclos_refl_trans_1n; auto.
apply lc_t_step_LF in H; auto.
Qed.

Fixpoint R M A {struct A} : Type :=
let Q M A := forall K,
               lc_t_LF M -> ContLC K -> RC K A ->
               WT (K @ M) in
match A with
| tvar => WT M
| A1 ---> A2 => prod (WT M)
                (forall N,
                   lc_t_LF N ->
                   Q N A1 ->
                   Q (appl_LF M N) A2)
| [*]A1 => prod (WT M) (forall K, RC K A1 -> WT (K @ (unbox_LF M)))
| <*>A1 => forall K, ContLC K ->
                     (forall V,
                        lc_t_LF V ->
                        R V A1 ->
                        WT (K @ (here_LF V))) ->
                     WT (K @ M)
end
with RC K A {struct A} : Type :=
let Q M A := forall K,
               lc_t_LF M -> ContLC K -> RC K A ->
               WT (K @ M) in
match A with
| tvar => forall V, lc_t_LF V -> WT V -> WT (K @ V)
| tbox A1 => forall V, lc_t_LF V ->
                       prod (WT V)
                        (forall K0, ContLC K0 ->
                                   RC K0 A1 ->
                                   WT (K0 @ (unbox_LF V))) ->
                       WT (K @ V)
| A1 ---> A2 => forall V, lc_t_LF V ->
                  prod (WT V)
                   (forall N,
                      lc_t_LF N ->
                      Q N A1 ->
                      Q (appl_LF V N) A2) ->
                  WT (K @ V)
| <*> A1 => forall V, lc_t_LF V ->
                       Q V A1 -> WT (K @ (here_LF V))
end.

Definition Q N A :=
    forall K, lc_t_LF N -> ContLC K -> RC K A -> WT (K @ N).

Hint Unfold Q.

(* This is required for the main theorem *)
Lemma RCIdK:
forall t, RC (IdK t) t.
induction t; simpl in *; intros; auto.
destruct X; auto.
destruct X; auto.
assert (WT ((IdK t) @ V)) by (apply X; auto; constructor).
apply WT_here; auto.
Qed.

Lemma steps_letdia:
forall M M', steps_LF M M' ->
forall N t, lc_t_LF M -> lc_t_n_LF 1 N ->
            steps_LF (letdia_LF t M N) (letdia_LF t M' N).
intros M M' H; induction H; intros; simpl in *.
constructor; constructor; auto.
constructor 2 with (y:=letdia_LF t y N); auto.
constructor; auto. 
apply IHclos_refl_trans_1n; auto. 
apply lc_t_step_LF in H; auto.
Qed.

Lemma steps_here:
forall M M', steps_LF M M' -> lc_t_LF M -> steps_LF (here_LF M) (here_LF M').
intros; induction H; simpl in *.
repeat constructor; auto.
constructor 2 with (here_LF y). constructor; auto.
apply IHclos_refl_trans_1n; auto. 
apply lc_t_step_LF in H; auto.
Qed.

Lemma Q_SL_hyp:
forall L G Gamma v A,
  OkL L nil ->
  concat (Gamma::G) *=* map fst_ L ->
  (forall a b c, Mem (a, b, c) L -> Q c b) ->
  G |= Gamma |- hyp_LF (fte v) ::: A ->
  Q (SL L (hyp_LF (fte v))) A.
intros. 
assert (Mem (v, A) (map fst_ L)).
  apply Mem_permut with (l:=concat (Gamma::G)); auto.
  rew_concat; rewrite Mem_app_or_eq; left; auto.
  inversion H1; subst; auto.
apply Mem_find_var_type in H2; auto. destruct H2.
simpl; rewrite e.
apply X with v.
apply find_var_Mem; auto.
Qed.

Lemma Fresh':
forall (L: fset var), {w0 : var | w0 \notin L}.
intro;
exists (var_gen L);
apply var_gen_spec.
Qed.

Theorem main_theorem:
forall G Gamma M A,
  lc_t_LF M ->
  G |= Gamma |- M ::: A ->
 forall L,
    OkL L nil ->
    concat(Gamma::G) *=* map fst_ L ->
    (forall a b c, Mem (a,b,c) L -> lc_t_LF c) ->
    (forall a b c, Mem (a,b,c) L -> Q c b) ->
    forall K,
      ContLC K ->
      RC K A ->
      WT (K @ (SL L M)).
intros G Gamma M A LC HT. 
(* We cannot do induction on HT, as it is not in Type *)
Admitted.
(*
induction HT;
intros; simpl in *.
(* hyp *)
assert (lc_t_LF (SL L (hyp_LF (fte v)))) by
  (apply lc_SL; auto; constructor);
simpl in *;
assert (Q (SL L (hyp_LF (fte v))) A);
[apply Q_SL_hyp with G Gamma; auto; constructor | apply H7]; auto.
(* lam *)
autounfold in *; inversion LC; subst; apply H6; simpl;
[ constructor; apply lc_SL; auto |];
split; intros; [repeat constructor | ];
apply WT_step_back with (N:=ContAppl K0 (((SL L0 M) ^t^ N)));
[ unfold open_LF in *;
  assert (exists x, x \notin L \u used_vars_te_LF (SL L0 M) \u FV_L L0
       \u  from_list (map fst_ (map fst_ L0))  \u from_list nil)
  as HF by apply Fresh; destruct HF | ];
[ | apply Step_KApplStep; auto; repeat constructor; auto; apply lc_SL; auto];
rewrite subst_t_neutral_free_LF with (v:=x); auto;
rewrite SL_bte_subst; auto;
[rewrite <- SL_extend with (A:=A) | apply notin_Mem]; auto;
[|apply notin_Mem]; auto;
apply H0; auto.
  apply lc_t_subst_t_LF_bound; [constructor | inversion LC; auto].
  constructor; [ rewrite Mem_nil_eq | apply OkL_fresh]; auto.
  rew_map in *; simpl; rewrite <-  H2; rew_concat; auto.
  intros; rewrite Mem_cons_eq in *; destruct H14; eauto;
  inversion H14; subst; auto.
  intros; rewrite Mem_cons_eq in *; destruct H14; eauto;
  inversion H14; subst; auto.
(* appl *)
inversion LC; subst;
assert (WT ((ConsA K (SL L N) A B) @ (SL L M))); [ | simpl; auto];
apply IHHT1; auto; [constructor; auto; apply lc_SL; auto | ];
autounfold in *; simpl; intros; destruct H6; apply H7; auto;
repeat constructor; auto; apply lc_SL; auto.
(* box *)
inversion LC; subst;
apply H4; [constructor; apply lc_SL; auto | ];
split; [repeat constructor | intros].
apply WT_step_back with (K0 @ (SL L M)).
  apply IHHT; auto; rewrite <- H0; rew_concat; permut_simpl.
  apply Step_KApplStep; auto; repeat constructor; apply lc_SL; auto.
(* unbox *)
inversion LC; subst;
assert (WT ((ConsU K A) @ (SL L M))); [ | simpl; auto];
apply IHHT; auto; [ constructor; auto | intros ];
destruct H6; simpl; apply H8; auto.
(* unbox-fetch *)
inversion LC; subst;
assert (WT ((ConsU K A) @ (SL L M))); [ | simpl; auto];
apply IHHT; auto; [ | constructor; auto | intros ];
[ | destruct H7; simpl; apply H9; auto];
rewrite <- H1; rew_concat; permut_simpl;
replace (Gamma ++ concat G) with (concat (Gamma::G)) by (rew_concat; auto);
apply PPermut_concat_permut; rewrite <- H; PPermut_LF_simpl.
(* here *)
inversion LC; subst; apply H4; [apply lc_SL; auto | intros]; apply IHHT; auto.
(* get-here *)
inversion LC; subst.
apply H5; [apply lc_SL; auto | ]; simpl; intros;
apply IHHT; auto.
rew_map in *; simpl; rewrite <-  H1; rew_concat; auto; permut_simpl;
replace (Gamma ++ concat G) with (concat (Gamma::G)) by (rew_concat; auto);
apply PPermut_concat_permut; rewrite <- H; PPermut_LF_simpl.
(* letdia *)
inversion LC; subst;
assert (WT ((ConsD K (<*>A) (SL L0 N) A B) @ (SL L0 M))); [ | simpl; auto];
apply IHHT; auto; [constructor; auto; apply lc_SL; auto | ]; intros; simpl in *.
assert (WT ((IdK A) @ V)).
  apply H7; auto. constructor. apply RCIdK.
simpl in H8; inversion H8; subst.
  (* value *)
  apply WT_step_back with (K @ ((SL L0 N) ^t^ V));
  [ | apply Step_KApplStep; auto; repeat constructor; auto; apply lc_SL; auto].
  unfold open_LF in *;
  assert (exists x, x \notin L \u used_vars_te_LF (SL L0 M) \u FV_L L0
       \u  used_vars_te_LF (SL L0 N)
       \u  from_list (map fst_ (map fst_ L0))  \u from_list nil)
  as HF by apply Fresh; destruct HF.
  rewrite subst_t_neutral_free_LF with (v:=x); auto;
  rewrite SL_bte_subst; auto;
  [rewrite <- SL_extend with (A:=A) | apply notin_Mem]; auto;
  [|apply notin_Mem]; auto.
  apply H with (G':=((x,A)::nil) :: G); auto.
    apply lc_t_subst_t_LF_bound; [constructor | inversion LC; auto].
    constructor; [ rewrite Mem_nil_eq | apply OkL_fresh]; auto.
    rew_map in *; simpl; rewrite <-  H1; rew_concat; auto;
    replace (Gamma ++ concat G) with (concat (Gamma::G)) by (rew_concat; auto);
    permut_simpl.
    intros; rewrite Mem_cons_eq in *; destruct H13; auto;
    inversion H13; subst; eauto.
    intros; rewrite Mem_cons_eq in *; destruct H13; auto;
    inversion H13; subst; eauto.
  (* step *)
  destruct H10 as (V', (H12, H13)).
  apply WT_steps_back with (K @ letdia_LF (<*>A) (here_LF V') (SL L0 N)).
    apply steps_KApplSteps; auto.
      repeat constructor; auto; apply lc_SL; auto.
      apply steps_letdia; [apply steps_here | |]; auto; repeat constructor;
      auto; apply lc_SL; auto.
  assert (lc_t_LF V') by (apply lc_t_steps_LF in H13; auto);
  apply WT_step_back with (K @ ((SL L0 N) ^t^ V'));
  [ | apply Step_KApplStep; auto; repeat constructor; auto; apply lc_SL; auto];
  unfold open_LF in *;
  assert (exists x, x \notin L \u used_vars_te_LF (SL L0 M) \u FV_L L0
       \u  used_vars_te_LF (SL L0 N)
       \u  from_list (map fst_ (map fst_ L0))  \u from_list nil)
  as HF by apply Fresh; destruct HF;
  rewrite subst_t_neutral_free_LF with (v:=x); auto;
  rewrite SL_bte_subst; auto;
  [rewrite <- SL_extend with (A:=A) | apply notin_Mem]; auto;
  [|apply notin_Mem]; auto.
  apply H with (G':=((x,A)::nil) :: G); auto.
    apply lc_t_subst_t_LF_bound; [constructor | inversion LC; auto].
    constructor; [ rewrite Mem_nil_eq | apply OkL_fresh]; auto.
    rew_map in *; simpl; rewrite <-  H1; rew_concat; auto;
    replace (Gamma ++ concat G) with (concat (Gamma::G)) by (rew_concat; auto);
    permut_simpl.
    intros; rewrite Mem_cons_eq in *; destruct H15; auto;
    inversion H15; subst; eauto.
    intros; rewrite Mem_cons_eq in *; destruct H15; auto;
    inversion H15; subst; eauto. autounfold. intros.
    apply WT_steps with (M:=K0 @ V).
      apply steps_KApplSteps; auto. apply H7; auto.
(* letdia-get *)
inversion LC; subst;
assert (WT ((ConsD K (<*> A) (SL L0 N) A B) @ (SL L0 M))); [ | simpl; auto];
apply IHHT; auto; [ |constructor; auto; apply lc_SL; auto | ];
[rewrite <-  H2; apply PPermut_concat_permut; rewrite <- H0; PPermut_LF_simpl|
 intros; simpl in *];
assert (WT ((IdK A) @ V)).
  apply H8; auto; [constructor | apply RCIdK].
simpl in H9; inversion H9; subst.
  (* value *)
  apply WT_step_back with (K @ ((SL L0 N) ^t^ V));
  [ | apply Step_KApplStep; auto; repeat constructor; auto; apply lc_SL; auto].
  unfold open_LF in *;
  assert (exists x, x \notin L \u used_vars_te_LF (SL L0 M) \u FV_L L0
       \u  used_vars_te_LF (SL L0 N)
       \u  from_list (map fst_ (map fst_ L0))  \u from_list nil)
  as HF by apply Fresh; destruct HF.
  rewrite subst_t_neutral_free_LF with (v:=x); auto;
  rewrite SL_bte_subst; auto;
  [rewrite <- SL_extend with (A:=A) | apply notin_Mem]; auto;
  [|apply notin_Mem]; auto.
  apply H; auto.
    apply lc_t_subst_t_LF_bound; [constructor | inversion LC; auto].
    constructor; [ rewrite Mem_nil_eq | apply OkL_fresh]; auto.
    rew_map in *; simpl; rewrite <-  H2; rew_concat; auto; permut_simpl;
    replace (concat G ++ Gamma) with (concat (G & Gamma)) by (rew_concat; auto);
    apply PPermut_concat_permut; auto.
    intros; rewrite Mem_cons_eq in *; destruct H14; auto;
    inversion H14; subst; eauto.
    intros; rewrite Mem_cons_eq in *; destruct H14; auto;
    inversion H14; subst; eauto.
  (* step *)
  destruct H11 as (V', (H13, H14)).
  apply WT_steps_back with (K @ letdia_LF (<*>A) (here_LF V') (SL L0 N)).
    apply steps_KApplSteps; auto.
      repeat constructor; auto; apply lc_SL; auto.
      apply steps_letdia; [apply steps_here | |]; auto; repeat constructor;
      auto; apply lc_SL; auto.
  assert (lc_t_LF V') by (apply lc_t_steps_LF in H14; auto);
  apply WT_step_back with (K @ ((SL L0 N) ^t^ V'));
  [ | apply Step_KApplStep; auto; repeat constructor; auto; apply lc_SL; auto];
  unfold open_LF in *;
  assert (exists x, x \notin L \u used_vars_te_LF (SL L0 M) \u FV_L L0
       \u  used_vars_te_LF (SL L0 N)
       \u  from_list (map fst_ (map fst_ L0))  \u from_list nil)
  as HF by apply Fresh; destruct HF;
  rewrite subst_t_neutral_free_LF with (v:=x); auto;
  rewrite SL_bte_subst; auto;
  [rewrite <- SL_extend with (A:=A) | apply notin_Mem]; auto;
  [|apply notin_Mem]; auto.
  apply H; auto.
    apply lc_t_subst_t_LF_bound; [constructor | inversion LC; auto].
    constructor; [ rewrite Mem_nil_eq | apply OkL_fresh]; auto.
    rew_map in *; simpl; rewrite <-  H2; rew_concat; auto; permut_simpl;
    replace (concat G ++ Gamma) with (concat (G & Gamma)) by (rew_concat; auto);
    apply PPermut_concat_permut; auto.
    intros; rewrite Mem_cons_eq in *; destruct H16; auto;
    inversion H16; subst; eauto.
    intros; rewrite Mem_cons_eq in *; destruct H16; auto;
    inversion H16; subst; eauto. autounfold. intros.
    apply WT_steps with (M:=K0 @ V).
      apply steps_KApplSteps; auto. apply H8; auto.
Qed.
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
assert (WT (ContAppl (IdK A) M)); [ | simpl in *; auto];
apply main_theorem with (L:=nil) (K:=IdK A) in H; auto.
rewrite SL_nil in H; auto.
constructor.
rew_concat; rew_map; clear M A H H0;
induction G; simpl; rew_concat; auto.
intros; rewrite Mem_nil_eq in *; contradiction.
intros; rewrite Mem_nil_eq in *; contradiction.
constructor.
apply RCIdK.
Qed.

Extract Inductive bool => "bool" [ "true" "false" ].
Extract Inductive list => "list" [ "[]" "(::)" ].
Extract Inductive prod => "(*)"  [ "(,)" ].
Extract Inductive sumbool => "bool" [ "true" "false" ].

Extract Inductive nat => "int"
  [ "0" "(fun x → x + 1)" ]
  "(fun zero succ n →
      if n=0 then zero () else succ (n-1))".
Extract Constant plus => "( + )".

Extract Constant eq_var_dec => "( = )".
Extraction Language Haskell.
Extraction "termination_LF" WT_Lang.